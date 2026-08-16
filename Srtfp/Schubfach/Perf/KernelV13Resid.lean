/- KernelV13, stage 0: band peelings, x10 residues, and `sFromP_floor`.
   Split out so the flip3 spec proof gets a process of its own. -/

/- KernelV13, stage 1: the flip3 kernel and its spec proof.
   Split from KernelV13.lean so the two heartbeat-heavy correctness
   proofs elaborate in separate processes (elaboration memory
   accumulates across a module's declarations on ≥4.32 toolchains). -/

/- v13 — `s` from the boundary product (Giulietti §9 at 128 bits).

   The kernel already computes `P = 4m·g′` (`g′ =` pow10 entry for
   `-(k+1)`) for the flipped interval tests. Since
   `s = ⌊m·2^q·10^(-k)⌋ = ⌊(10m)·g′/2^w⌋` for `w = h′ - q` (the same
   in-window shift), the digit count comes from `5P = P + (P <<< 2)`
   by extracting the top limb — no 192-bit table, no 5-limb multiply.

   Soundness: the existing certified far bound (`band{1,2}_far`, the
   §9.7 sweep at `a = 71`) gives the R20 residue at multiplicand `10m`
   for shift `w ≥ 128`; the reachable window is `w ∈ [127, 131]` with
   `w = 127` only on irregular bands (excluded by the runtime guard,
   falling back to the packed path). -/

import Srtfp.Schubfach.Perf.KernelSupport
import Srtfp.Schubfach.Perf.KernelV13WReg
import Srtfp.Tactics

namespace Srtfp.Schubfach

/-! ## Multiplicand-decoupled band peelings

`residueR20Cond_band{1,2}_of_{twoAdic,fiveAdic}` couple the orbit
multiplicand and the condition multiplicand; the `x10` forms need them
split (`orbit at m`, `condition at 10m`). Copies with a free `m'`. -/

theorem residueR20Cond_band2_of_fiveAdic'
    (m m' q k s : Nat)
    (hkle : k ≤ q)
    (hDist : (5 ^ k - (m * 2 ^ (q - k)) % 5 ^ k) * 2 ^ s
              ≥ m' * 5 ^ k) :
    residueR20Cond m' (10 ^ k) s (m * 2 ^ q) := by
  unfold residueR20Cond
  set j := q - k with hj
  have h10 : (10 : Nat) ^ k = 2 ^ k * 5 ^ k := by
    rw [show (10 : Nat) = 2 * 5 from rfl, Nat.mul_pow]
  have hsplit : (2 : Nat) ^ q = 2 ^ k * 2 ^ j := by
    rw [hj, ← Nat.pow_add]; congr 1; omega
  have hN : m * 2 ^ q = 2 ^ k * (m * 2 ^ j) := by rw [hsplit]; grind
  have hmod : (m * 2 ^ q) % 10 ^ k = 2 ^ k * ((m * 2 ^ j) % 5 ^ k) := by
    rw [hN, h10, Nat.mul_mod_mul_left (2 ^ k) (m * 2 ^ j) (5 ^ k)]
  set r := (m * 2 ^ j) % 5 ^ k with hr
  have hgap : 10 ^ k - (m * 2 ^ q) % 10 ^ k = 2 ^ k * (5 ^ k - r) := by
    rw [hmod, h10, Nat.mul_sub]
  rw [hgap, h10]
  have hcancel : m' * (2 ^ k * 5 ^ k) = 2 ^ k * (m' * 5 ^ k) := by grind
  have hRHS : 2 ^ k * (5 ^ k - r) * 2 ^ s = 2 ^ k * ((5 ^ k - r) * 2 ^ s) := by grind
  rw [hcancel, hRHS]
  apply Nat.mul_le_mul_left
  rw [Nat.mul_comm (5 ^ k - r) (2 ^ s)] at hDist ⊢
  grind

theorem residueR20Cond_band1_of_twoAdic'
    (m m' qNeg kNeg s : Nat)
    (hkle : kNeg ≤ qNeg)
    (hDist : (2 ^ (qNeg - kNeg) - (m * 5 ^ kNeg) % 2 ^ (qNeg - kNeg)) * 2 ^ s
              ≥ m' * 2 ^ (qNeg - kNeg)) :
    residueR20Cond m' (2 ^ qNeg) s (m * 10 ^ kNeg) := by
  unfold residueR20Cond
  set e := qNeg - kNeg with he
  have h10 : (10 : Nat) ^ kNeg = 2 ^ kNeg * 5 ^ kNeg := by
    rw [show (10 : Nat) = 2 * 5 from rfl, Nat.mul_pow]
  have hsplit : (2 : Nat) ^ qNeg = 2 ^ kNeg * 2 ^ e := by
    rw [he, ← Nat.pow_add]; congr 1; omega
  have hN : m * 10 ^ kNeg = (m * 5 ^ kNeg) * 2 ^ kNeg := by rw [h10]; grind
  have hmod : (m * 10 ^ kNeg) % 2 ^ qNeg = 2 ^ kNeg * ((m * 5 ^ kNeg) % 2 ^ e) := by
    rw [hN, hsplit, Nat.mul_comm (m * 5 ^ kNeg) (2 ^ kNeg),
        Nat.mul_mod_mul_left (2 ^ kNeg) (m * 5 ^ kNeg) (2 ^ e)]
  set r := (m * 5 ^ kNeg) % 2 ^ e with hr
  have hgap : 2 ^ qNeg - (m * 10 ^ kNeg) % 2 ^ qNeg = 2 ^ kNeg * (2 ^ e - r) := by
    rw [hmod, hsplit, Nat.mul_sub]
  rw [hgap, hsplit]
  have hcancel : m' * (2 ^ kNeg * 2 ^ e) = 2 ^ kNeg * (m' * 2 ^ e) := by grind
  have hRHS : 2 ^ kNeg * (2 ^ e - r) * 2 ^ s = 2 ^ kNeg * ((2 ^ e - r) * 2 ^ s) := by grind
  rw [hcancel, hRHS]
  apply Nat.mul_le_mul_left
  rw [Nat.mul_comm (2 ^ e - r) (2 ^ s)] at hDist ⊢
  grind

/-! ## The ×10 band residues at shift `≥ 128` -/

open Srtfp.Schubfach.R20Sweep in
theorem residueR20Cond_band2_x10
    (m q kNat s : Nat) (hq : q ≤ 971)
    (hk : kNat = (floorLog10Pow2 q).toNat ∨ kNat = (floorLog10ThreeQuartersPow2 q).toNat)
    (hkq : kNat ≤ q) (hm : 0 < m) (hm53 : m < 2 ^ 53)
    (hsl : 10 * m * 2 ^ 71 ≤ 2 ^ s) (hsl5 : 10 * m * 5 ^ 30 ≤ 2 ^ s) :
    residueR20Cond (10 * m) (10 ^ kNat) s (m * 2 ^ q) := by
  apply residueR20Cond_band2_of_fiveAdic' m (10 * m) q kNat s hkq
  have hgap1 : 1 ≤ 5 ^ kNat - (m * 2 ^ (q - kNat)) % 5 ^ kNat := by
    have := Nat.mod_lt (m * 2 ^ (q - kNat)) (show 0 < 5 ^ kNat from Nat.pow_pos (by grind))
    omega
  rcases Nat.lt_or_ge kNat 31 with hk30 | hk31
  · -- elementary: 10m·5^k ≤ 10m·5^30 ≤ 2^s ≤ (gap)·2^s
    calc 10 * m * 5 ^ kNat
        ≤ 10 * m * 5 ^ 30 := Nat.mul_le_mul_left _
            (Nat.pow_le_pow_right (by grind) (by omega))
      _ ≤ 2 ^ s := hsl5
      _ = 1 * 2 ^ s := (Nat.one_mul _).symm
      _ ≤ (5 ^ kNat - (m * 2 ^ (q - kNat)) % 5 ^ kNat) * 2 ^ s :=
          Nat.mul_le_mul_right _ hgap1
  · -- sweep: far at a = 71, slack 10m·2^71 ≤ 2^128 ≤ 2^s
    have hFar := band2_far m q hq kNat hk hk31 hkq hm hm53
    unfold farFromMultipleBelow at hFar
    calc 10 * m * 5 ^ kNat
        ≤ 10 * m * ((5 ^ kNat - (m * 2 ^ (q - kNat)) % 5 ^ kNat) * 2 ^ 71) :=
          Nat.mul_le_mul_left _ hFar
      _ = (5 ^ kNat - (m * 2 ^ (q - kNat)) % 5 ^ kNat) * (10 * m * 2 ^ 71) := by grind
      _ ≤ (5 ^ kNat - (m * 2 ^ (q - kNat)) % 5 ^ kNat) * 2 ^ s :=
          Nat.mul_le_mul_left _ hsl

open Srtfp.Schubfach.R20Sweep in
theorem residueR20Cond_band1_x10
    (m qNeg kNeg s : Nat) (h1 : 1 ≤ qNeg) (hq : qNeg ≤ 1074)
    (hk : kNeg = (-(floorLog10Pow2 (-(qNeg : Int)))).toNat
          ∨ kNeg = (-(floorLog10ThreeQuartersPow2 (-(qNeg : Int)))).toNat)
    (hkq : kNeg ≤ qNeg) (hm : 0 < m) (hm53 : m < 2 ^ 53)
    (hsl : 10 * m * 2 ^ 71 ≤ 2 ^ s) :
    residueR20Cond (10 * m) (2 ^ qNeg) s (m * 10 ^ kNeg) := by
  apply residueR20Cond_band1_of_twoAdic' m (10 * m) qNeg kNeg s hkq
  have hgap1 : 1 ≤ 2 ^ (qNeg - kNeg) - (m * 5 ^ kNeg) % 2 ^ (qNeg - kNeg) := by
    have := Nat.mod_lt (m * 5 ^ kNeg) (show 0 < 2 ^ (qNeg - kNeg) from Nat.two_pow_pos _)
    omega
  rcases Nat.lt_or_ge (qNeg - kNeg) 72 with he71 | he72
  · calc 10 * m * 2 ^ (qNeg - kNeg)
        ≤ 10 * m * 2 ^ 71 := Nat.mul_le_mul_left _
            (Nat.pow_le_pow_right (by grind) (by omega))
      _ ≤ 2 ^ s := hsl
      _ = 1 * 2 ^ s := (Nat.one_mul _).symm
      _ ≤ (2 ^ (qNeg - kNeg) - (m * 5 ^ kNeg) % 2 ^ (qNeg - kNeg)) * 2 ^ s :=
          Nat.mul_le_mul_right _ hgap1
  · have hFar := band1_far m qNeg kNeg h1 hq hk he72 hkq hm hm53
    unfold farFromMultipleBelow at hFar
    calc 10 * m * 2 ^ (qNeg - kNeg)
        ≤ 10 * m * ((2 ^ (qNeg - kNeg) - (m * 5 ^ kNeg) % 2 ^ (qNeg - kNeg)) * 2 ^ 71) :=
          Nat.mul_le_mul_left _ hFar
      _ = (2 ^ (qNeg - kNeg) - (m * 5 ^ kNeg) % 2 ^ (qNeg - kNeg)) * (10 * m * 2 ^ 71) := by
          grind
      _ ≤ (2 ^ (qNeg - kNeg) - (m * 5 ^ kNeg) % 2 ^ (qNeg - kNeg)) * 2 ^ s :=
          Nat.mul_le_mul_left _ hsl

set_option maxRecDepth 4000 in
/-- ×10 mirror of `residueR20Cond_decode_binary64`: the residue at
    condition multiplicand `10·m` for shift `s ≥ 128`, over the same
    `B`/`N` quantities at `k = kOfMQ m q`. -/
theorem residueR20Cond_decode_binary64_x10
    (m : Nat) (q : Int) (s : Nat)
    (hm : 0 < m) (hm53 : m < 2 ^ 53)
    (hq_lo : -1074 ≤ q) (hq_hi : q ≤ 971)
    (hsl : 10 * m * 2 ^ 71 ≤ 2 ^ s) (hsl5 : 10 * m * 5 ^ 30 ≤ 2 ^ s) :
    residueR20Cond (10 * m)
      (2 ^ (if q < 0 then (-q).toNat else 0) *
        10 ^ (if kOfMQ m q ≥ 0 then (kOfMQ m q).toNat else 0))
      s
      (m * 2 ^ (if q ≥ 0 then q.toNat else 0) *
        10 ^ (if kOfMQ m q < 0 then (-(kOfMQ m q)).toNat else 0)) := by
  set k : Int := kOfMQ m q with hk_def
  by_cases hq0 : 0 ≤ q
  · have hq_not : ¬ q < 0 := by omega
    rw [if_neg hq_not, if_pos hq0]
    by_cases hk0 : 0 ≤ k
    · have hk_not : ¬ k < 0 := by omega
      have hk_ge : k ≥ 0 := hk0
      rw [if_pos hk_ge, if_neg hk_not]
      simp only [Nat.pow_zero, Nat.mul_one, Nat.one_mul]
      have hqcast : ((q.toNat : Nat) : Int) = q := Int.toNat_of_nonneg hq0
      have hkq : k.toNat ≤ q.toNat := by
        have := kOfMQ_le_self m q hq0
        rw [← hk_def] at this; omega
      have hcand := kOfMQ_toNat_candidate2 m q.toNat
      rw [show kOfMQ m (↑q.toNat) = k by rw [hk_def, hqcast]] at hcand
      have hband := residueR20Cond_band2_x10 m q.toNat k.toNat s
                      (by omega) hcand hkq hm hm53 hsl hsl5
      simpa using hband
    · push_neg at hk0
      have hk_lt : k < 0 := hk0
      have hk_ge_not : ¬ k ≥ 0 := by omega
      rw [if_neg hk_ge_not, if_pos hk_lt]
      simp only [Nat.pow_zero, Nat.one_mul]
      apply residueR20Cond_of_safe (10 * m) 1 s _ (by grind)
      rw [Nat.mul_one]
      calc 10 * m = 10 * m * 1 := by grind
        _ ≤ 10 * m * 2 ^ 71 := Nat.mul_le_mul_left _ (Nat.one_le_two_pow)
        _ ≤ 2 ^ s := hsl
  · push_neg at hq0
    have hq_lt : q < 0 := hq0
    have hq_ge_not : ¬ q ≥ 0 := by omega
    have hk_lt : k < 0 := by rw [hk_def]; exact kOfMQ_neg_of_neg m q hq_lt
    have hk_ge_not : ¬ k ≥ 0 := by omega
    rw [if_pos hq_lt, if_neg hq_ge_not, if_neg hk_ge_not, if_pos hk_lt]
    simp only [Nat.pow_zero, Nat.mul_one]
    set qNeg : Nat := (-q).toNat with hqNeg_def
    set kNeg : Nat := (-k).toNat with hkNeg_def
    have hkq : kNeg ≤ qNeg := by
      have hle := self_le_kOfMQ m q hq_lt
      rw [← hk_def] at hle
      rw [hqNeg_def, hkNeg_def]; omega
    have hcand := kOfMQ_neg_toNat_candidate1 m q
    rw [← hk_def] at hcand
    have hcand' :
        kNeg = (-(floorLog10Pow2 q)).toNat ∨
        kNeg = (-(floorLog10ThreeQuartersPow2 q)).toNat := by
      rw [hkNeg_def]; exact hcand
    have hqNeg_lo : 1 ≤ qNeg := by rw [hqNeg_def]; omega
    have hqNeg_hi : qNeg ≤ 1074 := by rw [hqNeg_def]; omega
    have hq_eq : (-(qNeg : Int)) = q := by rw [hqNeg_def]; omega
    have hcand'' :
        kNeg = (-(floorLog10Pow2 (-(qNeg : Int)))).toNat
          ∨ kNeg = (-(floorLog10ThreeQuartersPow2 (-(qNeg : Int)))).toNat := by
      rw [hq_eq]; exact hcand'
    exact residueR20Cond_band1_x10 m qNeg kNeg s
            hqNeg_lo hqNeg_hi hcand'' hkq hm hm53 hsl

/-- `(10M − 10N mod 10M)·2^s ≥ C·10M` from the un-scaled bound. -/
theorem resid_mul10 (M N C s : Nat)
    (h : (M - N % M) * 2 ^ s ≥ C * M) :
    ((10 * M) - (10 * N) % (10 * M)) * 2 ^ s ≥ C * (10 * M) := by
  rw [Nat.mul_mod_mul_left, ← Nat.mul_sub]
  calc C * (10 * M) = 10 * (C * M) := by grind
    _ ≤ 10 * ((M - N % M) * 2 ^ s) := Nat.mul_le_mul_left _ h
    _ = 10 * (M - N % M) * 2 ^ s := by grind

/-- Reassociation: the ×10 residue over the `k`-quantities equals the
    residue at the `(k+1)`-quantities with numerator multiplicand `10m`
    (`N′/B′ = N/B` as rationals; the factor 10 moves across). -/
theorem residueR20Cond_x10_reassoc
    (m : Nat) (q k : Int) (s : Nat)
    (h : residueR20Cond (10 * m)
      (2 ^ (if q < 0 then (-q).toNat else 0) *
        10 ^ (if k ≥ 0 then k.toNat else 0))
      s
      (m * 2 ^ (if q ≥ 0 then q.toNat else 0) *
        10 ^ (if k < 0 then (-k).toNat else 0))) :
    residueR20Cond (10 * m)
      (2 ^ (if q < 0 then (-q).toNat else 0) *
        10 ^ (if k + 1 ≥ 0 then (k + 1).toNat else 0))
      s
      (10 * m * 2 ^ (if q ≥ 0 then q.toNat else 0) *
        10 ^ (if k + 1 < 0 then (-(k + 1)).toNat else 0)) := by
  unfold residueR20Cond at h ⊢
  set Q : Nat := 2 ^ (if q < 0 then (-q).toNat else 0) with hQ
  set P : Nat := 2 ^ (if q ≥ 0 then q.toNat else 0) with hP
  by_cases hk0 : k ≥ 0
  · have e1 : (if k ≥ 0 then k.toNat else 0) = k.toNat := if_pos hk0
    have e2 : (if k < 0 then (-k).toNat else 0) = 0 := if_neg (by omega)
    have e3 : (if k + 1 ≥ 0 then (k + 1).toNat else 0) = k.toNat + 1 := by
      rw [if_pos (by omega : k + 1 ≥ 0)]; omega
    have e4 : (if k + 1 < 0 then (-(k + 1)).toNat else 0) = 0 := if_neg (by omega)
    rw [e1, e2, Nat.pow_zero, Nat.mul_one] at h
    rw [e3, e4, Nat.pow_zero, Nat.mul_one, Nat.pow_succ]
    have hB10 : Q * (10 ^ k.toNat * 10) = 10 * (Q * 10 ^ k.toNat) := by grind
    have hN10 : 10 * m * P = 10 * (m * P) := by grind
    rw [hB10, hN10]
    exact resid_mul10 _ _ _ _ h
  · push_neg at hk0
    have e1 : (if k ≥ 0 then k.toNat else 0) = 0 := if_neg (by omega)
    have e2 : (if k < 0 then (-k).toNat else 0) = (-k).toNat := if_pos (by omega)
    rw [e1, e2, Nat.pow_zero, Nat.mul_one] at h
    by_cases hk1 : k + 1 ≥ 0
    · have e3 : (if k + 1 ≥ 0 then (k + 1).toNat else 0) = 0 := by
        rw [if_pos hk1]; omega
      have e4 : (if k + 1 < 0 then (-(k + 1)).toNat else 0) = 0 := if_neg (by omega)
      rw [e3, e4, Nat.pow_zero, Nat.mul_one, Nat.mul_one]
      have hknn : (-k).toNat = 1 := by omega
      rw [hknn] at h
      have hre : m * P * 10 ^ 1 = 10 * m * P := by grind
      rw [hre] at h
      exact h
    · push_neg at hk1
      have e3 : (if k + 1 ≥ 0 then (k + 1).toNat else 0) = 0 := if_neg (by omega)
      have e4 : (if k + 1 < 0 then (-(k + 1)).toNat else 0) = (-(k + 1)).toNat :=
        if_pos (by omega)
      rw [e3, e4, Nat.pow_zero, Nat.mul_one]
      have hpow : (-k).toNat = (-(k + 1)).toNat + 1 := by omega
      rw [hpow, Nat.pow_succ] at h
      have hre : m * P * (10 ^ (-(k + 1)).toNat * 10)
          = 10 * m * P * 10 ^ (-(k + 1)).toNat := by grind
      rw [hre] at h
      exact h

/-- The `(k+1)`-quantities quotient with numerator multiplicand `10m`
    IS `shiftedSig m q k` (both factors of 10 cancel). -/
theorem shiftedSig_x10_succ (m : Nat) (q k : Int) :
    (10 * m * 2 ^ (if q ≥ 0 then q.toNat else 0)
        * 10 ^ (if k + 1 < 0 then (-(k + 1)).toNat else 0))
      / (2 ^ (if q < 0 then (-q).toNat else 0)
        * 10 ^ (if k + 1 ≥ 0 then (k + 1).toNat else 0))
    = shiftedSig m q k := by
  unfold shiftedSig
  simp only []
  set P : Nat := 2 ^ (if q ≥ 0 then q.toNat else 0) with hP
  set Q : Nat := 2 ^ (if q < 0 then (-q).toNat else 0) with hQ
  by_cases hk0 : k ≥ 0
  · rw [if_neg (show ¬ k + 1 < 0 by omega), if_pos (show k + 1 ≥ 0 by omega),
        if_pos hk0, if_neg (show ¬ k < 0 by omega)]
    rw [show (k + 1).toNat = k.toNat + 1 from by omega, Nat.pow_zero, Nat.pow_succ,
        Nat.mul_one]
    rw [show 10 * m * P = 10 * (m * P) from by grind,
        show Q * (10 ^ k.toNat * 10) = 10 * (Q * 10 ^ k.toNat) from by grind]
    rw [Nat.mul_div_mul_left _ _ (by grind : 0 < 10)]
    rw [Nat.mul_one]
  · push_neg at hk0
    by_cases hk1 : k + 1 ≥ 0
    · rw [if_neg (show ¬ k + 1 < 0 by omega),
          show (if k + 1 ≥ 0 then (k + 1).toNat else 0) = 0 from by
            rw [if_pos hk1]; omega,
          if_neg (show ¬ k ≥ 0 by omega), if_pos (show k < 0 by omega)]
      rw [show (-k).toNat = 1 from by omega]
      rw [Nat.pow_zero]
      rw [show m * P * 10 ^ 1 = 10 * m * P * 1 from by grind]
    · push_neg at hk1
      rw [if_pos (show k + 1 < 0 by omega), if_neg (show ¬ k + 1 ≥ 0 by omega),
          if_neg (show ¬ k ≥ 0 by omega), if_pos (show k < 0 by omega)]
      rw [Nat.pow_zero, Nat.mul_one]
      rw [show (-k).toNat = (-(k + 1)).toNat + 1 from by omega, Nat.pow_succ]
      rw [show m * P * (10 ^ (-(k + 1)).toNat * 10)
            = 10 * m * P * 10 ^ (-(k + 1)).toNat from by grind]

set_option maxRecDepth 4000 in
/-- **`s` from the boundary product.** For binary64 `(m, q)` with the
    `-(k+1)` entry in range and the shift `w = h' - q ≥ 128`, the top
    `w` bits of `(10m)·g'` are exactly `shiftedSig m q k`. -/
theorem sFromP_floor (m : Nat) (q : Int)
    (hm_pos : 0 < m) (hm53 : m < 2 ^ 53)
    (hq_lo : -1074 ≤ q) (hq_hi : q ≤ 971)
    (hkLo : pow10Table128_kMin ≤ -(kOfMQ m q + 1))
    (hkHi : -(kOfMQ m q + 1) ≤ pow10Table128_kMax)
    (hw_lo : 127 ≤ (pow10Lookup128 (-(kOfMQ m q + 1))).2.2 - q)
    (hcov : 128 ≤ (pow10Lookup128 (-(kOfMQ m q + 1))).2.2 - q ∨ m ≤ 2 ^ 52) :
    (10 * m * ((pow10Lookup128 (-(kOfMQ m q + 1))).1.toNat * 2 ^ 64
        + (pow10Lookup128 (-(kOfMQ m q + 1))).2.1.toNat))
      / 2 ^ ((pow10Lookup128 (-(kOfMQ m q + 1))).2.2 - q).toNat
      = shiftedSig m q (kOfMQ m q) := by
  set k : Int := kOfMQ m q with hk_def
  set h_t : Int := (pow10Lookup128 (-(k + 1))).2.2 with hh_def
  set w : Int := h_t - q with hw_def
  have hw_nn : 0 ≤ w := by rw [hw_def]; omega
  set qPos : Nat := if q ≥ 0 then q.toNat else 0 with hqPos_def
  set qNeg : Nat := if q < 0 then (-q).toNat else 0 with hqNeg_def
  set kPos' : Nat := if k + 1 ≥ 0 then (k + 1).toNat else 0 with hkPos'_def
  set kNeg' : Nat := if k + 1 < 0 then (-(k + 1)).toNat else 0 with hkNeg'_def
  set hPos : Nat := if h_t ≥ 0 then h_t.toNat else 0 with hhPos_def
  set hNeg : Nat := if h_t < 0 then (-h_t).toNat else 0 with hhNeg_def
  set G : Nat := (pow10Lookup128 (-(k + 1))).1.toNat * 2 ^ 64
      + (pow10Lookup128 (-(k + 1))).2.1.toNat with hG_def
  set B : Nat := 2 ^ qNeg * 10 ^ kPos' with hB_def
  set N : Nat := 10 * m * 2 ^ qPos * 10 ^ kNeg' with hN_def
  have hB_pos : 0 < B := by
    rw [hB_def]; exact Nat.mul_pos (Nat.two_pow_pos _) (Nat.pow_pos (by decide))
  -- Regrouping: w.toNat + qPos + hNeg = qNeg + hPos.
  have hregroup_eq : w.toNat + qPos + hNeg = qNeg + hPos := by
    have hwInt : (w.toNat : Int) = w := Int.toNat_of_nonneg hw_nn
    have hIntEq : (w.toNat : Int) + (qPos : Int) + (hNeg : Int)
        = (qNeg : Int) + (hPos : Int) := by
      rw [hwInt, hw_def, hqPos_def, hqNeg_def, hhPos_def, hhNeg_def]
      by_cases hq : q ≥ 0
      · have hq_neg : ¬ q < 0 := by omega
        have hqtoNat : (q.toNat : Int) = q := Int.toNat_of_nonneg hq
        rw [if_pos hq, if_neg hq_neg]
        have hh_nn : 0 ≤ h_t := by omega
        have hh_neg : ¬ h_t < 0 := by omega
        have hhtoNat : (h_t.toNat : Int) = h_t := Int.toNat_of_nonneg hh_nn
        rw [if_pos hh_nn, if_neg hh_neg, hqtoNat, hhtoNat]
        push_cast
        grind
      · push_neg at hq
        have hq_nn : ¬ q ≥ 0 := by omega
        have hqtoNat : ((-q).toNat : Int) = -q := Int.toNat_of_nonneg (by omega)
        rw [if_neg hq_nn, if_pos hq, hqtoNat]
        by_cases hh : h_t ≥ 0
        · have hh_neg : ¬ h_t < 0 := by omega
          have hhtoNat : (h_t.toNat : Int) = h_t := Int.toNat_of_nonneg hh
          rw [if_pos hh, if_neg hh_neg, hhtoNat]
          push_cast
          grind
        · push_neg at hh
          have hh_nn : ¬ h_t ≥ 0 := by omega
          have hhtoNat : ((-h_t).toNat : Int) = -h_t := Int.toNat_of_nonneg (by omega)
          rw [if_neg hh_nn, if_pos hh, hhtoNat]
          push_cast
          grind
    exact_mod_cast hIntEq
  have hRegroup : 2 ^ w.toNat * 2 ^ qPos * 2 ^ hNeg = 2 ^ qNeg * 2 ^ hPos :=
    two_pow_regroup w.toNat qNeg qPos hPos hNeg (by omega)
  -- Table invariant at the -(k+1) entry.
  have hInv := pow10Lookup128_invariant (-(k + 1)) hkLo hkHi
  have hkPos'_eq : (if (-(k + 1) : Int) ≥ 0 then (-(k + 1)).toNat else 0) = kNeg' := by
    rw [hkNeg'_def]
    by_cases hc : k + 1 < 0
    · rw [if_pos (show (-(k + 1) : Int) ≥ 0 by omega), if_pos hc]
    · rw [if_neg hc]
      by_cases hz : k + 1 = 0
      · rw [if_pos (show (-(k + 1) : Int) ≥ 0 by omega)]
        omega
      · rw [if_neg (show ¬ (-(k + 1) : Int) ≥ 0 by omega)]
  have hkNeg'_eq : (if (-(k + 1) : Int) < 0 then (-(-(k + 1))).toNat else 0) = kPos' := by
    rw [hkPos'_def]
    by_cases hc : k + 1 ≥ 0
    · by_cases hz : k + 1 = 0
      · rw [if_neg (show ¬ (-(k + 1) : Int) < 0 by omega), if_pos hc]
        omega
      · rw [if_pos (show (-(k + 1) : Int) < 0 by omega), if_pos hc]
        congr 1
        omega
    · rw [if_neg (show ¬ (-(k + 1) : Int) < 0 by omega), if_neg hc]
  have hhPos_eq : (if (pow10Lookup128 (-(k + 1))).2.2 ≥ 0
      then ((pow10Lookup128 (-(k + 1))).2.2).toNat else 0) = hPos := by
    rw [hhPos_def, hh_def]
  have hhNeg_eq : (if (pow10Lookup128 (-(k + 1))).2.2 < 0
      then (-(pow10Lookup128 (-(k + 1))).2.2).toNat else 0) = hNeg := by
    rw [hhNeg_def, hh_def]
  have hInv' : 10 ^ kNeg' * 2 ^ hPos ≤ G * 10 ^ kPos' * 2 ^ hNeg
      ∧ G * 10 ^ kPos' * 2 ^ hNeg < 10 ^ kNeg' * 2 ^ hPos + 10 ^ kPos' * 2 ^ hNeg := by
    have h1 := hInv
    simp only at h1
    rw [hkPos'_eq, hkNeg'_eq, hhPos_eq, hhNeg_eq, ← hG_def] at h1
    exact h1
  -- Sandwich at multiplicand 10m.
  have hSandwich := shiftedSig_sandwich (10 * m) G qPos qNeg kPos' kNeg' hPos hNeg
      w.toNat (by omega) hRegroup hInv'
  -- Residue at multiplicand 10m, shift w ≥ 127 with the coverage split.
  have hsl : 10 * m * 2 ^ 71 ≤ 2 ^ w.toNat := by
    rcases hcov with hw128 | hm52
    · calc 10 * m * 2 ^ 71 ≤ 10 * (2 ^ 53 - 1) * 2 ^ 71 :=
            Nat.mul_le_mul_right _ (by omega)
        _ ≤ 2 ^ 128 := by grind
        _ ≤ 2 ^ w.toNat := Nat.pow_le_pow_right (by grind) (by omega)
    · calc 10 * m * 2 ^ 71 ≤ 10 * 2 ^ 52 * 2 ^ 71 :=
            Nat.mul_le_mul_right _ (by omega)
        _ ≤ 2 ^ 127 := by grind
        _ ≤ 2 ^ w.toNat := Nat.pow_le_pow_right (by grind) (by omega)
  have hsl5 : 10 * m * 5 ^ 30 ≤ 2 ^ w.toNat := by
    rcases hcov with hw128 | hm52
    · calc 10 * m * 5 ^ 30 ≤ 10 * (2 ^ 53 - 1) * 5 ^ 30 :=
            Nat.mul_le_mul_right _ (by omega)
        _ ≤ 2 ^ 128 := by grind
        _ ≤ 2 ^ w.toNat := Nat.pow_le_pow_right (by grind) (by omega)
    · calc 10 * m * 5 ^ 30 ≤ 10 * 2 ^ 52 * 5 ^ 30 :=
            Nat.mul_le_mul_right _ (by omega)
        _ ≤ 2 ^ 127 := by grind
        _ ≤ 2 ^ w.toNat := Nat.pow_le_pow_right (by grind) (by omega)
  have hres0 := residueR20Cond_decode_binary64_x10 m q w.toNat hm_pos hm53 hq_lo hq_hi hsl hsl5
  rw [← hk_def] at hres0
  have hres1 := residueR20Cond_x10_reassoc m q k w.toNat hres0
  have hResidue : residueR20Cond (10 * m) B w.toNat N := by
    rw [hB_def, hN_def, hqNeg_def, hkPos'_def, hqPos_def, hkNeg'_def]
    exact hres1
  -- Floor.
  have hFloor := shiftedSig_floor_of_residue (10 * m) G B w.toNat N hB_pos hSandwich hResidue
  -- Assemble.
  calc 10 * m * G / 2 ^ w.toNat = N / B := hFloor
    _ = shiftedSig m q k := by
        rw [hN_def, hB_def, hqPos_def, hqNeg_def, hkPos'_def, hkNeg'_def]
        exact shiftedSig_x10_succ m q k


end Srtfp.Schubfach

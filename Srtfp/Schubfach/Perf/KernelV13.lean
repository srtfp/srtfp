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

import Srtfp.Schubfach.Perf.KernelV12

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
    rw [hj, ← pow_add]; congr 1; omega
  have hN : m * 2 ^ q = 2 ^ k * (m * 2 ^ j) := by rw [hsplit]; ring
  have hmod : (m * 2 ^ q) % 10 ^ k = 2 ^ k * ((m * 2 ^ j) % 5 ^ k) := by
    rw [hN, h10, Nat.mul_mod_mul_left (2 ^ k) (m * 2 ^ j) (5 ^ k)]
  set r := (m * 2 ^ j) % 5 ^ k with hr
  have hgap : 10 ^ k - (m * 2 ^ q) % 10 ^ k = 2 ^ k * (5 ^ k - r) := by
    rw [hmod, h10, Nat.mul_sub]
  rw [hgap, h10]
  have hcancel : m' * (2 ^ k * 5 ^ k) = 2 ^ k * (m' * 5 ^ k) := by ring
  have hRHS : 2 ^ k * (5 ^ k - r) * 2 ^ s = 2 ^ k * ((5 ^ k - r) * 2 ^ s) := by ring
  rw [hcancel, hRHS]
  apply Nat.mul_le_mul_left
  rw [Nat.mul_comm (5 ^ k - r) (2 ^ s)] at hDist ⊢
  linarith [hDist]

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
    rw [he, ← pow_add]; congr 1; omega
  have hN : m * 10 ^ kNeg = (m * 5 ^ kNeg) * 2 ^ kNeg := by rw [h10]; ring
  have hmod : (m * 10 ^ kNeg) % 2 ^ qNeg = 2 ^ kNeg * ((m * 5 ^ kNeg) % 2 ^ e) := by
    rw [hN, hsplit, Nat.mul_comm (m * 5 ^ kNeg) (2 ^ kNeg),
        Nat.mul_mod_mul_left (2 ^ kNeg) (m * 5 ^ kNeg) (2 ^ e)]
  set r := (m * 5 ^ kNeg) % 2 ^ e with hr
  have hgap : 2 ^ qNeg - (m * 10 ^ kNeg) % 2 ^ qNeg = 2 ^ kNeg * (2 ^ e - r) := by
    rw [hmod, hsplit, Nat.mul_sub]
  rw [hgap, hsplit]
  have hcancel : m' * (2 ^ kNeg * 2 ^ e) = 2 ^ kNeg * (m' * 2 ^ e) := by ring
  have hRHS : 2 ^ kNeg * (2 ^ e - r) * 2 ^ s = 2 ^ kNeg * ((2 ^ e - r) * 2 ^ s) := by ring
  rw [hcancel, hRHS]
  apply Nat.mul_le_mul_left
  rw [Nat.mul_comm (2 ^ e - r) (2 ^ s)] at hDist ⊢
  linarith [hDist]

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
    have := Nat.mod_lt (m * 2 ^ (q - kNat)) (show 0 < 5 ^ kNat from Nat.pow_pos (by norm_num))
    omega
  rcases Nat.lt_or_ge kNat 31 with hk30 | hk31
  · -- elementary: 10m·5^k ≤ 10m·5^30 ≤ 2^s ≤ (gap)·2^s
    calc 10 * m * 5 ^ kNat
        ≤ 10 * m * 5 ^ 30 := Nat.mul_le_mul_left _
            (Nat.pow_le_pow_right (by norm_num) (by omega))
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
      _ = (5 ^ kNat - (m * 2 ^ (q - kNat)) % 5 ^ kNat) * (10 * m * 2 ^ 71) := by ring
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
            (Nat.pow_le_pow_right (by norm_num) (by omega))
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
          ring
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
      simp only [pow_zero, Nat.mul_one, Nat.one_mul]
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
      simp only [pow_zero, Nat.one_mul]
      apply residueR20Cond_of_safe (10 * m) 1 s _ (by norm_num)
      rw [Nat.mul_one]
      calc 10 * m = 10 * m * 1 := by ring
        _ ≤ 10 * m * 2 ^ 71 := Nat.mul_le_mul_left _ (Nat.one_le_two_pow)
        _ ≤ 2 ^ s := hsl
  · push_neg at hq0
    have hq_lt : q < 0 := hq0
    have hq_ge_not : ¬ q ≥ 0 := by omega
    have hk_lt : k < 0 := by rw [hk_def]; exact kOfMQ_neg_of_neg m q hq_lt
    have hk_ge_not : ¬ k ≥ 0 := by omega
    rw [if_pos hq_lt, if_neg hq_ge_not, if_neg hk_ge_not, if_pos hk_lt]
    simp only [pow_zero, Nat.mul_one]
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
  calc C * (10 * M) = 10 * (C * M) := by ring
    _ ≤ 10 * ((M - N % M) * 2 ^ s) := Nat.mul_le_mul_left _ h
    _ = 10 * (M - N % M) * 2 ^ s := by ring

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
    rw [e1, e2, pow_zero, Nat.mul_one] at h
    rw [e3, e4, pow_zero, Nat.mul_one, pow_succ]
    have hB10 : Q * (10 ^ k.toNat * 10) = 10 * (Q * 10 ^ k.toNat) := by ring
    have hN10 : 10 * m * P = 10 * (m * P) := by ring
    rw [hB10, hN10]
    exact resid_mul10 _ _ _ _ h
  · push_neg at hk0
    have e1 : (if k ≥ 0 then k.toNat else 0) = 0 := if_neg (by omega)
    have e2 : (if k < 0 then (-k).toNat else 0) = (-k).toNat := if_pos (by omega)
    rw [e1, e2, pow_zero, Nat.mul_one] at h
    by_cases hk1 : k + 1 ≥ 0
    · have e3 : (if k + 1 ≥ 0 then (k + 1).toNat else 0) = 0 := by
        rw [if_pos hk1]; omega
      have e4 : (if k + 1 < 0 then (-(k + 1)).toNat else 0) = 0 := if_neg (by omega)
      rw [e3, e4, pow_zero, Nat.mul_one, Nat.mul_one]
      have hknn : (-k).toNat = 1 := by omega
      rw [hknn] at h
      have hre : m * P * 10 ^ 1 = 10 * m * P := by ring
      rw [hre] at h
      exact h
    · push_neg at hk1
      have e3 : (if k + 1 ≥ 0 then (k + 1).toNat else 0) = 0 := if_neg (by omega)
      have e4 : (if k + 1 < 0 then (-(k + 1)).toNat else 0) = (-(k + 1)).toNat :=
        if_pos (by omega)
      rw [e3, e4, pow_zero, Nat.mul_one]
      have hpow : (-k).toNat = (-(k + 1)).toNat + 1 := by omega
      rw [hpow, pow_succ] at h
      have hre : m * P * (10 ^ (-(k + 1)).toNat * 10)
          = 10 * m * P * 10 ^ (-(k + 1)).toNat := by ring
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
    rw [show (k + 1).toNat = k.toNat + 1 from by omega, pow_zero, pow_succ,
        Nat.mul_one]
    rw [show 10 * m * P = 10 * (m * P) from by ring,
        show Q * (10 ^ k.toNat * 10) = 10 * (Q * 10 ^ k.toNat) from by ring]
    rw [Nat.mul_div_mul_left _ _ (by norm_num : 0 < 10)]
    rw [Nat.mul_one]
  · push_neg at hk0
    by_cases hk1 : k + 1 ≥ 0
    · rw [if_neg (show ¬ k + 1 < 0 by omega),
          show (if k + 1 ≥ 0 then (k + 1).toNat else 0) = 0 from by
            rw [if_pos hk1]; omega,
          if_neg (show ¬ k ≥ 0 by omega), if_pos (show k < 0 by omega)]
      rw [show (-k).toNat = 1 from by omega]
      rw [pow_zero]
      rw [show m * P * 10 ^ 1 = 10 * m * P * 1 from by ring]
    · push_neg at hk1
      rw [if_pos (show k + 1 < 0 by omega), if_neg (show ¬ k + 1 ≥ 0 by omega),
          if_neg (show ¬ k ≥ 0 by omega), if_pos (show k < 0 by omega)]
      rw [pow_zero, Nat.mul_one]
      rw [show (-k).toNat = (-(k + 1)).toNat + 1 from by omega, pow_succ]
      rw [show m * P * (10 ^ (-(k + 1)).toNat * 10)
            = 10 * m * P * 10 ^ (-(k + 1)).toNat from by ring]

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
        ring
      · push_neg at hq
        have hq_nn : ¬ q ≥ 0 := by omega
        have hqtoNat : ((-q).toNat : Int) = -q := Int.toNat_of_nonneg (by omega)
        rw [if_neg hq_nn, if_pos hq, hqtoNat]
        by_cases hh : h_t ≥ 0
        · have hh_neg : ¬ h_t < 0 := by omega
          have hhtoNat : (h_t.toNat : Int) = h_t := Int.toNat_of_nonneg hh
          rw [if_pos hh, if_neg hh_neg, hhtoNat]
          push_cast
          ring
        · push_neg at hh
          have hh_nn : ¬ h_t ≥ 0 := by omega
          have hhtoNat : ((-h_t).toNat : Int) = -h_t := Int.toNat_of_nonneg (by omega)
          rw [if_neg hh_nn, if_pos hh, hhtoNat]
          push_cast
          ring
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
        _ ≤ 2 ^ 128 := by norm_num
        _ ≤ 2 ^ w.toNat := Nat.pow_le_pow_right (by norm_num) (by omega)
    · calc 10 * m * 2 ^ 71 ≤ 10 * 2 ^ 52 * 2 ^ 71 :=
            Nat.mul_le_mul_right _ (by omega)
        _ ≤ 2 ^ 127 := by norm_num
        _ ≤ 2 ^ w.toNat := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsl5 : 10 * m * 5 ^ 30 ≤ 2 ^ w.toNat := by
    rcases hcov with hw128 | hm52
    · calc 10 * m * 5 ^ 30 ≤ 10 * (2 ^ 53 - 1) * 5 ^ 30 :=
            Nat.mul_le_mul_right _ (by omega)
        _ ≤ 2 ^ 128 := by norm_num
        _ ≤ 2 ^ w.toNat := Nat.pow_le_pow_right (by norm_num) (by omega)
    · calc 10 * m * 5 ^ 30 ≤ 10 * 2 ^ 52 * 5 ^ 30 :=
            Nat.mul_le_mul_right _ (by omega)
        _ ≤ 2 ^ 127 := by norm_num
        _ ≤ 2 ^ w.toNat := Nat.pow_le_pow_right (by norm_num) (by omega)
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

/-! ## 192-bit shift-left-2 and top-limb extraction -/

/-- `4·` a 192-bit triple (exact when `4·value < 2^192`). -/
@[inline]
def shl2_192 (hi mid lo : UInt64) : UInt64 × UInt64 × UInt64 :=
  ((hi <<< 2) + (mid >>> 62), (mid <<< 2) + (lo >>> 62), lo <<< 2)

theorem shl2_192_toNat (hi mid lo : UInt64)
    (hno : 4 * triple192Nat hi mid lo < 2 ^ 192) :
    triple192Nat (shl2_192 hi mid lo).1 (shl2_192 hi mid lo).2.1
      (shl2_192 hi mid lo).2.2
      = 4 * triple192Nat hi mid lo := by
  unfold shl2_192 triple192Nat
  unfold triple192Nat at hno
  simp only []
  have h1 := hi.toNat_lt; have h2 := mid.toNat_lt; have h3 := lo.toNat_lt
  have h2c : (2 : UInt64) = UInt64.ofNat 2 := rfl
  have h62 : (62 : UInt64) = UInt64.ofNat 62 := rfl
  have eL : (lo <<< (2 : UInt64)).toNat = lo.toNat * 4 % 2 ^ 64 := by
    rw [h2c, UInt64_shl_toNat_lt lo 2 (by omega)]
    norm_num
  have eM : (mid <<< (2 : UInt64)).toNat = mid.toNat * 4 % 2 ^ 64 := by
    rw [h2c, UInt64_shl_toNat_lt mid 2 (by omega)]
    norm_num
  have eH : (hi <<< (2 : UInt64)).toNat = hi.toNat * 4 % 2 ^ 64 := by
    rw [h2c, UInt64_shl_toNat_lt hi 2 (by omega)]
    norm_num
  have eMs : (mid >>> (62 : UInt64)).toNat = mid.toNat / 2 ^ 62 := by
    rw [h62, UInt64_shr_toNat_lt mid 62 (by omega)]
  have eLs : (lo >>> (62 : UInt64)).toNat = lo.toNat / 2 ^ 62 := by
    rw [h62, UInt64_shr_toNat_lt lo 62 (by omega)]
  have hHi4 : hi.toNat * 4 < 2 ^ 64 := by omega
  have m1 : ((hi <<< (2 : UInt64)) + (mid >>> (62 : UInt64))).toNat
      = hi.toNat * 4 % 2 ^ 64 + mid.toNat / 2 ^ 62 := by
    rw [UInt64.toNat_add, eH, eMs, Nat.mod_eq_of_lt (by omega)]
  have m2 : ((mid <<< (2 : UInt64)) + (lo >>> (62 : UInt64))).toNat
      = mid.toNat * 4 % 2 ^ 64 + lo.toNat / 2 ^ 62 := by
    rw [UInt64.toNat_add, eM, eLs, Nat.mod_eq_of_lt (by omega)]
  rw [m1, m2, eL]
  rw [Nat.mod_eq_of_lt (by omega : hi.toNat * 4 < 2 ^ 64)]
  omega

/-- Top-limb extraction: bits `[128 + t, 192)` of a 192-bit triple. -/
theorem triple192_top_extract (hi mid lo : UInt64) (t : Nat)
    (ht : t < 64) :
    (hi >>> (UInt64.ofNat t)).toNat
      = triple192Nat hi mid lo / 2 ^ (128 + t) := by
  rw [UInt64_shr_toNat_lt hi t ht]
  unfold triple192Nat
  have h2 := mid.toNat_lt; have h3 := lo.toNat_lt
  have hsplit : hi.toNat * 2 ^ 128 + mid.toNat * 2 ^ 64 + lo.toNat
      = hi.toNat * 2 ^ 128 + (mid.toNat * 2 ^ 64 + lo.toNat) := by ring
  rw [hsplit]
  have hrem : mid.toNat * 2 ^ 64 + lo.toNat < 2 ^ 128 := by omega
  have hdiv128 : (hi.toNat * 2 ^ 128 + (mid.toNat * 2 ^ 64 + lo.toNat)) / 2 ^ 128
      = hi.toNat := by
    rw [Nat.mul_comm (hi.toNat) (2 ^ 128), Nat.mul_add_div (by positivity),
        Nat.div_eq_of_lt hrem]
    omega
  rw [show (128 : Nat) + t = 128 + t from rfl, pow_add, ← Nat.div_div_eq_div_mul,
      hdiv128]

/-- flip2 with `s` extracted from the boundary product: `5P = P + 4P`,
    digit count = top limb shifted by `w - 127` (licensed by
    `sFromP_floor`, window `[128, 132]`). (Also: the pickNearer path flipped
    too: one product per table entry, all tests on shared boundary
    triples, midpoint by exact halving. Base-level (spec-table) kernel with the Giulietti-style flipped
    `k+1` interval tests: one boundary product `P = 4m·g'` per decode,
    boundary products derived by 192-bit add/sub, candidate on the
    exact-shift side, shared across the `uV`/`wV` tests. Everything
    else matches `shortestUnsigned_u64_opt`. -/
@[inline]
def shortestUnsigned_u64_opt_flip3 (m : Nat) (q : Int) : Option (UInt64 × Int) :=
  if _h_m0 : m = 0 then none
  else if _h_m : m ≥ (1 <<< 53 : Nat) then none
  else if _h_q_lo : q < (-1074 : Int) then none
  else if _h_q_hi : q > 971 then none
  else
    let irregular := isIrregular m q
    let k := kOfMQ_fast m q
    if _h_k_lo : k < pow10Table128_kMin then none
    else if _h_k_hi : k + 1 > pow10Table128_kMax then none
    else
    let mU : UInt64 := UInt64.ofNat m
    let kHigh : Int := k + 1
    let gT := pow10Lookup128 (-kHigh)
    let wPlusH : Int := -q + gT.2.2
    if _h_qh_lo : wPlusH < 127 then none
    else if _h_qh_hi : wPlusH > 132 then none
    else
      let w8 : UInt64 := UInt64.ofNat wPlusH.toNat
      let m4 : UInt64 := mU <<< 2
      let pLo  : UInt64 := m4 * gT.2.1
      let pLoH : UInt64 := mulHi64 m4 gT.2.1
      let pHi  : UInt64 := m4 * gT.1
      let pHiH : UInt64 := mulHi64 m4 gT.1
      let pMidSum : UInt64 := pHi + pLoH
      let pCarry : UInt64 := if pMidSum < pHi then 1 else 0
      let p192Hi : UInt64 := pHiH + pCarry
      let p4 := shl2_192 p192Hi pMidSum pLo
      let p5 := add192_192 p4.1 p4.2.1 p4.2.2 p192Hi pMidSum pLo
      let sU : UInt64 := p5.1 >>> (UInt64.ofNat (wPlusH - 127).toNat)
      if _h_s : sU ≥ (144115188075855872 : UInt64) then none
      else if sU ≥ (10 : UInt64) then
          let sHighU : UInt64 := sU / 10
          let leftU : UInt64 := if irregular then m4 - 1 else m4 - 2
          let rightU : UInt64 := m4 + 2
          let tg := add192_192 0 gT.1 gT.2.1 0 gT.1 gT.2.1
          let sbHi : UInt64 := if irregular then 0 else tg.1
          let sbMid : UInt64 := if irregular then gT.1 else tg.2.1
          let sbLo : UInt64 := if irregular then gT.2.1 else tg.2.2
          let lB := sub192_192 p192Hi pMidSum pLo sbHi sbMid sbLo
          let rB := add192_192 p192Hi pMidSum pLo tg.1 tg.2.1 tg.2.2
          let uV := inRoundingInterval_u64_flipped_u8 lB.1 lB.2.1 lB.2.2 leftU
                      rB.1 rB.2.1 rB.2.2 rightU w8 sHighU
          if uV = inRoundingInterval_u8_AMBIG then none
          else if uV = inRoundingInterval_u8_TRUE then some (sHighU, kHigh)
          else
            let wV := inRoundingInterval_u64_flipped_u8 lB.1 lB.2.1 lB.2.2 leftU
                        rB.1 rB.2.1 rB.2.2 rightU w8 (sHighU + 1)
            if wV = inRoundingInterval_u8_AMBIG then none
            else if wV = inRoundingInterval_u8_TRUE then some (sHighU + 1, kHigh)
            else
              let gT2 := pow10Lookup128 (-k)
              let w2PlusH : Int := -q + gT2.2.2
              if _h_qh2_lo : w2PlusH < 64 then none
              else if _h_qh2_hi : w2PlusH > 132 then none
              else
                let w28 : UInt64 := UInt64.ofNat w2PlusH.toNat
                let pLo2  : UInt64 := m4 * gT2.2.1
                let pLoH2 : UInt64 := mulHi64 m4 gT2.2.1
                let pHi2  : UInt64 := m4 * gT2.1
                let pHiH2 : UInt64 := mulHi64 m4 gT2.1
                let pMidSum2 : UInt64 := pHi2 + pLoH2
                let pCarry2 : UInt64 := if pMidSum2 < pHi2 then 1 else 0
                let p192Hi2 : UInt64 := pHiH2 + pCarry2
                let tg2 := add192_192 0 gT2.1 gT2.2.1 0 gT2.1 gT2.2.1
                let sbHi2 : UInt64 := if irregular then 0 else tg2.1
                let sbMid2 : UInt64 := if irregular then gT2.1 else tg2.2.1
                let sbLo2 : UInt64 := if irregular then gT2.2.1 else tg2.2.2
                let lB2 := sub192_192 p192Hi2 pMidSum2 pLo2 sbHi2 sbMid2 sbLo2
                let rB2 := add192_192 p192Hi2 pMidSum2 pLo2 tg2.1 tg2.2.1 tg2.2.2
                let mH := shr1_192 p192Hi2 pMidSum2 pLo2
                let twoM : UInt64 := mU <<< 1
                match pickNearer_u64_flipped lB2.1 lB2.2.1 lB2.2.2 leftU
                        rB2.1 rB2.2.1 rB2.2.2 rightU mH.1 mH.2.1 mH.2.2 twoM w28 sU with
                | none => none
                | some chosen => some (chosen, k)
      else if _h_s1 : sU = 0 then none
      else
        let gT2 := pow10Lookup128 (-k)
        let w2PlusH : Int := -q + gT2.2.2
        if _h_qh2_lo : w2PlusH < 64 then none
        else if _h_qh2_hi : w2PlusH > 132 then none
        else
          let w28 : UInt64 := UInt64.ofNat w2PlusH.toNat
          let m4 : UInt64 := mU <<< 2
          let leftU : UInt64 := if irregular then m4 - 1 else m4 - 2
          let rightU : UInt64 := m4 + 2
          let pLo2  : UInt64 := m4 * gT2.2.1
          let pLoH2 : UInt64 := mulHi64 m4 gT2.2.1
          let pHi2  : UInt64 := m4 * gT2.1
          let pHiH2 : UInt64 := mulHi64 m4 gT2.1
          let pMidSum2 : UInt64 := pHi2 + pLoH2
          let pCarry2 : UInt64 := if pMidSum2 < pHi2 then 1 else 0
          let p192Hi2 : UInt64 := pHiH2 + pCarry2
          let tg2 := add192_192 0 gT2.1 gT2.2.1 0 gT2.1 gT2.2.1
          let sbHi2 : UInt64 := if irregular then 0 else tg2.1
          let sbMid2 : UInt64 := if irregular then gT2.1 else tg2.2.1
          let sbLo2 : UInt64 := if irregular then gT2.2.1 else tg2.2.2
          let lB2 := sub192_192 p192Hi2 pMidSum2 pLo2 sbHi2 sbMid2 sbLo2
          let rB2 := add192_192 p192Hi2 pMidSum2 pLo2 tg2.1 tg2.2.1 tg2.2.2
          let mH := shr1_192 p192Hi2 pMidSum2 pLo2
          let twoM : UInt64 := mU <<< 1
          match pickNearer_u64_flipped lB2.1 lB2.2.1 lB2.2.2 leftU
                  rB2.1 rB2.2.1 rB2.2.2 rightU mH.1 mH.2.1 mH.2.2 twoM w28 sU with
          | none => none
          | some chosen => some (chosen, k)


/-! ## Regular bands never reach `w = 127`

A per-`q` table sweep: for every binary64 `q` with the *regular*
Schubfach exponent `k = floorLog10Pow2 q` (and the `-(k+1)` entry in
range), the flipped window satisfies `h' - q ≥ 128`. Hence `w = 127`
occurs only on irregular bands, where `m = 2^52` and the certificate
covers the slack directly. -/

/-- Per-index well-regulated predicate (shared by `wRegBool` and the
    chunked checker). -/
def wRegPred (qn : Nat) : Bool :=
  let q : Int := (qn : Int) - 1074
  let k : Int := floorLog10Pow2 q
  decide (k < -324 ∨ k + 1 > 324 ∨ 128 ≤ (pow10Lookup128 (-(k + 1))).2.2 - q)

def wRegBool : Bool :=
  (List.range 2046).all wRegPred

/-- Chunked checker: `wRegPred` holds across the sub-range `[lo, lo+n)`.
    A single `decide +kernel` over the full 2046-wide range expands the
    `pow10Lookup128` table 2046x in one kernel reduction (~20 GB peak).
    Splitting it into many narrow fixed-width chunks, each elaborated as a
    separate declaration so they never coexist in memory, caps the peak at
    one chunk's reduction (~4.5 GB at this width). Do NOT merge the chunks
    back into one `decide`, and keep the width small — that is what holds
    the module under the lakefile's `lean -M` budget. -/
def wRegChunk (lo n : Nat) : Bool :=
  (List.range' lo n).all wRegPred

theorem wRegChunk_0 : wRegChunk 0 93 = true := by decide +kernel
theorem wRegChunk_1 : wRegChunk 93 93 = true := by decide +kernel
theorem wRegChunk_2 : wRegChunk 186 93 = true := by decide +kernel
theorem wRegChunk_3 : wRegChunk 279 93 = true := by decide +kernel
theorem wRegChunk_4 : wRegChunk 372 93 = true := by decide +kernel
theorem wRegChunk_5 : wRegChunk 465 93 = true := by decide +kernel
theorem wRegChunk_6 : wRegChunk 558 93 = true := by decide +kernel
theorem wRegChunk_7 : wRegChunk 651 93 = true := by decide +kernel
theorem wRegChunk_8 : wRegChunk 744 93 = true := by decide +kernel
theorem wRegChunk_9 : wRegChunk 837 93 = true := by decide +kernel
theorem wRegChunk_10 : wRegChunk 930 93 = true := by decide +kernel
theorem wRegChunk_11 : wRegChunk 1023 93 = true := by decide +kernel
theorem wRegChunk_12 : wRegChunk 1116 93 = true := by decide +kernel
theorem wRegChunk_13 : wRegChunk 1209 93 = true := by decide +kernel
theorem wRegChunk_14 : wRegChunk 1302 93 = true := by decide +kernel
theorem wRegChunk_15 : wRegChunk 1395 93 = true := by decide +kernel
theorem wRegChunk_16 : wRegChunk 1488 93 = true := by decide +kernel
theorem wRegChunk_17 : wRegChunk 1581 93 = true := by decide +kernel
theorem wRegChunk_18 : wRegChunk 1674 93 = true := by decide +kernel
theorem wRegChunk_19 : wRegChunk 1767 93 = true := by decide +kernel
theorem wRegChunk_20 : wRegChunk 1860 93 = true := by decide +kernel
theorem wRegChunk_21 : wRegChunk 1953 93 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem wRegRange_split : List.range 2046
    = List.range' 0 93 ++ (List.range' 93 93 ++ (List.range' 186 93 ++ (List.range' 279 93 ++ (List.range' 372 93 ++ (List.range' 465 93 ++ (List.range' 558 93 ++ (List.range' 651 93 ++ (List.range' 744 93 ++ (List.range' 837 93 ++ (List.range' 930 93 ++ (List.range' 1023 93 ++ (List.range' 1116 93 ++ (List.range' 1209 93 ++ (List.range' 1302 93 ++ (List.range' 1395 93 ++ (List.range' 1488 93 ++ (List.range' 1581 93 ++ (List.range' 1674 93 ++ (List.range' 1767 93 ++ (List.range' 1860 93 ++ (List.range' 1953 93))))))))))))))))))))) := by
  rfl

theorem wReg_check : wRegBool = true := by
  unfold wRegBool
  rw [wRegRange_split]
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨wRegChunk_0, wRegChunk_1, wRegChunk_2, wRegChunk_3, wRegChunk_4, wRegChunk_5, wRegChunk_6, wRegChunk_7, wRegChunk_8, wRegChunk_9, wRegChunk_10, wRegChunk_11, wRegChunk_12, wRegChunk_13, wRegChunk_14, wRegChunk_15, wRegChunk_16, wRegChunk_17, wRegChunk_18, wRegChunk_19, wRegChunk_20, wRegChunk_21⟩

theorem wReg_at (q : Int) (h1 : -1074 ≤ q) (h2 : q ≤ 971)
    (hklo : ¬ floorLog10Pow2 q < pow10Table128_kMin)
    (hkhi : ¬ floorLog10Pow2 q + 1 > pow10Table128_kMax) :
    128 ≤ (pow10Lookup128 (-(floorLog10Pow2 q + 1))).2.2 - q := by
  have hAll := wReg_check
  unfold wRegBool at hAll
  rw [List.all_eq_true] at hAll
  have h := hAll (q + 1074).toNat (List.mem_range.mpr (by omega))
  unfold wRegPred at h
  simp only [decide_eq_true_eq] at h
  have hq : (((q + 1074).toNat : Int)) - 1074 = q := by omega
  rw [hq] at h
  have hklo' : ¬ floorLog10Pow2 q < (-324 : Int) := hklo
  have hkhi' : ¬ floorLog10Pow2 q + 1 > (324 : Int) := hkhi
  rcases h with h | h | h
  · exact absurd h (by omega)
  · exact absurd h (by omega)
  · exact h

set_option maxRecDepth 16384 in
set_option maxHeartbeats 3200000 in
/-- Fast-path correctness for flip3: a `some` result is the
    `shortestUnsigned_packed` (= spec) value. The `s` leg rides
    `sFromP_floor` instead of the 192-bit table chain. -/
theorem shortestUnsigned_u64_opt_flip3_some_eq_packed
    (m : Nat) (q : Int) (sUo : UInt64) (ko : Int)
    (hopt : shortestUnsigned_u64_opt_flip3 m q = some (sUo, ko)) :
    shortestUnsigned_packed m q = (sUo.toNat, ko) := by
  rw [shortestUnsigned_packed_eq]
  show shortestUnsigned m q = (sUo.toNat, ko)
  unfold shortestUnsigned_u64_opt_flip3 at hopt
  simp only [kOfMQ_fast_eq] at hopt
  by_cases hm0 : m = 0
  · rw [dif_pos hm0] at hopt; cases hopt
  rw [dif_neg hm0] at hopt
  by_cases hm_ge : m ≥ (1 <<< 53 : Nat)
  · rw [dif_pos hm_ge] at hopt; cases hopt
  rw [dif_neg hm_ge] at hopt
  push_neg at hm_ge
  by_cases hq_lo : q < (-1074 : Int)
  · rw [dif_pos hq_lo] at hopt; cases hopt
  rw [dif_neg hq_lo] at hopt
  by_cases hq_hi : q > 971
  · rw [dif_pos hq_hi] at hopt; cases hopt
  rw [dif_neg hq_hi] at hopt
  push_neg at hq_lo hq_hi
  by_cases hk_lo : kOfMQ m q < pow10Table128_kMin
  · rw [dif_pos hk_lo] at hopt; cases hopt
  rw [dif_neg hk_lo] at hopt
  by_cases hk_hi1 : kOfMQ m q + 1 > pow10Table128_kMax
  · rw [dif_pos hk_hi1] at hopt; cases hopt
  rw [dif_neg hk_hi1] at hopt
  push_neg at hk_lo hk_hi1
  have hkMin_lit : pow10Table128_kMin = (-324 : Int) := rfl
  have hkMax_lit : pow10Table128_kMax = (324 : Int) := rfl
  have hm_lt : m < (1 <<< 58 : Nat) := by
    have : (1 <<< 53 : Nat) < (1 <<< 58 : Nat) := by decide
    omega
  have hm_pos : m ≥ 1 := Nat.pos_of_ne_zero hm0
  by_cases hqh127 : -q + (pow10Lookup128 (-(kOfMQ m q + 1))).2.2 < 127
  · rw [dif_pos hqh127] at hopt; cases hopt
  rw [dif_neg hqh127] at hopt
  by_cases hqh_hi : -q + (pow10Lookup128 (-(kOfMQ m q + 1))).2.2 > 132
  · rw [dif_pos hqh_hi] at hopt; cases hopt
  rw [dif_neg hqh_hi] at hopt
  push_neg at hqh127 hqh_hi
  have hqh_lo : 64 ≤ -q + (pow10Lookup128 (-(kOfMQ m q + 1))).2.2 := by omega
  set gT := pow10Lookup128 (-(kOfMQ m q + 1)) with hgT
  set m4 : UInt64 := UInt64.ofNat m <<< 2 with hm4
  set pLo : UInt64 := m4 * gT.2.1 with hpLo
  set pLoH : UInt64 := mulHi64 m4 gT.2.1 with hpLoH
  set pHi : UInt64 := m4 * gT.1 with hpHi
  set pHiH : UInt64 := mulHi64 m4 gT.1 with hpHiH
  set pMid : UInt64 := pHi + pLoH with hpMid
  set pC : UInt64 := (if pMid < pHi then (1 : UInt64) else 0) with hpC
  set pH : UInt64 := pHiH + pC with hpH
  set p4 := shl2_192 pH pMid pLo with hp4
  set p5 := add192_192 p4.1 p4.2.1 p4.2.2 pH pMid pLo with hp5
  have hG_lt : gT.1.toNat * 2 ^ 64 + gT.2.1.toNat < 2 ^ 128 := by
    have h1 := gT.1.toNat_lt; have h2 := gT.2.1.toNat_lt
    omega
  have hm4_toNat : m4.toNat = 4 * m := by
    rw [hm4, uint64_shiftLeft_2, UInt64.toNat_mul,
        toNat_ofNat_bounded (show m < 2 ^ 64 by omega),
        show ((4 : UInt64)).toNat = 4 from rfl]
    exact Nat.mod_eq_of_lt (by omega)
  have hmulG_lt : ∀ b : Nat, b ≤ 4 * m + 2 →
      b * (gT.1.toNat * 2 ^ 64 + gT.2.1.toNat) < 2 ^ 192 := by
    intro b hb
    have h3 : b * (gT.1.toNat * 2 ^ 64 + gT.2.1.toNat) ≤ 2 ^ 60 * 2 ^ 128 :=
      Nat.mul_le_mul (by omega) (by omega)
    have h4 : (2 : Nat) ^ 60 * 2 ^ 128 < 2 ^ 192 := by
      rw [← pow_add]
      exact Nat.pow_lt_pow_right (by omega) (by omega)
    omega
  have htrip0G : triple192Nat 0 gT.1 gT.2.1
      = gT.1.toNat * 2 ^ 64 + gT.2.1.toNat := by
    unfold triple192Nat
    simp only [show ((0 : UInt64)).toNat = 0 from rfl]
    omega
  have hP_val : triple192Nat pH pMid pLo
      = 4 * m * (gT.1.toNat * 2 ^ 64 + gT.2.1.toNat) := by
    have h := mul192_b_g_toNat m4 gT.1 gT.2.1
    simp only [] at h
    rw [← hpLo, ← hpLoH, ← hpHi, ← hpHiH, ← hpMid, ← hpC, ← hpH] at h
    rw [hm4_toNat, Nat.mod_eq_of_lt (hmulG_lt (4 * m) (by omega))] at h
    exact h
  have hmulG_lt2 : ∀ b : Nat, b ≤ 32 * m →
      b * (gT.1.toNat * 2 ^ 64 + gT.2.1.toNat) < 2 ^ 192 := by
    intro b hb
    have h3 : b * (gT.1.toNat * 2 ^ 64 + gT.2.1.toNat) ≤ 2 ^ 63 * 2 ^ 128 :=
      Nat.mul_le_mul (by omega) (by omega)
    have h4 : (2 : Nat) ^ 63 * 2 ^ 128 < 2 ^ 192 := by
      rw [← pow_add]
      exact Nat.pow_lt_pow_right (by omega) (by omega)
    omega
  have hp4_val : triple192Nat p4.1 p4.2.1 p4.2.2
      = 16 * m * (gT.1.toNat * 2 ^ 64 + gT.2.1.toNat) := by
    rw [hp4, shl2_192_toNat pH pMid pLo (by
      rw [hP_val]
      rw [show 4 * (4 * m * (gT.1.toNat * 2 ^ 64 + gT.2.1.toNat))
            = 16 * m * (gT.1.toNat * 2 ^ 64 + gT.2.1.toNat) from by ring]
      exact hmulG_lt2 (16 * m) (by omega)), hP_val]
    ring
  have hp5_val : triple192Nat p5.1 p5.2.1 p5.2.2
      = 20 * m * (gT.1.toNat * 2 ^ 64 + gT.2.1.toNat) := by
    rw [hp5, add192_192_toNat _ _ _ _ _ _ (by
      rw [hp4_val, hP_val]
      rw [show 16 * m * (gT.1.toNat * 2 ^ 64 + gT.2.1.toNat)
            + 4 * m * (gT.1.toNat * 2 ^ 64 + gT.2.1.toNat)
            = 20 * m * (gT.1.toNat * 2 ^ 64 + gT.2.1.toNat) from by ring]
      exact hmulG_lt2 (20 * m) (by omega)), hp4_val, hP_val]
    ring
  have ht_lt : (-q + gT.2.2 - 127).toNat < 64 := by omega
  have hext := triple192_top_extract p5.1 p5.2.1 p5.2.2 _ ht_lt
  rw [hp5_val] at hext
  have h128t : 128 + (-q + gT.2.2 - 127).toNat = (-q + gT.2.2).toNat + 1 := by
    omega
  rw [h128t] at hext
  have hhalf : 20 * m * (gT.1.toNat * 2 ^ 64 + gT.2.1.toNat)
        / 2 ^ ((-q + gT.2.2).toNat + 1)
      = 10 * m * (gT.1.toNat * 2 ^ 64 + gT.2.1.toNat) / 2 ^ (-q + gT.2.2).toNat := by
    rw [show (2 : Nat) ^ ((-q + gT.2.2).toNat + 1)
          = 2 ^ (-q + gT.2.2).toNat * 2 from pow_succ _ _,
        show 20 * m * (gT.1.toNat * 2 ^ 64 + gT.2.1.toNat)
          = 10 * m * (gT.1.toNat * 2 ^ 64 + gT.2.1.toNat) * 2 from by ring,
        Nat.mul_div_mul_right _ _ (by norm_num : (0 : Nat) < 2)]
  have hfl := sFromP_floor m q hm_pos (by
      have : (1 <<< 53 : Nat) = 2 ^ 53 := by decide
      omega) hq_lo hq_hi
    (by rw [hkMin_lit]; omega) (by rw [hkMax_lit]; omega)
    (by rw [← hgT]; omega)
    (by
      by_cases hirr : isIrregular m q = true
      · right
        unfold isIrregular at hirr
        rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hirr
        rw [hirr.1]
        unfold minNormalSignificand
        have : (1 <<< 52 : Nat) = 2 ^ 52 := by decide
        omega
      · left
        have hk_eq : kOfMQ m q = floorLog10Pow2 q := by
          unfold kOfMQ
          rw [if_neg hirr]
        rw [hk_eq]
        exact wReg_at q (by omega) (by omega)
          (by rw [← hk_eq]; omega) (by rw [← hk_eq]; omega))
  rw [← hgT] at hfl
  have hexp_eq : ((gT.2.2 - q)).toNat = (-q + gT.2.2).toNat := by omega
  rw [hexp_eq] at hfl
  have hs_eq : (p5.1 >>> UInt64.ofNat ((-q + gT.2.2 - 127)).toNat).toNat
      = shiftedSig m q (kOfMQ m q) := by
    rw [hext, hhalf]
    exact hfl
  have hsU_form : p5.1 >>> UInt64.ofNat ((-q + gT.2.2 - 127)).toNat
      = UInt64.ofNat (shiftedSig m q (kOfMQ m q)) := by
    rw [← hs_eq, UInt64.ofNat_toNat]
  rw [hsU_form] at hopt
  have hbound64 : shiftedSig m q (kOfMQ m q) < 2 ^ 64 := by
    rw [← hs_eq]
    exact (p5.1 >>> UInt64.ofNat ((-q + gT.2.2 - 127)).toNat).toNat_lt
  by_cases h_s : UInt64.ofNat (shiftedSig m q (kOfMQ m q)) ≥ (144115188075855872 : UInt64)
  · rw [dif_pos h_s] at hopt; cases hopt
  rw [dif_neg h_s] at hopt
  have hs_ge : shiftedSig m q (kOfMQ m q) < (1 <<< 57 : Nat) := by
    by_contra hc
    push_neg at hc
    apply h_s
    rw [ge_iff_le, UInt64.le_iff_toNat_le, toNat_ofNat_bounded hbound64,
        show ((144115188075855872 : UInt64)).toNat = (1 <<< 57 : Nat) from rfl]
    exact hc
  have e10 : (UInt64.ofNat (shiftedSig m q (kOfMQ m q)) ≥ (10 : UInt64))
      = (shiftedSig m q (kOfMQ m q) ≥ 10) := by
    rw [propext (uint64_ge_10 _), toNat_ofNat_bounded hbound64]
  have e0 : (UInt64.ofNat (shiftedSig m q (kOfMQ m q)) = 0)
      = (shiftedSig m q (kOfMQ m q) = 0) := by
    rw [propext (uint64_eq_0 _), toNat_ofNat_bounded hbound64]
  simp only [e10, e0] at hopt
  unfold shortestUnsigned
  by_cases hs10 : shiftedSig m q (kOfMQ m q) ≥ 10
  · rw [if_pos hs10]
    simp only [hs10, if_true] at hopt
    have hdiv10 : UInt64.ofNat (shiftedSig m q (kOfMQ m q)) / 10 =
        UInt64.ofNat (shiftedSig m q (kOfMQ m q) / 10) := uint64_div_10 hs_ge
    rw [hdiv10] at hopt
    -- Abbreviate the flipped-block subterms (hopt is fully zeta-expanded).
    set tg := add192_192 0 gT.1 gT.2.1 0 gT.1 gT.2.1 with htg
    set sbHi : UInt64 := (if isIrregular m q = true then 0 else tg.1) with hsbHi
    set sbMid : UInt64 := (if isIrregular m q = true then gT.1 else tg.2.1) with hsbMid
    set sbLo : UInt64 := (if isIrregular m q = true then gT.2.1 else tg.2.2) with hsbLo
    set lB := sub192_192 pH pMid pLo sbHi sbMid sbLo with hlB
    set rB := add192_192 pH pMid pLo tg.1 tg.2.1 tg.2.2 with hrB
    set leftU : UInt64 := (if isIrregular m q = true then m4 - 1 else m4 - 2) with hleftU
    set w8 : UInt64 := UInt64.ofNat (-q + gT.2.2).toNat with hw8
    -- Value facts.
    have h2G_val : triple192Nat tg.1 tg.2.1 tg.2.2
        = 2 * (gT.1.toNat * 2 ^ 64 + gT.2.1.toNat) := by
      rw [htg, add192_192_toNat 0 gT.1 gT.2.1 0 gT.1 gT.2.1 (by
        rw [htrip0G]; omega), htrip0G]
      omega
    have hlB_val : triple192Nat lB.1 lB.2.1 lB.2.2
        = (if isIrregular m q = true then 4 * m - 1 else 4 * m - 2)
            * (gT.1.toNat * 2 ^ 64 + gT.2.1.toNat) := by
      rw [hlB, hsbHi, hsbMid, hsbLo]
      by_cases hirr : isIrregular m q = true
      · rw [if_pos hirr, if_pos hirr, if_pos hirr, if_pos hirr,
            sub192_192_toNat pH pMid pLo 0 gT.1 gT.2.1 (by
              rw [htrip0G, hP_val]
              exact Nat.le_mul_of_pos_left _ (by omega)),
            hP_val, htrip0G, Nat.sub_mul, Nat.one_mul]
      · rw [if_neg hirr, if_neg hirr, if_neg hirr, if_neg hirr,
            sub192_192_toNat pH pMid pLo tg.1 tg.2.1 tg.2.2 (by
              rw [h2G_val, hP_val]
              exact Nat.mul_le_mul_right _ (by omega)),
            hP_val, h2G_val, Nat.sub_mul]
    have hrB_val : triple192Nat rB.1 rB.2.1 rB.2.2
        = (4 * m + 2) * (gT.1.toNat * 2 ^ 64 + gT.2.1.toNat) := by
      rw [hrB, add192_192_toNat pH pMid pLo tg.1 tg.2.1 tg.2.2 (by
            rw [hP_val, h2G_val]
            have := hmulG_lt (4 * m + 2) (by omega)
            rw [Nat.add_mul] at this
            omega),
          hP_val, h2G_val, Nat.add_mul]
    -- Bridge preconditions.
    have hsHigh_pos : shiftedSig m q (kOfMQ m q) / 10 ≥ 1 := by omega
    have hsHigh_lt58 : shiftedSig m q (kOfMQ m q) / 10 < (1 <<< 58 : Nat) := by
      have h1 : shiftedSig m q (kOfMQ m q) / 10 ≤ shiftedSig m q (kOfMQ m q) :=
        Nat.div_le_self _ _
      have h2 : (1 <<< 57 : Nat) < (1 <<< 58 : Nat) := by decide
      omega
    have hsHigh1_lt58 : shiftedSig m q (kOfMQ m q) / 10 + 1 < (1 <<< 58 : Nat) := by
      have h1 : shiftedSig m q (kOfMQ m q) / 10 ≤ shiftedSig m q (kOfMQ m q) :=
        Nat.div_le_self _ _
      have h2 : (1 <<< 57 : Nat) + 1 ≤ (1 <<< 58 : Nat) := by decide
      omega
    have hk_lo' : pow10Table128_kMin ≤ -(kOfMQ m q + 1) := by omega
    have hk_hi' : -(kOfMQ m q + 1) ≤ pow10Table128_kMax := by omega
    -- uV leg.
    by_cases hAmb : inRoundingInterval_u64_flipped_u8 lB.1 lB.2.1 lB.2.2 leftU
        rB.1 rB.2.1 rB.2.2 (m4 + 2) w8
        (UInt64.ofNat (shiftedSig m q (kOfMQ m q) / 10)) = inRoundingInterval_u8_AMBIG
    · rw [if_pos hAmb] at hopt; cases hopt
    rw [if_neg hAmb] at hopt
    have huV := inRoundingInterval_u64_flipped_u8_some_eq q (kOfMQ m q + 1)
      (shiftedSig m q (kOfMQ m q) / 10) m (isIrregular m q)
      lB.1 lB.2.1 lB.2.2 rB.1 rB.2.1 rB.2.2
      hm_pos hsHigh_pos hm_lt hsHigh_lt58 hk_lo' hk_hi' hqh_lo hqh_hi
      hlB_val hrB_val hAmb
    by_cases hT : inRoundingInterval_u64_flipped_u8 lB.1 lB.2.1 lB.2.2 leftU
        rB.1 rB.2.1 rB.2.2 (m4 + 2) w8
        (UInt64.ofNat (shiftedSig m q (kOfMQ m q) / 10)) = inRoundingInterval_u8_TRUE
    · rw [if_pos hT] at hopt
      have huIn_true : inRoundingInterval (shiftedSig m q (kOfMQ m q) / 10)
          (kOfMQ m q + 1) m q (isIrregular m q) = true := by
        rw [huV]
        simp only [decide_eq_true_eq]
        exact hT
      simp only [huIn_true, if_true]
      cases hopt
      have hsHigh_eq : (UInt64.ofNat (shiftedSig m q (kOfMQ m q) / 10)).toNat =
          shiftedSig m q (kOfMQ m q) / 10 := by
        apply toNat_ofNat_bounded
        have : (1 <<< 58 : Nat) < 2 ^ 64 := by decide
        omega
      simp [hsHigh_eq]
    rw [if_neg hT] at hopt
    have huIn_false : inRoundingInterval (shiftedSig m q (kOfMQ m q) / 10)
        (kOfMQ m q + 1) m q (isIrregular m q) = false := by
      rw [huV]
      exact decide_eq_false hT
    simp only [huIn_false, Bool.false_eq_true, if_false]
    -- wV leg.
    have hsHigh1_eq : UInt64.ofNat (shiftedSig m q (kOfMQ m q) / 10) + 1 =
        UInt64.ofNat (shiftedSig m q (kOfMQ m q) / 10 + 1) := (ofNat_succ _).symm
    rw [hsHigh1_eq] at hopt
    by_cases hAmb2 : inRoundingInterval_u64_flipped_u8 lB.1 lB.2.1 lB.2.2 leftU
        rB.1 rB.2.1 rB.2.2 (m4 + 2) w8
        (UInt64.ofNat (shiftedSig m q (kOfMQ m q) / 10 + 1)) = inRoundingInterval_u8_AMBIG
    · rw [if_pos hAmb2] at hopt; cases hopt
    rw [if_neg hAmb2] at hopt
    have hwV := inRoundingInterval_u64_flipped_u8_some_eq q (kOfMQ m q + 1)
      (shiftedSig m q (kOfMQ m q) / 10 + 1) m (isIrregular m q)
      lB.1 lB.2.1 lB.2.2 rB.1 rB.2.1 rB.2.2
      hm_pos (by omega) hm_lt hsHigh1_lt58 hk_lo' hk_hi' hqh_lo hqh_hi
      hlB_val hrB_val hAmb2
    by_cases hT2 : inRoundingInterval_u64_flipped_u8 lB.1 lB.2.1 lB.2.2 leftU
        rB.1 rB.2.1 rB.2.2 (m4 + 2) w8
        (UInt64.ofNat (shiftedSig m q (kOfMQ m q) / 10 + 1)) = inRoundingInterval_u8_TRUE
    · rw [if_pos hT2] at hopt
      have hwIn_true : inRoundingInterval (shiftedSig m q (kOfMQ m q) / 10 + 1)
          (kOfMQ m q + 1) m q (isIrregular m q) = true := by
        rw [hwV]
        simp only [decide_eq_true_eq]
        exact hT2
      simp only [hwIn_true, if_true]
      cases hopt
      have hwIn_eq : (UInt64.ofNat (shiftedSig m q (kOfMQ m q) / 10 + 1)).toNat =
          shiftedSig m q (kOfMQ m q) / 10 + 1 := by
        apply toNat_ofNat_bounded
        have : (1 <<< 58 : Nat) < 2 ^ 64 := by decide
        omega
      simp []
      omega
    rw [if_neg hT2] at hopt
    have hwIn_false : inRoundingInterval (shiftedSig m q (kOfMQ m q) / 10 + 1)
        (kOfMQ m q + 1) m q (isIrregular m q) = false := by
      rw [hwV]
      exact decide_eq_false hT2
    simp only [hwIn_false, Bool.false_eq_true, if_false]
    by_cases hqh2_lo : -q + (pow10Lookup128 (-(kOfMQ m q))).2.2 < 64
    · rw [dif_pos hqh2_lo] at hopt; cases hopt
    rw [dif_neg hqh2_lo] at hopt
    by_cases hqh2_hi : -q + (pow10Lookup128 (-(kOfMQ m q))).2.2 > 132
    · rw [dif_pos hqh2_hi] at hopt; cases hopt
    rw [dif_neg hqh2_hi] at hopt
    push_neg at hqh2_lo hqh2_hi
    set gT2 := pow10Lookup128 (-(kOfMQ m q)) with hgT2
    set pLo2 : UInt64 := m4 * gT2.2.1 with hpLo2
    set pLoH2 : UInt64 := mulHi64 m4 gT2.2.1 with hpLoH2
    set pHi2 : UInt64 := m4 * gT2.1 with hpHi2
    set pHiH2 : UInt64 := mulHi64 m4 gT2.1 with hpHiH2
    set pMid2 : UInt64 := pHi2 + pLoH2 with hpMid2
    set pC2 : UInt64 := (if pMid2 < pHi2 then (1 : UInt64) else 0) with hpC2
    set pH2 : UInt64 := pHiH2 + pC2 with hpH2
    set tg2 := add192_192 0 gT2.1 gT2.2.1 0 gT2.1 gT2.2.1 with htg2
    set sbHi2 : UInt64 := (if isIrregular m q = true then 0 else tg2.1) with hsbHi2
    set sbMid2 : UInt64 := (if isIrregular m q = true then gT2.1 else tg2.2.1) with hsbMid2
    set sbLo2 : UInt64 := (if isIrregular m q = true then gT2.2.1 else tg2.2.2) with hsbLo2
    set lB2 := sub192_192 pH2 pMid2 pLo2 sbHi2 sbMid2 sbLo2 with hlB2
    set rB2 := add192_192 pH2 pMid2 pLo2 tg2.1 tg2.2.1 tg2.2.2 with hrB2
    set mH2 := shr1_192 pH2 pMid2 pLo2 with hmH2
    have hG2_lt : gT2.1.toNat * 2 ^ 64 + gT2.2.1.toNat < 2 ^ 128 := by
      have h1 := gT2.1.toNat_lt; have h2 := gT2.2.1.toNat_lt
      omega
    have hmulG2_lt : ∀ b : Nat, b ≤ 4 * m + 2 →
        b * (gT2.1.toNat * 2 ^ 64 + gT2.2.1.toNat) < 2 ^ 192 := by
      intro b hb
      have h3 : b * (gT2.1.toNat * 2 ^ 64 + gT2.2.1.toNat) ≤ 2 ^ 60 * 2 ^ 128 :=
        Nat.mul_le_mul (by omega) (by omega)
      have h4 : (2 : Nat) ^ 60 * 2 ^ 128 < 2 ^ 192 := by
        rw [← pow_add]
        exact Nat.pow_lt_pow_right (by omega) (by omega)
      omega
    have htrip0G2 : triple192Nat 0 gT2.1 gT2.2.1
        = gT2.1.toNat * 2 ^ 64 + gT2.2.1.toNat := by
      unfold triple192Nat
      simp only [show ((0 : UInt64)).toNat = 0 from rfl]
      omega
    have hP2_val : triple192Nat pH2 pMid2 pLo2
        = 4 * m * (gT2.1.toNat * 2 ^ 64 + gT2.2.1.toNat) := by
      have h := mul192_b_g_toNat m4 gT2.1 gT2.2.1
      simp only [] at h
      rw [← hpLo2, ← hpLoH2, ← hpHi2, ← hpHiH2, ← hpMid2, ← hpC2, ← hpH2] at h
      rw [hm4_toNat, Nat.mod_eq_of_lt (hmulG2_lt (4 * m) (by omega))] at h
      exact h
    have h2G2_val : triple192Nat tg2.1 tg2.2.1 tg2.2.2
        = 2 * (gT2.1.toNat * 2 ^ 64 + gT2.2.1.toNat) := by
      rw [htg2, add192_192_toNat 0 gT2.1 gT2.2.1 0 gT2.1 gT2.2.1 (by
        rw [htrip0G2]; omega), htrip0G2]
      omega
    have hlB2_val : triple192Nat lB2.1 lB2.2.1 lB2.2.2
        = (if isIrregular m q = true then 4 * m - 1 else 4 * m - 2)
            * (gT2.1.toNat * 2 ^ 64 + gT2.2.1.toNat) := by
      rw [hlB2, hsbHi2, hsbMid2, hsbLo2]
      by_cases hirr : isIrregular m q = true
      · rw [if_pos hirr, if_pos hirr, if_pos hirr, if_pos hirr,
            sub192_192_toNat pH2 pMid2 pLo2 0 gT2.1 gT2.2.1 (by
              rw [htrip0G2, hP2_val]
              exact Nat.le_mul_of_pos_left _ (by omega)),
            hP2_val, htrip0G2, Nat.sub_mul, Nat.one_mul]
      · rw [if_neg hirr, if_neg hirr, if_neg hirr, if_neg hirr,
            sub192_192_toNat pH2 pMid2 pLo2 tg2.1 tg2.2.1 tg2.2.2 (by
              rw [h2G2_val, hP2_val]
              exact Nat.mul_le_mul_right _ (by omega)),
            hP2_val, h2G2_val, Nat.sub_mul]
    have hrB2_val : triple192Nat rB2.1 rB2.2.1 rB2.2.2
        = (4 * m + 2) * (gT2.1.toNat * 2 ^ 64 + gT2.2.1.toNat) := by
      rw [hrB2, add192_192_toNat pH2 pMid2 pLo2 tg2.1 tg2.2.1 tg2.2.2 (by
            rw [hP2_val, h2G2_val]
            have := hmulG2_lt (4 * m + 2) (by omega)
            rw [Nat.add_mul] at this
            omega),
          hP2_val, h2G2_val, Nat.add_mul]
    have hmH2_val : triple192Nat mH2.1 mH2.2.1 mH2.2.2
        = 2 * m * (gT2.1.toNat * 2 ^ 64 + gT2.2.1.toNat) := by
      rw [hmH2, shr1_192_toNat, hP2_val,
          show 4 * m * (gT2.1.toNat * 2 ^ 64 + gT2.2.1.toNat)
              = 2 * (2 * m * (gT2.1.toNat * 2 ^ 64 + gT2.2.1.toNat)) from by ring,
          Nat.mul_div_cancel_left _ (by omega)]
    have hk_lo2 : pow10Table128_kMin ≤ -(kOfMQ m q) := by omega
    have hk_hi2 : -(kOfMQ m q) ≤ pow10Table128_kMax := by omega
    match hp : pickNearer_u64_flipped lB2.1 lB2.2.1 lB2.2.2 leftU
                 rB2.1 rB2.2.1 rB2.2.2 (m4 + 2) mH2.1 mH2.2.1 mH2.2.2
                 (UInt64.ofNat m <<< 1)
                 (UInt64.ofNat (-q + gT2.2.2).toNat)
                 (UInt64.ofNat (shiftedSig m q (kOfMQ m q))) with
    | none => rw [hp] at hopt; cases hopt
    | some chosen =>
      rw [hp] at hopt
      have hpkd : pickNearer (shiftedSig m q (kOfMQ m q)) (kOfMQ m q) m q = chosen.toNat :=
        pickNearer_u64_flipped_some_eq q (kOfMQ m q) (shiftedSig m q (kOfMQ m q)) m
          (isIrregular m q) chosen lB2.1 lB2.2.1 lB2.2.2 rB2.1 rB2.2.1 rB2.2.2
          mH2.1 mH2.2.1 mH2.2.2
          hm_pos (by omega) hm_lt hs_ge hk_lo2 hk_hi2 hqh2_lo hqh2_hi rfl
          hlB2_val hrB2_val hmH2_val hp
      rw [hpkd]
      cases hopt
      rfl
  · rw [if_neg hs10]
    push_neg at hs10
    simp only [show (shiftedSig m q (kOfMQ m q) ≥ 10) = False from by simp [hs10],
      if_false] at hopt
    by_cases hs_zero : shiftedSig m q (kOfMQ m q) = 0
    · rw [dif_pos hs_zero] at hopt; cases hopt
    rw [dif_neg hs_zero] at hopt
    by_cases hqh2_lo : -q + (pow10Lookup128 (-(kOfMQ m q))).2.2 < 64
    · rw [dif_pos hqh2_lo] at hopt; cases hopt
    rw [dif_neg hqh2_lo] at hopt
    by_cases hqh2_hi : -q + (pow10Lookup128 (-(kOfMQ m q))).2.2 > 132
    · rw [dif_pos hqh2_hi] at hopt; cases hopt
    rw [dif_neg hqh2_hi] at hopt
    push_neg at hqh2_lo hqh2_hi
    set gT2 := pow10Lookup128 (-(kOfMQ m q)) with hgT2
    set m4 : UInt64 := UInt64.ofNat m <<< 2 with hm4
    set leftU : UInt64 := (if isIrregular m q = true then m4 - 1 else m4 - 2) with hleftU
    have hm4_toNat : m4.toNat = 4 * m := by
      rw [hm4, uint64_shiftLeft_2, UInt64.toNat_mul,
          toNat_ofNat_bounded (show m < 2 ^ 64 by omega),
          show ((4 : UInt64)).toNat = 4 from rfl]
      exact Nat.mod_eq_of_lt (by omega)
    set pLo2 : UInt64 := m4 * gT2.2.1 with hpLo2
    set pLoH2 : UInt64 := mulHi64 m4 gT2.2.1 with hpLoH2
    set pHi2 : UInt64 := m4 * gT2.1 with hpHi2
    set pHiH2 : UInt64 := mulHi64 m4 gT2.1 with hpHiH2
    set pMid2 : UInt64 := pHi2 + pLoH2 with hpMid2
    set pC2 : UInt64 := (if pMid2 < pHi2 then (1 : UInt64) else 0) with hpC2
    set pH2 : UInt64 := pHiH2 + pC2 with hpH2
    set tg2 := add192_192 0 gT2.1 gT2.2.1 0 gT2.1 gT2.2.1 with htg2
    set sbHi2 : UInt64 := (if isIrregular m q = true then 0 else tg2.1) with hsbHi2
    set sbMid2 : UInt64 := (if isIrregular m q = true then gT2.1 else tg2.2.1) with hsbMid2
    set sbLo2 : UInt64 := (if isIrregular m q = true then gT2.2.1 else tg2.2.2) with hsbLo2
    set lB2 := sub192_192 pH2 pMid2 pLo2 sbHi2 sbMid2 sbLo2 with hlB2
    set rB2 := add192_192 pH2 pMid2 pLo2 tg2.1 tg2.2.1 tg2.2.2 with hrB2
    set mH2 := shr1_192 pH2 pMid2 pLo2 with hmH2
    have hG2_lt : gT2.1.toNat * 2 ^ 64 + gT2.2.1.toNat < 2 ^ 128 := by
      have h1 := gT2.1.toNat_lt; have h2 := gT2.2.1.toNat_lt
      omega
    have hmulG2_lt : ∀ b : Nat, b ≤ 4 * m + 2 →
        b * (gT2.1.toNat * 2 ^ 64 + gT2.2.1.toNat) < 2 ^ 192 := by
      intro b hb
      have h3 : b * (gT2.1.toNat * 2 ^ 64 + gT2.2.1.toNat) ≤ 2 ^ 60 * 2 ^ 128 :=
        Nat.mul_le_mul (by omega) (by omega)
      have h4 : (2 : Nat) ^ 60 * 2 ^ 128 < 2 ^ 192 := by
        rw [← pow_add]
        exact Nat.pow_lt_pow_right (by omega) (by omega)
      omega
    have htrip0G2 : triple192Nat 0 gT2.1 gT2.2.1
        = gT2.1.toNat * 2 ^ 64 + gT2.2.1.toNat := by
      unfold triple192Nat
      simp only [show ((0 : UInt64)).toNat = 0 from rfl]
      omega
    have hP2_val : triple192Nat pH2 pMid2 pLo2
        = 4 * m * (gT2.1.toNat * 2 ^ 64 + gT2.2.1.toNat) := by
      have h := mul192_b_g_toNat m4 gT2.1 gT2.2.1
      simp only [] at h
      rw [← hpLo2, ← hpLoH2, ← hpHi2, ← hpHiH2, ← hpMid2, ← hpC2, ← hpH2] at h
      rw [hm4_toNat, Nat.mod_eq_of_lt (hmulG2_lt (4 * m) (by omega))] at h
      exact h
    have h2G2_val : triple192Nat tg2.1 tg2.2.1 tg2.2.2
        = 2 * (gT2.1.toNat * 2 ^ 64 + gT2.2.1.toNat) := by
      rw [htg2, add192_192_toNat 0 gT2.1 gT2.2.1 0 gT2.1 gT2.2.1 (by
        rw [htrip0G2]; omega), htrip0G2]
      omega
    have hlB2_val : triple192Nat lB2.1 lB2.2.1 lB2.2.2
        = (if isIrregular m q = true then 4 * m - 1 else 4 * m - 2)
            * (gT2.1.toNat * 2 ^ 64 + gT2.2.1.toNat) := by
      rw [hlB2, hsbHi2, hsbMid2, hsbLo2]
      by_cases hirr : isIrregular m q = true
      · rw [if_pos hirr, if_pos hirr, if_pos hirr, if_pos hirr,
            sub192_192_toNat pH2 pMid2 pLo2 0 gT2.1 gT2.2.1 (by
              rw [htrip0G2, hP2_val]
              exact Nat.le_mul_of_pos_left _ (by omega)),
            hP2_val, htrip0G2, Nat.sub_mul, Nat.one_mul]
      · rw [if_neg hirr, if_neg hirr, if_neg hirr, if_neg hirr,
            sub192_192_toNat pH2 pMid2 pLo2 tg2.1 tg2.2.1 tg2.2.2 (by
              rw [h2G2_val, hP2_val]
              exact Nat.mul_le_mul_right _ (by omega)),
            hP2_val, h2G2_val, Nat.sub_mul]
    have hrB2_val : triple192Nat rB2.1 rB2.2.1 rB2.2.2
        = (4 * m + 2) * (gT2.1.toNat * 2 ^ 64 + gT2.2.1.toNat) := by
      rw [hrB2, add192_192_toNat pH2 pMid2 pLo2 tg2.1 tg2.2.1 tg2.2.2 (by
            rw [hP2_val, h2G2_val]
            have := hmulG2_lt (4 * m + 2) (by omega)
            rw [Nat.add_mul] at this
            omega),
          hP2_val, h2G2_val, Nat.add_mul]
    have hmH2_val : triple192Nat mH2.1 mH2.2.1 mH2.2.2
        = 2 * m * (gT2.1.toNat * 2 ^ 64 + gT2.2.1.toNat) := by
      rw [hmH2, shr1_192_toNat, hP2_val,
          show 4 * m * (gT2.1.toNat * 2 ^ 64 + gT2.2.1.toNat)
              = 2 * (2 * m * (gT2.1.toNat * 2 ^ 64 + gT2.2.1.toNat)) from by ring,
          Nat.mul_div_cancel_left _ (by omega)]
    have hk_lo2 : pow10Table128_kMin ≤ -(kOfMQ m q) := by omega
    have hk_hi2 : -(kOfMQ m q) ≤ pow10Table128_kMax := by omega
    match hp : pickNearer_u64_flipped lB2.1 lB2.2.1 lB2.2.2 leftU
                 rB2.1 rB2.2.1 rB2.2.2 (m4 + 2) mH2.1 mH2.2.1 mH2.2.2
                 (UInt64.ofNat m <<< 1)
                 (UInt64.ofNat (-q + gT2.2.2).toNat)
                 (UInt64.ofNat (shiftedSig m q (kOfMQ m q))) with
    | none => rw [hp] at hopt; cases hopt
    | some chosen =>
      rw [hp] at hopt
      have hpkd : pickNearer (shiftedSig m q (kOfMQ m q)) (kOfMQ m q) m q = chosen.toNat :=
        pickNearer_u64_flipped_some_eq q (kOfMQ m q) (shiftedSig m q (kOfMQ m q)) m
          (isIrregular m q) chosen lB2.1 lB2.2.1 lB2.2.2 rB2.1 rB2.2.1 rB2.2.2
          mH2.1 mH2.2.1 mH2.2.2
          hm_pos (by omega) hm_lt hs_ge hk_lo2 hk_hi2 hqh2_lo hqh2_hi rfl
          hlB2_val hrB2_val hmH2_val hp
      rw [hpkd]
      cases hopt
      rfl


/-! ## Biased-window bridges at the `[5198, 5202]` guard -/

theorem wB128_lt (q h : Int) (h1 : ¬ q < -1074) (h2 : ¬ q > 971)
    (hh : -2048 ≤ h ∧ h < 2048) :
    (((UInt64.ofNat (h + 2048).toNat + 4096) - UInt64.ofNat (q + 1074).toNat)
        < (5197 : UInt64)) = (-q + h < 127) := by
  have ht := toNat_tA q h h1 h2 hh
  rw [show (((UInt64.ofNat (h + 2048).toNat + 4096) - UInt64.ofNat (q + 1074).toNat)
        < (5197 : UInt64)) ↔ _ from UInt64.lt_iff_toNat_lt,
      show ((5197 : UInt64)).toNat = 5197 from rfl]
  exact propext (by omega)

theorem wB128_gt (q h : Int) (h1 : ¬ q < -1074) (h2 : ¬ q > 971)
    (hh : -2048 ≤ h ∧ h < 2048) :
    (((UInt64.ofNat (h + 2048).toNat + 4096) - UInt64.ofNat (q + 1074).toNat)
        > (5202 : UInt64)) = (-q + h > 132) := by
  have ht := toNat_tA q h h1 h2 hh
  rw [show (((UInt64.ofNat (h + 2048).toNat + 4096) - UInt64.ofNat (q + 1074).toNat)
        > (5202 : UInt64)) ↔ _ from UInt64.lt_iff_toNat_lt,
      show ((5202 : UInt64)).toNat = 5202 from rfl]
  exact propext (by omega)

theorem wB128_val (q h : Int) (h1 : ¬ q < -1074) (h2 : ¬ q > 971)
    (hh : -2048 ≤ h ∧ h < 2048) (hlo : ¬ -q + h < 127) (hhi : ¬ -q + h > 132) :
    ((UInt64.ofNat (h + 2048).toNat + 4096) - UInt64.ofNat (q + 1074).toNat) - 5197
      = UInt64.ofNat (-q + h - 127).toNat := by
  have ht := toNat_tA q h h1 h2 hh
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_sub_of_le _ _ (by
        rw [UInt64.le_iff_toNat_le, show ((5197 : UInt64)).toNat = 5197 from rfl]
        omega),
      show ((5197 : UInt64)).toNat = 5197 from rfl,
      UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  omega

/-- v12 with `s` from the boundary product: `5P = P + (P <<< 2)`, digit
    count = top limb of `5P` shifted by `uB' - 5197`; window tightened
    to `[5198, 5202]` (`w ∈ [128, 132]`); the 192-bit table, its biased
    windows, and the 5-limb multiply are gone. (v11 with the pickNearer path flipped too: table entry for `-k` at
    biased index `648 - kB`, same `[5134, 5202]` biased window, one
    product `P₂ = 4m·g″` for all fall-through tests, midpoint by exact
    halving. (v8 with the `k+1` interval tests replaced by the flipped scheme:
    table entry for `-(k+1)` at biased index `647 - kB`, window guard
    `uB' = (h'+2048+4096) - qB ∈ [5134, 5202]`, one boundary product
    `P = 4m·g'` shared across `uV`/`wV`, candidate on the shift side. -/
@[inline]
def shortestUnsigned_u64_opt_v13 (mU : UInt64) (qB : UInt64) : Option (UInt64 × Int) :=
  if _h_m0 : mU = 0 then none
  else if _h_m : mU ≥ (9007199254740992 : UInt64) then none
  else if _h_q : qB > 2045 then none
  else
    let irregular := isIrregularB mU qB
    let kB : UInt64 := kBOfMQ mU qB
    if _h_k : kB > 647 then none
    else
      let kBn : Nat := kB.toNat
      let k : Int := (kBn : Int) - 324
      let gT := pow10Table128.getD (647 - kBn) pow10Table128_default
      let uB' : UInt64 := (hB128.getD (647 - kBn) 0 + 4096) - qB
      if _h_qh_lo : uB' < 5197 then none
      else if _h_qh_hi : uB' > 5202 then none
      else
        let w8 : UInt64 := uB' - 5070
        let m4 : UInt64 := mU <<< 2
        let pLo  : UInt64 := m4 * gT.2.1
        let pLoH : UInt64 := mulHi64 m4 gT.2.1
        let pHi  : UInt64 := m4 * gT.1
        let pHiH : UInt64 := mulHi64 m4 gT.1
        let pMidSum : UInt64 := pHi + pLoH
        let pCarry : UInt64 := if pMidSum < pHi then 1 else 0
        let p192Hi : UInt64 := pHiH + pCarry
        let p4 := shl2_192 p192Hi pMidSum pLo
        let p5 := add192_192 p4.1 p4.2.1 p4.2.2 p192Hi pMidSum pLo
        let sU : UInt64 := p5.1 >>> (uB' - 5197)
        if _h_s : sU ≥ (144115188075855872 : UInt64) then none
        else if sU ≥ (10 : UInt64) then
            let sHighU : UInt64 := sU / 10
            let leftU : UInt64 := if irregular then m4 - 1 else m4 - 2
            let rightU : UInt64 := m4 + 2
            let tg := add192_192 0 gT.1 gT.2.1 0 gT.1 gT.2.1
            let sbHi : UInt64 := if irregular then 0 else tg.1
            let sbMid : UInt64 := if irregular then gT.1 else tg.2.1
            let sbLo : UInt64 := if irregular then gT.2.1 else tg.2.2
            let lB := sub192_192 p192Hi pMidSum pLo sbHi sbMid sbLo
            let rB := add192_192 p192Hi pMidSum pLo tg.1 tg.2.1 tg.2.2
            let uV := inRoundingInterval_u64_flipped_u8 lB.1 lB.2.1 lB.2.2 leftU
                        rB.1 rB.2.1 rB.2.2 rightU w8 sHighU
            if uV = inRoundingInterval_u8_AMBIG then none
            else if uV = inRoundingInterval_u8_TRUE then some (sHighU, k + 1)
            else
              let wV := inRoundingInterval_u64_flipped_u8 lB.1 lB.2.1 lB.2.2 leftU
                          rB.1 rB.2.1 rB.2.2 rightU w8 (sHighU + 1)
              if wV = inRoundingInterval_u8_AMBIG then none
              else if wV = inRoundingInterval_u8_TRUE then some (sHighU + 1, k + 1)
              else
                let gT2 := pow10Table128.getD (648 - kBn) pow10Table128_default
                let uC' : UInt64 := (hB128.getD (648 - kBn) 0 + 4096) - qB
                if _h_qh2_lo : uC' < 5134 then none
                else if _h_qh2_hi : uC' > 5202 then none
                else
                  let w28 : UInt64 := uC' - 5070
                  let pLo2  : UInt64 := m4 * gT2.2.1
                  let pLoH2 : UInt64 := mulHi64 m4 gT2.2.1
                  let pHi2  : UInt64 := m4 * gT2.1
                  let pHiH2 : UInt64 := mulHi64 m4 gT2.1
                  let pMidSum2 : UInt64 := pHi2 + pLoH2
                  let pCarry2 : UInt64 := if pMidSum2 < pHi2 then 1 else 0
                  let p192Hi2 : UInt64 := pHiH2 + pCarry2
                  let tg2 := add192_192 0 gT2.1 gT2.2.1 0 gT2.1 gT2.2.1
                  let sbHi2 : UInt64 := if irregular then 0 else tg2.1
                  let sbMid2 : UInt64 := if irregular then gT2.1 else tg2.2.1
                  let sbLo2 : UInt64 := if irregular then gT2.2.1 else tg2.2.2
                  let lB2 := sub192_192 p192Hi2 pMidSum2 pLo2 sbHi2 sbMid2 sbLo2
                  let rB2 := add192_192 p192Hi2 pMidSum2 pLo2 tg2.1 tg2.2.1 tg2.2.2
                  let mH := shr1_192 p192Hi2 pMidSum2 pLo2
                  let twoM : UInt64 := mU <<< 1
                  match pickNearer_u64_flipped lB2.1 lB2.2.1 lB2.2.2 leftU
                          rB2.1 rB2.2.1 rB2.2.2 rightU mH.1 mH.2.1 mH.2.2 twoM w28 sU with
                  | none => none
                  | some chosen => some (chosen, k)
        else if _h_s1 : sU = 0 then none
        else
          let gT2 := pow10Table128.getD (648 - kBn) pow10Table128_default
          let uC' : UInt64 := (hB128.getD (648 - kBn) 0 + 4096) - qB
          if _h_qh2_lo : uC' < 5134 then none
          else if _h_qh2_hi : uC' > 5202 then none
          else
            let w28 : UInt64 := uC' - 5070
            let m4 : UInt64 := mU <<< 2
            let leftU : UInt64 := if irregular then m4 - 1 else m4 - 2
            let rightU : UInt64 := m4 + 2
            let pLo2  : UInt64 := m4 * gT2.2.1
            let pLoH2 : UInt64 := mulHi64 m4 gT2.2.1
            let pHi2  : UInt64 := m4 * gT2.1
            let pHiH2 : UInt64 := mulHi64 m4 gT2.1
            let pMidSum2 : UInt64 := pHi2 + pLoH2
            let pCarry2 : UInt64 := if pMidSum2 < pHi2 then 1 else 0
            let p192Hi2 : UInt64 := pHiH2 + pCarry2
            let tg2 := add192_192 0 gT2.1 gT2.2.1 0 gT2.1 gT2.2.1
            let sbHi2 : UInt64 := if irregular then 0 else tg2.1
            let sbMid2 : UInt64 := if irregular then gT2.1 else tg2.2.1
            let sbLo2 : UInt64 := if irregular then gT2.2.1 else tg2.2.2
            let lB2 := sub192_192 p192Hi2 pMidSum2 pLo2 sbHi2 sbMid2 sbLo2
            let rB2 := add192_192 p192Hi2 pMidSum2 pLo2 tg2.1 tg2.2.1 tg2.2.2
            let mH := shr1_192 p192Hi2 pMidSum2 pLo2
            let twoM : UInt64 := mU <<< 1
            match pickNearer_u64_flipped lB2.1 lB2.2.1 lB2.2.2 leftU
                    rB2.1 rB2.2.1 rB2.2.2 rightU mH.1 mH.2.1 mH.2.2 twoM w28 sU with
            | none => none
            | some chosen => some (chosen, k)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 3200000 in
/-- Arg-biasing transfer: a `some` result of the pure-UInt64 v11 kernel
    is a `some` result of the spec-table flipped kernel. Assembles the
    existing biased-index/window component lemmas. -/
theorem shortestUnsigned_u64_opt_v13_some_eq_flip3 (mU qB : UInt64) (r : UInt64 × Int)
    (hopt : shortestUnsigned_u64_opt_v13 mU qB = some r) :
    shortestUnsigned_u64_opt_flip3 mU.toNat ((qB.toNat : Int) - 1074) = some r := by
  unfold shortestUnsigned_u64_opt_v13 at hopt
  unfold shortestUnsigned_u64_opt_flip3
  by_cases h_m0 : mU = 0
  · rw [dif_pos h_m0] at hopt; cases hopt
  rw [dif_neg h_m0] at hopt
  by_cases h_m : mU ≥ (9007199254740992 : UInt64)
  · rw [dif_pos h_m] at hopt; cases hopt
  rw [dif_neg h_m] at hopt
  rw [dif_neg (show ¬ mU.toNat = 0 from fun hc => h_m0 (by
    apply UInt64.toNat_inj.mp
    rw [hc]; rfl))]
  have h_m' : ¬ mU.toNat ≥ (1 <<< 53 : Nat) := by
    rw [ge_iff_le, UInt64.le_iff_toNat_le,
        show ((9007199254740992 : UInt64)).toNat = 1 <<< 53 from rfl] at h_m
    exact h_m
  rw [dif_neg h_m']
  rw [dif_neg (show ¬ ((qB.toNat : Int) - 1074) < -1074 from by omega)]
  by_cases h_q : qB > 2045
  · rw [dif_pos h_q] at hopt; cases hopt
  rw [dif_neg h_q] at hopt
  have h_q' : qB.toNat ≤ 2045 := by
    rw [gt_iff_lt, UInt64.lt_iff_toNat_lt, show ((2045 : UInt64)).toNat = 2045 from rfl] at h_q
    omega
  rw [dif_neg (show ¬ ((qB.toNat : Int) - 1074) > 971 from by omega)]
  have hkf := kBOfMQ_eq mU qB h_q'
  have hknn := hkf.1
  have hkval := hkf.2
  by_cases h_k : kBOfMQ mU qB > 647
  · rw [dif_pos h_k] at hopt; cases hopt
  rw [dif_neg h_k] at hopt
  have hkB_le : (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) + 324).toNat ≤ 647 := by
    rw [← hkval]
    rw [gt_iff_lt, UInt64.lt_iff_toNat_lt, show ((647 : UInt64)).toNat = 647 from rfl] at h_k
    omega
  have hkMin_lit : pow10Table128_kMin = (-324 : Int) := rfl
  have hkMax_lit : pow10Table128_kMax = (324 : Int) := rfl
  have hklo : ¬ kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) < pow10Table128_kMin := by
    rw [hkMin_lit]; omega
  have hkhi : ¬ kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) + 1 > pow10Table128_kMax := by
    rw [hkMax_lit]; omega
  rw [dif_neg hklo, dif_neg hkhi]
  -- Alignment equations.
  have ekidx : (kBOfMQ mU qB).toNat
      = (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) + 324).toNat := hkval
  have ekexit : (((kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) + 324).toNat : Int)) - 324
      = kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) := by omega
  have eqb : UInt64.ofNat (((qB.toNat : Int) - 1074) + 1074).toNat = qB := by
    rw [show (((qB.toNat : Int) - 1074) + 1074).toNat = qB.toNat from by omega,
        UInt64.ofNat_toNat]
  have em : UInt64.ofNat mU.toNat = mU := UInt64.ofNat_toNat
  have eirr : isIrregular mU.toNat ((qB.toNat : Int) - 1074) = isIrregularB mU qB :=
    (isIrregularB_eq mU qB).symm
  simp only [ekidx, ekexit] at hopt
  -- Index bounds.
  have hiflip : 647 - (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) + 324).toNat
      < pow10Table128.size := by rw [pow10Table128_size_eq]; omega
  have hilow : 648 - (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) + 324).toNat
      < pow10Table128.size := by rw [pow10Table128_size_eq]; omega
  -- Goal side: lookups → getD, ofNat mU.toNat → mU, isIrregular → isIrregularB.
  have eflip := lookup128_negHigh (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074)) hklo hkhi
  have elow := lookup128_neg (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074)) hklo hkhi
  simp only []
  rw [eflip, elow]
  simp only [em, eirr]
  -- hopt side: biased h-tables → ofNat (h + 2048) forms.
  have cflip := hB128_getD _ hiflip
  have clow := hB128_getD _ hilow
  simp only [cflip, clow] at hopt
  -- h bounds at the three entries.
  have hhflip := hBound128_getD _ hiflip
  have hhlow := hBound128_getD _ hilow
  have h_q_lo' : ¬ ((qB.toNat : Int) - 1074) < -1074 := by omega
  have h_q_hi' : ¬ ((qB.toNat : Int) - 1074) > 971 := by omega
  -- Flipped window guards (top-level, tightened to [5198, 5202]).
  have wlt := wB128_lt ((qB.toNat : Int) - 1074) _ h_q_lo' h_q_hi' hhflip
  have wgt := wB128_gt ((qB.toNat : Int) - 1074) _ h_q_lo' h_q_hi' hhflip
  rw [eqb] at wlt wgt
  simp only [wlt, wgt] at hopt
  by_cases hqhlo : -((qB.toNat : Int) - 1074) + (pow10Table128.getD
      (647 - (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) + 324).toNat)
      pow10Table128_default).2.2 < 127
  · rw [dif_pos hqhlo] at hopt; cases hopt
  rw [dif_neg hqhlo] at hopt
  rw [dif_neg hqhlo]
  by_cases hqhhi : -((qB.toNat : Int) - 1074) + (pow10Table128.getD
      (647 - (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) + 324).toNat)
      pow10Table128_default).2.2 > 132
  · rw [dif_pos hqhhi] at hopt; cases hopt
  rw [dif_neg hqhhi] at hopt
  rw [dif_neg hqhhi]
  have hqhlo64 : ¬ -((qB.toNat : Int) - 1074) + (pow10Table128.getD
      (647 - (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) + 324).toNat)
      pow10Table128_default).2.2 < 64 := by omega
  have wval := wB_val ((qB.toNat : Int) - 1074) _ h_q_lo' h_q_hi' hhflip hqhlo64 hqhhi
  rw [eqb] at wval
  rw [wval] at hopt
  have wval197 := wB128_val ((qB.toNat : Int) - 1074) _ h_q_lo' h_q_hi' hhflip hqhlo hqhhi
  rw [eqb] at wval197
  rw [wval197] at hopt
  -- Compact the aligned product pipeline.
  set gTb := (pow10Table128.getD
      (647 - (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) + 324).toNat)
      pow10Table128_default) with hgTb
  set m4b : UInt64 := mU <<< 2 with hm4b
  set pLob : UInt64 := m4b * gTb.2.1 with hpLob
  set pLoHb : UInt64 := mulHi64 m4b gTb.2.1 with hpLoHb
  set pHib : UInt64 := m4b * gTb.1 with hpHib
  set pHiHb : UInt64 := mulHi64 m4b gTb.1 with hpHiHb
  set pMidb : UInt64 := pHib + pLoHb with hpMidb
  set pCb : UInt64 := (if pMidb < pHib then (1 : UInt64) else 0) with hpCb
  set pHb : UInt64 := pHiHb + pCb with hpHb
  set p4b := shl2_192 pHb pMidb pLob with hp4b
  set p5b := add192_192 p4b.1 p4b.2.1 p4b.2.2 pHb pMidb pLob with hp5b
  set sUb : UInt64 := p5b.1 >>> UInt64.ofNat
      (-((qB.toNat : Int) - 1074) + gTb.2.2 - 127).toNat with hsUb
  by_cases h_s : sUb ≥ (144115188075855872 : UInt64)
  · rw [dif_pos h_s] at hopt; cases hopt
  rw [dif_neg h_s] at hopt
  rw [dif_neg h_s]
  -- pickNearer windows propexts (the -k entry).
  have uclt := wB_lt ((qB.toNat : Int) - 1074) _ h_q_lo' h_q_hi' hhlow
  have ucgt := wB_gt ((qB.toNat : Int) - 1074) _ h_q_lo' h_q_hi' hhlow
  rw [eqb] at uclt ucgt
  simp only [uclt, ucgt] at hopt
  by_cases hge10 : sUb ≥ (10 : UInt64)
  · rw [if_pos hge10] at hopt
    rw [if_pos hge10]
    by_cases huc1 : -((qB.toNat : Int) - 1074) + (pow10Table128.getD
        (648 - (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) + 324).toNat)
        pow10Table128_default).2.2 < 64
    · simp only [dif_pos huc1] at hopt ⊢
      exact hopt
    simp only [dif_neg huc1] at hopt ⊢
    by_cases huc2 : -((qB.toNat : Int) - 1074) + (pow10Table128.getD
        (648 - (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) + 324).toNat)
        pow10Table128_default).2.2 > 132
    · simp only [dif_pos huc2] at hopt ⊢
      exact hopt
    simp only [dif_neg huc2] at hopt ⊢
    have ucval := wB_val ((qB.toNat : Int) - 1074) _ h_q_lo' h_q_hi' hhlow huc1 huc2
    rw [eqb] at ucval
    rw [ucval] at hopt
    exact hopt
  · rw [if_neg hge10] at hopt
    rw [if_neg hge10]
    by_cases hs0 : sUb = 0
    · rw [dif_pos hs0] at hopt; cases hopt
    rw [dif_neg hs0] at hopt
    rw [dif_neg hs0]
    by_cases huc1 : -((qB.toNat : Int) - 1074) + (pow10Table128.getD
        (648 - (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) + 324).toNat)
        pow10Table128_default).2.2 < 64
    · simp only [dif_pos huc1] at hopt ⊢
      exact hopt
    simp only [dif_neg huc1] at hopt ⊢
    by_cases huc2 : -((qB.toNat : Int) - 1074) + (pow10Table128.getD
        (648 - (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) + 324).toNat)
        pow10Table128_default).2.2 > 132
    · simp only [dif_pos huc2] at hopt ⊢
      exact hopt
    simp only [dif_neg huc2] at hopt ⊢
    have ucval := wB_val ((qB.toNat : Int) - 1074) _ h_q_lo' h_q_hi' hhlow huc1 huc2
    rw [eqb] at ucval
    rw [ucval] at hopt
    exact hopt

/-! ## Wrapper, exponent range, emit, entry point -/

/-- v13 entry: same packed fallback as v8/v9. -/
@[inline]
def shortestUnsigned_v13 (mU qB : UInt64) : Nat × Int :=
  match shortestUnsigned_u64_opt_v13 mU qB with
  | some (sU, k) => (sU.toNat, k)
  | none => shortestUnsigned_packed mU.toNat ((qB.toNat : Int) - 1074)

theorem shortestUnsigned_v13_eq_packed (mU qB : UInt64) :
    shortestUnsigned_v13 mU qB
      = shortestUnsigned_packed mU.toNat ((qB.toNat : Int) - 1074) := by
  unfold shortestUnsigned_v13
  match h : shortestUnsigned_u64_opt_v13 mU qB with
  | none => rfl
  | some (sU, k) =>
    exact (shortestUnsigned_u64_opt_flip3_some_eq_packed _ _ _ _
      (shortestUnsigned_u64_opt_v13_some_eq_flip3 mU qB (sU, k) h)).symm

theorem shortestUnsigned_v13_eq_v8 (mU qB : UInt64) :
    shortestUnsigned_v13 mU qB = shortestUnsigned_v8 mU qB := by
  rw [shortestUnsigned_v13_eq_packed, shortestUnsigned_packed_eq,
      ← shortestUnsigned_v5_eq, ← shortestUnsigned_v7_eq_v5,
      ← shortestUnsigned_v8_eq_v7]

set_option maxHeartbeats 1600000 in
/-- Every successful v11 exit carries an exponent in `[-324, 325]`
    (mirror of the v11 one). -/
theorem shortestUnsigned_u64_opt_v13_k_range (mU qB : UInt64)
    (s : UInt64) (k : Int)
    (h : shortestUnsigned_u64_opt_v13 mU qB = some (s, k)) :
    -324 ≤ k ∧ k ≤ 325 := by
  by_cases h1 : mU = 0
  · rw [show shortestUnsigned_u64_opt_v13 mU qB = none from by
      unfold shortestUnsigned_u64_opt_v13; rw [dif_pos h1]] at h
    cases h
  by_cases h2 : mU ≥ (9007199254740992 : UInt64)
  · rw [show shortestUnsigned_u64_opt_v13 mU qB = none from by
      unfold shortestUnsigned_u64_opt_v13; rw [dif_neg h1, dif_pos h2]] at h
    cases h
  by_cases h3 : qB > 2045
  · rw [show shortestUnsigned_u64_opt_v13 mU qB = none from by
      unfold shortestUnsigned_u64_opt_v13; rw [dif_neg h1, dif_neg h2, dif_pos h3]] at h
    cases h
  by_cases h4 : kBOfMQ mU qB > 647
  · rw [show shortestUnsigned_u64_opt_v13 mU qB = none from by
      unfold shortestUnsigned_u64_opt_v13;
        rw [dif_neg h1, dif_neg h2, dif_neg h3, dif_pos h4]] at h
    cases h
  -- Transfer the value to the spec through the chain.
  have hwrap : shortestUnsigned mU.toNat ((qB.toNat : Int) - 1074) = (s.toNat, k) := by
    have h11 : shortestUnsigned_v13 mU qB = (s.toNat, k) := by
      unfold shortestUnsigned_v13
      rw [h]
    rw [← shortestUnsigned_packed_eq, ← shortestUnsigned_v13_eq_packed, h11]
  have hsnd : (shortestUnsigned mU.toNat ((qB.toNat : Int) - 1074)).2 = k := by
    rw [hwrap]
  have hmem : k = kOfMQ mU.toNat ((qB.toNat : Int) - 1074)
      ∨ k = kOfMQ mU.toNat ((qB.toNat : Int) - 1074) + 1 := by
    unfold shortestUnsigned at hsnd
    dsimp only [] at hsnd
    split at hsnd
    · split at hsnd
      · right; exact hsnd.symm
      · split at hsnd
        · right; exact hsnd.symm
        · left; exact hsnd.symm
    · left; exact hsnd.symm
  have hq_le : qB.toNat ≤ 2045 := by
    have := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp h3)
    simpa using this
  have hkof := kBOfMQ_eq mU qB hq_le
  have hk_le : (kBOfMQ mU qB).toNat ≤ 647 := by
    have := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp h4)
    simpa using this
  have hk_hi : kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) ≤ 323 := by
    rw [hkof.2] at hk_le
    omega
  have hkk : kOfMQ mU.toNat ((qB.toNat : Int) - 1074)
      = kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) :=
    congrFun (congrFun kOfMQ_eq_fast_csimp mU.toNat) ((qB.toNat : Int) - 1074)
  have hk_lo := hkof.1
  rcases hmem with rfl | rfl <;> rw [hkk] <;> omega

/-- `emitTail7` over the v13 kernel. -/
@[inline]
def emitTail7 (sign : Bool) (mU qB : UInt64) : String :=
  if mU = 0 then (if sign then "-0" else "0")
  else
    match shortestUnsigned_u64_opt_v13 mU qB with
    | some (sU, exp) =>
      let sig := sU.toNat
      if sig = 0 then (if sign then "-0" else "0")
      else if sig % 10 ≠ 0 then
        emitCheckedIdx sign sig exp
      else
        let (sig', exp') := Srtfp.Decimal.canonicaliseAux sig exp
        if sig' = 0 then (if sign then "-0" else "0")
        else emitChecked sign sig' exp'
    | none =>
      let (sig, exp) := shortestUnsigned_packed mU.toNat ((qB.toNat : Int) - 1074)
      if sig = 0 then (if sign then "-0" else "0")
      else if sig % 10 ≠ 0 then
        emitChecked sign sig exp
      else
        let (sig', exp') := Srtfp.Decimal.canonicaliseAux sig exp
        if sig' = 0 then (if sign then "-0" else "0")
        else emitChecked sign sig' exp'

theorem emitTail7_eq (sign : Bool) (mU qB : UInt64) :
    emitTail7 sign mU qB = emitTail2 sign mU qB := by
  unfold emitTail7 emitTail2
  by_cases h0 : mU = 0
  · rw [if_pos h0, if_pos h0]
  rw [if_neg h0, if_neg h0]
  have h8pk : shortestUnsigned_v8 mU qB
      = shortestUnsigned_packed mU.toNat ((qB.toNat : Int) - 1074) := by
    rw [shortestUnsigned_v8_eq_v7, shortestUnsigned_v7_eq_v5, shortestUnsigned_v5_eq,
        ← shortestUnsigned_packed_eq]
  rw [h8pk]
  cases hv : shortestUnsigned_u64_opt_v13 mU qB with
  | none => rfl
  | some p =>
    obtain ⟨sU, exp⟩ := p
    have hpk : shortestUnsigned_packed mU.toNat ((qB.toNat : Int) - 1074)
        = (sU.toNat, exp) :=
      shortestUnsigned_u64_opt_flip3_some_eq_packed _ _ _ _
        (shortestUnsigned_u64_opt_v13_some_eq_flip3 mU qB (sU, exp) hv)
    rw [hpk]
    have hrange := shortestUnsigned_u64_opt_v13_k_range mU qB sU exp hv
    simp only []
    rw [emitCheckedIdx_eq sign sU.toNat exp hrange.1]

/-- `toStringFast9` over the v13 kernel. -/
@[inline]
def toStringFast9 (f : _root_.Float) : String :=
  let bits := f.toBits
  let expBits : UInt64 := (bits >>> 52) &&& 0x7FF
  let mantBits : UInt64 := bits &&& 0x000F_FFFF_FFFF_FFFF
  if expBits = 0x7FF then
    if mantBits ≠ 0 then "NaN"
    else if (bits >>> 63) ≠ 0 then "-Infinity" else "Infinity"
  else
    emitTail7 (decide (bits >>> 63 ≠ 0))
      (if expBits = 0 then mantBits else mantBits + 4503599627370496)
      (if expBits = 0 then 0 else expBits - 1)

theorem toStringFast9_eq (f : _root_.Float) : toStringFast9 f = toStringFast4 f := by
  unfold toStringFast9 toStringFast4
  simp only [emitTail7_eq]

@[csimp]
theorem floatToStrRef_eq_toStringFast9 : @floatToStrRef = @toStringFast9 := by
  funext f
  rw [toStringFast9_eq]
  exact congrFun floatToStrRef_eq_toStringFast4 f

end Srtfp.Schubfach

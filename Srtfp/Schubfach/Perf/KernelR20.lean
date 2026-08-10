/- R20 decode glue: the unconditional (`B`-unbounded) widened floor
   equality for the Schubfach fast kernel over the full binary64 domain.

   The R20 band sweeps (`R20BandSweep.lean`) establish `residueR20Cond` for
   every binary64 input *keyed by the band shape* (`q ≥ 0` ↦ band 2,
   `q < 0` ↦ band 1).  This file connects those band-keyed residues to the
   *kernel-keyed* residue consumed by `shiftedSig_floor_widened_of_residue`
   (`B = 2^qNeg · 10^kPos`, `N = m · 2^qPos · 10^kNeg`, with the four
   sign-split exponents of a real decode).

   The sign correspondence for a real binary64 decode `(m, q)` with
   `k = kOfMQ m q` is:

   * `q ≥ 0, k ≥ 0` → band 2: `B = 10^kPos`, `N = m · 2^q`.
   * `q < 0, k < 0` → band 1: `B = 2^qNeg`, `N = m · 10^kNeg`.
   * `q ≥ 0, k < 0` → `B = 1` (safe, residue trivial: `m ≤ 2^s`).

   The fourth case `q < 0, k ≥ 0` is impossible (`q < 0 ⇒ k < 0` since the
   `floorLog10*` magic constants are positive-scaled floors).

   Combining the residue with `shiftedSig_floor_widened_of_residue` gives
   the floor equality with NO `B < 2^64` accuracy guard, valid over the
   entire binary64 domain.  This is what lets the orchestration drop the
   `B < 2^64` dispatch and route every real decode through the UInt64
   kernel.
-/
import Srtfp.Schubfach.R20BandSweep
import Srtfp.Schubfach.KernelCorrectness
import Srtfp.Schubfach.Perf.Kernel128

namespace Srtfp.Schubfach

open Srtfp.Schubfach.R20Sweep

/-! ## `floorLog10*` sign / magnitude bounds

The magic constants satisfy `0 < C ≤ 2^41` and `A < 0`, so the floors are
sign-faithful and `|k| ≤ |q|`. -/

/-- `C ≤ 2^41`: the `log₁₀ 2` numerator is below the shift width. -/
private theorem constC_le : constC ≤ 2 ^ shiftQ := by decide

/-- `floorLog10Pow2 q ≤ q` for `q ≥ 0`. -/
theorem floorLog10Pow2_le_self (q : Int) (hq : 0 ≤ q) : floorLog10Pow2 q ≤ q := by
  unfold floorLog10Pow2 shiftQ constC
  rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide)]
  have hle : q * 661971961083 ≤ q * 2 ^ 41 := by
    apply Int.mul_le_mul_of_nonneg_left _ hq; decide
  calc q * 661971961083 / 2 ^ 41 ≤ q * 2 ^ 41 / 2 ^ 41 :=
        Int.ediv_le_ediv (by decide) hle
    _ = q := Int.mul_ediv_cancel _ (by decide)

/-- `floorLog10ThreeQuartersPow2 q ≤ q` for `q ≥ 0`. -/
theorem floorLog10ThreeQuartersPow2_le_self (q : Int) (hq : 0 ≤ q) :
    floorLog10ThreeQuartersPow2 q ≤ q := by
  unfold floorLog10ThreeQuartersPow2 shiftQ constC constA
  rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide)]
  have hle : q * 661971961083 + (-274743187321) ≤ q * 2 ^ 41 := by
    have : (661971961083 : Int) ≤ 2 ^ 41 := by decide
    nlinarith [hq, this]
  calc (q * 661971961083 + (-274743187321)) / 2 ^ 41 ≤ q * 2 ^ 41 / 2 ^ 41 :=
        Int.ediv_le_ediv (by decide) hle
    _ = q := Int.mul_ediv_cancel _ (by decide)

/-- `floorLog10Pow2 q < 0` for `q < 0`. -/
theorem floorLog10Pow2_neg (q : Int) (hq : q < 0) : floorLog10Pow2 q < 0 := by
  unfold floorLog10Pow2 shiftQ constC
  apply Int.fdiv_neg_of_neg_of_pos
  · exact Int.mul_neg_of_neg_of_pos hq (by decide)
  · decide

/-- `floorLog10ThreeQuartersPow2 q < 0` for `q < 0`. -/
theorem floorLog10ThreeQuartersPow2_neg (q : Int) (hq : q < 0) :
    floorLog10ThreeQuartersPow2 q < 0 := by
  unfold floorLog10ThreeQuartersPow2 shiftQ constC constA
  apply Int.fdiv_neg_of_neg_of_pos
  · have : q * 661971961083 < 0 := Int.mul_neg_of_neg_of_pos hq (by decide)
    omega
  · decide

/-- `q ≤ floorLog10Pow2 q` for `q < 0` (i.e. `|k| ≤ |q|` in band 1). -/
theorem self_le_floorLog10Pow2 (q : Int) (hq : q < 0) : q ≤ floorLog10Pow2 q := by
  unfold floorLog10Pow2 shiftQ constC
  rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide)]
  have hle : q * 2 ^ 41 ≤ q * 661971961083 := by
    have : (661971961083 : Int) ≤ 2 ^ 41 := by decide
    nlinarith [hq, this]
  calc q = q * 2 ^ 41 / 2 ^ 41 := (Int.mul_ediv_cancel _ (by decide)).symm
    _ ≤ q * 661971961083 / 2 ^ 41 := Int.ediv_le_ediv (by decide) hle

/-- `q ≤ floorLog10ThreeQuartersPow2 q` for `q < 0`. -/
theorem self_le_floorLog10ThreeQuartersPow2 (q : Int) (hq : q < 0) :
    q ≤ floorLog10ThreeQuartersPow2 q := by
  unfold floorLog10ThreeQuartersPow2 shiftQ constC constA
  rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide)]
  have hle : q * 2 ^ 41 ≤ q * 661971961083 + (-274743187321) := by
    have : (661971961083 : Int) ≤ 2 ^ 41 := by decide
    nlinarith [hq, this]
  calc q = q * 2 ^ 41 / 2 ^ 41 := (Int.mul_ediv_cancel _ (by decide)).symm
    _ ≤ (q * 661971961083 + (-274743187321)) / 2 ^ 41 := Int.ediv_le_ediv (by decide) hle

/-- `kOfMQ m q < 0` whenever `q < 0`. -/
theorem kOfMQ_neg_of_neg (m : Nat) (q : Int) (hq : q < 0) : kOfMQ m q < 0 := by
  unfold kOfMQ
  by_cases h : isIrregular m q = true
  · rw [if_pos h]; exact floorLog10ThreeQuartersPow2_neg q hq
  · rw [if_neg h]; exact floorLog10Pow2_neg q hq

/-- `kOfMQ m q ≤ q` whenever `q ≥ 0` (band-2 magnitude bound). -/
theorem kOfMQ_le_self (m : Nat) (q : Int) (hq : 0 ≤ q) : kOfMQ m q ≤ q := by
  unfold kOfMQ
  by_cases h : isIrregular m q = true
  · rw [if_pos h]; exact floorLog10ThreeQuartersPow2_le_self q hq
  · rw [if_neg h]; exact floorLog10Pow2_le_self q hq

/-- `q ≤ kOfMQ m q` whenever `q < 0` (band-1 magnitude bound). -/
theorem self_le_kOfMQ (m : Nat) (q : Int) (hq : q < 0) : q ≤ kOfMQ m q := by
  unfold kOfMQ
  by_cases h : isIrregular m q = true
  · rw [if_pos h]; exact self_le_floorLog10ThreeQuartersPow2 q hq
  · rw [if_neg h]; exact self_le_floorLog10Pow2 q hq

/-! ## Decode-keyed residue over the binary64 domain

The central glue: `residueR20Cond` for the kernel quantities
`B = 2^qNeg · 10^kPos`, `N = m · 2^qPos · 10^kNeg` (the four sign-split
exponents of `q` and `k = kOfMQ m q`), with NO `B < 2^64` guard. -/

/-- Band-2 candidate membership: `(kOfMQ m q).toNat` is one of the two
    `floorLog10*` candidates the band sweep checks. -/
theorem kOfMQ_toNat_candidate2 (m : Nat) (q : Nat) :
    (kOfMQ m q).toNat = (floorLog10Pow2 q).toNat ∨
    (kOfMQ m q).toNat = (floorLog10ThreeQuartersPow2 q).toNat := by
  unfold kOfMQ
  by_cases h : isIrregular m q = true
  · rw [if_pos h]; exact Or.inr rfl
  · rw [if_neg h]; exact Or.inl rfl

/-- Band-1 candidate membership: `(-(kOfMQ m q)).toNat` is one of the two
    negated `floorLog10*` candidates the band-1 sweep checks. -/
theorem kOfMQ_neg_toNat_candidate1 (m : Nat) (q : Int) :
    (-(kOfMQ m q)).toNat = (-(floorLog10Pow2 q)).toNat ∨
    (-(kOfMQ m q)).toNat = (-(floorLog10ThreeQuartersPow2 q)).toNat := by
  unfold kOfMQ
  by_cases h : isIrregular m q = true
  · rw [if_pos h]; exact Or.inr rfl
  · rw [if_neg h]; exact Or.inl rfl

/-- **R20 decode glue.**  For every binary64 `(m, q)` (`0 < m < 2^53`,
    `-1074 ≤ q ≤ 971`) with `k = kOfMQ m q` and `s ≥ 124`, the kernel
    residue condition holds — with NO `B < 2^64` accuracy guard.

    This is the unconditional input to `shiftedSig_floor_widened_of_residue`.
    The proof splits on the sign of `q` and `k`:
    * `q ≥ 0, k ≥ 0` → band 2 (`B = 10^kPos`, `N = m·2^q`);
    * `q < 0, k < 0` → band 1 (`B = 2^qNeg`, `N = m·10^kNeg`);
    * `q ≥ 0, k < 0` → `B = 1`, residue trivial (`m ≤ 2^s`). -/
theorem residueR20Cond_decode_binary64
    (m : Nat) (q : Int) (s : Nat)
    (hm : 0 < m) (hm53 : m < 2 ^ 53)
    (hq_lo : -1074 ≤ q) (hq_hi : q ≤ 971) (hs : 124 ≤ s) :
    residueR20Cond m
      (2 ^ (if q < 0 then (-q).toNat else 0) *
        10 ^ (if kOfMQ m q ≥ 0 then (kOfMQ m q).toNat else 0))
      s
      (m * 2 ^ (if q ≥ 0 then q.toNat else 0) *
        10 ^ (if kOfMQ m q < 0 then (-(kOfMQ m q)).toNat else 0)) := by
  set k : Int := kOfMQ m q with hk_def
  by_cases hq0 : 0 ≤ q
  · -- q ≥ 0:  qNeg = 0, qPos = q.toNat.
    have hq_not : ¬ q < 0 := by omega
    rw [if_neg hq_not, if_pos hq0]
    by_cases hk0 : 0 ≤ k
    · -- k ≥ 0:  kNeg = 0, kPos = k.toNat → band 2.
      have hk_not : ¬ k < 0 := by omega
      have hk_ge : k ≥ 0 := hk0
      rw [if_pos hk_ge, if_neg hk_not]
      simp only [pow_zero, Nat.mul_one, Nat.one_mul]
      -- B = 10^k.toNat, N = m * 2^q.toNat.
      have hqcast : ((q.toNat : Nat) : Int) = q := Int.toNat_of_nonneg hq0
      have hkq : k.toNat ≤ q.toNat := by
        have := kOfMQ_le_self m q hq0
        rw [← hk_def] at this; omega
      -- band2 keyed by `q.toNat`; `kOfMQ m ↑q.toNat = kOfMQ m q = k`.
      have hcand := kOfMQ_toNat_candidate2 m q.toNat
      rw [show kOfMQ m (↑q.toNat) = k by rw [hk_def, hqcast]] at hcand
      have hband := residueR20Cond_band2_binary64 m q.toNat k.toNat s
                      (by omega) hcand hkq hm hm53 hs
      -- band gives `residueR20Cond m (10^k.toNat) s (m * 2^q.toNat)`.
      simpa using hband
    · -- k < 0:  kNeg = -k.toNat, kPos = 0 → B = 1 (safe).
      push_neg at hk0
      have hk_lt : k < 0 := hk0
      have hk_ge_not : ¬ k ≥ 0 := by omega
      rw [if_neg hk_ge_not, if_pos hk_lt]
      simp only [pow_zero, Nat.one_mul]
      -- B = 1, residue trivial.
      apply residueR20Cond_of_safe m 1 s _ (by norm_num)
      rw [Nat.mul_one]
      calc m ≤ 2 ^ 53 := by omega
        _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) (by omega)
  · -- q < 0:  qNeg = -q.toNat, qPos = 0, and k < 0 → band 1.
    push_neg at hq0
    have hq_lt : q < 0 := hq0
    have hq_ge_not : ¬ q ≥ 0 := by omega
    have hk_lt : k < 0 := by rw [hk_def]; exact kOfMQ_neg_of_neg m q hq_lt
    have hk_ge_not : ¬ k ≥ 0 := by omega
    rw [if_pos hq_lt, if_neg hq_ge_not, if_neg hk_ge_not, if_pos hk_lt]
    simp only [pow_zero, Nat.mul_one]
    -- B = 2^qNeg, N = m * 10^kNeg with qNeg = (-q).toNat, kNeg = (-k).toNat.
    set qNeg : Nat := (-q).toNat with hqNeg_def
    set kNeg : Nat := (-k).toNat with hkNeg_def
    -- kNeg ≤ qNeg from q ≤ k (both negative).
    have hkq : kNeg ≤ qNeg := by
      have hle := self_le_kOfMQ m q hq_lt
      rw [← hk_def] at hle
      rw [hqNeg_def, hkNeg_def]; omega
    -- candidate membership for band 1.
    have hcand := kOfMQ_neg_toNat_candidate1 m q
    rw [← hk_def] at hcand
    have hcand' :
        kNeg = (-(floorLog10Pow2 q)).toNat ∨
        kNeg = (-(floorLog10ThreeQuartersPow2 q)).toNat := by
      rw [hkNeg_def]; exact hcand
    -- bounds on qNeg.
    have hqNeg_lo : 1 ≤ qNeg := by rw [hqNeg_def]; omega
    have hqNeg_hi : qNeg ≤ 1074 := by rw [hqNeg_def]; omega
    -- band 1 keyed by qNeg : the statement uses q := -(qNeg : Int).
    have hq_eq : (-(qNeg : Int)) = q := by rw [hqNeg_def]; omega
    have hcand'' :
        kNeg = (-(floorLog10Pow2 (-(qNeg : Int)))).toNat
          ∨ kNeg = (-(floorLog10ThreeQuartersPow2 (-(qNeg : Int)))).toNat := by
      rw [hq_eq]; exact hcand'
    have hband := residueR20Cond_band1_binary64 m qNeg kNeg s
                    hqNeg_lo hqNeg_hi hcand'' hkq hm hm53 hs
    exact hband

/-! ## Widened fast kernel (`B`-unbounded)

`shiftedSig_fast2_w` is `shiftedSig_fast2` with the `B < 2^64` accuracy
guard removed.  The remaining guards (`m ≥ 2^60`, table range, shiftAmt
range) are *width* guards: structural conditions for the UInt64 kernel to
be exact, which never fire on real binary64.  Correctness now rests on
the R20 residue (`residueR20Cond_decode_binary64`) rather than the
safe-regime bound, so the fast UInt64 branch is taken for the full
binary64 domain. -/

/-- Widened multiply-shift kernel: `shiftedSig_fast2` without the
    `B < 2^64` accuracy guard. -/
def shiftedSig_fast2_w (m : Nat) (q : Int) (k : Int) : Nat :=
  if m ≥ (1 <<< 60 : Nat) then shiftedSig_fast m q k
  else
    let kLookup : Int := -k
    if kLookup < pow10Table128_kMin ∨ kLookup > pow10Table128_kMax then
      shiftedSig_fast m q k
    else
      let (gHi, gLo, h) := pow10Lookup128 kLookup
      let shiftAmt : Int := h - q
      if shiftAmt < 124 ∨ shiftAmt ≥ 192 then shiftedSig_fast m q k
      else
        let mU : UInt64 := UInt64.ofNat m
        let pLo  : UInt64 := mU * gLo
        let pLoH : UInt64 := mulHi64 mU gLo
        let pHi  : UInt64 := mU * gHi
        let pHiH : UInt64 := mulHi64 mU gHi
        let midSum   : UInt64 := pHi + pLoH
        let midCarry : UInt64 := if midSum < pHi then 1 else 0
        let rHi  : UInt64 := pHiH + midCarry
        let rMid : UInt64 := midSum
        let rLo  : UInt64 := pLo
        let s : UInt64 := UInt64.ofNat shiftAmt.toNat
        let resU : UInt64 :=
          if s < 64 then
            if s = 0 then rLo
            else (rLo >>> s) ||| (rMid <<< (64 - s))
          else if s < 128 then
            let s64 := s - 64
            if s64 = 0 then rMid
            else (rMid >>> s64) ||| (rHi <<< (64 - s64))
          else
            let s64 := s - 128
            rHi >>> s64
        resU.toNat

/-- When the width guards fire, the widened kernel falls back to
    `shiftedSig_fast` (= `shiftedSig`). -/
theorem shiftedSig_fast2_w_guards
    (m : Nat) (q k : Int)
    (hGuard : m ≥ (1 <<< 60 : Nat) ∨
              -k < pow10Table128_kMin ∨ -k > pow10Table128_kMax ∨
              ((pow10Lookup128 (-k)).2.2 - q) < 124 ∨
              ((pow10Lookup128 (-k)).2.2 - q) ≥ 192) :
    shiftedSig_fast2_w m q k = shiftedSig_fast m q k := by
  unfold shiftedSig_fast2_w
  rcases hGuard with h | h | h | h | h
  · simp only [if_pos h]
  · by_cases h1 : m ≥ (1 <<< 60 : Nat)
    · simp only [if_pos h1]
    · simp only [if_neg h1, if_pos (Or.inl h)]
  · by_cases h1 : m ≥ (1 <<< 60 : Nat)
    · simp only [if_pos h1]
    · simp only [if_neg h1, if_pos (Or.inr h)]
  · by_cases h1 : m ≥ (1 <<< 60 : Nat)
    · simp only [if_pos h1]
    · by_cases h2 : (-k : Int) < pow10Table128_kMin ∨ (-k : Int) > pow10Table128_kMax
      · simp only [if_neg h1, if_pos h2]
      · simp only [if_neg h1, if_neg h2]
        have hk : ((pow10Lookup128 (-k)).2.2 - q < 124 ∨
                   (pow10Lookup128 (-k)).2.2 - q ≥ 192) := Or.inl h
        rw [show (pow10Lookup128 (-k)) =
              ((pow10Lookup128 (-k)).1, (pow10Lookup128 (-k)).2.1, (pow10Lookup128 (-k)).2.2) from rfl]
        simp only [if_pos hk]
  · by_cases h1 : m ≥ (1 <<< 60 : Nat)
    · simp only [if_pos h1]
    · by_cases h2 : (-k : Int) < pow10Table128_kMin ∨ (-k : Int) > pow10Table128_kMax
      · simp only [if_neg h1, if_pos h2]
      · simp only [if_neg h1, if_neg h2]
        have hk : ((pow10Lookup128 (-k)).2.2 - q < 124 ∨
                   (pow10Lookup128 (-k)).2.2 - q ≥ 192) := Or.inr h
        rw [show (pow10Lookup128 (-k)) =
              ((pow10Lookup128 (-k)).1, (pow10Lookup128 (-k)).2.1, (pow10Lookup128 (-k)).2.2) from rfl]
        simp only [if_pos hk]

set_option maxRecDepth 4000 in
/-- **Widened floor equality over binary64.**  For every binary64 `(m, q)`
    (`0 < m < 2^53`, `-1074 ≤ q ≤ 971`) and `k = kOfMQ m q`, the widened
    UInt64 kernel equals the spec `shiftedSig` — with NO `B < 2^64` guard.
    The fast branch is now correct on the full binary64 domain via the R20
    residue. -/
theorem shiftedSig_fast2_w_eq_binary64
    (m : Nat) (q : Int)
    (hm : 0 < m) (hm53 : m < 2 ^ 53)
    (hq_lo : -1074 ≤ q) (hq_hi : q ≤ 971) :
    shiftedSig m q (kOfMQ m q) = shiftedSig_fast2_w m q (kOfMQ m q) := by
  set k : Int := kOfMQ m q with hk_def
  -- Stage 1: dispatch the width-guard branches.
  by_cases hm60 : m ≥ (1 <<< 60 : Nat)
  · rw [shiftedSig_eq_fast]
    exact (shiftedSig_fast2_w_guards m q k (Or.inl hm60)).symm
  by_cases hkg : (-k : Int) < pow10Table128_kMin ∨ (-k : Int) > pow10Table128_kMax
  · rw [shiftedSig_eq_fast]
    rcases hkg with h | h
    · exact (shiftedSig_fast2_w_guards m q k (Or.inr (Or.inl h))).symm
    · exact (shiftedSig_fast2_w_guards m q k (Or.inr (Or.inr (Or.inl h)))).symm
  by_cases hsg : (pow10Lookup128 (-k)).2.2 - q < 124 ∨ (pow10Lookup128 (-k)).2.2 - q ≥ 192
  · rw [shiftedSig_eq_fast]
    rcases hsg with h | h
    · exact (shiftedSig_fast2_w_guards m q k (Or.inr (Or.inr (Or.inr (Or.inl h))))).symm
    · exact (shiftedSig_fast2_w_guards m q k
              (Or.inr (Or.inr (Or.inr (Or.inr h))))).symm
  -- Stage 2: fast branch. All width guards pass.
  push_neg at hm60 hkg hsg
  obtain ⟨hkLo, hkHi⟩ := hkg
  obtain ⟨hsLo, hsHi⟩ := hsg
  have hm60_not : ¬ m ≥ (1 <<< 60 : Nat) := by omega
  have hk_not : ¬ ((-k : Int) < pow10Table128_kMin ∨ (-k : Int) > pow10Table128_kMax) := by
    push_neg; exact ⟨hkLo, hkHi⟩
  have hs_not : ¬ ((pow10Lookup128 (-k)).2.2 - q < 124 ∨
                   (pow10Lookup128 (-k)).2.2 - q ≥ 192) := by
    push_neg; exact ⟨hsLo, hsHi⟩
  unfold shiftedSig_fast2_w
  rw [if_neg hm60_not]
  rw [if_neg hk_not]
  rw [show (pow10Lookup128 (-k)) =
        ((pow10Lookup128 (-k)).1, (pow10Lookup128 (-k)).2.1,
         (pow10Lookup128 (-k)).2.2) from rfl]
  simp only [if_neg hs_not]
  -- Kernel intermediates (mirrors `shiftedSig_eq_fast2`).
  set gHi : UInt64 := (pow10Lookup128 (-k)).1 with hgHi_def
  set gLo : UInt64 := (pow10Lookup128 (-k)).2.1 with hgLo_def
  set h_t : Int := (pow10Lookup128 (-k)).2.2 with hh_def
  set shiftAmt : Int := h_t - q with hshiftAmt_def
  set mU : UInt64 := UInt64.ofNat m with hmU_def
  set s : UInt64 := UInt64.ofNat shiftAmt.toNat with hs_def
  have hshiftAmt_nn : 0 ≤ shiftAmt := by rw [hshiftAmt_def]; omega
  have hshiftAmt_lo : 124 ≤ shiftAmt := by rw [hshiftAmt_def]; omega
  have hshiftAmt_hi : shiftAmt < 192 := by rw [hshiftAmt_def]; omega
  have hshiftAmt_toNat_lo : 124 ≤ shiftAmt.toNat := by
    have := Int.toNat_of_nonneg hshiftAmt_nn; omega
  have hshiftAmt_toNat_hi : shiftAmt.toNat < 192 := by
    have := Int.toNat_of_nonneg hshiftAmt_nn; omega
  have hshiftAmt_lt_2_64 : shiftAmt.toNat < 2 ^ 64 := by
    have h264 : (192 : Nat) < 2 ^ 64 := by decide
    omega
  have hs_toNat : s.toNat = shiftAmt.toNat :=
    UInt64_ofNat_toNat_of_lt _ hshiftAmt_lt_2_64
  have hm_lt_60 : m < 2 ^ 60 := by
    have : (1 <<< 60 : Nat) = 2 ^ 60 := by decide
    omega
  have hm_lt_64 : m < 2 ^ 64 := by
    have : (2 : Nat) ^ 60 ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by decide)
    omega
  have hmU_toNat : mU.toNat = m := UInt64_ofNat_toNat_of_lt _ hm_lt_64
  have hmU_lt_60 : mU.toNat < 2 ^ 60 := hmU_toNat.symm ▸ hm_lt_60
  set pLo  : UInt64 := mU * gLo with hpLo_def
  set pLoH : UInt64 := mulHi64 mU gLo with hpLoH_def
  set pHi  : UInt64 := mU * gHi with hpHi_def
  set pHiH : UInt64 := mulHi64 mU gHi with hpHiH_def
  set midSum : UInt64 := pHi + pLoH with hmidSum_def
  set midCarry : UInt64 := if midSum < pHi then (1 : UInt64) else 0 with hmidCarry_def
  set rHi  : UInt64 := pHiH + midCarry with hrHi_def
  set rMid : UInt64 := midSum with hrMid_def
  set rLo  : UInt64 := pLo with hrLo_def
  have hTriple : triple192Nat rHi rMid rLo = m * (gHi.toNat * 2 ^ 64 + gLo.toNat) := by
    have := kernel_R_eq mU gHi gLo hmU_lt_60
    rw [hmU_toNat] at this
    exact this
  have hs_ge_64 : ¬ s < (64 : UInt64) := by
    rw [UInt64_lt_64_iff]; rw [hs_toNat]; omega
  simp only [if_neg hs_ge_64]
  have hG_lt : gHi.toNat * 2 ^ 64 + gLo.toNat < 2 ^ 128 := by
    have hgHi_lt : gHi.toNat < 2 ^ 64 := gHi.toNat_lt
    have hgLo_lt : gLo.toNat < 2 ^ 64 := gLo.toNat_lt
    have h1 : gHi.toNat * 2 ^ 64 ≤ (2 ^ 64 - 1) * 2 ^ 64 := by
      apply Nat.mul_le_mul_right; omega
    have h2 : (2 ^ 64 - 1) * 2 ^ 64 + 2 ^ 64 = 2 ^ 64 * 2 ^ 64 := by
      have hpow_pos : (0 : Nat) < 2 ^ 64 := Nat.two_pow_pos _
      have : (2 ^ 64 - 1) * 2 ^ 64 = 2 ^ 64 * 2 ^ 64 - 2 ^ 64 := by
        rw [Nat.sub_mul]; ring_nf
      omega
    have h128 : (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 := by decide
    omega
  have hMG_lt : m * (gHi.toNat * 2 ^ 64 + gLo.toNat) < 2 ^ 188 := by
    have : m * (gHi.toNat * 2 ^ 64 + gLo.toNat) < 2 ^ 60 * 2 ^ 128 :=
      Nat.mul_lt_mul_of_lt_of_lt hm_lt_60 hG_lt
    have h60_128 : (2 : Nat) ^ 60 * 2 ^ 128 = 2 ^ 188 := by rw [← Nat.pow_add]
    omega
  have hKernel_eq : (if s < 128 then
                       if s - 64 = 0 then rMid
                       else rMid >>> (s - 64) ||| rHi <<< (64 - (s - 64))
                     else rHi >>> (s - 128)).toNat
                    = triple192Nat rHi rMid rLo / 2 ^ shiftAmt.toNat := by
    by_cases hs_128 : s < (128 : UInt64)
    · rw [if_pos hs_128]
      have hs_toNat_lt_128 : s.toNat < 128 := by
        rw [UInt64_lt_128_iff] at hs_128; exact hs_128
      have hs_toNat_ge_64 : 64 ≤ s.toNat := by rw [hs_toNat]; omega
      set s64 : UInt64 := s - 64 with hs64_def
      have hs64_toNat : s64.toNat = s.toNat - 64 := by
        rw [hs64_def]; apply UInt64_sub_toNat_of_ge s 64 (by decide) hs_toNat_ge_64
      have hs64_lo : 60 ≤ s64.toNat := by rw [hs64_toNat, hs_toNat]; omega
      have hs64_lt_64 : s64.toNat < 64 := by rw [hs64_toNat, hs_toNat]; omega
      have hs64_pos : 0 < s64.toNat := by omega
      have hs64_nz : s64 ≠ 0 := by
        intro hz; have : s64.toNat = 0 := by rw [hz]; rfl
        omega
      rw [if_neg hs64_nz]
      have hTriple_lt : triple192Nat rHi rMid rLo < 2 ^ 188 := by
        rw [hTriple]; exact hMG_lt
      have hrHi_lt_60 : rHi.toNat < 2 ^ 60 := by
        have hle : rHi.toNat * 2 ^ 128 ≤ triple192Nat rHi rMid rLo := by
          unfold triple192Nat; omega
        have hlt : rHi.toNat * 2 ^ 128 < 2 ^ 188 := by omega
        have hpow : (2 : Nat) ^ 188 = 2 ^ 60 * 2 ^ 128 := by rw [← Nat.pow_add]
        rw [hpow] at hlt
        exact Nat.lt_of_mul_lt_mul_right hlt
      have hrHi_lt_s64 : rHi.toNat < 2 ^ s64.toNat := by
        have h60_le : (2 : Nat) ^ 60 ≤ 2 ^ s64.toNat := Nat.pow_le_pow_right (by decide) hs64_lo
        omega
      have := shift_kernel_extract_mid rHi rMid rLo s s64
                hs_toNat_ge_64 hs_toNat_lt_128 hs64_def hs64_nz hrHi_lt_s64
      rw [hs_toNat] at this
      exact this
    · rw [if_neg hs_128]
      have hs_toNat_ge_128 : 128 ≤ s.toNat := by
        by_contra hp; push_neg at hp
        apply hs_128; rw [UInt64_lt_128_iff]; exact hp
      have hs_toNat_lt_192 : s.toNat < 192 := by rw [hs_toNat]; omega
      set s64 : UInt64 := s - 128 with hs64_def
      have := shift_kernel_extract_hi rHi rMid rLo s s64
                hs_toNat_ge_128 hs_toNat_lt_192 hs64_def
      rw [hs_toNat] at this
      exact this
  rw [hKernel_eq, hTriple]
  -- m = 0 excluded (hm : 0 < m).
  have hm_pos : 0 < m := hm
  rw [shiftedSig_eq_fast]
  unfold shiftedSig_fast
  simp only [pow2Lookup_eq, pow10Lookup_eq]
  set qPos : Nat := if q ≥ 0 then q.toNat else 0 with hqPos_def
  set qNeg : Nat := if q < 0 then (-q).toNat else 0 with hqNeg_def
  set kPos : Nat := if k ≥ 0 then k.toNat else 0 with hkPos_def
  set kNeg : Nat := if k < 0 then (-k).toNat else 0 with hkNeg_def
  set hPos : Nat := if h_t ≥ 0 then h_t.toNat else 0 with hhPos_def
  set hNeg : Nat := if h_t < 0 then (-h_t).toNat else 0 with hhNeg_def
  set G : Nat := gHi.toNat * 2 ^ 64 + gLo.toNat with hG_def
  set B : Nat := 2 ^ qNeg * 10 ^ kPos with hB_def
  set N : Nat := m * 2 ^ qPos * 10 ^ kNeg with hN_def
  have hB_pos : 0 < B := by
    rw [hB_def]; exact Nat.mul_pos (Nat.two_pow_pos _) (Nat.pow_pos (by decide))
  -- Regrouping identity (verbatim from the safe-regime proof).
  have hregroup_eq : shiftAmt.toNat + qPos + hNeg = qNeg + hPos := by
    have hShiftAmt_int : (shiftAmt.toNat : Int) = shiftAmt := Int.toNat_of_nonneg hshiftAmt_nn
    have hIntEq : (shiftAmt.toNat : Int) + (qPos : Int) + (hNeg : Int)
                    = (qNeg : Int) + (hPos : Int) := by
      rw [hShiftAmt_int]
      have hShift_eq : shiftAmt = h_t - q := hshiftAmt_def
      rw [hShift_eq, hqPos_def, hqNeg_def, hhPos_def, hhNeg_def]
      by_cases hq : q ≥ 0
      · have hq_neg : ¬ q < 0 := by omega
        have hqtoNat : (q.toNat : Int) = q := Int.toNat_of_nonneg hq
        rw [if_pos hq, if_neg hq_neg]
        push_cast
        have hh_nn : 0 ≤ h_t := by
          have : 124 ≤ h_t - q := hsLo; omega
        have hh_neg : ¬ h_t < 0 := by omega
        have hhtoNat : (h_t.toNat : Int) = h_t := Int.toNat_of_nonneg hh_nn
        rw [if_pos hh_nn, if_neg hh_neg, hqtoNat, hhtoNat]; ring
      · push_neg at hq
        have hq_lt : q < 0 := hq
        have hq_nn : ¬ q ≥ 0 := by omega
        have hqtoNat : ((-q).toNat : Int) = -q := Int.toNat_of_nonneg (by omega)
        rw [if_neg hq_nn, if_pos hq_lt, hqtoNat]
        by_cases hh : h_t ≥ 0
        · have hh_neg : ¬ h_t < 0 := by omega
          have hhtoNat : (h_t.toNat : Int) = h_t := Int.toNat_of_nonneg hh
          rw [if_pos hh, if_neg hh_neg, hhtoNat]; push_cast; ring
        · push_neg at hh
          have hh_nn : ¬ h_t ≥ 0 := by omega
          have hhtoNat : ((-h_t).toNat : Int) = -h_t := Int.toNat_of_nonneg (by omega)
          rw [if_neg hh_nn, if_pos hh, hhtoNat]; push_cast; ring
    have hL : ((shiftAmt.toNat + qPos + hNeg : Nat) : Int)
                = ((qNeg + hPos : Nat) : Int) := by push_cast; omega
    exact_mod_cast hL
  have hRegroup : 2 ^ shiftAmt.toNat * 2 ^ qPos * 2 ^ hNeg = 2 ^ qNeg * 2 ^ hPos :=
    two_pow_regroup shiftAmt.toNat qNeg qPos hPos hNeg (by have := hregroup_eq; omega)
  -- Table invariant.
  have hInv := pow10Lookup128_invariant (-k) hkLo hkHi
  have hkPos'_eq_kNeg : (if (-k : Int) ≥ 0 then (-k).toNat else 0) = kNeg := by
    rw [hkNeg_def]
    by_cases hk_nn : k ≥ 0
    · by_cases hk_pos : k = 0
      · rw [hk_pos]; simp
      · have hk_pos' : k > 0 := lt_of_le_of_ne hk_nn (Ne.symm hk_pos)
        have h_neg_k_not_nn : ¬ (-k : Int) ≥ 0 := by omega
        have h_k_not_lt_0 : ¬ k < 0 := by omega
        rw [if_neg h_neg_k_not_nn, if_neg h_k_not_lt_0]
    · push_neg at hk_nn
      have h_neg_k_nn : (-k : Int) ≥ 0 := by omega
      have h_k_lt_0 : k < 0 := hk_nn
      rw [if_pos h_neg_k_nn, if_pos h_k_lt_0]
  have hkNeg'_eq_kPos : (if (-k : Int) < 0 then (-(-k)).toNat else 0) = kPos := by
    rw [hkPos_def]
    by_cases hk_nn : k ≥ 0
    · by_cases hk_zero : k = 0
      · rw [hk_zero]; simp
      · have hk_pos : k > 0 := lt_of_le_of_ne hk_nn (Ne.symm hk_zero)
        have h_neg_k_lt : (-k : Int) < 0 := by omega
        have hk_nn' : k ≥ 0 := hk_nn
        rw [if_pos h_neg_k_lt, if_pos hk_nn']
        have : -(-k) = k := by ring
        rw [this]
    · push_neg at hk_nn
      have h_neg_k_nn : ¬ (-k : Int) < 0 := by omega
      have hk_nn_not : ¬ k ≥ 0 := by omega
      rw [if_neg h_neg_k_nn, if_neg hk_nn_not]
  have hG_eq : (pow10Lookup128 (-k)).1.toNat * 2 ^ 64 + (pow10Lookup128 (-k)).2.1.toNat = G := by
    rw [hG_def, ← hgHi_def, ← hgLo_def]
  have hh_t_eq : (pow10Lookup128 (-k)).2.2 = h_t := by rw [← hh_def]
  have hInv' : 10 ^ kNeg * 2 ^ hPos ≤ G * 10 ^ kPos * 2 ^ hNeg
              ∧ G * 10 ^ kPos * 2 ^ hNeg < 10 ^ kNeg * 2 ^ hPos + 10 ^ kPos * 2 ^ hNeg := by
    have h1 := hInv
    simp only at h1
    have hkPos'_eq : (if (-k : Int) ≥ 0 then (-k).toNat else 0) = kNeg := hkPos'_eq_kNeg
    have hkNeg'_eq : (if (-k : Int) < 0 then (-(-k)).toNat else 0) = kPos := hkNeg'_eq_kPos
    have hhPos'_eq : (if (pow10Lookup128 (-k)).2.2 ≥ 0 then ((pow10Lookup128 (-k)).2.2).toNat else 0)
                      = hPos := by rw [hhPos_def, hh_t_eq]
    have hhNeg'_eq : (if (pow10Lookup128 (-k)).2.2 < 0 then
                        (-(pow10Lookup128 (-k)).2.2).toNat else 0) = hNeg := by
      rw [hhNeg_def, hh_t_eq]
    rw [hkPos'_eq, hkNeg'_eq, hhPos'_eq, hhNeg'_eq, hG_eq] at h1
    exact h1
  -- Sandwich.
  have hSandwich := shiftedSig_sandwich m G qPos qNeg kPos kNeg hPos hNeg shiftAmt.toNat
                      hm_pos hRegroup hInv'
  -- R20 residue (the widened input, no `B < 2^64`).
  have hResidue : residueR20Cond m B shiftAmt.toNat N := by
    have hr := residueR20Cond_decode_binary64 m q shiftAmt.toNat hm hm53 hq_lo hq_hi
                 hshiftAmt_toNat_lo
    rw [← hk_def] at hr
    -- hr keyed by the same sign-splits; rewrite to B, N.
    rw [hB_def, hN_def, hqNeg_def, hkPos_def, hqPos_def, hkNeg_def]
    -- align `kOfMQ m q ≥ 0` vs `k ≥ 0` etc.
    rw [hk_def] at *
    convert hr using 3
  -- Floor equality.
  have hFloor := shiftedSig_floor_of_residue m G B shiftAmt.toNat N hB_pos hSandwich hResidue
  exact hFloor.symm

/-! ## Packed widened kernel

`shiftedSig_packed_w` is the precomputed-argument form of
`shiftedSig_fast2_w`: the `(q, k)`-only lookups `(gHi, gLo, shiftAmt)` are
supplied directly so the orchestration computes them once.  Unlike the
original `shiftedSig_packed`, it carries NO `B` argument and no `B < 2^64`
guard — the widened kernel is correct over the full binary64 domain. -/

/-- Packed widened kernel: same body as `shiftedSig_fast2_w`, with the
    `(q, k)`-only precomputations supplied directly. -/
def shiftedSig_packed_w
    (q : Int) (k : Int)
    (gHi : UInt64) (gLo : UInt64) (shiftAmt : Int)
    (m : Nat) : Nat :=
  if m ≥ (1 <<< 60 : Nat) then shiftedSig_fast m q k
  else
    let kLookup : Int := -k
    if kLookup < pow10Table128_kMin ∨ kLookup > pow10Table128_kMax then
      shiftedSig_fast m q k
    else
      if shiftAmt < 124 ∨ shiftAmt ≥ 192 then shiftedSig_fast m q k
      else
        let mU : UInt64 := UInt64.ofNat m
        let pLo  : UInt64 := mU * gLo
        let pLoH : UInt64 := mulHi64 mU gLo
        let pHi  : UInt64 := mU * gHi
        let pHiH : UInt64 := mulHi64 mU gHi
        let midSum   : UInt64 := pHi + pLoH
        let midCarry : UInt64 := if midSum < pHi then 1 else 0
        let rHi  : UInt64 := pHiH + midCarry
        let rMid : UInt64 := midSum
        let rLo  : UInt64 := pLo
        let s : UInt64 := UInt64.ofNat shiftAmt.toNat
        let resU : UInt64 :=
          if s < 64 then
            if s = 0 then rLo
            else (rLo >>> s) ||| (rMid <<< (64 - s))
          else if s < 128 then
            let s64 := s - 64
            if s64 = 0 then rMid
            else (rMid >>> s64) ||| (rHi <<< (64 - s64))
          else
            let s64 := s - 128
            rHi >>> s64
        resU.toNat

/-- When the precomputed `(gHi, gLo, shiftAmt)` match `pow10Lookup128 (-k)`,
    the packed widened kernel equals `shiftedSig_fast2_w`. -/
theorem shiftedSig_packed_w_eq_fast2_w (m : Nat) (q k : Int) :
    shiftedSig_packed_w q k (pow10Lookup128 (-k)).1 (pow10Lookup128 (-k)).2.1
        ((pow10Lookup128 (-k)).2.2 - q) m
      = shiftedSig_fast2_w m q k := by
  unfold shiftedSig_packed_w shiftedSig_fast2_w
  rfl

/-- Round-trip over binary64: the packed widened kernel (with the
    `pow10Lookup128`-derived precomputations) equals the spec `shiftedSig`
    — with NO `B < 2^64` guard, valid over the full binary64 domain. -/
theorem shiftedSig_packed_w_eq_binary64
    (m : Nat) (q : Int)
    (hm : 0 < m) (hm53 : m < 2 ^ 53)
    (hq_lo : -1074 ≤ q) (hq_hi : q ≤ 971) :
    shiftedSig_packed_w q (kOfMQ m q)
        (pow10Lookup128 (-(kOfMQ m q))).1 (pow10Lookup128 (-(kOfMQ m q))).2.1
        ((pow10Lookup128 (-(kOfMQ m q))).2.2 - q) m
      = shiftedSig m q (kOfMQ m q) := by
  rw [shiftedSig_packed_w_eq_fast2_w]
  exact (shiftedSig_fast2_w_eq_binary64 m q hm hm53 hq_lo hq_hi).symm

end Srtfp.Schubfach

/- Correctness of `kOfMQ` (M3.8.3).

   Schubfach's "decimal exponent" `k` is the unique integer such that the
   width `‖R_v‖` of the rounding interval lies in `[10^k, 10^(k+1))`
   (paper Result R10). The printer computes `k` from `(m, q)` directly,
   using the magic-constant floor-log approximations established in
   M3.8.1 (`R14HoldsAt` / `R15HoldsAt`) together with the case-split on
   `isIrregular m q`.

   ## Predicate shape

   `KCorrect k width` says `10^k ≤ width ∧ width < 10^(k+1)`, in
   pure-integer cross-multiplied form. The `10^k` factor splits as
       p10Num k / p10Den k     -- depending on sign of k
   and `width = width.num / 2^width.denPow2`. Using `shiftFactor` to
   subsume the sign split on `denPow2`, this becomes

       p10Num k · shiftFactor width.denPow2
         ≤ width.num · shiftFactor (-width.denPow2) · p10Den k

   with the symmetric form for the strict upper bound.

   ## Proof strategy

   The K-correctness over the binary64 `q ∈ [-1074, 971]` range is a
   `Decidable` predicate (in pure Nat-cross-mul'd form). We follow the
   same brute-force `decide` strategy as M3.8.1 (R14/R15 ranges):
   express `KCorrectRegAt q` / `KCorrectIrregAt q` as `Bool`-valued
   universal-over-range, close the range by a single `decide`, then
   lift the result via a `Decidable` bridge.

   This mirrors M3.8.1's structure exactly and avoids the algebraic
   bookkeeping involved in transforming R14/R15 into KCorrect's form
   pointwise. The proof runs in ~5–10 s at build time (slightly more
   than M3.8.1 because the K-correctness inequality involves three
   factors of 2^? in the cross-mul).

   No `native_decide`. The only axioms inherited from M3.8.1 are
   `propext, Quot.sound, Classical.choice`. -/

import Srtfp.Schubfach
import Srtfp.Proofs.Schubfach.R14R15
import Srtfp.Proofs.Schubfach.RoundingInterval

namespace Srtfp.Schubfach

open RoundingInterval Midpoint

/-! ## `KCorrect` and helper definitions -/

/-- `10^k`'s numerator: `10^|k|` if `k ≥ 0`, else `1`. -/
@[reducible] def p10Num (k : Int) : Nat := if k ≥ 0 then 10 ^ k.natAbs else 1

/-- `10^k`'s denominator: `1` if `k ≥ 0`, else `10^|k|`. -/
@[reducible] def p10Den (k : Int) : Nat := if k ≥ 0 then 1 else 10 ^ k.natAbs

/-- `10^k ≤ midpoint-value < 10^(k+1)` in pure-integer cross-multiplied
form. Decidable when the inputs are concrete. -/
@[reducible] def KCorrect (k : Int) (width : Midpoint) : Prop :=
  ((p10Num k : Int) * shiftFactor width.denPow2
      ≤ width.num * shiftFactor (-width.denPow2) * p10Den k)
  ∧ (width.num * shiftFactor (-width.denPow2) * p10Den (k + 1)
      < (p10Num (k + 1) : Int) * shiftFactor width.denPow2)

/-! ## Pure-integer predicates `KCorrectRegAt q` and `KCorrectIrregAt q`

These are `KCorrect (floor… q) ⟨c, -q+2⟩` for `c ∈ {4, 3}`, expressed
in cross-multiplied form with no `Midpoint` projections. -/

/-- KCorrect for the regular-case width `⟨4, -q+2⟩`. -/
@[reducible] def KCorrectRegAt (q : Int) : Prop :=
  KCorrect (floorLog10Pow2 q) ⟨4, -q + 2⟩

/-- KCorrect for the irregular-case width `⟨3, -q+2⟩`. -/
@[reducible] def KCorrectIrregAt (q : Int) : Prop :=
  KCorrect (floorLog10ThreeQuartersPow2 q) ⟨3, -q + 2⟩

/-! ## Range predicates and decidable bridges -/

/-- Bounded universal: `KCorrectRegAt` over `[lo, hi]`. -/
def KCorrectRegForRange (lo hi : Int) : Prop :=
  (List.range (hi - lo + 1).toNat).all (fun i => decide (KCorrectRegAt (lo + i))) = true

/-- Bounded universal: `KCorrectIrregAt` over `[lo, hi]`. -/
def KCorrectIrregForRange (lo hi : Int) : Prop :=
  (List.range (hi - lo + 1).toNat).all (fun i => decide (KCorrectIrregAt (lo + i))) = true

/-- Bridge: `Bool` form ↔ `∀ q` form for KCorrectReg. Identical to
M3.8.1's R15ForRange_iff_forall. -/
theorem KCorrectRegForRange_iff_forall (lo hi : Int) (hlh : lo ≤ hi + 1) :
    KCorrectRegForRange lo hi ↔ ∀ q : Int, lo ≤ q → q ≤ hi → KCorrectRegAt q := by
  unfold KCorrectRegForRange
  have hnn : 0 ≤ hi - lo + 1 := by omega
  refine ⟨?_, ?_⟩
  · intro hall e hlo hhi
    have h0 : 0 ≤ e - lo := by omega
    have hlt : e - lo < hi - lo + 1 := by omega
    have hi_eq : (((e - lo).toNat : Nat) : Int) = e - lo := Int.toNat_of_nonneg h0
    have hi_lt : (e - lo).toNat < (hi - lo + 1).toNat := by
      have h1 : (((e - lo).toNat : Nat) : Int) < (((hi - lo + 1).toNat : Nat) : Int) := by
        rw [hi_eq, Int.toNat_of_nonneg hnn]; exact hlt
      exact_mod_cast h1
    rw [List.all_eq_true] at hall
    have hd := hall (e - lo).toNat (List.mem_range.mpr hi_lt)
    have hadd : lo + ((e - lo).toNat : Int) = e := by rw [hi_eq]; omega
    rw [hadd] at hd
    exact of_decide_eq_true hd
  · intro hall
    rw [List.all_eq_true]
    intro i hi_mem
    rw [List.mem_range] at hi_mem
    apply decide_eq_true
    have hi_lt_nat : (i : Int) < ((hi - lo + 1).toNat : Int) := by exact_mod_cast hi_mem
    rw [Int.toNat_of_nonneg hnn] at hi_lt_nat
    have hi_nn : (0 : Int) ≤ i := Int.natCast_nonneg _
    apply hall <;> omega

theorem KCorrectIrregForRange_iff_forall (lo hi : Int) (hlh : lo ≤ hi + 1) :
    KCorrectIrregForRange lo hi ↔ ∀ q : Int, lo ≤ q → q ≤ hi → KCorrectIrregAt q := by
  unfold KCorrectIrregForRange
  have hnn : 0 ≤ hi - lo + 1 := by omega
  refine ⟨?_, ?_⟩
  · intro hall e hlo hhi
    have h0 : 0 ≤ e - lo := by omega
    have hlt : e - lo < hi - lo + 1 := by omega
    have hi_eq : (((e - lo).toNat : Nat) : Int) = e - lo := Int.toNat_of_nonneg h0
    have hi_lt : (e - lo).toNat < (hi - lo + 1).toNat := by
      have h1 : (((e - lo).toNat : Nat) : Int) < (((hi - lo + 1).toNat : Nat) : Int) := by
        rw [hi_eq, Int.toNat_of_nonneg hnn]; exact hlt
      exact_mod_cast h1
    rw [List.all_eq_true] at hall
    have hd := hall (e - lo).toNat (List.mem_range.mpr hi_lt)
    have hadd : lo + ((e - lo).toNat : Int) = e := by rw [hi_eq]; omega
    rw [hadd] at hd
    exact of_decide_eq_true hd
  · intro hall
    rw [List.all_eq_true]
    intro i hi_mem
    rw [List.mem_range] at hi_mem
    apply decide_eq_true
    have hi_lt_nat : (i : Int) < ((hi - lo + 1).toNat : Int) := by exact_mod_cast hi_mem
    rw [Int.toNat_of_nonneg hnn] at hi_lt_nat
    have hi_nn : (0 : Int) ≤ i := Int.natCast_nonneg _
    apply hall <;> omega

/-! ## Brute-force sweeps over the binary64 range -/

set_option exponentiation.threshold 4096 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 32000000 in
/-- Regular KCorrect sweep over the binary64 exponent range. -/
theorem KCorrectReg_binary64_decidable : KCorrectRegForRange (-1074) 971 := by
  unfold KCorrectRegForRange; decide

set_option exponentiation.threshold 4096 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 32000000 in
/-- Irregular KCorrect sweep over the binary64 exponent range. -/
theorem KCorrectIrreg_binary64_decidable : KCorrectIrregForRange (-1074) 971 := by
  unfold KCorrectIrregForRange; decide

/-- Universal statement: KCorrectReg holds over the binary64 q range. -/
theorem KCorrectRegAt_in_binary64_range :
    ∀ q : Int, -1074 ≤ q → q ≤ 971 → KCorrectRegAt q :=
  (KCorrectRegForRange_iff_forall (-1074) 971 (by decide)).mp KCorrectReg_binary64_decidable

/-- Universal statement: KCorrectIrreg holds over the binary64 q range. -/
theorem KCorrectIrregAt_in_binary64_range :
    ∀ q : Int, -1074 ≤ q → q ≤ 971 → KCorrectIrregAt q :=
  (KCorrectIrregForRange_iff_forall (-1074) 971 (by decide)).mp KCorrectIrreg_binary64_decidable

/-! ## Main theorem: `kOfMQ` is correct -/

/-- The Schubfach `k` from `kOfMQ m q` satisfies the R10 correctness
predicate `10^k ≤ ‖R_v‖ < 10^(k+1)`. -/
theorem kOfMQ_correct (m : Nat) (q : Int)
    (hm_pos : 1 ≤ m) (hm_le : m < 2 ^ 53) (hq_lo : -1074 ≤ q) (hq_hi : q ≤ 971) :
    KCorrect (kOfMQ m q) (RoundingInterval.ofMQ m q hm_pos hm_le hq_lo hq_hi).width := by
  unfold kOfMQ
  by_cases h_irreg : isIrregular m q = true
  · simp only [h_irreg, if_true]
    have hwidth :
        (RoundingInterval.ofMQ m q hm_pos hm_le hq_lo hq_hi).width
          = ⟨3, -q + 2⟩ := by
      have hn := ofMQ_width_num_irregular m q hm_pos hm_le hq_lo hq_hi h_irreg
      have hd := ofMQ_width_denPow2 m q hm_pos hm_le hq_lo hq_hi
      cases hw : (RoundingInterval.ofMQ m q hm_pos hm_le hq_lo hq_hi).width with
      | mk n d =>
        rw [hw] at hn hd
        simp at hn hd
        rw [hn, hd]
    rw [hwidth]
    exact KCorrectIrregAt_in_binary64_range q hq_lo hq_hi
  · have h_reg : ¬ (isIrregular m q = true) := h_irreg
    simp only [h_reg]
    have hwidth :
        (RoundingInterval.ofMQ m q hm_pos hm_le hq_lo hq_hi).width
          = ⟨4, -q + 2⟩ := by
      have hn := ofMQ_width_num_regular m q hm_pos hm_le hq_lo hq_hi h_reg
      have hd := ofMQ_width_denPow2 m q hm_pos hm_le hq_lo hq_hi
      cases hw : (RoundingInterval.ofMQ m q hm_pos hm_le hq_lo hq_hi).width with
      | mk n d =>
        rw [hw] at hn hd
        simp at hn hd
        rw [hn, hd]
    rw [hwidth]
    exact KCorrectRegAt_in_binary64_range q hq_lo hq_hi

/-! ## Convenience: pre-projected lower/upper bounds -/

theorem kOfMQ_le_log_width (m : Nat) (q : Int)
    (hm_pos : 1 ≤ m) (hm_le : m < 2 ^ 53) (hq_lo : -1074 ≤ q) (hq_hi : q ≤ 971) :
    let k := kOfMQ m q
    let w := (RoundingInterval.ofMQ m q hm_pos hm_le hq_lo hq_hi).width
    (p10Num k : Int) * shiftFactor w.denPow2
      ≤ w.num * shiftFactor (-w.denPow2) * p10Den k :=
  (kOfMQ_correct m q hm_pos hm_le hq_lo hq_hi).1

theorem log_width_lt_succK (m : Nat) (q : Int)
    (hm_pos : 1 ≤ m) (hm_le : m < 2 ^ 53) (hq_lo : -1074 ≤ q) (hq_hi : q ≤ 971) :
    let k := kOfMQ m q
    let w := (RoundingInterval.ofMQ m q hm_pos hm_le hq_lo hq_hi).width
    w.num * shiftFactor (-w.denPow2) * p10Den (k + 1)
      < (p10Num (k + 1) : Int) * shiftFactor w.denPow2 :=
  (kOfMQ_correct m q hm_pos hm_le hq_lo hq_hi).2

/-! ## Positivity of the shifted significand

`shiftedSig m q (kOfMQ m q) ≥ 1` whenever `m ≥ 1` and `q` lies in the
binary64 range.  This is the integer-division statement
`denominator ≤ numerator`, which — after dropping the `m ≥ 1` factor —
reduces to the first conjunct of `R15HoldsAt` (regular) or `R14HoldsAt`
(irregular). -/

/-- `shiftedSig m q (kOfMQ m q) ≥ 1` on the binary64 range, for `m ≥ 1`. -/
theorem shiftedSig_ge_one (m : Nat) (q : Int)
    (hm_pos : 1 ≤ m) (hq_lo : -1074 ≤ q) (hq_hi : q ≤ 971) :
    1 ≤ shiftedSig m q (kOfMQ m q) := by
  set k := kOfMQ m q with hk_def
  -- `shiftedSig m q k = (m * qP * kN) / (qN * kP)` with the four sign-split factors.
  show 1 ≤ (m * 2 ^ (if q ≥ 0 then q.toNat else 0) * 10 ^ (if k < 0 then (-k).toNat else 0))
            / (2 ^ (if q < 0 then (-q).toNat else 0) * 10 ^ (if k ≥ 0 then k.toNat else 0))
  rw [Nat.one_le_div_iff
        (Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos (by decide)))]
  -- Goal: 2^qN * 10^kP ≤ m * 2^qP * 10^kN.  Drop the `m ≥ 1` factor.
  rw [Nat.mul_assoc]
  refine Nat.le_trans ?_ (Nat.le_mul_of_pos_left _ hm_pos)
  -- Goal: 2^qN * 10^kP ≤ 2^qP * 10^kN.  Commute LHS to 10^kP * 2^qN.
  rw [Nat.mul_comm (2 ^ _) (10 ^ _)]
  -- Rewrite R1x's `natAbs` exponents to the same `if … toNat …` form as the
  -- goal (an unconditional identity), then resolve the `if`s on the signs of
  -- `q` / `kk` so the power atoms coincide and `omega` closes the goal.
  have hq_abs : q.natAbs = if q ≥ 0 then q.toNat else (-q).toNat := by split <;> omega
  by_cases hirr : isIrregular m q
  · -- irregular: k = floorLog10ThreeQuartersPow2 q, use R14 first conjunct.
    have hk : k = floorLog10ThreeQuartersPow2 q := by rw [hk_def, kOfMQ, if_pos hirr]
    obtain ⟨h1, _⟩ := R14HoldsAt_in_binary64_range q hq_lo hq_hi
    -- h1 : 4 * p10k_n * p2e_d ≤ 3 * p2e_n * p10k_d  (natAbs/if form).
    rw [hk]
    set kj := floorLog10ThreeQuartersPow2 q with hkj
    have hk_abs : kj.natAbs = if kj ≥ 0 then kj.toNat else (-kj).toNat := by split <;> omega
    rw [hq_abs, hk_abs] at h1
    -- Resolve the `if`s on the signs of `q` and `kj`.  In two sign-combos the
    -- inequality is linear in the power atoms (`4X ≤ 3Y ⟹ X ≤ Y`, `omega`);
    -- in a third the goal is `1 ≤ positive` (positivity); the fourth has a
    -- contradictory `4·(≥1) ≤ 3` hypothesis (`nlinarith`).
    rcases le_or_gt 0 q with hq | hq <;> rcases le_or_gt 0 kj with hkz | hkz <;>
      simp only [ge_iff_le, hq, hkz, if_pos, if_neg, Int.not_le, Int.not_lt,
        pow_zero, Nat.mul_one, Nat.one_mul] at h1 ⊢ <;>
      first
      | omega
      | exact Nat.one_le_iff_ne_zero.mpr (by positivity)
      | (exfalso
         have hpos : (1 : Nat) ≤ 10 ^ kj.toNat * 2 ^ (-q).toNat :=
           Nat.one_le_iff_ne_zero.mpr (by positivity)
         nlinarith [h1, hpos])
  · -- regular: k = floorLog10Pow2 q, use R15 first conjunct.
    have hk : k = floorLog10Pow2 q := by rw [hk_def, kOfMQ, if_neg hirr]
    obtain ⟨h1, _⟩ := R15HoldsAt_in_binary64_range q hq_lo hq_hi
    rw [hk]
    set kj := floorLog10Pow2 q with hkj
    have hk_abs : kj.natAbs = if kj ≥ 0 then kj.toNat else (-kj).toNat := by split <;> omega
    rw [hq_abs, hk_abs] at h1
    -- Here R15's first conjunct is exactly the goal (no `4/3` factor), so
    -- `omega` closes every sign-combo directly.
    rcases le_or_gt 0 q with hq | hq <;> rcases le_or_gt 0 kj with hkz | hkz <;>
      simp only [ge_iff_le, hq, hkz, if_pos, if_neg, Int.not_le, Int.not_lt,
        pow_zero, Nat.mul_one, Nat.one_mul] at h1 ⊢ <;>
      omega

end Srtfp.Schubfach

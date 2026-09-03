/- The cleared-denominator interval vocabulary the reader proofs are
   written against: `inRoundingInterval` and `cmpScaledMixed` reified as
   `Nat`/`Int` comparisons of their cleared sides. Moved here unchanged
   from the old printer proof stack so the reader proofs depend on
   nothing Schubfach. Retired by the reader rewrite. -/
import Srtfp.Proofs.Clinger.NatIntervalDefs
import Srtfp.Rat
import Srtfp.Tactics

open Srtfp.Compat

namespace Srtfp.Schubfach

/-- `2^{max q 0}`: the positive-side factor of `2^q`. -/
def twoPosPow (q : Int) : Nat := 2 ^ (if q ≥ 0 then q.toNat else 0)

/-- `2^{max -q 0}`: the negative-side factor of `2^q`. -/
def twoNegPow (q : Int) : Nat := 2 ^ (if q < 0 then (-q).toNat else 0)

/-- `10^{max k 0}`: the positive-side factor of `10^k`. -/
def tenPosPow (k : Int) : Nat := 10 ^ (if k ≥ 0 then k.toNat else 0)

/-- `10^{max -k 0}`: the negative-side factor of `10^k`. -/
def tenNegPow (k : Int) : Nat := 10 ^ (if k < 0 then (-k).toNat else 0)

@[simp] theorem tenPosPow_nonneg {k : Int} (h : 0 ≤ k) :
    tenPosPow k = 10 ^ k.toNat := by
  unfold tenPosPow; rw [if_pos h]

@[simp] theorem tenPosPow_neg {k : Int} (h : k < 0) :
    tenPosPow k = 1 := by
  unfold tenPosPow
  have : ¬ (0 ≤ k) := Int.not_le.mpr h
  rw [if_neg this]

@[simp] theorem tenNegPow_neg {k : Int} (h : k < 0) :
    tenNegPow k = 10 ^ (-k).toNat := by
  unfold tenNegPow; rw [if_pos h]

@[simp] theorem tenNegPow_nonneg {k : Int} (h : 0 ≤ k) :
    tenNegPow k = 1 := by
  unfold tenNegPow
  have : ¬ (k < 0) := Int.not_lt.mpr h
  rw [if_neg this]

/-- Positivity of any `twoPosPow` factor (always non-zero). -/
theorem twoPosPow_pos (q : Int) : 0 < twoPosPow q :=
  Nat.pow_pos (a := 2) (by decide)

/-- Positivity of any `twoNegPow` factor (always non-zero). -/
theorem twoNegPow_pos (q : Int) : 0 < twoNegPow q :=
  Nat.pow_pos (a := 2) (by decide)

/-- Positivity of any `tenPosPow` factor (always non-zero). -/
theorem tenPosPow_pos (k : Int) : 0 < tenPosPow k :=
  Nat.pow_pos (a := 10) (by decide)

/-- Positivity of any `tenNegPow` factor (always non-zero). -/
theorem tenNegPow_pos (k : Int) : 0 < tenNegPow k :=
  Nat.pow_pos (a := 10) (by decide)

/-- The cleared-denominator left-hand side:
`a · 2^{max q 0} · 10^{max -k 0}`. -/
def cmpScaledMixed.lhs (a : Int) (q k : Int) : Int :=
  a * (2 ^ (if q ≥ 0 then q.toNat else 0) : Int)
    * (10 ^ (if k < 0 then (-k).toNat else 0) : Int)

/-- The cleared-denominator right-hand side:
`b · 10^{max k 0} · 2^{max -q 0}`. -/
def cmpScaledMixed.rhs (b : Int) (q k : Int) : Int :=
  b * (10 ^ (if k ≥ 0 then k.toNat else 0) : Int)
    * (2 ^ (if q < 0 then (-q).toNat else 0) : Int)

/-- Reify `cmpScaledMixed` as the integer comparison of `lhs` vs `rhs`. -/
theorem cmpScaledMixed_eq (a : Int) (q : Int) (b : Int) (k : Int) :
    cmpScaledMixed a q b k =
      (if cmpScaledMixed.lhs a q k < cmpScaledMixed.rhs b q k then -1
       else if cmpScaledMixed.lhs a q k = cmpScaledMixed.rhs b q k then 0
       else 1) := by
  rfl

/-- `cmpScaledMixed < 0 ↔ a · 2^q < b · 10^k` (in cleared form). -/
theorem cmpScaledMixed_lt_iff (a : Int) (q : Int) (b : Int) (k : Int) :
    cmpScaledMixed a q b k < 0 ↔
      cmpScaledMixed.lhs a q k < cmpScaledMixed.rhs b q k := by
  rw [cmpScaledMixed_eq]
  by_cases h1 : cmpScaledMixed.lhs a q k < cmpScaledMixed.rhs b q k
  · simp [h1]
  · simp [h1]
    by_cases h2 : cmpScaledMixed.lhs a q k = cmpScaledMixed.rhs b q k
    · simp [h2]
    · simp [h2]

/-- `cmpScaledMixed = 0 ↔ a · 2^q = b · 10^k` (in cleared form). -/
theorem cmpScaledMixed_eq_zero_iff (a : Int) (q : Int) (b : Int) (k : Int) :
    cmpScaledMixed a q b k = 0 ↔
      cmpScaledMixed.lhs a q k = cmpScaledMixed.rhs b q k := by
  rw [cmpScaledMixed_eq]
  by_cases h1 : cmpScaledMixed.lhs a q k < cmpScaledMixed.rhs b q k
  · simp [h1]; intro h2; omega
  · simp [h1]

/-- `cmpScaledMixed > 0 ↔ a · 2^q > b · 10^k` (in cleared form). -/
theorem cmpScaledMixed_gt_iff (a : Int) (q : Int) (b : Int) (k : Int) :
    cmpScaledMixed a q b k > 0 ↔
      cmpScaledMixed.lhs a q k > cmpScaledMixed.rhs b q k := by
  rw [cmpScaledMixed_eq]
  by_cases h1 : cmpScaledMixed.lhs a q k < cmpScaledMixed.rhs b q k
  · simp [h1]; omega
  · simp [h1]
    by_cases h2 : cmpScaledMixed.lhs a q k = cmpScaledMixed.rhs b q k
    · simp [h2]
    · simp [h2]; omega

/-- Cleared `4 · u` for `u = s · 10^k`. -/
@[reducible] def fourU (s : Nat) (q k : Int) : Int :=
  cmpScaledMixed.rhs (4 * (s : Int)) q k

/-- Cleared `4 · v_R = (4m + 2) · 2^q`. -/
@[reducible] def fourVR (m : Nat) (q k : Int) : Int :=
  cmpScaledMixed.lhs (4 * (m : Int) + 2) q k

/-- Cleared `4 · v_L` (regular: `(4m-2) · 2^q`; irregular: `(4m-1) · 2^q`). -/
@[reducible] def fourVL (m : Nat) (q k : Int) (irreg : Bool) : Int :=
  cmpScaledMixed.lhs (if irreg then 4 * (m : Int) - 1 else 4 * (m : Int) - 2) q k

/-- Reified form: `inRoundingInterval s k m q irreg` is true iff the
left-side check and the right-side check both pass, in cleared form. -/
theorem inRoundingInterval_iff (s : Nat) (k : Int) (m : Nat) (q : Int) (irreg : Bool) :
    inRoundingInterval s k m q irreg = true ↔
      (fourVL m q k irreg < fourU s q k ∨
        (fourVL m q k irreg = fourU s q k ∧ m % 2 = 0)) ∧
      (fourU s q k < fourVR m q k ∨
        (fourU s q k = fourVR m q k ∧ m % 2 = 0)) := by
  unfold inRoundingInterval
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
             Bool.and_eq_true, decide_eq_true_eq]
  -- Unfold the two cmp calls in lhs/rhs form.
  have hL := cmpScaledMixed_lt_iff
              (if irreg then 4 * (m : Int) - 1 else 4 * (m : Int) - 2) q (4 * (s : Int)) k
  have hL0 := cmpScaledMixed_eq_zero_iff
              (if irreg then 4 * (m : Int) - 1 else 4 * (m : Int) - 2) q (4 * (s : Int)) k
  have hR := cmpScaledMixed_gt_iff
              (4 * (m : Int) + 2) q (4 * (s : Int)) k
  have hR0 := cmpScaledMixed_eq_zero_iff
              (4 * (m : Int) + 2) q (4 * (s : Int)) k
  -- Push both cmp forms into their lhs/rhs forms.
  constructor
  · intro ⟨hleft, hright⟩
    refine ⟨?_, ?_⟩
    · rcases hleft with hlt | ⟨heq, heven⟩
      · left
        unfold fourVL fourU
        exact hL.mp hlt
      · right
        refine ⟨?_, heven⟩
        unfold fourVL fourU
        exact hL0.mp heq
    · rcases hright with hgt | ⟨heq, heven⟩
      · left
        unfold fourU fourVR
        have := hR.mp hgt
        omega
      · right
        refine ⟨?_, heven⟩
        unfold fourU fourVR
        have := hR0.mp heq
        omega
  · intro ⟨hleft, hright⟩
    refine ⟨?_, ?_⟩
    · rcases hleft with hlt | ⟨heq, heven⟩
      · left
        apply hL.mpr
        unfold fourVL fourU at hlt
        exact hlt
      · right
        refine ⟨?_, heven⟩
        apply hL0.mpr
        unfold fourVL fourU at heq
        exact heq
    · rcases hright with hgt | ⟨heq, heven⟩
      · left
        apply hR.mpr
        unfold fourU fourVR at hgt
        omega
      · right
        refine ⟨?_, heven⟩
        apply hR0.mpr
        unfold fourU fourVR at heq
        omega

/-- `fourU = (4s) · tenPosPow k · twoNegPow q`. -/
theorem fourU_eq (s : Nat) (q k : Int) :
    fourU s q k = (4 * (s : Int)) * (tenPosPow k : Int) * (twoNegPow q : Int) := by
  unfold fourU cmpScaledMixed.rhs tenPosPow twoNegPow
  rfl

/-- `fourVR = (4m+2) · twoPosPow q · tenNegPow k`. -/
theorem fourVR_eq (m : Nat) (q k : Int) :
    fourVR m q k = (4 * (m : Int) + 2) * (twoPosPow q : Int) * (tenNegPow k : Int) := by
  unfold fourVR cmpScaledMixed.lhs twoPosPow tenNegPow
  rfl

/-- `fourVL` in regular case: `(4m - 2) · twoPosPow q · tenNegPow k`. -/
theorem fourVL_eq_regular (m : Nat) (q k : Int) (h_reg : ¬ (isIrregular m q = true)) :
    fourVL m q k (isIrregular m q)
      = (4 * (m : Int) - 2) * (twoPosPow q : Int) * (tenNegPow k : Int) := by
  unfold fourVL cmpScaledMixed.lhs twoPosPow tenNegPow
  have hreg : isIrregular m q = false := Bool.eq_false_iff.mpr h_reg
  rw [hreg]
  simp

/-- `fourVL` in irregular case: `(4m - 1) · twoPosPow q · tenNegPow k`. -/
theorem fourVL_eq_irregular (m : Nat) (q k : Int) (h_irreg : isIrregular m q = true) :
    fourVL m q k (isIrregular m q)
      = (4 * (m : Int) - 1) * (twoPosPow q : Int) * (tenNegPow k : Int) := by
  unfold fourVL cmpScaledMixed.lhs twoPosPow tenNegPow
  rw [h_irreg]
  simp

/-- Positivity of `twoPosPow q * tenNegPow k` as an Int. -/
theorem twoPos_tenNeg_pos_Int (q k : Int) :
    (0 : Int) < (twoPosPow q : Int) * (tenNegPow k : Int) := by
  unfold twoPosPow tenNegPow
  apply Int.mul_pos
  · exact_mod_cast Nat.pow_pos (a := 2) (by decide)
  · exact_mod_cast Nat.pow_pos (a := 10) (by decide)

end Srtfp.Schubfach

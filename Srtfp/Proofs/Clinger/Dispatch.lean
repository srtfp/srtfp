/- Clinger Decimal→Float correctness — dispatch (M4).

   This module discharges `BranchDispatch` (== `AbstractCorrectness`):
   case-split on the nested if-tree of `decodedAbs`, calling the
   appropriate per-branch helper (`regular_branch_correct`,
   `irregular_no_carry_correct`, `irregular_carry_correct`) for each
   non-overflow leaf. Overflow leaves are ruled out by `IsFiniteAbs`.

   ## Implementation approach

   We factor `decodedAbs` through `decodedAbsAB` (defined in `Base.lean`)
   which takes `a, b` as explicit Nat parameters (no outer pair-match).
   The dispatch then proves a single lemma on `decodedAbsAB` for any
   concrete `(a, b)`, and `branch_dispatch` instantiates it twice (once
   per `exp ≥ 0` case). -/

import Srtfp.Proofs.Clinger.Base
import Srtfp.Proofs.Clinger.Regular
import Srtfp.Proofs.Clinger.FindBinaryExp
import Srtfp.Proofs.Clinger.IrregularNoCarry
import Srtfp.Proofs.Clinger.IrregularCarry
import Srtfp.Proofs.Schubfach.Shorter

namespace Srtfp.Clinger

open Srtfp.Float
open Srtfp.Schubfach
open Srtfp

/-! ## Local helpers -/

/-- The subnormal branch always produces `q = -1074`, which is *not*
irregular (since `isIrregular` requires `q > minBinaryExp = -1074`). -/
private theorem subnormal_not_irregular (m : Nat) :
    isIrregular m (-1074 : Int) = false := by
  unfold isIrregular minBinaryExp
  simp

/-- `(1 : Nat) <<< 52 = 2^52`. -/
private theorem one_shl_52 : (1 : Nat) <<< 52 = 2 ^ 52 := by decide

/-- Cleared form at the regular scale `q = e - 52`. -/
private theorem regular_cleared
    (sig : Nat) (exp e : Int) (a b : Nat)
    (ha_eq : a = sig * tenPosPow exp) (hb_eq : b = tenNegPow exp)
    (hb : 0 < b) :
    ((scaleByPow2 a b (52 - e)).1 : Int) = sig * (tenPosPow exp) * (twoNegPow (e - 52)) ∧
    ((scaleByPow2 a b (52 - e)).2 : Int) = (tenNegPow exp) * (twoPosPow (e - 52)) ∧
    0 < (scaleByPow2 a b (52 - e)).2 := by
  have h_a : a = (if exp ≥ 0 then sig * 10 ^ exp.toNat else sig) := by
    rw [ha_eq]
    by_cases hexp : 0 ≤ exp
    · rw [tenPosPow_nonneg hexp, if_pos hexp]
    · have hexp' : exp < 0 := Int.not_le.mp hexp
      rw [tenPosPow_neg hexp', if_neg hexp, Nat.mul_one]
  have h_b : b = (if exp ≥ 0 then 1 else 10 ^ (-exp).toNat) := by
    rw [hb_eq]
    by_cases hexp : 0 ≤ exp
    · rw [tenNegPow_nonneg hexp, if_pos hexp]
    · have hexp' : exp < 0 := Int.not_le.mp hexp
      rw [tenNegPow_neg hexp', if_neg hexp]
  have hk_eq : (e - 52 : Int) = -(52 - e) := by omega
  refine ⟨?_, ?_, scaleByPow2_denom_pos hb⟩
  · rw [scaleByPow2_num_clear', h_a]
    have h_at := scaleByPow2_num_clear_at' sig exp (52 - e) (e - 52) hk_eq
    have h_cast :
        (((if exp ≥ 0 then sig * 10 ^ exp.toNat else sig)
            * (2 ^ (if (52 - e : Int) ≥ 0 then (52 - e).toNat else 0)) : Nat) : Int)
         = ((sig * (tenPosPow exp) * (twoNegPow (e - 52)) : Nat) : Int) := by
      congr 1
    exact h_cast
  · rw [scaleByPow2_denom_clear', h_b]
    have h_at := scaleByPow2_denom_clear_at' sig exp (52 - e) (e - 52) hk_eq
    have h_cast :
        (((if exp ≥ 0 then 1 else 10 ^ (-exp).toNat)
            * (2 ^ (if ¬ ((52 - e : Int) ≥ 0) then (-(52 - e)).toNat else 0)) : Nat) : Int)
         = ((tenNegPow exp * twoPosPow (e - 52) : Nat) : Int) := by
      congr 1
    exact h_cast

/-- Cleared form at the subnormal scale `q = -1074` (k = 1074). -/
private theorem subnormal_cleared
    (sig : Nat) (exp : Int) (a b : Nat)
    (ha_eq : a = sig * tenPosPow exp) (hb_eq : b = tenNegPow exp)
    (hb : 0 < b) :
    ((scaleByPow2 a b 1074).1 : Int) = sig * (tenPosPow exp) * (twoNegPow (-1074)) ∧
    ((scaleByPow2 a b 1074).2 : Int) = (tenNegPow exp) * (twoPosPow (-1074)) ∧
    0 < (scaleByPow2 a b 1074).2 := by
  have h_a : a = (if exp ≥ 0 then sig * 10 ^ exp.toNat else sig) := by
    rw [ha_eq]
    by_cases hexp : 0 ≤ exp
    · rw [tenPosPow_nonneg hexp, if_pos hexp]
    · have hexp' : exp < 0 := Int.not_le.mp hexp
      rw [tenPosPow_neg hexp', if_neg hexp, Nat.mul_one]
  have h_b : b = (if exp ≥ 0 then 1 else 10 ^ (-exp).toNat) := by
    rw [hb_eq]
    by_cases hexp : 0 ≤ exp
    · rw [tenNegPow_nonneg hexp, if_pos hexp]
    · have hexp' : exp < 0 := Int.not_le.mp hexp
      rw [tenNegPow_neg hexp', if_neg hexp]
  have hk_eq : ((-1074 : Int)) = -(1074 : Int) := by omega
  refine ⟨?_, ?_, scaleByPow2_denom_pos hb⟩
  · rw [scaleByPow2_num_clear', h_a]
    have h_at := scaleByPow2_num_clear_at' sig exp 1074 (-1074) hk_eq
    have h_cast :
        (((if exp ≥ 0 then sig * 10 ^ exp.toNat else sig)
            * (2 ^ (if (1074 : Int) ≥ 0 then (1074 : Int).toNat else 0)) : Nat) : Int)
         = ((sig * (tenPosPow exp) * (twoNegPow (-1074)) : Nat) : Int) := by
      congr 1
    exact h_cast
  · rw [scaleByPow2_denom_clear', h_b]
    have h_at := scaleByPow2_denom_clear_at' sig exp 1074 (-1074) hk_eq
    have h_cast :
        (((if exp ≥ 0 then 1 else 10 ^ (-exp).toNat)
            * (2 ^ (if ¬ ((1074 : Int) ≥ 0) then (-(1074 : Int)).toNat else 0)) : Nat) : Int)
         = ((tenNegPow exp * twoPosPow (-1074) : Nat) : Int) := by
      congr 1
    exact h_cast

/-- Subnormal helper: any `(m, -1074)` with `m = roundNearestEven (scaleByPow2 a b 1074).1 .2`
satisfies the rounding interval. -/
private theorem dispatch_subnormal_at_minus1074
    (_sign : Bool) (sig : Nat) (exp : Int) (a b : Nat)
    (m : Nat)
    (ha_eq : a = sig * tenPosPow exp)
    (hb_eq : b = tenNegPow exp)
    (hb_pos : 0 < b)
    (hm_eq : m = roundNearestEven (scaleByPow2 a b 1074).1
                                   (scaleByPow2 a b 1074).2) :
    inRoundingInterval sig exp m (-1074) (isIrregular m (-1074)) = true := by
  obtain ⟨hnum_int, hdenom_int, hdenom_pos⟩ :=
    subnormal_cleared sig exp a b ha_eq hb_eq hb_pos
  have h_irreg_false : ¬ isIrregular m (-1074) = true := by
    rw [subnormal_not_irregular]; decide
  exact regular_branch_correct sig exp m (-1074)
          (scaleByPow2 a b 1074).1 (scaleByPow2 a b 1074).2
          h_irreg_false hnum_int hdenom_int hm_eq hdenom_pos

/-! ## Dispatch on `decodedAbsAB` (concrete `(a, b)`)

This is the heart of the proof. The if-tree of `decodedAbsAB` is
walked case-by-case using `by_cases` + `rw [if_pos/neg]`. Once a leaf
is reached, the appropriate per-branch helper (regular,
irregular-carry, irregular-no-carry, or subnormal) closes the goal. -/

/-- The normal-spaced branch result as a `Decoded`. -/
private def normalDecoded (sign : Bool) (a b : Nat) : Decoded :=
  have e := findBinaryExp a b
  have m := roundNearestEven (scaleByPow2 a b (52 - e)).1
                              (scaleByPow2 a b (52 - e)).2
  if m ≥ 2 ^ 53 then
    have e' := e + 1
    if e' > 1023 then ({sign := sign, m := 0, q := 1024} : Decoded)
    else {sign := sign, m := 1 <<< 52, q := e' - 52}
  else {sign := sign, m := m, q := e - 52}

/-- The subnormal branch result as a `Decoded`. -/
private def subnormalDecoded (sign : Bool) (a b : Nat) : Decoded :=
  have m := roundNearestEven (scaleByPow2 a b 1074).1
                              (scaleByPow2 a b 1074).2
  if m = 0 then ({sign := sign, m := 0, q := -1074} : Decoded)
  else if m ≥ 2 ^ 52 then {sign := sign, m := m, q := -1074}
  else {sign := sign, m := m, q := -1074}

/-- Dispatch the normal-spaced branch (`e ≥ -1022`). -/
private theorem dispatch_normal_AB
    (sign : Bool) (sig : Nat) (exp : Int) (a b : Nat)
    (ha_eq : a = sig * tenPosPow exp)
    (hb_eq : b = tenNegPow exp)
    (ha_pos : 0 < a)
    (hb_pos : 0 < b)
    (h_normal : findBinaryExp a b ≥ -1022)
    (h_finite : (normalDecoded sign a b).q ≤ 971) :
    inRoundingInterval sig exp (normalDecoded sign a b).m (normalDecoded sign a b).q
      (isIrregular (normalDecoded sign a b).m (normalDecoded sign a b).q) = true := by
  -- Trick: substitute `normalDecoded sign a b` by its concrete value via
  -- `have h_eq : ... = ⟨...⟩` + `rw [h_eq]`. Direct rewrites cause kernel
  -- "deep recursion" — see project notes.
  by_cases h_carry :
      roundNearestEven (scaleByPow2 a b (52 - findBinaryExp a b)).1
                        (scaleByPow2 a b (52 - findBinaryExp a b)).2 ≥ 2 ^ 53
  · by_cases h_over2 : findBinaryExp a b + 1 > 1023
    · exfalso
      have h_eq_fin : normalDecoded sign a b = (⟨sign, 0, 1024⟩ : Decoded) := by
        unfold normalDecoded; rw [if_pos h_carry, if_pos h_over2]
      rw [h_eq_fin] at h_finite
      exact absurd (show (1024 : Int) ≤ 971 from h_finite) (by decide)
    · have h_eq : normalDecoded sign a b =
          (⟨sign, 1 <<< 52, findBinaryExp a b + 1 - 52⟩ : Decoded) := by
        unfold normalDecoded; rw [if_pos h_carry, if_neg h_over2]
      rw [h_eq]
      show inRoundingInterval sig exp (1 <<< 52) (findBinaryExp a b + 1 - 52)
            (isIrregular (1 <<< 52) (findBinaryExp a b + 1 - 52)) = true
      have h_q_eq : (findBinaryExp a b + 1 - 52 : Int)
                      = findBinaryExp a b - 51 := by omega
      rw [one_shl_52, h_q_eq]
      exact irregular_carry_correct sig exp (findBinaryExp a b) a b ha_eq hb_eq
              ha_pos hb_pos rfl h_normal h_carry
  · have h_eq : normalDecoded sign a b =
        (⟨sign, roundNearestEven (scaleByPow2 a b (52 - findBinaryExp a b)).1
                                  (scaleByPow2 a b (52 - findBinaryExp a b)).2,
          findBinaryExp a b - 52⟩ : Decoded) := by
      unfold normalDecoded; rw [if_neg h_carry]
    rw [h_eq]
    show inRoundingInterval sig exp _ (findBinaryExp a b - 52)
          (isIrregular _ (findBinaryExp a b - 52)) = true
    by_cases h_irreg :
        isIrregular
          (roundNearestEven (scaleByPow2 a b (52 - findBinaryExp a b)).1
                             (scaleByPow2 a b (52 - findBinaryExp a b)).2)
          (findBinaryExp a b - 52) = true
    · have h_irreg' := h_irreg
      unfold isIrregular minNormalSignificand minBinaryExp at h_irreg'
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h_irreg'
      obtain ⟨h_m_eq, _h_q⟩ := h_irreg'
      rw [h_m_eq]
      rw [one_shl_52]
      rw [one_shl_52] at h_m_eq
      exact irregular_no_carry_correct sig exp (findBinaryExp a b) a b ha_eq hb_eq
              ha_pos hb_pos rfl h_m_eq.symm
    · obtain ⟨hnum_int, hdenom_int, hdenom_pos⟩ :=
        regular_cleared sig exp (findBinaryExp a b) a b ha_eq hb_eq hb_pos
      exact regular_branch_correct sig exp _ _ _ _
              h_irreg hnum_int hdenom_int rfl hdenom_pos

/-- Dispatch the subnormal branch (`e < -1022`). -/
private theorem dispatch_subnormal_AB
    (sign : Bool) (sig : Nat) (exp : Int) (a b : Nat)
    (ha_eq : a = sig * tenPosPow exp)
    (hb_eq : b = tenNegPow exp)
    (hb_pos : 0 < b) :
    inRoundingInterval sig exp (subnormalDecoded sign a b).m (subnormalDecoded sign a b).q
      (isIrregular (subnormalDecoded sign a b).m (subnormalDecoded sign a b).q) = true := by
  -- Trick: substitute `subnormalDecoded sign a b` by its concrete value
  -- via `have h_eq : ... = ⟨...⟩` + `rw [h_eq]`. Direct `rw [if_pos]`
  -- chains here cause kernel "deep recursion" — see project notes.
  by_cases h_zero : roundNearestEven (scaleByPow2 a b 1074).1
                                      (scaleByPow2 a b 1074).2 = 0
  · have h_eq : subnormalDecoded sign a b = (⟨sign, 0, -1074⟩ : Decoded) := by
      unfold subnormalDecoded; rw [if_pos h_zero]
    rw [h_eq]
    exact dispatch_subnormal_at_minus1074 sign sig exp a b 0 ha_eq hb_eq hb_pos h_zero.symm
  · by_cases h_nb : roundNearestEven (scaleByPow2 a b 1074).1
                                      (scaleByPow2 a b 1074).2 ≥ 2 ^ 52
    · have h_eq : subnormalDecoded sign a b =
          (⟨sign, roundNearestEven (scaleByPow2 a b 1074).1
                                    (scaleByPow2 a b 1074).2, -1074⟩ : Decoded) := by
        unfold subnormalDecoded; rw [if_neg h_zero, if_pos h_nb]
      rw [h_eq]
      exact dispatch_subnormal_at_minus1074 sign sig exp a b
              (roundNearestEven (scaleByPow2 a b 1074).1 (scaleByPow2 a b 1074).2)
              ha_eq hb_eq hb_pos rfl
    · have h_eq : subnormalDecoded sign a b =
          (⟨sign, roundNearestEven (scaleByPow2 a b 1074).1
                                    (scaleByPow2 a b 1074).2, -1074⟩ : Decoded) := by
        unfold subnormalDecoded; rw [if_neg h_zero, if_neg h_nb]
      rw [h_eq]
      exact dispatch_subnormal_at_minus1074 sign sig exp a b
              (roundNearestEven (scaleByPow2 a b 1074).1 (scaleByPow2 a b 1074).2)
              ha_eq hb_eq hb_pos rfl

private theorem branch_dispatch_AB
    (sign : Bool) (sig : Nat) (exp : Int) (a b : Nat)
    (ha_eq : a = sig * tenPosPow exp)
    (hb_eq : b = tenNegPow exp)
    (ha_pos : 0 < a)
    (hb_pos : 0 < b)
    (h_finite : (decodedAbsAB sign a b).q ≤ 971) :
    inRoundingInterval sig exp (decodedAbsAB sign a b).m
      (decodedAbsAB sign a b).q
      (isIrregular (decodedAbsAB sign a b).m (decodedAbsAB sign a b).q) = true := by
  -- Substitute decodedAbsAB by its concrete branch value via `have h_eq` + `rw`
  -- to avoid kernel "deep recursion" issues.
  by_cases h_over : findBinaryExp a b > 1023
  · exfalso
    have h_eq : decodedAbsAB sign a b = (⟨sign, 0, 1024⟩ : Decoded) := by
      unfold decodedAbsAB; rw [if_pos h_over]
    rw [h_eq] at h_finite
    exact absurd (show (1024 : Int) ≤ 971 from h_finite) (by decide)
  · by_cases h_normal : findBinaryExp a b ≥ -1022
    · -- Normal branch: reduce to dispatch_normal_AB.
      have h_eq : decodedAbsAB sign a b = normalDecoded sign a b := by
        unfold decodedAbsAB normalDecoded; rw [if_neg h_over, if_pos h_normal]
      rw [h_eq]
      rw [h_eq] at h_finite
      exact dispatch_normal_AB sign sig exp a b ha_eq hb_eq ha_pos hb_pos h_normal h_finite
    · -- Subnormal branch.
      have h_eq : decodedAbsAB sign a b = subnormalDecoded sign a b := by
        unfold decodedAbsAB subnormalDecoded; rw [if_neg h_over, if_neg h_normal]
      rw [h_eq]
      exact dispatch_subnormal_AB sign sig exp a b ha_eq hb_eq hb_pos

/-! ## Top-level `BranchDispatch` -/

theorem branch_dispatch : BranchDispatch := by
  intro sign sig exp h_sig h_finite
  unfold IsFiniteAbs at h_finite
  by_cases hexp : exp ≥ 0
  · rw [decodedAbs_eq_decodedAbsAB_pos sign sig exp h_sig hexp] at h_finite ⊢
    have ha_eq : sig * 10 ^ exp.toNat = sig * tenPosPow exp := by
      rw [tenPosPow_nonneg hexp]
    have hb_eq : (1 : Nat) = tenNegPow exp := by rw [tenNegPow_nonneg hexp]
    have ha_pos : 0 < sig * 10 ^ exp.toNat :=
      Nat.mul_pos (Nat.pos_of_ne_zero h_sig)
                  (Nat.pow_pos (by decide : 0 < (10 : Nat)))
    have hb_pos : (0 : Nat) < 1 := by decide
    exact branch_dispatch_AB sign sig exp _ _ ha_eq hb_eq ha_pos hb_pos h_finite
  · have hexp' : exp < 0 := Int.not_le.mp hexp
    rw [decodedAbs_eq_decodedAbsAB_neg sign sig exp h_sig hexp] at h_finite ⊢
    have ha_eq : sig = sig * tenPosPow exp := by
      rw [tenPosPow_neg hexp', Nat.mul_one]
    have hb_eq : (10 : Nat) ^ (-exp).toNat = tenNegPow exp := by
      rw [tenNegPow_neg hexp']
    have ha_pos : 0 < sig := Nat.pos_of_ne_zero h_sig
    have hb_pos : 0 < (10 : Nat) ^ (-exp).toNat :=
      Nat.pow_pos (by decide : 0 < (10 : Nat))
    exact branch_dispatch_AB sign sig exp _ _ ha_eq hb_eq ha_pos hb_pos h_finite

end Srtfp.Clinger

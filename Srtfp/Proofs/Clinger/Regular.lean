/- Clinger Decimal→Float correctness — regular branch (M4).

   This module discharges the *regular* sub-branches of `decodedAbs`:
   the six non-overflow non-irregular outputs. The single theorem
   `regular_branch_correct` covers all six in a uniform cleared-form
   argument from the half-ULP bound + tie-to-even parity. -/

import Srtfp.Proofs.Clinger.Base
import Srtfp.Proofs.Schubfach.Shorter

namespace Srtfp.Clinger

open Srtfp.Float
open Srtfp.Schubfach
open Srtfp

/-! ## Cleared-form scaling identities -/

/-- The numerator of `scaleByPow2 a b k` equals `a · 2^max(k,0)`. -/
private theorem scaleByPow2_num_clear (a b : Nat) (k : Int) :
    (scaleByPow2 a b k).1 = a * (2 ^ (if k ≥ 0 then k.toNat else 0)) := by
  rw [scaleByPow2_num_eq]
  by_cases hk : k ≥ 0
  · simp [hk]
  · simp [hk]

/-- The denominator of `scaleByPow2 a b k` equals `b · 2^max(-k,0)`. -/
private theorem scaleByPow2_denom_clear (a b : Nat) (k : Int) :
    (scaleByPow2 a b k).2 = b * (2 ^ (if ¬ k ≥ 0 then (-k).toNat else 0)) := by
  rw [scaleByPow2_denom_eq]
  by_cases hk : k ≥ 0
  · simp [hk]
  · simp [hk]

/-- Numerator identity at `q = -k`. -/
private theorem scaleByPow2_num_clear_at (sig : Nat) (exp : Int) (k q : Int)
    (hq : q = -k) :
    let a : Nat := if exp ≥ 0 then sig * 10 ^ exp.toNat else sig
    a * (2 ^ (if k ≥ 0 then k.toNat else 0))
      = sig * (tenPosPow exp) * (twoNegPow q) := by
  intro a
  unfold tenPosPow twoNegPow
  show a * (2 ^ (if k ≥ 0 then k.toNat else 0))
      = sig * (10 ^ (if exp ≥ 0 then exp.toNat else 0))
            * (2 ^ (if q < 0 then (-q).toNat else 0))
  have h2eq : (if k ≥ 0 then k.toNat else 0) = (if q < 0 then (-q).toNat else 0) := by
    by_cases hk : k ≥ 0
    · rw [if_pos hk]
      by_cases hk0 : k = 0
      · have hq0 : q = 0 := by omega
        have h_lhs : k.toNat = 0 := by rw [hk0]; rfl
        have h_rhs : ¬ (q < 0) := by omega
        rw [h_lhs, if_neg h_rhs]
      · have hk_pos : k > 0 := by omega
        have hq_neg : q < 0 := by omega
        rw [if_pos hq_neg]
        have : (-q).toNat = k.toNat := by
          have : -q = k := by omega
          rw [this]
        rw [this]
    · rw [if_neg hk]
      have hk_neg : k < 0 := by omega
      have hnotq : ¬ (q < 0) := by omega
      rw [if_neg hnotq]
  rw [h2eq]
  by_cases hexp : exp ≥ 0
  · show (if exp ≥ 0 then sig * 10 ^ exp.toNat else sig)
            * (2 ^ (if q < 0 then (-q).toNat else 0))
        = sig * (10 ^ (if exp ≥ 0 then exp.toNat else 0))
              * (2 ^ (if q < 0 then (-q).toNat else 0))
    rw [if_pos hexp, if_pos hexp]
  · show (if exp ≥ 0 then sig * 10 ^ exp.toNat else sig)
            * (2 ^ (if q < 0 then (-q).toNat else 0))
        = sig * (10 ^ (if exp ≥ 0 then exp.toNat else 0))
              * (2 ^ (if q < 0 then (-q).toNat else 0))
    rw [if_neg hexp, if_neg hexp, Nat.pow_zero, Nat.mul_one]

/-- Denominator identity at `q = -k`. -/
private theorem scaleByPow2_denom_clear_at (_sig : Nat) (exp : Int) (k q : Int)
    (hq : q = -k) :
    let b : Nat := if exp ≥ 0 then 1 else 10 ^ (-exp).toNat
    b * (2 ^ (if ¬ (k ≥ 0) then (-k).toNat else 0))
      = (tenNegPow exp) * (twoPosPow q) := by
  intro b
  unfold tenNegPow twoPosPow
  show b * (2 ^ (if ¬ (k ≥ 0) then (-k).toNat else 0))
      = (10 ^ (if exp < 0 then (-exp).toNat else 0))
        * (2 ^ (if q ≥ 0 then q.toNat else 0))
  have h2eq : (if ¬ (k ≥ 0) then (-k).toNat else 0)
              = (if q ≥ 0 then q.toNat else 0) := by
    by_cases hk : k ≥ 0
    · rw [if_neg (by simp [hk] : ¬ ¬ (k ≥ 0))]
      by_cases hk0 : k = 0
      · have hq0 : q = 0 := by omega
        have h_rhs : q ≥ 0 := by omega
        rw [if_pos h_rhs]
        have : q.toNat = 0 := by rw [hq0]; rfl
        rw [this]
      · have hk_pos : k > 0 := by omega
        have hnot : ¬ (q ≥ 0) := by omega
        rw [if_neg hnot]
    · rw [if_pos hk]
      have hk_neg : k < 0 := by omega
      have hq_pos : q ≥ 0 := by omega
      rw [if_pos hq_pos]
      have : (-k).toNat = q.toNat := by
        have : -k = q := by omega
        rw [this]
      rw [this]
  rw [h2eq]
  by_cases hexp : exp ≥ 0
  · show (if exp ≥ 0 then 1 else 10 ^ (-exp).toNat)
            * (2 ^ (if q ≥ 0 then q.toNat else 0))
        = (10 ^ (if exp < 0 then (-exp).toNat else 0))
              * (2 ^ (if q ≥ 0 then q.toNat else 0))
    rw [if_pos hexp]
    have h_exp_not_lt : ¬ exp < 0 := by omega
    rw [if_neg h_exp_not_lt]
  · show (if exp ≥ 0 then 1 else 10 ^ (-exp).toNat)
            * (2 ^ (if q ≥ 0 then q.toNat else 0))
        = (10 ^ (if exp < 0 then (-exp).toNat else 0))
              * (2 ^ (if q ≥ 0 then q.toNat else 0))
    rw [if_neg hexp]
    have h_exp_lt : exp < 0 := by omega
    rw [if_pos h_exp_lt]

/-! ## Algebraic helpers for the regular bound -/

/-- Algebraic helper: `4·sig · (TP · Q) = 4·num`. -/
private theorem fourSigTPQ_eq_fourNum
    (sig : Nat) (exp q : Int) (num : Nat)
    (hnum_pos : (num : Int) = sig * (tenPosPow exp) * (twoNegPow q)) :
    4 * (sig : Int) * ((tenPosPow exp : Int) * (twoNegPow q : Int))
      = 4 * (num : Int) := by
  rw [hnum_pos]
  rw [Int.mul_assoc (4 : Int) (sig : Int) ((tenPosPow exp : Int) * (twoNegPow q : Int)),
      ← Int.mul_assoc (sig : Int) (tenPosPow exp : Int) (twoNegPow q : Int)]

/-- Algebraic helper: `P · TN = denom`. -/
private theorem PQ_eq_denom
    (exp q : Int) (denom : Nat)
    (hdenom_pos : (denom : Int) = (tenNegPow exp) * (twoPosPow q)) :
    ((twoPosPow q : Int) * (tenNegPow exp : Int)) = (denom : Int) := by
  rw [hdenom_pos, Int.mul_comm]

/-- For `m = roundNearestEven num denom` on the cleared form, the regular
half-ULP bound `(4m-2)·P ≤ 4·sig·Q ≤ (4m+2)·P` holds. -/
private theorem rounded_in_regular_Rv
    (sig : Nat) (exp q : Int) (m : Nat)
    (num denom : Nat)
    (hnum_pos : (num : Int) = sig * (tenPosPow exp) * (twoNegPow q))
    (hdenom_pos : (denom : Int) = (tenNegPow exp) * (twoPosPow q))
    (hm : m = roundNearestEven num denom)
    (hdenom : 0 < denom) :
    (4 * (m : Int) - 2) * ((twoPosPow q : Int) * (tenNegPow exp : Int))
      ≤ 4 * (sig : Int) * ((tenPosPow exp : Int) * (twoNegPow q : Int))
    ∧ 4 * (sig : Int) * ((tenPosPow exp : Int) * (twoNegPow q : Int))
      ≤ (4 * (m : Int) + 2) * ((twoPosPow q : Int) * (tenNegPow exp : Int)) := by
  have hbound := roundNearestEven_cleared_bound num denom hdenom
  obtain ⟨h_lo, h_hi⟩ := hbound
  rw [← hm] at h_lo h_hi
  have hN_eq : 4 * (sig : Int) * ((tenPosPow exp : Int) * (twoNegPow q : Int))
                  = 4 * (num : Int) := fourSigTPQ_eq_fourNum sig exp q num hnum_pos
  have hD_eq : (twoPosPow q : Int) * (tenNegPow exp : Int) = denom :=
    PQ_eq_denom exp q denom hdenom_pos
  generalize hM : (m : Int) = M at h_lo h_hi
  generalize hN : (num : Int) = N at h_lo h_hi hN_eq
  generalize hD' : (denom : Int) = D at h_lo h_hi hD_eq
  have h_eq_lo : (4 * M - 2) * D = 4 * (M * D) - 2 * D := by
    rw [Int.sub_mul, Int.mul_assoc]
  have h_eq_hi : (4 * M + 2) * D = 4 * (M * D) + 2 * D := by
    rw [Int.add_mul, Int.mul_assoc]
  have h_4MD : 4 * (M * D) = 2 * (2 * M * D) := by
    rw [show (4 : Int) = 2 * 2 from rfl, Int.mul_assoc 2 2 (M * D),
        Int.mul_assoc 2 M D]
  refine ⟨?_, ?_⟩
  · rw [hN_eq, hD_eq, h_eq_lo, h_4MD]
    have h2 : 2 * (2 * M * D) ≤ 2 * (2 * N + D) := by
      apply Int.mul_le_mul_of_nonneg_left h_hi; decide
    omega
  · rw [hN_eq, hD_eq, h_eq_hi, h_4MD]
    have h2 : 2 * (2 * N - D) ≤ 2 * (2 * M * D) := by
      apply Int.mul_le_mul_of_nonneg_left h_lo; decide
    omega

/-! ## Parity at tie -/

/-- Tie-to-even parity for `roundNearestEven`. -/
private theorem roundNearestEven_even_of_tie (a b : Nat) (hb : 0 < b)
    (htie : 2 * a = (roundNearestEven a b) * (2 * b) - b
            ∨ (roundNearestEven a b) * (2 * b) = 2 * a + b
            ∨ (roundNearestEven a b) * (2 * b) + b = 2 * a) :
    (roundNearestEven a b) % 2 = 0 := by
  have h_div : a / b * b + a % b = a := by
    rw [Nat.mul_comm]; exact Nat.div_add_mod a b
  have h_eq_amod : a - a / b * b = a % b := by omega
  have hassoc : a / b * (2 * b) = 2 * (a / b * b) := by
    rw [show 2 * b = b * 2 from Nat.mul_comm 2 b, ← Nat.mul_assoc]
    rw [show a / b * b * 2 = 2 * (a / b * b) from Nat.mul_comm _ _]
  by_cases h1 : 2 * (a - a / b * b) < b
  · have hM_eq : roundNearestEven a b = a / b := by
      show (if 2 * (a - a / b * b) < b then a / b
         else if 2 * (a - a / b * b) > b then a / b + 1
         else if a / b % 2 = 0 then a / b else a / b + 1) = a / b
      rw [if_pos h1]
    have h1' : 2 * (a % b) < b := by rw [← h_eq_amod]; exact h1
    have h_2a : 2 * a = 2 * (a / b * b) + 2 * (a % b) := by omega
    rcases htie with htie | htie | htie
    · rw [hM_eq, hassoc] at htie
      have h_sub_le : 2 * (a / b * b) - b ≤ 2 * (a / b * b) := Nat.sub_le _ _
      have h2amod0 : 2 * (a % b) = 0 := by omega
      have hamod0 : a % b = 0 := by omega
      have ha_eq : a = a / b * b := by omega
      rw [← ha_eq] at htie
      by_cases h2a_b : 2 * a < b
      · have h_2a_sub : 2 * a - b = 0 := by omega
        rw [h_2a_sub] at htie
        have ha0 : a = 0 := by omega
        rw [hM_eq, ha0]; simp
      · have : 2 * a ≥ b := by omega
        have : b = 0 := by omega
        omega
    · rw [hM_eq, hassoc] at htie
      have hMb_le : (a / b) * b ≤ a := Nat.div_mul_le_self _ _
      exfalso; omega
    · rw [hM_eq, hassoc] at htie
      have h2amod : 2 * (a % b) = b := by omega
      exfalso; omega
  · by_cases h2 : 2 * (a - a / b * b) > b
    · have hM_eq : roundNearestEven a b = a / b + 1 := by
        show (if 2 * (a - a / b * b) < b then a / b
           else if 2 * (a - a / b * b) > b then a / b + 1
           else if a / b % 2 = 0 then a / b else a / b + 1) = a / b + 1
        rw [if_neg h1, if_pos h2]
      have h2' : 2 * (a % b) > b := by rw [← h_eq_amod]; exact h2
      have hexp_M : ((a / b + 1) * (2 * b) : Nat) = 2 * (a / b * b) + 2 * b := by
        rw [Nat.add_mul, Nat.one_mul, hassoc]
      have h_mod_lt : a % b < b := Nat.mod_lt a hb
      exfalso
      rcases htie with htie | htie | htie
      · rw [hM_eq, hexp_M] at htie; omega
      · rw [hM_eq, hexp_M] at htie; omega
      · rw [hM_eq, hexp_M] at htie; omega
    · have htie_b : 2 * (a - a / b * b) = b := by omega
      by_cases h3 : a / b % 2 = 0
      · have hM_eq : roundNearestEven a b = a / b := by
          show (if 2 * (a - a / b * b) < b then a / b
             else if 2 * (a - a / b * b) > b then a / b + 1
             else if a / b % 2 = 0 then a / b else a / b + 1) = a / b
          rw [if_neg h1, if_neg h2, if_pos h3]
        rw [hM_eq]; exact h3
      · have hM_eq : roundNearestEven a b = a / b + 1 := by
          show (if 2 * (a - a / b * b) < b then a / b
             else if 2 * (a - a / b * b) > b then a / b + 1
             else if a / b % 2 = 0 then a / b else a / b + 1) = a / b + 1
          rw [if_neg h1, if_neg h2, if_neg h3]
        rw [hM_eq]; omega

/-- At the lower cleared boundary, `m` is even. -/
private theorem parity_at_tie_lower
    (sig : Nat) (exp q : Int) (m : Nat) (num denom : Nat)
    (hnum_pos : (num : Int) = sig * (tenPosPow exp) * (twoNegPow q))
    (hdenom_pos : (denom : Int) = (tenNegPow exp) * (twoPosPow q))
    (hm : m = roundNearestEven num denom)
    (hdenom : 0 < denom)
    (h_eq : (4 * (m : Int) - 2) * ((twoPosPow q : Int) * (tenNegPow exp : Int))
              = 4 * (sig : Int) * ((tenPosPow exp : Int) * (twoNegPow q : Int))) :
    m % 2 = 0 := by
  rw [PQ_eq_denom exp q denom hdenom_pos] at h_eq
  rw [fourSigTPQ_eq_fourNum sig exp q num hnum_pos] at h_eq
  have h_int : (m : Int) * (2 * denom) = 2 * (num : Int) + denom := by
    have hexp : (4 * (m : Int) - 2) * denom = 4 * (m : Int) * denom - 2 * denom := by
      rw [Int.sub_mul]
    rw [hexp] at h_eq
    have hassoc : (m : Int) * (2 * denom) = 2 * (m : Int) * denom := by
      rw [Int.mul_comm (m : Int) (2 * denom), Int.mul_assoc 2 denom (m : Int),
          Int.mul_comm denom (m : Int), ← Int.mul_assoc 2 (m : Int) denom]
    have h_4mD : 4 * (m : Int) * denom = 2 * (2 * (m : Int) * denom) := by
      rw [show (4 : Int) = 2 * 2 from rfl, Int.mul_assoc 2 2 (m : Int),
          Int.mul_assoc 2 (2 * (m : Int)) denom]
    rw [h_4mD] at h_eq
    rw [hassoc]; omega
  have h_nat : m * (2 * denom) = 2 * num + denom := by exact_mod_cast h_int
  rw [hm]
  apply roundNearestEven_even_of_tie num denom hdenom
  right; left
  rw [← hm]; exact h_nat

/-- At the upper cleared boundary, `m` is even. -/
private theorem parity_at_tie_upper
    (sig : Nat) (exp q : Int) (m : Nat) (num denom : Nat)
    (hnum_pos : (num : Int) = sig * (tenPosPow exp) * (twoNegPow q))
    (hdenom_pos : (denom : Int) = (tenNegPow exp) * (twoPosPow q))
    (hm : m = roundNearestEven num denom)
    (hdenom : 0 < denom)
    (h_eq : 4 * (sig : Int) * ((tenPosPow exp : Int) * (twoNegPow q : Int))
              = (4 * (m : Int) + 2) * ((twoPosPow q : Int) * (tenNegPow exp : Int))) :
    m % 2 = 0 := by
  rw [PQ_eq_denom exp q denom hdenom_pos] at h_eq
  rw [fourSigTPQ_eq_fourNum sig exp q num hnum_pos] at h_eq
  have hexp : (4 * (m : Int) + 2) * denom = 4 * (m : Int) * denom + 2 * denom := by
    rw [Int.add_mul]
  rw [hexp] at h_eq
  have hassoc : (m : Int) * (2 * denom) = 2 * (m : Int) * denom := by
    rw [Int.mul_comm (m : Int) (2 * denom), Int.mul_assoc 2 denom (m : Int),
        Int.mul_comm denom (m : Int), ← Int.mul_assoc 2 (m : Int) denom]
  have h_4mD : 4 * (m : Int) * denom = 2 * (2 * (m : Int) * denom) := by
    rw [show (4 : Int) = 2 * 2 from rfl, Int.mul_assoc 2 2 (m : Int),
        Int.mul_assoc 2 (2 * (m : Int)) denom]
  rw [h_4mD] at h_eq
  have h_int : (m : Int) * (2 * denom) + denom = 2 * (num : Int) := by
    rw [hassoc]; omega
  have h_nat : m * (2 * denom) + denom = 2 * num := by exact_mod_cast h_int
  rw [hm]
  apply roundNearestEven_even_of_tie num denom hdenom
  right; right
  rw [← hm]; exact h_nat

/-! ## Regular-branch correctness -/

/-- Combined regular-branch correctness: applies to all `decodedAbs`
sub-branches except the irregular ones. -/
theorem regular_branch_correct
    (sig : Nat) (exp : Int) (m : Nat) (q : Int)
    (num denom : Nat)
    (h_irreg : ¬ (isIrregular m q = true))
    (hnum_pos : (num : Int) = sig * (tenPosPow exp) * (twoNegPow q))
    (hdenom_pos : (denom : Int) = (tenNegPow exp) * (twoPosPow q))
    (hm : m = roundNearestEven num denom)
    (hdenom : 0 < denom) :
    inRoundingInterval sig exp m q (isIrregular m q) = true := by
  obtain ⟨h_lo, h_hi⟩ := rounded_in_regular_Rv sig exp q m num denom
                          hnum_pos hdenom_pos hm hdenom
  rw [inRoundingInterval_iff]
  rw [fourVL_eq_regular m q exp h_irreg, fourVR_eq, fourU_eq]
  have hreassoc_VL : (4 * (m : Int) - 2) * (twoPosPow q : Int) * (tenNegPow exp : Int)
                       = (4 * (m : Int) - 2) * ((twoPosPow q : Int) * (tenNegPow exp : Int)) :=
    Int.mul_assoc _ _ _
  have hreassoc_VR : (4 * (m : Int) + 2) * (twoPosPow q : Int) * (tenNegPow exp : Int)
                       = (4 * (m : Int) + 2) * ((twoPosPow q : Int) * (tenNegPow exp : Int)) :=
    Int.mul_assoc _ _ _
  have hreassoc_U : 4 * (sig : Int) * (tenPosPow exp : Int) * (twoNegPow q : Int)
                       = 4 * (sig : Int) * ((tenPosPow exp : Int) * (twoNegPow q : Int)) :=
    Int.mul_assoc _ _ _
  rw [hreassoc_VL, hreassoc_VR, hreassoc_U]
  refine ⟨?_, ?_⟩
  · by_cases h_eq : (4 * (m : Int) - 2) * ((twoPosPow q : Int) * (tenNegPow exp : Int))
                      = 4 * (sig : Int) * ((tenPosPow exp : Int) * (twoNegPow q : Int))
    · right
      exact ⟨h_eq, parity_at_tie_lower sig exp q m num denom
                    hnum_pos hdenom_pos hm hdenom h_eq⟩
    · left; omega
  · by_cases h_eq : 4 * (sig : Int) * ((tenPosPow exp : Int) * (twoNegPow q : Int))
                      = (4 * (m : Int) + 2) * ((twoPosPow q : Int) * (tenNegPow exp : Int))
    · right
      exact ⟨h_eq, parity_at_tie_upper sig exp q m num denom
                    hnum_pos hdenom_pos hm hdenom h_eq⟩
    · left; omega

/-! ## Re-exports needed by irregular branches -/

/-- Public re-export of `scaleByPow2_num_clear`. -/
theorem scaleByPow2_num_clear' (a b : Nat) (k : Int) :
    (scaleByPow2 a b k).1 = a * (2 ^ (if k ≥ 0 then k.toNat else 0)) :=
  scaleByPow2_num_clear a b k

/-- Public re-export of `scaleByPow2_denom_clear`. -/
theorem scaleByPow2_denom_clear' (a b : Nat) (k : Int) :
    (scaleByPow2 a b k).2 = b * (2 ^ (if ¬ k ≥ 0 then (-k).toNat else 0)) :=
  scaleByPow2_denom_clear a b k

/-- Public re-export of `scaleByPow2_num_clear_at` with let unfolded. -/
theorem scaleByPow2_num_clear_at' (sig : Nat) (exp : Int) (k q : Int) (hq : q = -k) :
    (if exp ≥ 0 then sig * 10 ^ exp.toNat else sig)
        * (2 ^ (if k ≥ 0 then k.toNat else 0))
      = sig * (tenPosPow exp) * (twoNegPow q) :=
  scaleByPow2_num_clear_at sig exp k q hq

/-- Public re-export of `scaleByPow2_denom_clear_at` with let unfolded. -/
theorem scaleByPow2_denom_clear_at' (_sig : Nat) (exp : Int) (k q : Int) (hq : q = -k) :
    (if exp ≥ 0 then 1 else 10 ^ (-exp).toNat)
        * (2 ^ (if ¬ (k ≥ 0) then (-k).toNat else 0))
      = (tenNegPow exp) * (twoPosPow q) :=
  scaleByPow2_denom_clear_at _sig exp k q hq

/-- Public re-export of `rounded_in_regular_Rv` for the irregular-carry case. -/
theorem rounded_in_regular_Rv'
    (sig : Nat) (exp q : Int) (m : Nat)
    (num denom : Nat)
    (hnum_pos : (num : Int) = sig * (tenPosPow exp) * (twoNegPow q))
    (hdenom_pos : (denom : Int) = (tenNegPow exp) * (twoPosPow q))
    (hm : m = roundNearestEven num denom)
    (hdenom : 0 < denom) :
    (4 * (m : Int) - 2) * ((twoPosPow q : Int) * (tenNegPow exp : Int))
      ≤ 4 * (sig : Int) * ((tenPosPow exp : Int) * (twoNegPow q : Int))
    ∧ 4 * (sig : Int) * ((tenPosPow exp : Int) * (twoNegPow q : Int))
      ≤ (4 * (m : Int) + 2) * ((twoPosPow q : Int) * (tenNegPow exp : Int)) :=
  rounded_in_regular_Rv sig exp q m num denom hnum_pos hdenom_pos hm hdenom

end Srtfp.Clinger

/- Clinger Decimal→Float correctness — irregular no-carry branch (M4).

   Branch 2-irregular: when normal-spaced rounding produces `m = 2^52`
   without a carry, the result `(m, q = e - 52)` lies in the irregular
   range. The lower bound `(4m - 1)·denom ≤ 4·num` follows from the
   `findBinaryExp` lower bound `2^52 · denom ≤ num`; the upper bound is
   the regular `(4m + 2)·denom ≥ 4·num` half-ULP. -/

import Srtfp.Proofs.Clinger.Base
import Srtfp.Proofs.Clinger.Regular
import Srtfp.Proofs.Clinger.FindBinaryExp
import Srtfp.Proofs.Schubfach.Shorter

namespace Srtfp.Clinger

open Srtfp.Float
open Srtfp.Schubfach
open Srtfp

/-! ## Cleared-form setup for the no-carry irregular branch.

To keep elaboration cheap, we localize the cleared-form translation
into a single `(num, denom)` pair at scale `q = e - 52`, avoiding the
nested `unfold tenPosPow twoNegPow` chains that previously caused
multi-minute compile times in this file. -/

/-- Cleared-form identities at `q = e - 52`. -/
private theorem nc_cleared (sig : Nat) (exp e : Int) (a b : Nat)
    (ha_eq : a = sig * tenPosPow exp) (hb_eq : b = tenNegPow exp)
    (hb : 0 < b) :
    let q : Int := e - 52
    let num := (scaleByPow2 a b (52 - e)).1
    let denom := (scaleByPow2 a b (52 - e)).2
    (num : Int) = sig * (tenPosPow exp) * (twoNegPow q) ∧
    (denom : Int) = (tenNegPow exp) * (twoPosPow q) ∧
    0 < denom := by
  simp only
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
  · show ((scaleByPow2 a b (52 - e)).1 : Int) = _
    rw [scaleByPow2_num_clear', h_a]
    have h_at := scaleByPow2_num_clear_at' sig exp (52 - e) (e - 52) hk_eq
    exact_mod_cast h_at
  · show ((scaleByPow2 a b (52 - e)).2 : Int) = _
    rw [scaleByPow2_denom_clear', h_b]
    have h_at := scaleByPow2_denom_clear_at' sig exp (52 - e) (e - 52) hk_eq
    exact_mod_cast h_at

/-! ## Irregular-side strict bound.

Once we have cleared form, the only thing the irregular branch needs
beyond the regular half-ULP bound is the strict lower bound
`(4m - 1) · denom < 4 · num`, which follows from
`m · denom ≤ num` (from findBinaryExp's lower bound at `m = 2^52`)
together with `denom > 0`. -/

private theorem irregular_lower_strict
    (m num denom : Nat) (hbound : (m : Int) * (denom : Int) ≤ (num : Int))
    (hd : 0 < denom) :
    (4 * (m : Int) - 1) * (denom : Int) < 4 * (num : Int) := by
  have hd_int : (0 : Int) < (denom : Int) := by exact_mod_cast hd
  have h_lhs : (4 * (m : Int) - 1) * (denom : Int)
                = 4 * (m : Int) * (denom : Int) - (denom : Int) := by
    rw [Int.sub_mul, Int.one_mul]
  have h4mn : 4 * (m : Int) * (denom : Int) ≤ 4 * (num : Int) := by
    have h := Int.mul_le_mul_of_nonneg_left hbound (by decide : (0 : Int) ≤ 4)
    have hassoc : 4 * ((m : Int) * (denom : Int)) = 4 * (m : Int) * (denom : Int) :=
      (Int.mul_assoc _ _ _).symm
    omega
  rw [h_lhs]; omega

/-- **Branch 2-irregular** (no-carry with `m_round = 2^52`).

Given that `m = roundNearestEven num denom = 2^52` where `(num, denom)`
came from `scaleByPow2 a b (52 - e)` with `e = findBinaryExp a b`, the
irregular rounding-interval bound holds at `(m, q = e - 52)`. -/
theorem irregular_no_carry_correct
    (sig : Nat) (exp e : Int) (a b : Nat)
    (ha_eq : a = sig * tenPosPow exp) (hb_eq : b = tenNegPow exp)
    (ha : 0 < a) (hb : 0 < b) (he_eq : e = findBinaryExp a b)
    (hm_eq : (2 ^ 52 : Nat) = roundNearestEven (scaleByPow2 a b (52 - e)).1
                                                 (scaleByPow2 a b (52 - e)).2) :
    inRoundingInterval sig exp (2 ^ 52) (e - 52)
        (isIrregular (2 ^ 52) (e - 52)) = true := by
  -- Cleared form (lifts num, denom, q).
  obtain ⟨hnum_int, hdenom_int, hdenom_pos⟩ := nc_cleared sig exp e a b ha_eq hb_eq hb
  -- For brevity below we use the unabbreviated forms.
  by_cases h_irreg : isIrregular (2 ^ 52) (e - 52) = true
  · -- Irregular case.
    have h_leBy2e : leBy2e a b e = true := he_eq ▸ findBinaryExp_le a b ha hb
    have hbound_nat : 2 ^ 52 * (scaleByPow2 a b (52 - e)).2
                        ≤ (scaleByPow2 a b (52 - e)).1 :=
      clinger_num_ge_2pow52_denom a b e ha hb h_leBy2e
    rw [inRoundingInterval_iff,
        fourVL_eq_irregular (2 ^ 52) (e - 52) exp h_irreg,
        fourVR_eq, fourU_eq]
    -- Reassociate.
    have hreVL : (4 * ((2 ^ 52 : Nat) : Int) - 1) * (twoPosPow (e - 52) : Int)
                    * (tenNegPow exp : Int)
                  = (4 * ((2 ^ 52 : Nat) : Int) - 1)
                    * ((twoPosPow (e - 52) : Int) * (tenNegPow exp : Int)) :=
      Int.mul_assoc _ _ _
    have hreVR : (4 * ((2 ^ 52 : Nat) : Int) + 2) * (twoPosPow (e - 52) : Int)
                    * (tenNegPow exp : Int)
                  = (4 * ((2 ^ 52 : Nat) : Int) + 2)
                    * ((twoPosPow (e - 52) : Int) * (tenNegPow exp : Int)) :=
      Int.mul_assoc _ _ _
    have hreU : 4 * (sig : Int) * (tenPosPow exp : Int) * (twoNegPow (e - 52) : Int)
                  = 4 * (sig : Int)
                    * ((tenPosPow exp : Int) * (twoNegPow (e - 52) : Int)) :=
      Int.mul_assoc _ _ _
    rw [hreVL, hreVR, hreU]
    have hPdenom : (twoPosPow (e - 52) : Int) * (tenNegPow exp : Int)
                  = ((scaleByPow2 a b (52 - e)).2 : Int) := by
      rw [hdenom_int]; exact Int.mul_comm _ _
    have hQnum : 4 * (sig : Int) * ((tenPosPow exp : Int) * (twoNegPow (e - 52) : Int))
                  = 4 * ((scaleByPow2 a b (52 - e)).1 : Int) := by
      rw [hnum_int]
      rw [Int.mul_assoc (sig : Int) (tenPosPow exp : Int) (twoNegPow (e - 52) : Int)]
      rw [← Int.mul_assoc (4 : Int) (sig : Int)
           ((tenPosPow exp : Int) * (twoNegPow (e - 52) : Int))]
    rw [hPdenom, hQnum]
    -- Upper bound from rounded_in_regular_Rv'.
    have hm_eq' : (2 ^ 52 : Nat) = roundNearestEven (scaleByPow2 a b (52 - e)).1
                                                     (scaleByPow2 a b (52 - e)).2 := hm_eq
    obtain ⟨_h_lo_reg, h_hi_reg⟩ :=
      rounded_in_regular_Rv' sig exp (e - 52) (2 ^ 52)
        (scaleByPow2 a b (52 - e)).1 (scaleByPow2 a b (52 - e)).2
        hnum_int hdenom_int hm_eq' hdenom_pos
    rw [hPdenom, hQnum] at h_hi_reg
    -- Final cleared-form bound from m·denom ≤ num.
    have hbound : ((2 ^ 52 : Nat) : Int) * ((scaleByPow2 a b (52 - e)).2 : Int)
                    ≤ ((scaleByPow2 a b (52 - e)).1 : Int) := by
      exact_mod_cast hbound_nat
    refine ⟨?_, ?_⟩
    · left
      exact irregular_lower_strict (2 ^ 52) _ _ hbound hdenom_pos
    · -- h_hi_reg : 4·num ≤ (4·2^52+2)·denom. Either strict (left) or eq + parity (right).
      rcases Int.lt_or_eq_of_le h_hi_reg with h_lt | h_eq
      · left; exact h_lt
      · right
        exact ⟨h_eq, by decide⟩
  · -- Regular case: directly apply regular_branch_correct.
    exact regular_branch_correct sig exp (2 ^ 52) (e - 52)
            (scaleByPow2 a b (52 - e)).1 (scaleByPow2 a b (52 - e)).2
            h_irreg hnum_int hdenom_int hm_eq hdenom_pos

end Srtfp.Clinger

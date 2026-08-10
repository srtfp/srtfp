/- Clinger Decimal→Float correctness — main file (M4).

   ## What this file establishes

   This file is the top-level entry point for M4 (Clinger
   correctly-rounded `Decimal → Float`). It re-exports the per-branch
   correctness machinery from the `Clinger/` sub-modules, assembles the
   abstract correctness theorem, and provides the unconditional
   headline theorem `ofDecimal_in_Rv` (via the runtime axiom
   `Float.toBits_ofBits`).

   ## Layering

   * **`Clinger/Base.lean`** — `roundNearestEven`/`findBinaryExp`/
     `scaleByPow2` shape lemmas, the abstract decode `decodedAbs`,
     `DecodeOfDecimalBridge`.
   * **`Clinger/Regular.lean`** — cleared-form scaling, parity at tie,
     `regular_branch_correct`.
   * **`Clinger/FindBinaryExp.lean`** — `findBinaryExp` lower/upper
     bounds, `clinger_num_ge_2pow52_denom`,
     `clinger_num_lt_2pow53_denom`, `num_pre_denom_eq`.
   * **`Clinger/IrregularNoCarry.lean`** — `irregular_no_carry_correct`.
   * **`Clinger/IrregularCarry.lean`** — `irregular_carry_correct`.
   * **`Clinger/Bridge.lean`** — `decodeOfDecimalBridge_thm` (uses
     `Float.toBits_ofBits` axiom).

   This file assembles the dispatch and the unconditional headline. -/

import Srtfp.Proofs.Clinger.Base
import Srtfp.Proofs.Clinger.Regular
import Srtfp.Proofs.Clinger.FindBinaryExp
import Srtfp.Proofs.Clinger.IrregularNoCarry
import Srtfp.Proofs.Clinger.IrregularCarry
import Srtfp.Proofs.Clinger.Dispatch
import Srtfp.Proofs.Clinger.Bridge
import Srtfp.Float.RuntimeAxiom
import Srtfp.Proofs.Schubfach.Shorter
import Srtfp.Proofs.Schubfach.ToDecimal

namespace Srtfp.Clinger

open Srtfp.Float
open Srtfp.Schubfach
open Srtfp

/-! ## Setup lemmas for the dispatch -/

/-- Cleared-form identity for the input `(a, b)` pair after the
`if exp ≥ 0` split. -/
private theorem ab_int (sig : Nat) (exp : Int) (h_sig : sig ≠ 0) :
    let a : Nat := if exp ≥ 0 then sig * 10 ^ exp.toNat else sig
    let b : Nat := if exp ≥ 0 then 1 else 10 ^ (-exp).toNat
    a = sig * tenPosPow exp ∧ b = tenNegPow exp ∧ 0 < a ∧ 0 < b := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show (if exp ≥ 0 then sig * 10 ^ exp.toNat else sig) = sig * tenPosPow exp
    by_cases hexp : 0 ≤ exp
    · rw [if_pos hexp, tenPosPow_nonneg hexp]
    · have hexp' : exp < 0 := Int.not_le.mp hexp
      rw [if_neg hexp, tenPosPow_neg hexp', Nat.mul_one]
  · show (if exp ≥ 0 then 1 else 10 ^ (-exp).toNat) = tenNegPow exp
    by_cases hexp : 0 ≤ exp
    · rw [if_pos hexp, tenNegPow_nonneg hexp]
    · have hexp' : exp < 0 := Int.not_le.mp hexp
      rw [if_neg hexp, tenNegPow_neg hexp']
  · show 0 < (if exp ≥ 0 then sig * 10 ^ exp.toNat else sig)
    by_cases hexp : 0 ≤ exp
    · rw [if_pos hexp]
      exact Nat.mul_pos (Nat.pos_of_ne_zero h_sig)
                        (Nat.pow_pos (by decide : 0 < (10 : Nat)))
    · rw [if_neg hexp]; exact Nat.pos_of_ne_zero h_sig
  · show 0 < (if exp ≥ 0 then 1 else 10 ^ (-exp).toNat)
    by_cases hexp : 0 ≤ exp
    · rw [if_pos hexp]; decide
    · rw [if_neg hexp]; exact Nat.pow_pos (by decide : 0 < (10 : Nat))

/-- For the regular subnormal branch, the cleared-form identities at
`q = -1074` and the scale `k = 1074`. -/
private theorem subnormal_cleared
    (sig : Nat) (exp : Int) (a b : Nat)
    (ha_eq : a = sig * tenPosPow exp) (hb_eq : b = tenNegPow exp)
    (hb : 0 < b) :
    let q : Int := -1074
    ((scaleByPow2 a b 1074).1 : Int) = sig * (tenPosPow exp) * (twoNegPow q) ∧
    ((scaleByPow2 a b 1074).2 : Int) = (tenNegPow exp) * (twoPosPow q) ∧
    0 < (scaleByPow2 a b 1074).2 := by
  show ((scaleByPow2 a b 1074).1 : Int) = _ ∧ _ ∧ _
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
  have hk_eq : ((-1074 : Int)) = -1074 := rfl
  have hk_eq' : ((-1074 : Int)) = -(1074 : Int) := by omega
  refine ⟨?_, ?_, scaleByPow2_denom_pos hb⟩
  · rw [scaleByPow2_num_clear', h_a]
    have h_at := scaleByPow2_num_clear_at' sig exp 1074 (-1074) hk_eq'
    have h_cast : (((if exp ≥ 0 then sig * 10 ^ exp.toNat else sig)
            * (2 ^ (if (1074 : Int) ≥ 0 then (1074 : Int).toNat else 0)) : Nat) : Int)
         = ((sig * (tenPosPow exp) * (twoNegPow (-1074)) : Nat) : Int) := by
      congr 1
    exact h_cast
  · rw [scaleByPow2_denom_clear', h_b]
    have h_at := scaleByPow2_denom_clear_at' sig exp 1074 (-1074) hk_eq'
    have h_cast : (((if exp ≥ 0 then 1 else 10 ^ (-exp).toNat)
            * (2 ^ (if ¬ ((1074 : Int) ≥ 0) then (-(1074 : Int)).toNat else 0)) : Nat) : Int)
         = ((tenNegPow exp * twoPosPow (-1074) : Nat) : Int) := by
      congr 1
    exact h_cast

/-- For the normal-spaced branch, cleared-form identities at `q = e - 52`. -/
private theorem normal_cleared
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
    have h_cast : (((if exp ≥ 0 then sig * 10 ^ exp.toNat else sig)
            * (2 ^ (if (52 - e : Int) ≥ 0 then (52 - e).toNat else 0)) : Nat) : Int)
         = ((sig * (tenPosPow exp) * (twoNegPow (e - 52)) : Nat) : Int) := by
      congr 1
    exact h_cast
  · rw [scaleByPow2_denom_clear', h_b]
    have h_at := scaleByPow2_denom_clear_at' sig exp (52 - e) (e - 52) hk_eq
    have h_cast : (((if exp ≥ 0 then 1 else 10 ^ (-exp).toNat)
            * (2 ^ (if ¬ ((52 - e : Int) ≥ 0) then (-(52 - e)).toNat else 0)) : Nat) : Int)
         = ((tenNegPow exp * twoPosPow (e - 52) : Nat) : Int) := by
      congr 1
    exact h_cast

/-! ## Headline correctness theorem -/

/-- **Headline correctness theorem.** For a non-overflow nonzero
`Decimal d`, `Clinger.ofDecimal d` decodes to a Float in the rounding
interval of `d = d.significand · 10^d.exponent`.

The bridge from `decode (ofDecimal d)` to the abstract `decodedAbs`
uses `Float.toBits_ofBits` (and a single derived `fromBits_proj` axiom)
to project bit fields through the IEEE-754 runtime intrinsics. The
abstract correctness reduces to the case-split dispatch on
`decodedAbs`'s if-tree. Both are now proven; this theorem is
unconditional. -/
theorem ofDecimal_in_Rv
    (d : Decimal)
    (h_nonzero : d.significand ≠ 0)
    (h_finite : IsFiniteAbs d.sign d.significand d.exponent) :
    let f := ofDecimal d
    let decoded := decode f
    inRoundingInterval d.significand d.exponent
        decoded.m decoded.q (isIrregular decoded.m decoded.q) = true := by
  simp only
  rw [decode_of_decimal_bridge d h_finite]
  exact (abstract_correctness_of_dispatch branch_dispatch)
          d.sign d.significand d.exponent h_nonzero h_finite

end Srtfp.Clinger

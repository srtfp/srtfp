/- Disjointness of `inRoundingInterval` for distinct IEEE-754 canonical pairs.

   ## Statement

   For canonical IEEE-754 binary64 pairs `(m₁, q₁)` and `(m₂, q₂)` (i.e.
   what `decode` produces for finite floats), if a decimal value
   `sig · 10^exp` lies in the rounding interval of both, then the pairs
   are equal: `m₁ = m₂ ∧ q₁ = q₂`.

   ## Why this works

   Two canonical IEEE-754 floats `f₁`, `f₂` either coincide (then trivially
   equal pairs) or are distinct (in which case their rounding intervals
   are disjoint as half-open intervals — they share endpoints but
   tie-breaking via `cEven` resolves to exactly one side).

   ## Approach

   We work entirely in the cleared-denominator form. The argument
   reduces to integer arithmetic over `(4m ± offset) · 2^q · 10^(-exp)`
   compared to `4·sig · 10^exp · 2^(-q)`.

   ## Current status

   The main disjointness theorem `inRoundingInterval_uniq` is stated
   here but its proof is deferred (TODO). The proof requires a careful
   case-analysis on the relative values `m₁·2^q₁` vs `m₂·2^q₂` and the
   structure of the IEEE-754 canonical encoding. -/

import Srtfp.Proofs.Schubfach.Shorter
import Srtfp.Proofs.Schubfach.PickNearer
import Srtfp.Proofs.Schubfach.RoundingInterval
import Srtfp.Proofs.Schubfach.ToDecimal
import Srtfp.Proofs.Clinger

namespace Srtfp

open Srtfp.Schubfach
open Srtfp.Float

/-! ## Legal IEEE-754 canonical pair predicate -/

/-- A canonical IEEE-754 binary64 pair `(m, q)`, with `m > 0`. Subnormal:
    `1 ≤ m < 2^52` and `q = -1074`. Normal: `2^52 ≤ m < 2^53` and
    `q ∈ [-1074, 971]`. -/
def LegalIEEE (m : Nat) (q : Int) : Prop :=
  (1 ≤ m ∧ m < 2^52 ∧ q = -1074) ∨ (2^52 ≤ m ∧ m < 2^53 ∧ -1074 ≤ q ∧ q ≤ 971)

instance (m : Nat) (q : Int) : Decidable (LegalIEEE m q) := by
  unfold LegalIEEE; exact inferInstance

/-- For a finite Float with nonzero magnitude, `decode` produces a LegalIEEE pair. -/
theorem decode_legalIEEE (f : _root_.Float)
    (h_fin : isFiniteBits f = true) (h_nonzero : (decode f).m ≠ 0) :
    LegalIEEE (decode f).m (decode f).q := by
  have hfin_lt : biasedExpBits f < 2047 := by
    unfold isFiniteBits at h_fin; simpa using h_fin
  have hmb : mantissaBits f < 2 ^ 52 := by
    unfold mantissaBits
    rw [UInt64.toNat_and]
    have hmask : ((0x000F_FFFF_FFFF_FFFF : UInt64).toNat) = 4503599627370495 := by decide
    rw [hmask]
    have hle : f.toBits.toNat &&& 4503599627370495 ≤ 4503599627370495 := Nat.and_le_right
    have hpow : (2 : Nat) ^ 52 = 4503599627370496 := by decide
    omega
  unfold LegalIEEE
  by_cases he : biasedExpBits f = 0
  · -- Subnormal: m = mantissaBits, q = -1074.
    have hm : (decode f).m = mantissaBits f := by unfold decode; rw [if_pos he]
    have hq : (decode f).q = -1074 := by unfold decode; rw [if_pos he]
    left
    refine ⟨?_, ?_, hq⟩
    · have hmb_ne : mantissaBits f ≠ 0 := by rw [hm] at h_nonzero; exact h_nonzero
      rw [hm]; omega
    · rw [hm]; exact hmb
  · -- Normal: m = mantissaBits + 2^52, q = (biasedExp : Int) - 1023 - 52.
    have hm : (decode f).m = mantissaBits f + (1 <<< 52) := by unfold decode; rw [if_neg he]
    have hq : (decode f).q = (biasedExpBits f : Int) - 1023 - 52 := by
      unfold decode; rw [if_neg he]
    right
    have h_be_pos : 1 ≤ biasedExpBits f := by omega
    have h_be_le : biasedExpBits f ≤ 2046 := by omega
    have h_shl : (1 : Nat) <<< 52 = 2 ^ 52 := by decide
    have h53 : (2 : Nat) ^ 53 = 2 * 2 ^ 52 := by decide
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hm, h_shl]; omega
    · rw [hm, h_shl, h53]; omega
    · rw [hq]
      have : (1 : Int) ≤ (biasedExpBits f : Int) := by exact_mod_cast h_be_pos
      omega
    · rw [hq]
      have : (biasedExpBits f : Int) ≤ 2046 := by exact_mod_cast h_be_le
      omega

/-! ## Canonicalization-invariance of `inRoundingInterval` (deferred)

`inRoundingInterval sig exp m q irreg` only depends on the real value
`sig · 10^exp`. Hence multiplying `sig` by 10 and decrementing `exp`
preserves the truth.

This sub-lemma is intuitively clear (both compare the same rational to
the same interval) but the formal proof in cleared-denominator form
requires case-splits on the signs of `exp` and `q`. -/

/-- Helper: `cmpScaledMixed a q (4·(10·s)) (exp-1) = cmpScaledMixed a q (4·s) exp`.
    Both compare the same rational `a · 2^q` to the same rational `4·s · 10^exp`. -/
private theorem cmpScaledMixed_scale10
    (a : Int) (q : Int) (s : Nat) (exp : Int) :
    cmpScaledMixed a q (4 * (10 * (s : Int))) (exp - 1)
      = cmpScaledMixed a q (4 * (s : Int)) exp := by
  -- Establish positivity factors.
  have h10 : (0 : Int) < 10 := by decide
  -- Unfold cmpScaledMixed into cleared form and case-split on exp's sign.
  unfold cmpScaledMixed
  -- We name the integer-pow expressions and case-analyze.
  set qP : Nat := if q ≥ 0 then q.toNat else 0
  set qN : Nat := if q < 0 then (-q).toNat else 0
  -- Old kP = if exp ≥ 0 then exp.toNat else 0; old kN = if exp < 0 then (-exp).toNat else 0.
  -- New kP = if exp-1 ≥ 0 then (exp-1).toNat else 0; new kN = similar.
  by_cases h_exp_ge1 : exp ≥ 1
  · -- exp ≥ 1: both Old and New have positive `exp` part. Old kP = exp.toNat, New kP = (exp-1).toNat.
    -- Both kN = 0.
    have h_exp_ge : exp ≥ 0 := by omega
    have h_exp_new_ge : exp - 1 ≥ 0 := by omega
    have h_exp_not_lt : ¬ (exp < 0) := by omega
    have h_exp_new_not_lt : ¬ (exp - 1 < 0) := by omega
    have h_eN_toN : (exp - 1).toNat = exp.toNat - 1 := by omega
    have h_eN_pos : exp.toNat ≥ 1 := by
      have h1 : (0 : Int) < exp := by omega
      omega
    simp only [h_exp_ge, h_exp_new_ge, h_exp_not_lt, h_exp_new_not_lt, if_true, if_false]
    -- Now goal compares (LHS_new vs RHS_new) with (LHS_old vs RHS_old) where:
    -- LHS_new = a · 2^qP · 10^0 = a · 2^qP.
    -- RHS_new = (4·(10·s)) · 10^(exp-1).toNat · 2^qN.
    -- LHS_old = a · 2^qP · 10^0 = a · 2^qP. (Same as LHS_new.)
    -- RHS_old = (4·s) · 10^exp.toNat · 2^qN.
    -- 40 · 10^(exp.toNat - 1) = 4 · 10^exp.toNat, so RHS_new = RHS_old.
    have h_RHS_eq : (4 * (10 * (s : Int))) * ((10 : Int) ^ (exp - 1).toNat) * (2 ^ qN : Int)
                  = (4 * (s : Int)) * ((10 : Int) ^ exp.toNat) * (2 ^ qN : Int) := by
      rw [h_eN_toN]
      have hexp_eq : exp.toNat = (exp.toNat - 1) + 1 := by omega
      conv_rhs => rw [hexp_eq, pow_succ]
      ring
    rw [h_RHS_eq]
  · -- exp ≤ 0.
    have h_exp_le0 : exp ≤ 0 := by omega
    by_cases h_exp_zero : exp = 0
    · subst h_exp_zero
      -- exp = 0: kP_old = 0, kN_old = 0. exp - 1 = -1: kP_new = 0, kN_new = 1.
      -- After simp [exp = 0], the new exp is `0 - 1 = -1`.
      -- The proof structure: use the fact that (0-1).toNat = 0 (since 0-1 < 0)
      -- and (-(0-1)).toNat = 1.
      have h_old_ge : (0 : Int) ≥ 0 := by decide
      have h_old_nlt : ¬ ((0 : Int) < 0) := by decide
      have h_new_nge : ¬ ((0 : Int) - 1 ≥ 0) := by decide
      have h_new_lt : (0 : Int) - 1 < 0 := by decide
      have h_pow_zero1 : ((10 : Int) ^ ((-0 : Int).toNat)) = 1 := by decide
      have h_pow_zero2 : ((10 : Int) ^ ((0 : Int).toNat)) = 1 := by decide
      have h_pow_zero3 : ((10 : Int) ^ ((0 - 1 : Int).toNat)) = 1 := by decide
      have h_pow_ten : ((10 : Int) ^ ((-(0 - 1 : Int)).toNat)) = 10 := by decide
      simp only [h_old_ge, h_old_nlt, h_new_nge, h_new_lt, if_true, if_false,
                 h_pow_zero2, h_pow_ten]
      -- Goal now: (if (a · 2^qP) · 10 < (4 · (10 · s)) · 1 · 2^qN then -1 ...)
      --          = (if (a · 2^qP) · 1 < (4 · s) · 1 · 2^qN then -1 ...)
      -- LHS_new = 10 · (a · 2^qP), RHS_new = 40 · s · 2^qN = 10 · (4 · s · 2^qN). Same factor.
      -- Use the int comparison invariance.
      by_cases hlt : a * (2 ^ qP : Int) < (4 * (s : Int)) * (2 ^ qN : Int)
      · have h10lt : a * (2 ^ qP : Int) * 10 < (4 * (10 * (s : Int))) * (2 ^ qN : Int) := by
          have hX_eq : a * (2 ^ qP : Int) * 10 = 10 * (a * (2 ^ qP : Int)) := by ring
          have hY_eq : (4 * (10 * (s : Int))) * (2 ^ qN : Int)
                     = 10 * ((4 * (s : Int)) * (2 ^ qN : Int)) := by ring
          rw [hX_eq, hY_eq]
          exact Int.mul_lt_mul_of_pos_left hlt h10
        simp [hlt, h10lt]
      · by_cases heq : a * (2 ^ qP : Int) = (4 * (s : Int)) * (2 ^ qN : Int)
        · have h10eq : a * (2 ^ qP : Int) * 10 = (4 * (10 * (s : Int))) * (2 ^ qN : Int) := by
            have hX_eq : a * (2 ^ qP : Int) * 10 = 10 * (a * (2 ^ qP : Int)) := by ring
            have hY_eq : (4 * (10 * (s : Int))) * (2 ^ qN : Int)
                       = 10 * ((4 * (s : Int)) * (2 ^ qN : Int)) := by ring
            rw [hX_eq, hY_eq, heq]
          have h_no_lt : ¬ (4 * (s : Int) * (2 ^ qN : Int) * 10 < (4 * (10 * (s : Int))) * (2 ^ qN : Int)) := by
            linarith
          have h_eq : 4 * (s : Int) * (2 ^ qN : Int) * 10 = (4 * (10 * (s : Int))) * (2 ^ qN : Int) := by
            linarith
          simp [h_eq, heq]
        · have hgt : a * (2 ^ qP : Int) > (4 * (s : Int)) * (2 ^ qN : Int) := by omega
          have h10gt : a * (2 ^ qP : Int) * 10 > (4 * (10 * (s : Int))) * (2 ^ qN : Int) := by
            have hX_eq : a * (2 ^ qP : Int) * 10 = 10 * (a * (2 ^ qP : Int)) := by ring
            have hY_eq : (4 * (10 * (s : Int))) * (2 ^ qN : Int)
                       = 10 * ((4 * (s : Int)) * (2 ^ qN : Int)) := by ring
            rw [hX_eq, hY_eq]
            exact Int.mul_lt_mul_of_pos_left hgt h10
          have h10nlt : ¬ a * (2 ^ qP : Int) * 10 < (4 * (10 * (s : Int))) * (2 ^ qN : Int) := by
            omega
          have h10neq : ¬ a * (2 ^ qP : Int) * 10 = (4 * (10 * (s : Int))) * (2 ^ qN : Int) := by
            omega
          simp [hlt, heq, h10nlt, h10neq]
    · -- exp < 0.
      have h_exp_neg : exp < 0 := by omega
      have h_exp_new_neg : exp - 1 < 0 := by omega
      have h_exp_not_ge : ¬ (exp ≥ 0) := by omega
      have h_exp_new_not_ge : ¬ (exp - 1 ≥ 0) := by omega
      have h_pow_new_pos : ((10 : Int) ^ ((exp - 1).toNat)) = 1 := by
        have : (exp - 1).toNat = 0 := by omega
        rw [this, pow_zero]
      have h_pow_old_pos : ((10 : Int) ^ (exp.toNat)) = 1 := by
        have : exp.toNat = 0 := by omega
        rw [this, pow_zero]
      have h_toN_new : (-(exp - 1)).toNat = (-exp).toNat + 1 := by
        have h1 : (-(exp - 1) : Int) = -exp + 1 := by ring
        rw [h1]
        have h2 : (-exp : Int) ≥ 1 := by omega
        omega
      have h_pow_lhs_new : ((10 : Int) ^ ((-(exp - 1)).toNat))
                         = 10 * ((10 : Int) ^ ((-exp).toNat)) := by
        rw [h_toN_new, pow_succ]; ring
      simp only [h_exp_neg, h_exp_new_neg, h_exp_not_ge, h_exp_new_not_ge,
                 if_true, if_false, h_pow_lhs_new]
      -- Goal should now have factors of 10 visible.
      -- LHS_new = a · 2^qP · (10 · 10^(-exp).toNat) = 10 · (a · 2^qP · 10^(-exp).toNat).
      -- RHS_new = (4·10·s) · 1 · 2^qN = 10 · (4 · s · 2^qN).
      -- LHS_old = a · 2^qP · 10^(-exp).toNat.
      -- RHS_old = (4 · s) · 1 · 2^qN.
      by_cases hlt : a * (2 ^ qP : Int) * ((10 : Int) ^ ((-exp).toNat))
                      < (4 * (s : Int)) * (2 ^ qN : Int)
      · have h10lt : a * (2 ^ qP : Int) * (10 * ((10 : Int) ^ ((-exp).toNat)))
                    < (4 * (10 * (s : Int))) * (2 ^ qN : Int) := by
          have hX_eq : a * (2 ^ qP : Int) * (10 * ((10 : Int) ^ ((-exp).toNat)))
                     = 10 * (a * (2 ^ qP : Int) * ((10 : Int) ^ ((-exp).toNat))) := by ring
          have hY_eq : (4 * (10 * (s : Int))) * (2 ^ qN : Int)
                     = 10 * ((4 * (s : Int)) * (2 ^ qN : Int)) := by ring
          rw [hX_eq, hY_eq]
          exact Int.mul_lt_mul_of_pos_left hlt h10
        simp [hlt, h10lt]
      · by_cases heq : a * (2 ^ qP : Int) * ((10 : Int) ^ ((-exp).toNat))
                        = (4 * (s : Int)) * (2 ^ qN : Int)
        · have h10eq : a * (2 ^ qP : Int) * (10 * ((10 : Int) ^ ((-exp).toNat)))
                     = (4 * (10 * (s : Int))) * (2 ^ qN : Int) := by
            have hX_eq : a * (2 ^ qP : Int) * (10 * ((10 : Int) ^ ((-exp).toNat)))
                       = 10 * (a * (2 ^ qP : Int) * ((10 : Int) ^ ((-exp).toNat))) := by ring
            have hY_eq : (4 * (10 * (s : Int))) * (2 ^ qN : Int)
                       = 10 * ((4 * (s : Int)) * (2 ^ qN : Int)) := by ring
            rw [hX_eq, hY_eq, heq]
          simp [heq, h10eq]
        · have hgt : a * (2 ^ qP : Int) * ((10 : Int) ^ ((-exp).toNat))
                      > (4 * (s : Int)) * (2 ^ qN : Int) := by omega
          have h10gt : a * (2 ^ qP : Int) * (10 * ((10 : Int) ^ ((-exp).toNat)))
                       > (4 * (10 * (s : Int))) * (2 ^ qN : Int) := by
            have hX_eq : a * (2 ^ qP : Int) * (10 * ((10 : Int) ^ ((-exp).toNat)))
                       = 10 * (a * (2 ^ qP : Int) * ((10 : Int) ^ ((-exp).toNat))) := by ring
            have hY_eq : (4 * (10 * (s : Int))) * (2 ^ qN : Int)
                       = 10 * ((4 * (s : Int)) * (2 ^ qN : Int)) := by ring
            rw [hX_eq, hY_eq]
            exact Int.mul_lt_mul_of_pos_left hgt h10
          have h10nlt : ¬ a * (2 ^ qP : Int) * (10 * ((10 : Int) ^ ((-exp).toNat)))
                        < (4 * (10 * (s : Int))) * (2 ^ qN : Int) := by omega
          have h10neq : ¬ a * (2 ^ qP : Int) * (10 * ((10 : Int) ^ ((-exp).toNat)))
                         = (4 * (10 * (s : Int))) * (2 ^ qN : Int) := by omega
          simp [hlt, heq, h10nlt, h10neq]

/-- `inRoundingInterval (10·sig) (exp - 1) m q irreg = inRoundingInterval sig exp m q irreg`. -/
theorem inRoundingInterval_scale10 (sig : Nat) (exp : Int) (m : Nat) (q : Int) (irreg : Bool) :
    inRoundingInterval (10 * sig) (exp - 1) m q irreg
      = inRoundingInterval sig exp m q irreg := by
  unfold inRoundingInterval
  have hcast : ((10 * sig : Nat) : Int) = 10 * (sig : Int) := by push_cast; ring
  have hL := cmpScaledMixed_scale10
    (if irreg then 4 * (m : Int) - 1 else 4 * (m : Int) - 2) q sig exp
  have hR := cmpScaledMixed_scale10 (4 * (m : Int) + 2) q sig exp
  simp only [hcast, hL, hR]

/-- Generalization: scaling `sig` by `10^k` and decrementing `exp` by `k`. -/
theorem inRoundingInterval_scale10_pow (sig : Nat) (exp : Int) (m : Nat) (q : Int)
    (irreg : Bool) (k : Nat) :
    inRoundingInterval (sig * 10^k) (exp - k) m q irreg
      = inRoundingInterval sig exp m q irreg := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hrw : sig * 10 ^ (k + 1) = 10 * (sig * 10 ^ k) := by ring
    have hexp : exp - (k + 1 : Nat) = exp - k - 1 := by push_cast; ring
    rw [hrw, hexp, inRoundingInterval_scale10, ih]

/-! ## Bracketing of `4·sig·10^exp` from `inRoundingInterval`

The two cleared-form endpoint comparisons give us a *closed integer
interval* containing `4·sig·tenPosPow exp · twoNegPow q`. We package
this as a single lemma. -/

/-- `inRoundingInterval` bracket: the cleared `4·u` lies in
`[4·v_ℓ_cleared, 4·v_R_cleared]` (with strict inequality unless `m`
is even). -/
private theorem inRoundingInterval_bracket
    (sig : Nat) (exp : Int) (m : Nat) (q : Int)
    (h_rv : inRoundingInterval sig exp m q (isIrregular m q) = true) :
    fourVL m q exp (isIrregular m q) ≤ fourU sig q exp ∧
    fourU sig q exp ≤ fourVR m q exp := by
  rw [inRoundingInterval_iff] at h_rv
  obtain ⟨hleft, hright⟩ := h_rv
  refine ⟨?_, ?_⟩
  · rcases hleft with hlt | ⟨heq, _⟩
    · exact Int.le_of_lt hlt
    · exact Int.le_of_eq heq
  · rcases hright with hlt | ⟨heq, _⟩
    · exact Int.le_of_lt hlt
    · exact Int.le_of_eq heq

/-! ## Canonicity of LegalIEEE encoding

For LegalIEEE pairs, the value `m·2^q` determines `(m, q)` uniquely.
The argument: the value lies in `[2^(q+log2 m), 2^(q+log2 m + 1))`, and
log2 of the value determines `q + log2 m`. Combined with the LegalIEEE
constraint `m ∈ [2^52, 2^53)` (normal) or `q = -1074` (subnormal), the
pair is recovered. -/

/-- Two LegalIEEE pairs with the same real value `m·2^q` are equal. -/
private theorem legalIEEE_unique
    (m₁ m₂ : Nat) (q₁ q₂ : Int)
    (h₁ : LegalIEEE m₁ q₁) (h₂ : LegalIEEE m₂ q₂)
    (h_val : (m₁ : Int) * (2 : Int) ^ (q₁ - (-1074)).toNat
             = (m₂ : Int) * (2 : Int) ^ (q₂ - (-1074)).toNat) :
    m₁ = m₂ ∧ q₁ = q₂ := by
  -- The "common scale" is `2^-1074`. So `m_i · 2^q_i = m_i · 2^(q_i+1074) · 2^(-1074)`.
  -- The integer values `m_i · 2^(q_i + 1074)` must coincide.
  rcases h₁ with ⟨hm1_pos, hm1_lt, hq1⟩ | ⟨hm1_ge, hm1_lt, hq1_lo, hq1_hi⟩
  · -- Case: m₁ subnormal (q₁ = -1074)
    subst hq1
    have hk1 : ((-1074 : Int) - (-1074)).toNat = 0 := by decide
    rw [hk1, pow_zero, Int.mul_one] at h_val
    rcases h₂ with ⟨hm2_pos, hm2_lt, hq2⟩ | ⟨hm2_ge, hm2_lt, hq2_lo, hq2_hi⟩
    · -- (sub, sub): q₂ = -1074 too; m₁ = m₂.
      subst hq2
      rw [hk1, pow_zero, Int.mul_one] at h_val
      have hm_eq : m₁ = m₂ := by exact_mod_cast h_val
      exact ⟨hm_eq, rfl⟩
    · -- (sub, norm): m₁ < 2^52 ≤ m₂. m₁ · 1 = m₂ · 2^(q₂+1074). RHS ≥ 2^52, LHS < 2^52. ⊥
      exfalso
      have hk2 : ((q₂ - (-1074)).toNat : Int) = q₂ + 1074 := by
        have := Int.toNat_of_nonneg (a := q₂ - -1074) (by omega)
        omega
      have hpow_pos : (0 : Int) ≤ (2 : Int) ^ (q₂ - (-1074)).toNat := by positivity
      have h_rhs_ge : (m₂ : Int) * (2 : Int) ^ (q₂ - (-1074)).toNat ≥ ((2^52 : Nat) : Int) := by
        have : ((2^52 : Nat) : Int) ≤ (m₂ : Int) := by exact_mod_cast hm2_ge
        have h_pp : (1 : Int) ≤ (2 : Int) ^ (q₂ - (-1074)).toNat := by
          have : (1 : Int) = (2 : Int) ^ 0 := by decide
          rw [this]; exact pow_le_pow_right₀ (by decide) (Nat.zero_le _)
        nlinarith
      have h_lhs_lt : (m₁ : Int) < ((2^52 : Nat) : Int) := by exact_mod_cast hm1_lt
      omega
  · -- Case: m₁ normal
    rcases h₂ with ⟨hm2_pos, hm2_lt, hq2⟩ | ⟨hm2_ge, hm2_lt, hq2_lo, hq2_hi⟩
    · -- (norm, sub): symmetric to above.
      exfalso
      subst hq2
      have hk2 : ((-1074 : Int) - (-1074)).toNat = 0 := by decide
      rw [hk2, pow_zero, Int.mul_one] at h_val
      have hk1 : ((q₁ - (-1074)).toNat : Int) = q₁ + 1074 := by
        have := Int.toNat_of_nonneg (a := q₁ - -1074) (by omega)
        omega
      have hpow_pos : (0 : Int) ≤ (2 : Int) ^ (q₁ - (-1074)).toNat := by positivity
      have h_lhs_ge : (m₁ : Int) * (2 : Int) ^ (q₁ - (-1074)).toNat ≥ ((2^52 : Nat) : Int) := by
        have : ((2^52 : Nat) : Int) ≤ (m₁ : Int) := by exact_mod_cast hm1_ge
        have h_pp : (1 : Int) ≤ (2 : Int) ^ (q₁ - (-1074)).toNat := by
          have : (1 : Int) = (2 : Int) ^ 0 := by decide
          rw [this]; exact pow_le_pow_right₀ (by decide) (Nat.zero_le _)
        nlinarith
      have h_rhs_lt : (m₂ : Int) < ((2^52 : Nat) : Int) := by exact_mod_cast hm2_lt
      omega
    · -- (norm, norm): both in [2^52, 2^53), so log2 determines q.
      -- m_i · 2^(q_i + 1074) has log2 ∈ [q_i + 1126, q_i + 1127).
      -- So if m₁·2^(q₁+1074) = m₂·2^(q₂+1074), then their log2's agree, so:
      --   q₁ + log2 m₁ = q₂ + log2 m₂. With log2 m_i ∈ [52, 53), need m₁ ≥ 2·m₂ or vice versa,
      -- or q₁ = q₂.
      have hk1 : (q₁ - (-1074)).toNat = (q₁ + 1074).toNat := by
        have : q₁ - (-1074) = q₁ + 1074 := by ring
        rw [this]
      have hk2 : (q₂ - (-1074)).toNat = (q₂ + 1074).toNat := by
        have : q₂ - (-1074) = q₂ + 1074 := by ring
        rw [this]
      rw [hk1, hk2] at h_val
      have hq1' : 0 ≤ q₁ + 1074 := by omega
      have hq2' : 0 ≤ q₂ + 1074 := by omega
      have hq1n : ((q₁ + 1074).toNat : Int) = q₁ + 1074 := Int.toNat_of_nonneg hq1'
      have hq2n : ((q₂ + 1074).toNat : Int) = q₂ + 1074 := Int.toNat_of_nonneg hq2'
      -- WLOG q₁ ≤ q₂ (symmetric case otherwise).
      by_cases hq_le : q₁ ≤ q₂
      · -- q₁ ≤ q₂. m₁ · 2^(q₁+1074) = m₂ · 2^(q₂+1074) ⇒ m₁ = m₂ · 2^(q₂ - q₁).
        have hk : (q₂ + 1074).toNat = (q₁ + 1074).toNat + (q₂ - q₁).toNat := by
          omega
        rw [hk, pow_add] at h_val
        -- h_val : m₁ * 2^(q₁+1074).toNat = m₂ * (2^(q₁+1074).toNat * 2^(q₂-q₁).toNat)
        have hpow_pos : (0 : Int) < (2 : Int) ^ (q₁ + 1074).toNat := by positivity
        have hcancel : (m₁ : Int) = (m₂ : Int) * (2 : Int) ^ (q₂ - q₁).toNat := by
          have hreshape : (m₂ : Int) * ((2 : Int) ^ (q₁ + 1074).toNat
                            * (2 : Int) ^ (q₂ - q₁).toNat)
                          = ((m₂ : Int) * (2 : Int) ^ (q₂ - q₁).toNat)
                            * (2 : Int) ^ (q₁ + 1074).toNat := by ring
          rw [hreshape] at h_val
          have := mul_right_cancel₀ (ne_of_gt hpow_pos) h_val
          exact this
        rcases (eq_or_lt_of_le hq_le) with hq_eq | hq_lt
        · -- q₁ = q₂: m₁ = m₂.
          subst hq_eq
          have hktz : (q₁ - q₁).toNat = 0 := by simp
          rw [hktz, pow_zero, Int.mul_one] at hcancel
          have hm_eq : m₁ = m₂ := by exact_mod_cast hcancel
          exact ⟨hm_eq, rfl⟩
        · -- q₁ < q₂: m₁ = m₂ · 2^k with k ≥ 1. But m₁ < 2^53 and m₂ ≥ 2^52, so m₁ ≥ 2^53. ⊥
          exfalso
          have hk_pos : (q₂ - q₁).toNat ≥ 1 := by
            have : (1 : Int) ≤ q₂ - q₁ := by omega
            omega
          have h2pow_ge2 : (2 : Int) ^ (q₂ - q₁).toNat ≥ 2 := by
            have : (2 : Int) ^ 1 ≤ (2 : Int) ^ (q₂ - q₁).toNat :=
              pow_le_pow_right₀ (by decide) hk_pos
            simpa using this
          have h_m1_ge : (m₁ : Int) ≥ 2 * ((2 ^ 52 : Nat) : Int) := by
            have : ((2 ^ 52 : Nat) : Int) ≤ (m₂ : Int) := by exact_mod_cast hm2_ge
            nlinarith
          have h_m1_lt : (m₁ : Int) < ((2 ^ 53 : Nat) : Int) := by exact_mod_cast hm1_lt
          have h_pow53 : ((2 ^ 53 : Nat) : Int) = 2 * ((2 ^ 52 : Nat) : Int) := by push_cast
          omega
      · -- q₁ > q₂: symmetric.
        have hq_lt : q₂ < q₁ := by omega
        have h_val' : (m₂ : Int) * (2 : Int) ^ (q₂ + 1074).toNat
                      = (m₁ : Int) * (2 : Int) ^ (q₁ + 1074).toNat := h_val.symm
        have hk : (q₁ + 1074).toNat = (q₂ + 1074).toNat + (q₁ - q₂).toNat := by
          omega
        rw [hk, pow_add] at h_val'
        have hpow_pos : (0 : Int) < (2 : Int) ^ (q₂ + 1074).toNat := by positivity
        have hcancel : (m₂ : Int) = (m₁ : Int) * (2 : Int) ^ (q₁ - q₂).toNat := by
          have hreshape : (m₁ : Int) * ((2 : Int) ^ (q₂ + 1074).toNat
                            * (2 : Int) ^ (q₁ - q₂).toNat)
                          = ((m₁ : Int) * (2 : Int) ^ (q₁ - q₂).toNat)
                            * (2 : Int) ^ (q₂ + 1074).toNat := by ring
          rw [hreshape] at h_val'
          have := mul_right_cancel₀ (ne_of_gt hpow_pos) h_val'
          exact this
        exfalso
        have hk_pos : (q₁ - q₂).toNat ≥ 1 := by
          have : (1 : Int) ≤ q₁ - q₂ := by omega
          omega
        have h2pow_ge2 : (2 : Int) ^ (q₁ - q₂).toNat ≥ 2 :=
          le_trans (le_of_eq (by simp [pow_one]))
                   (pow_le_pow_right₀ (by decide) hk_pos)
        have h_m2_ge : (m₂ : Int) ≥ 2 * ((2 ^ 52 : Nat) : Int) := by
          have : ((2 ^ 52 : Nat) : Int) ≤ (m₁ : Int) := by exact_mod_cast hm1_ge
          nlinarith
        have h_m2_lt : (m₂ : Int) < ((2 ^ 53 : Nat) : Int) := by exact_mod_cast hm2_lt
        have h_pow53 : ((2 ^ 53 : Nat) : Int) = 2 * ((2 ^ 52 : Nat) : Int) := by push_cast
        omega

/-! ## The disjointness theorem -/

/-- Algebraic identity for the cleared-power exponents:
`max(q, 0) - max(-q, 0) = q`. -/
private theorem twoPos_minus_twoNeg_exp (q : Int) :
    ((if q ≥ 0 then q.toNat else 0 : Int)
       - (if q < 0 then (-q).toNat else 0 : Int)) = q := by
  by_cases h : q ≥ 0
  · have h' : ¬ q < 0 := by omega
    rw [if_pos h, if_neg h']
    have : ((q.toNat : Int)) = q := Int.toNat_of_nonneg h
    omega
  · have h' : q < 0 := by omega
    rw [if_neg h, if_pos h']
    have : (((-q).toNat : Int)) = -q := Int.toNat_of_nonneg (by omega)
    omega

/-- Helper: for `q₁ < q₂` and both LegalIEEE, the bracketing produced by
`inRoundingInterval` on `(m₁, q₁)` and `(m₂, q₂)` is contradictory.

This is one half of the WLOG case-split in `inRoundingInterval_uniq` for
`q₁ ≠ q₂`. The other half (`q₁ > q₂`) reduces here by swapping pairs.

**Strategy**: Multiply the right-bracket of pair 1 (`fourU sig q₁ exp ≤
fourVR m₁ q₁ exp`) by `twoNegPow q₂` and the left-bracket of pair 2
(`fourVL m₂ q₂ exp irreg₂ ≤ fourU sig q₂ exp`) by `twoNegPow q₁`. Both
yield expressions with the common factor `4·sig · tenPosPow exp ·
twoNegPow q₁ · twoNegPow q₂`. Chaining gives an integer inequality
between cleared-form `leftN₂` and `rightN₁`, scaled by `2^α` where
`α = (q₂ - q₁).toNat`. The legal-IEEE bounds on `m₁`, `m₂`, together with
the boundary cEven analysis, contradict this. -/
private theorem inRoundingInterval_uniq_lt
    (sig : Nat) (exp : Int)
    (m₁ m₂ : Nat) (q₁ q₂ : Int)
    (h_dec₁ : LegalIEEE m₁ q₁)
    (h_dec₂ : LegalIEEE m₂ q₂)
    (h₁ : inRoundingInterval sig exp m₁ q₁ (isIrregular m₁ q₁) = true)
    (h₂ : inRoundingInterval sig exp m₂ q₂ (isIrregular m₂ q₂) = true)
    (h_lt : q₁ < q₂) : False := by
  -- Rewrite both bracketings into cleared form.
  rw [inRoundingInterval_iff] at h₁ h₂
  -- Set up named quantities matching the q₁=q₂ proof style.
  set leftN₁ : Int :=
    if isIrregular m₁ q₁ then 4 * (m₁ : Int) - 1 else 4 * (m₁ : Int) - 2 with hleftN₁_def
  set leftN₂ : Int :=
    if isIrregular m₂ q₂ then 4 * (m₂ : Int) - 1 else 4 * (m₂ : Int) - 2 with hleftN₂_def
  set rightN₁ : Int := 4 * (m₁ : Int) + 2 with hrightN₁_def
  -- Cleared-form expansions for the four bracket values we'll use.
  have hL2_eq :
      fourVL m₂ q₂ exp (isIrregular m₂ q₂) =
        leftN₂ * ((twoPosPow q₂ : Int) * (tenNegPow exp : Int)) := by
    unfold fourVL cmpScaledMixed.lhs
    show ((if isIrregular m₂ q₂ = true then 4 * (m₂ : Int) - 1 else 4 * (m₂ : Int) - 2)
            * ((2 ^ if q₂ ≥ 0 then q₂.toNat else 0 : Nat) : Int))
          * ((10 ^ if exp < 0 then (-exp).toNat else 0 : Nat) : Int)
        = leftN₂ * ((twoPosPow q₂ : Int) * (tenNegPow exp : Int))
    show leftN₂ * ((twoPosPow q₂ : Nat) : Int) * ((tenNegPow exp : Nat) : Int)
          = leftN₂ * ((twoPosPow q₂ : Int) * (tenNegPow exp : Int))
    ring
  have hR1_eq :
      fourVR m₁ q₁ exp =
        rightN₁ * ((twoPosPow q₁ : Int) * (tenNegPow exp : Int)) := by
    unfold fourVR cmpScaledMixed.lhs
    show rightN₁ * ((twoPosPow q₁ : Nat) : Int) * ((tenNegPow exp : Nat) : Int)
          = rightN₁ * ((twoPosPow q₁ : Int) * (tenNegPow exp : Int))
    ring
  have hU1_eq :
      fourU sig q₁ exp =
        4 * (sig : Int) * ((tenPosPow exp : Int) * (twoNegPow q₁ : Int)) := by
    unfold fourU cmpScaledMixed.rhs
    show (4 * (sig : Int)) * ((tenPosPow exp : Nat) : Int) * ((twoNegPow q₁ : Nat) : Int)
          = 4 * (sig : Int) * ((tenPosPow exp : Int) * (twoNegPow q₁ : Int))
    ring
  have hU2_eq :
      fourU sig q₂ exp =
        4 * (sig : Int) * ((tenPosPow exp : Int) * (twoNegPow q₂ : Int)) := by
    unfold fourU cmpScaledMixed.rhs
    show (4 * (sig : Int)) * ((tenPosPow exp : Nat) : Int) * ((twoNegPow q₂ : Nat) : Int)
          = 4 * (sig : Int) * ((tenPosPow exp : Int) * (twoNegPow q₂ : Int))
    ring
  -- Bracket inequalities (`≤` versions; equality cases held separately).
  have h_l2_le_u2 :
      leftN₂ * ((twoPosPow q₂ : Int) * (tenNegPow exp : Int))
        ≤ 4 * (sig : Int) * ((tenPosPow exp : Int) * (twoNegPow q₂ : Int)) := by
    have ⟨hleft, _⟩ := h₂
    rcases hleft with hlt | ⟨heq, _⟩
    · exact Int.le_of_lt (by rw [← hL2_eq, ← hU2_eq]; exact hlt)
    · exact Int.le_of_eq (by rw [← hL2_eq, ← hU2_eq]; exact heq)
  have h_u1_le_r1 :
      4 * (sig : Int) * ((tenPosPow exp : Int) * (twoNegPow q₁ : Int))
        ≤ rightN₁ * ((twoPosPow q₁ : Int) * (tenNegPow exp : Int)) := by
    have ⟨_, hright⟩ := h₁
    rcases hright with hlt | ⟨heq, _⟩
    · exact Int.le_of_lt (by rw [← hR1_eq, ← hU1_eq]; exact hlt)
    · exact Int.le_of_eq (by rw [← hR1_eq, ← hU1_eq]; exact heq)
  -- Multiply h_l2_le_u2 by twoNegPow q₁ (positive) and h_u1_le_r1 by twoNegPow q₂ (positive).
  have hT₁_pos : (0 : Int) < (twoNegPow q₁ : Int) := by
    exact_mod_cast twoNegPow_pos q₁
  have hT₂_pos : (0 : Int) < (twoNegPow q₂ : Int) := by
    exact_mod_cast twoNegPow_pos q₂
  have hS_pos : (0 : Int) < (twoPosPow q₁ : Int) := by
    exact_mod_cast twoPosPow_pos q₁
  have hS'_pos : (0 : Int) < (twoPosPow q₂ : Int) := by
    exact_mod_cast twoPosPow_pos q₂
  have hTk_pos : (0 : Int) < (tenNegPow exp : Int) := by
    exact_mod_cast tenNegPow_pos exp
  have hPk_pos : (0 : Int) < (tenPosPow exp : Int) := by
    exact_mod_cast tenPosPow_pos exp
  -- Multiply h_l2_le_u2 by (tenNegPow exp · twoNegPow q₁): wait, tenNegPow exp is already on
  -- both sides. We multiply by twoNegPow q₁ (right-multiplication preserves ≤).
  -- After multiplying by twoNegPow q₁ on the right (and using commutativity):
  -- leftN₂ · twoPosPow q₂ · tenNegPow exp · twoNegPow q₁
  --   ≤ 4·sig · tenPosPow exp · twoNegPow q₂ · twoNegPow q₁
  -- And from h_u1_le_r1, multiplying by twoNegPow q₂:
  -- 4·sig · tenPosPow exp · twoNegPow q₁ · twoNegPow q₂
  --   ≤ rightN₁ · twoPosPow q₁ · tenNegPow exp · twoNegPow q₂
  -- Chain: middle terms equal, so:
  -- leftN₂ · twoPosPow q₂ · twoNegPow q₁ · tenNegPow exp
  --   ≤ rightN₁ · twoPosPow q₁ · twoNegPow q₂ · tenNegPow exp.
  have h_l2_scaled :
      leftN₂ * ((twoPosPow q₂ : Int) * (tenNegPow exp : Int)) * (twoNegPow q₁ : Int)
        ≤ 4 * (sig : Int) * ((tenPosPow exp : Int) * (twoNegPow q₂ : Int)) * (twoNegPow q₁ : Int) :=
    Int.mul_le_mul_of_nonneg_right h_l2_le_u2 (Int.le_of_lt hT₁_pos)
  have h_u1_scaled :
      4 * (sig : Int) * ((tenPosPow exp : Int) * (twoNegPow q₁ : Int)) * (twoNegPow q₂ : Int)
        ≤ rightN₁ * ((twoPosPow q₁ : Int) * (tenNegPow exp : Int)) * (twoNegPow q₂ : Int) :=
    Int.mul_le_mul_of_nonneg_right h_u1_le_r1 (Int.le_of_lt hT₂_pos)
  -- The middles are equal (just rearrangement of factors).
  have hMid :
      4 * (sig : Int) * ((tenPosPow exp : Int) * (twoNegPow q₂ : Int)) * (twoNegPow q₁ : Int)
        = 4 * (sig : Int) * ((tenPosPow exp : Int) * (twoNegPow q₁ : Int)) * (twoNegPow q₂ : Int) := by
    ring
  -- Chain.
  have hChain :
      leftN₂ * ((twoPosPow q₂ : Int) * (tenNegPow exp : Int)) * (twoNegPow q₁ : Int)
        ≤ rightN₁ * ((twoPosPow q₁ : Int) * (tenNegPow exp : Int)) * (twoNegPow q₂ : Int) := by
    calc leftN₂ * ((twoPosPow q₂ : Int) * (tenNegPow exp : Int)) * (twoNegPow q₁ : Int)
        ≤ 4 * (sig : Int) * ((tenPosPow exp : Int) * (twoNegPow q₂ : Int)) * (twoNegPow q₁ : Int) := h_l2_scaled
      _ = 4 * (sig : Int) * ((tenPosPow exp : Int) * (twoNegPow q₁ : Int)) * (twoNegPow q₂ : Int) := hMid
      _ ≤ rightN₁ * ((twoPosPow q₁ : Int) * (tenNegPow exp : Int)) * (twoNegPow q₂ : Int) := h_u1_scaled
  -- Rearrange hChain to expose the exponent factors.
  -- LHS = leftN₂ · (twoPosPow q₂ · twoNegPow q₁) · tenNegPow exp
  -- RHS = rightN₁ · (twoPosPow q₁ · twoNegPow q₂) · tenNegPow exp
  -- Cancel tenNegPow exp (positive) and reduce to:
  -- leftN₂ · (twoPosPow q₂ · twoNegPow q₁) ≤ rightN₁ · (twoPosPow q₁ · twoNegPow q₂).
  have hChain' :
      leftN₂ * ((twoPosPow q₂ : Int) * (twoNegPow q₁ : Int)) * (tenNegPow exp : Int)
        ≤ rightN₁ * ((twoPosPow q₁ : Int) * (twoNegPow q₂ : Int)) * (tenNegPow exp : Int) := by
    have hLHS_eq :
        leftN₂ * ((twoPosPow q₂ : Int) * (tenNegPow exp : Int)) * (twoNegPow q₁ : Int)
          = leftN₂ * ((twoPosPow q₂ : Int) * (twoNegPow q₁ : Int)) * (tenNegPow exp : Int) := by ring
    have hRHS_eq :
        rightN₁ * ((twoPosPow q₁ : Int) * (tenNegPow exp : Int)) * (twoNegPow q₂ : Int)
          = rightN₁ * ((twoPosPow q₁ : Int) * (twoNegPow q₂ : Int)) * (tenNegPow exp : Int) := by ring
    rw [← hLHS_eq, ← hRHS_eq]; exact hChain
  have hChain_no_tk :
      leftN₂ * ((twoPosPow q₂ : Int) * (twoNegPow q₁ : Int))
        ≤ rightN₁ * ((twoPosPow q₁ : Int) * (twoNegPow q₂ : Int)) :=
    Int.le_of_mul_le_mul_right (by linarith) hTk_pos
  -- Now show twoPosPow q₂ · twoNegPow q₁ = 2^α · (twoPosPow q₁ · twoNegPow q₂)
  -- where α = (q₂ - q₁).toNat.
  -- Key fact: (max(q, 0) + max(-q', 0)) - (max(q', 0) + max(-q, 0)) = q - q' (cross identity).
  -- Hence twoPos q₂ · twoNeg q₁ = 2^α · twoPos q₁ · twoNeg q₂ where α = q₂ - q₁.
  -- Concretely:
  set e1Pos : Nat := if q₁ ≥ 0 then q₁.toNat else 0 with he1Pos_def
  set e1Neg : Nat := if q₁ < 0 then (-q₁).toNat else 0 with he1Neg_def
  set e2Pos : Nat := if q₂ ≥ 0 then q₂.toNat else 0 with he2Pos_def
  set e2Neg : Nat := if q₂ < 0 then (-q₂).toNat else 0 with he2Neg_def
  -- Express twoPosPow q_i, twoNegPow q_i:
  have h_S_eq : (twoPosPow q₁ : Int) = (2 : Int) ^ e1Pos := by
    unfold twoPosPow; push_cast; rfl
  have h_S'_eq : (twoPosPow q₂ : Int) = (2 : Int) ^ e2Pos := by
    unfold twoPosPow; push_cast; rfl
  have h_T_eq : (twoNegPow q₁ : Int) = (2 : Int) ^ e1Neg := by
    unfold twoNegPow; push_cast; rfl
  have h_T'_eq : (twoNegPow q₂ : Int) = (2 : Int) ^ e2Neg := by
    unfold twoNegPow; push_cast; rfl
  -- Exponent identity: e1Pos + e2Neg + α = e2Pos + e1Neg, where α = (q₂ - q₁).toNat.
  -- Or: e2Pos + e1Neg = e1Pos + e2Neg + α.
  -- We derive this via twoPos_minus_twoNeg_exp.
  have he1 : (e1Pos : Int) - (e1Neg : Int) = q₁ := by
    simp only [he1Pos_def, he1Neg_def]; push_cast; split_ifs <;> omega
  have he2 : (e2Pos : Int) - (e2Neg : Int) = q₂ := by
    simp only [he2Pos_def, he2Neg_def]; push_cast; split_ifs <;> omega
  -- So (e2Pos - e2Neg) - (e1Pos - e1Neg) = q₂ - q₁,
  -- i.e., e2Pos + e1Neg = e1Pos + e2Neg + (q₂ - q₁).
  set α : Nat := (q₂ - q₁).toNat with hα_def
  have hα_pos : 1 ≤ α := by
    have : (1 : Int) ≤ q₂ - q₁ := by omega
    have h_eq : ((q₂ - q₁).toNat : Int) = q₂ - q₁ := Int.toNat_of_nonneg (by omega)
    show 1 ≤ (q₂ - q₁).toNat; omega
  have hα_int : ((α : Int)) = q₂ - q₁ := Int.toNat_of_nonneg (by omega)
  have he_id : e2Pos + e1Neg = e1Pos + e2Neg + α := by
    -- Coerce to Int and use he1, he2.
    have h : ((e2Pos : Int) + (e1Neg : Int)) = ((e1Pos : Int) + (e2Neg : Int)) + (α : Int) := by
      rw [hα_int]; linarith
    exact_mod_cast h
  -- Now derive: twoPosPow q₂ · twoNegPow q₁ = 2^α · (twoPosPow q₁ · twoNegPow q₂).
  have hExp_id :
      (twoPosPow q₂ : Int) * (twoNegPow q₁ : Int)
        = (2 : Int) ^ α * ((twoPosPow q₁ : Int) * (twoNegPow q₂ : Int)) := by
    rw [h_S_eq, h_S'_eq, h_T_eq, h_T'_eq]
    rw [show (2 : Int) ^ e2Pos * (2 : Int) ^ e1Neg
              = (2 : Int) ^ (e2Pos + e1Neg) by rw [pow_add]]
    rw [show (2 : Int) ^ α * ((2 : Int) ^ e1Pos * (2 : Int) ^ e2Neg)
              = (2 : Int) ^ (e1Pos + e2Neg + α) by
            rw [pow_add, pow_add]; ring]
    rw [he_id]
  rw [hExp_id] at hChain_no_tk
  -- Cancel the common positive factor (twoPosPow q₁ · twoNegPow q₂).
  set R : Int := (twoPosPow q₁ : Int) * (twoNegPow q₂ : Int) with hR_def
  have hR_pos : 0 < R := Int.mul_pos hS_pos hT₂_pos
  have hChain_red : leftN₂ * (2 : Int) ^ α ≤ rightN₁ := by
    have h_step : leftN₂ * (2 : Int) ^ α * R ≤ rightN₁ * R := by
      have hLHS : leftN₂ * ((2 : Int) ^ α * R) = leftN₂ * (2 : Int) ^ α * R := by ring
      rw [hLHS] at hChain_no_tk
      exact hChain_no_tk
    exact Int.le_of_mul_le_mul_right (by linarith) hR_pos
  -- Now derive the contradiction from hChain_red.
  -- Step 1: q₂ > -1074 (since q₂ ≥ q₁ + 1 ≥ -1074 + 1 = -1073).
  have h_q₂_norm : -1074 < q₂ := by
    rcases h_dec₁ with ⟨_, _, hq1⟩ | ⟨_, _, hq1_lo, _⟩ <;> omega
  -- Step 2: m₂ is in normal range (since q₂ > -1074 contradicts subnormal q = -1074).
  have h_m₂_ge : (m₂ : Int) ≥ ((2 : Nat) ^ 52 : Int) := by
    rcases h_dec₂ with ⟨_, _, hq2⟩ | ⟨hm2_ge, _, _, _⟩
    · exfalso; omega
    · exact_mod_cast hm2_ge
  have h_m₂_lt : (m₂ : Int) < ((2 : Nat) ^ 53 : Int) := by
    rcases h_dec₂ with ⟨_, hm2_lt, _⟩ | ⟨_, hm2_lt, _, _⟩
    · have : (2 : Nat) ^ 52 < (2 : Nat) ^ 53 := by decide
      exact_mod_cast (Nat.lt_of_lt_of_le hm2_lt (Nat.le_of_lt this))
    · exact_mod_cast hm2_lt
  -- Step 3: m₁ ≤ 2^53 - 1.
  have h_m₁_lt : (m₁ : Int) < ((2 : Nat) ^ 53 : Int) := by
    rcases h_dec₁ with ⟨_, hm1_lt, _⟩ | ⟨_, hm1_lt, _, _⟩
    · have : (2 : Nat) ^ 52 < (2 : Nat) ^ 53 := by decide
      exact_mod_cast (Nat.lt_of_lt_of_le hm1_lt (Nat.le_of_lt this))
    · exact_mod_cast hm1_lt
  -- leftN₂ bounds:
  -- leftN₂ ∈ {4m₂ - 1, 4m₂ - 2} with m₂ ≥ 2^52, so leftN₂ ≥ 4·2^52 - 2 = 2^54 - 2.
  -- rightN₁ = 4m₁ + 2 ≤ 4(2^53 - 1) + 2 = 2^55 - 2.
  have h_leftN₂_ge : leftN₂ ≥ 4 * ((2 : Nat) ^ 52 : Int) - 2 := by
    show (if isIrregular m₂ q₂ = true then 4 * (m₂ : Int) - 1 else 4 * (m₂ : Int) - 2)
          ≥ 4 * ((2 : Nat) ^ 52 : Int) - 2
    by_cases hirr : isIrregular m₂ q₂ = true
    · rw [if_pos hirr]; linarith
    · rw [if_neg hirr]; linarith
  have h_rightN₁_le : rightN₁ ≤ 4 * ((2 : Nat) ^ 53 : Int) - 2 := by
    show 4 * (m₁ : Int) + 2 ≤ 4 * ((2 : Nat) ^ 53 : Int) - 2
    linarith
  -- Case-split on α.
  by_cases hα_ge2 : α ≥ 2
  · -- α ≥ 2: leftN₂ · 2^α ≥ leftN₂ · 4 ≥ 4 · (2^54 - 2) = 2^56 - 8 > 2^55 - 2 ≥ rightN₁.
    exfalso
    have h_pow_α : (2 : Int) ^ α ≥ 4 := by
      have : (2 : Int) ^ 2 ≤ (2 : Int) ^ α :=
        pow_le_pow_right₀ (by decide) hα_ge2
      have h4 : (2 : Int) ^ 2 = 4 := by decide
      linarith
    have h_leftN₂_pos : leftN₂ > 0 := by
      have h2_pos : ((2 : Nat) ^ 52 : Int) > 0 := by decide
      linarith
    have h_step : leftN₂ * (2 : Int) ^ α ≥ leftN₂ * 4 := by
      have := Int.mul_le_mul_of_nonneg_left h_pow_α (by linarith : (0 : Int) ≤ leftN₂)
      linarith
    have h_pow52 : ((2 : Nat) ^ 52 : Int) = 4503599627370496 := by decide
    have h_pow53 : ((2 : Nat) ^ 53 : Int) = 9007199254740992 := by decide
    linarith
  · -- α = 1 case (since α ≥ 1 and ¬ α ≥ 2).
    have hα_eq : α = 1 := by omega
    rw [hα_eq] at hChain_red
    -- 2^1 = 2:
    have hpow1 : (2 : Int) ^ 1 = 2 := by norm_num
    rw [hpow1] at hChain_red
    -- hChain_red : leftN₂ * 2 ≤ rightN₁
    -- Now split on irreg₂:
    by_cases hirr2 : isIrregular m₂ q₂ = true
    · -- Irregular case: leftN₂ = 4m₂ - 1. Then (4m₂ - 1)·2 = 8m₂ - 2 ≤ 4m₁ + 2.
      -- m₂ ≥ 2^52, m₁ ≤ 2^53 - 1: forces equality at m₂ = 2^52, m₁ = 2^53 - 1.
      -- Then equality in the combined ⟹ equality in h_l2_le_u2 AND h_u1_le_r1,
      -- ⟹ both require m % 2 = 0. m₁ = 2^53 - 1 is ODD. Contradiction.
      have hleftN₂_val : leftN₂ = 4 * (m₂ : Int) - 1 := by
        show (if isIrregular m₂ q₂ = true then 4 * (m₂ : Int) - 1 else 4 * (m₂ : Int) - 2)
              = 4 * (m₂ : Int) - 1
        rw [if_pos hirr2]
      have h_pow52 : ((2 : Nat) ^ 52 : Int) = 4503599627370496 := by decide
      have h_pow53 : ((2 : Nat) ^ 53 : Int) = 9007199254740992 := by decide
      -- From hChain_red: (4m₂ - 1)·2 ≤ 4m₁ + 2 ⟹ 8m₂ ≤ 4m₁ + 4 ⟹ 2m₂ ≤ m₁ + 1.
      have h_2m₂_le : 2 * (m₂ : Int) ≤ (m₁ : Int) + 1 := by
        rw [hleftN₂_val] at hChain_red
        show 2 * (m₂ : Int) ≤ (m₁ : Int) + 1
        have hrn1 : rightN₁ = 4 * (m₁ : Int) + 2 := rfl
        rw [hrn1] at hChain_red
        linarith
      -- m₁ < 2^53 ⟹ m₁ ≤ 2^53 - 1. So 2m₂ ≤ 2^53.
      have h_m₂_le_2pow52 : (m₂ : Int) ≤ ((2 : Nat) ^ 52 : Int) := by
        have : 2 * (m₂ : Int) ≤ 2 * ((2 : Nat) ^ 52 : Int) := by
          have h53 : (2 : Int) * ((2 : Nat) ^ 52 : Int) = ((2 : Nat) ^ 53 : Int) := by
            rw [h_pow52, h_pow53]; ring
          linarith
        linarith
      have hm₂_eq : (m₂ : Int) = ((2 : Nat) ^ 52 : Int) := by linarith
      have hm₁_eq : (m₁ : Int) = ((2 : Nat) ^ 53 : Int) - 1 := by linarith
      -- Now we have hChain_red equality:
      -- leftN₂ · 2 = (4·2^52 - 1)·2 = 2^55 - 2 = 4·(2^53 - 1) + 2 = rightN₁.
      have hChain_eq : leftN₂ * 2 = rightN₁ := by
        rw [hleftN₂_val, hm₂_eq]
        have hrn1 : rightN₁ = 4 * (m₁ : Int) + 2 := rfl
        rw [hrn1, hm₁_eq]
        have hp53_eq : ((2 : Nat) ^ 53 : Int) = 2 * ((2 : Nat) ^ 52 : Int) := by
          rw [h_pow52, h_pow53]; ring
        linarith
      -- So h_l2_le_u2 and h_u1_le_r1 are both equalities (since they chain to equality
      -- when multiplied by positive factors). Extract equalities.
      -- From hChain_red as equality (chain becomes equality):
      have hChain'_eq :
          leftN₂ * ((twoPosPow q₂ : Int) * (twoNegPow q₁ : Int)) * (tenNegPow exp : Int)
            = rightN₁ * ((twoPosPow q₁ : Int) * (twoNegPow q₂ : Int)) * (tenNegPow exp : Int) := by
        have h_eq_red : leftN₂ * (2 : Int) ^ α = rightN₁ := by
          rw [hα_eq, hpow1]; exact hChain_eq
        rw [hExp_id]
        have h_eq_unrwap :
            leftN₂ * ((2 : Int) ^ α * ((twoPosPow q₁ : Int) * (twoNegPow q₂ : Int)))
              * (tenNegPow exp : Int)
              = (leftN₂ * (2 : Int) ^ α) * ((twoPosPow q₁ : Int) * (twoNegPow q₂ : Int))
                  * (tenNegPow exp : Int) := by ring
        rw [h_eq_unrwap, h_eq_red]
      -- From hChain (the un-cancelled-Tk version) being squeezed equality:
      have hChain_eq_full :
          leftN₂ * ((twoPosPow q₂ : Int) * (tenNegPow exp : Int)) * (twoNegPow q₁ : Int)
            = rightN₁ * ((twoPosPow q₁ : Int) * (tenNegPow exp : Int)) * (twoNegPow q₂ : Int) := by
        have hLHS_eq :
            leftN₂ * ((twoPosPow q₂ : Int) * (tenNegPow exp : Int)) * (twoNegPow q₁ : Int)
              = leftN₂ * ((twoPosPow q₂ : Int) * (twoNegPow q₁ : Int)) * (tenNegPow exp : Int) := by ring
        have hRHS_eq :
            rightN₁ * ((twoPosPow q₁ : Int) * (tenNegPow exp : Int)) * (twoNegPow q₂ : Int)
              = rightN₁ * ((twoPosPow q₁ : Int) * (twoNegPow q₂ : Int)) * (tenNegPow exp : Int) := by ring
        rw [hLHS_eq, hRHS_eq]; exact hChain'_eq
      -- Squeeze h_l2_scaled = h_u1_scaled = chain via hChain_eq_full.
      -- h_l2_scaled: LHS_scaled ≤ MID_scaled.
      -- h_u1_scaled: MID_scaled = MID_scaled' ≤ RHS_scaled. (MID_scaled = MID_scaled' by hMid.)
      -- LHS_scaled ≤ MID ≤ RHS_scaled = LHS_scaled (from hChain_eq_full).
      -- So all three equal. Thus h_l2_le_u2 (after multiply by twoNegPow q₁) becomes equal.
      -- Cancel positive twoNegPow q₁ to get h_l2_le_u2 = equal.
      have h_l2_eq_u2 :
          leftN₂ * ((twoPosPow q₂ : Int) * (tenNegPow exp : Int))
            = 4 * (sig : Int) * ((tenPosPow exp : Int) * (twoNegPow q₂ : Int)) := by
        -- LHS_scaled ≤ MID_scaled and chain LHS_scaled = RHS_scaled
        --   ⟹ MID_scaled ≥ LHS_scaled ≥ RHS_scaled ≥ MID_scaled.
        have hUpper : 4 * (sig : Int) * ((tenPosPow exp : Int) * (twoNegPow q₂ : Int)) * (twoNegPow q₁ : Int)
                      ≤ rightN₁ * ((twoPosPow q₁ : Int) * (tenNegPow exp : Int)) * (twoNegPow q₂ : Int) := by
          rw [hMid]; exact h_u1_scaled
        have h_l2_scaled_eq :
            leftN₂ * ((twoPosPow q₂ : Int) * (tenNegPow exp : Int)) * (twoNegPow q₁ : Int)
              = 4 * (sig : Int) * ((tenPosPow exp : Int) * (twoNegPow q₂ : Int)) * (twoNegPow q₁ : Int) := by
          linarith
        -- Cancel twoNegPow q₁.
        have hLHS_eq :
            leftN₂ * ((twoPosPow q₂ : Int) * (tenNegPow exp : Int)) * (twoNegPow q₁ : Int)
              = leftN₂ * ((twoPosPow q₂ : Int) * (tenNegPow exp : Int)) * (twoNegPow q₁ : Int) := rfl
        exact mul_right_cancel₀ (ne_of_gt hT₁_pos) h_l2_scaled_eq
      -- Similarly, h_u1_le_r1 is an equality.
      have h_u1_eq_r1 :
          4 * (sig : Int) * ((tenPosPow exp : Int) * (twoNegPow q₁ : Int))
            = rightN₁ * ((twoPosPow q₁ : Int) * (tenNegPow exp : Int)) := by
        -- From h_l2_eq_u2, multiplying by twoNegPow q₁:
        -- LHS_scaled = MID_scaled. Combined with hChain_eq_full (LHS_scaled = RHS_scaled)
        -- and hMid (MID_scaled = MID_scaled'), we get MID_scaled' = RHS_scaled.
        have h_LHS_eq_MID :
            leftN₂ * ((twoPosPow q₂ : Int) * (tenNegPow exp : Int)) * (twoNegPow q₁ : Int)
              = 4 * (sig : Int) * ((tenPosPow exp : Int) * (twoNegPow q₂ : Int)) * (twoNegPow q₁ : Int) := by
          rw [h_l2_eq_u2]
        have h_u1_scaled_eq :
            4 * (sig : Int) * ((tenPosPow exp : Int) * (twoNegPow q₁ : Int)) * (twoNegPow q₂ : Int)
              = rightN₁ * ((twoPosPow q₁ : Int) * (tenNegPow exp : Int)) * (twoNegPow q₂ : Int) := by
          -- Chain: MID_scaled' = MID_scaled (by hMid.symm) = LHS_scaled (by h_LHS_eq_MID.symm)
          --                     = RHS_scaled (by hChain_eq_full).
          rw [← hMid, ← h_LHS_eq_MID, hChain_eq_full]
        exact mul_right_cancel₀ (ne_of_gt hT₂_pos) h_u1_scaled_eq
      -- Now use h_u1_eq_r1 (fourU = fourVR for pair 1) and h₁'s right bracket structure
      -- which requires m₁ % 2 = 0 in the equality case.
      have h_fourU1_eq_fourVR1 : fourU sig q₁ exp = fourVR m₁ q₁ exp := by
        rw [hU1_eq, hR1_eq]; exact h_u1_eq_r1
      -- From h₁'s right bracket: fourU < fourVR ∨ (fourU = fourVR ∧ m₁ % 2 = 0).
      have ⟨_, hright⟩ := h₁
      rcases hright with hlt | ⟨_, hm1_even⟩
      · -- Strict: contradicts h_fourU1_eq_fourVR1.
        exact absurd h_fourU1_eq_fourVR1 (ne_of_lt hlt)
      · -- Equality + m₁ even. But m₁ = 2^53 - 1 (odd).
        -- m₁ = 2^53 - 1; (2^53 - 1) % 2 = 1.
        have h_m₁_nat : m₁ = (2 : Nat) ^ 53 - 1 := by
          have h_cast : ((m₁ : Nat) : Int) = ((2 : Nat) ^ 53 : Int) - 1 := hm₁_eq
          -- Convert to Nat using the cast.
          have h_2pow53_pos : 1 ≤ (2 : Nat) ^ 53 := by decide
          omega
        have h_odd : m₁ % 2 = 1 := by
          rw [h_m₁_nat]; decide
        omega
    · -- Regular case: leftN₂ = 4m₂ - 2. m₂ ≠ 2^52 (since isIrregular false and q₂ > -1074).
      have hirr2_def : isIrregular m₂ q₂ = false := by
        cases hh : isIrregular m₂ q₂ with
        | false => rfl
        | true => exact absurd hh hirr2
      have hleftN₂_val : leftN₂ = 4 * (m₂ : Int) - 2 := by
        show (if isIrregular m₂ q₂ = true then 4 * (m₂ : Int) - 1 else 4 * (m₂ : Int) - 2)
              = 4 * (m₂ : Int) - 2
        rw [if_neg hirr2]
      -- isIrregular m₂ q₂ = (m₂ = 2^52 && q₂ > -1074). With q₂ > -1074 confirmed,
      -- isIrregular = false ⟹ m₂ ≠ 2^52.
      have h_m₂_ne_2pow52 : m₂ ≠ (2 : Nat) ^ 52 := by
        intro h_eq
        have h_irreg_true : isIrregular m₂ q₂ = true := by
          unfold isIrregular minNormalSignificand minBinaryExp
          simp [h_eq, h_q₂_norm]
        exact absurd h_irreg_true hirr2
      -- Hence m₂ ≥ 2^52 + 1.
      have h_m₂_ge_strict : (m₂ : Int) ≥ ((2 : Nat) ^ 52 : Int) + 1 := by
        have h_2pow52 : ((2 : Nat) ^ 52 : Int) ≥ 1 := by decide
        have : (m₂ : Nat) ≥ (2 : Nat) ^ 52 + 1 := by
          have h_nat_ge : (2 : Nat) ^ 52 ≤ m₂ := by
            have h_cast : ((2 : Nat) ^ 52 : Int) ≤ (m₂ : Int) := h_m₂_ge
            exact_mod_cast h_cast
          omega
        exact_mod_cast this
      -- Now: leftN₂ * 2 = (4m₂ - 2)·2 = 8m₂ - 4 ≥ 8·(2^52 + 1) - 4 = 2^55 + 4.
      -- rightN₁ = 4m₁ + 2 ≤ 4·(2^53 - 1) + 2 = 2^55 - 2.
      -- 2^55 + 4 > 2^55 - 2: contradiction.
      have h_pow52 : ((2 : Nat) ^ 52 : Int) = 4503599627370496 := by decide
      have h_pow53 : ((2 : Nat) ^ 53 : Int) = 9007199254740992 := by decide
      rw [hleftN₂_val] at hChain_red
      have hrn1 : rightN₁ = 4 * (m₁ : Int) + 2 := rfl
      rw [hrn1] at hChain_red
      linarith

/-- **Disjointness of `inRoundingInterval` for distinct LegalIEEE pairs.**

This is the geometric uniqueness theorem: round-to-nearest-ties-to-even
maps each decimal value to at most one IEEE-754 canonical pair.

The proof works at the cleared-form integer level. We bracket
`4·sig·10^exp` between the two endpoint values for each pair, multiply
both endpoint inequalities by the appropriate positive factors, and
compare. The argument reduces to: the rounding intervals of distinct
LegalIEEE pairs only overlap at adjacent boundaries, where parity (cEven)
of consecutive m's alternates, so endpoint inclusion is mutually
exclusive. -/
theorem inRoundingInterval_uniq
    (sig : Nat) (exp : Int)
    (m₁ m₂ : Nat) (q₁ q₂ : Int)
    (h_dec₁ : LegalIEEE m₁ q₁)
    (h_dec₂ : LegalIEEE m₂ q₂)
    (h₁ : inRoundingInterval sig exp m₁ q₁ (isIrregular m₁ q₁) = true)
    (h₂ : inRoundingInterval sig exp m₂ q₂ (isIrregular m₂ q₂) = true) :
    m₁ = m₂ ∧ q₁ = q₂ := by
  -- Proof: case-split on q₁ vs q₂. The q₁ = q₂ case is tractable directly.
  -- The q₁ ≠ q₂ case requires multiplying brackets by appropriate positive
  -- factors to align scales; deferred as a multi-cycle task.
  by_cases hq_eq : q₁ = q₂
  · -- q₁ = q₂ case.
    subst hq_eq
    -- Need to show m₁ = m₂.
    refine ⟨?_, rfl⟩
    -- Extract cleared-form brackets.
    rw [inRoundingInterval_iff] at h₁ h₂
    -- For each pair, extract `fourVL ≤ fourU ≤ fourVR` plus parity refinements.
    -- Set helpful names.
    set leftN₁ : Int := if isIrregular m₁ q₁ then 4 * (m₁ : Int) - 1 else 4 * (m₁ : Int) - 2
    set leftN₂ : Int := if isIrregular m₂ q₁ then 4 * (m₂ : Int) - 1 else 4 * (m₂ : Int) - 2
    set rightN₁ : Int := 4 * (m₁ : Int) + 2
    set rightN₂ : Int := 4 * (m₂ : Int) + 2
    set P : Int := (twoPosPow q₁ : Int) * (tenNegPow exp : Int) with hP_def
    set U : Int := 4 * (sig : Int) * (tenPosPow exp : Int) * (twoNegPow q₁ : Int) with hU_def
    -- Rewrite hypotheses in cleared form.
    have hL1_eq : fourVL m₁ q₁ exp (isIrregular m₁ q₁) = leftN₁ * P := by
      unfold fourVL cmpScaledMixed.lhs
      show ((if isIrregular m₁ q₁ = true then 4 * (m₁ : Int) - 1 else 4 * (m₁ : Int) - 2)
              * ((2 ^ if q₁ ≥ 0 then q₁.toNat else 0 : Nat) : Int))
            * ((10 ^ if exp < 0 then (-exp).toNat else 0 : Nat) : Int) = leftN₁ * P
      show leftN₁ * ((twoPosPow q₁ : Nat) : Int) * ((tenNegPow exp : Nat) : Int) = leftN₁ * P
      ring
    have hL2_eq : fourVL m₂ q₁ exp (isIrregular m₂ q₁) = leftN₂ * P := by
      unfold fourVL cmpScaledMixed.lhs
      show leftN₂ * ((twoPosPow q₁ : Nat) : Int) * ((tenNegPow exp : Nat) : Int) = leftN₂ * P
      ring
    have hR1_eq : fourVR m₁ q₁ exp = rightN₁ * P := by
      unfold fourVR cmpScaledMixed.lhs
      show rightN₁ * ((twoPosPow q₁ : Nat) : Int) * ((tenNegPow exp : Nat) : Int) = rightN₁ * P
      ring
    have hR2_eq : fourVR m₂ q₁ exp = rightN₂ * P := by
      unfold fourVR cmpScaledMixed.lhs
      show rightN₂ * ((twoPosPow q₁ : Nat) : Int) * ((tenNegPow exp : Nat) : Int) = rightN₂ * P
      ring
    have hU_eq_clear : fourU sig q₁ exp = U := by
      unfold fourU cmpScaledMixed.rhs
      show (4 * (sig : Int)) * ((tenPosPow exp : Nat) : Int) * ((twoNegPow q₁ : Nat) : Int) = U
      ring
    -- Positivity.
    have hP_pos : 0 < P := twoPos_tenNeg_pos_Int q₁ exp
    -- Extract bounds: l_i · P ≤ U ≤ r_i · P, plus parity at equality.
    have h_l1_le : leftN₁ * P ≤ U := by
      obtain ⟨hleft, _⟩ := h₁
      rcases hleft with hlt | ⟨heq, _⟩
      · exact Int.le_of_lt (by rw [← hL1_eq, ← hU_eq_clear]; exact hlt)
      · exact Int.le_of_eq (by rw [← hL1_eq, ← hU_eq_clear]; exact heq)
    have h_u_le_r1 : U ≤ rightN₁ * P := by
      obtain ⟨_, hright⟩ := h₁
      rcases hright with hlt | ⟨heq, _⟩
      · exact Int.le_of_lt (by rw [← hR1_eq, ← hU_eq_clear]; exact hlt)
      · exact Int.le_of_eq (by rw [← hR1_eq, ← hU_eq_clear]; exact heq)
    have h_l2_le : leftN₂ * P ≤ U := by
      obtain ⟨hleft, _⟩ := h₂
      rcases hleft with hlt | ⟨heq, _⟩
      · exact Int.le_of_lt (by rw [← hL2_eq, ← hU_eq_clear]; exact hlt)
      · exact Int.le_of_eq (by rw [← hL2_eq, ← hU_eq_clear]; exact heq)
    have h_u_le_r2 : U ≤ rightN₂ * P := by
      obtain ⟨_, hright⟩ := h₂
      rcases hright with hlt | ⟨heq, _⟩
      · exact Int.le_of_lt (by rw [← hR2_eq, ← hU_eq_clear]; exact hlt)
      · exact Int.le_of_eq (by rw [← hR2_eq, ← hU_eq_clear]; exact heq)
    -- Combine: l_2 · P ≤ U ≤ r_1 · P, so leftN₂ ≤ rightN₁.
    -- And l_1 · P ≤ U ≤ r_2 · P, so leftN₁ ≤ rightN₂.
    have h_l2_le_r1 : leftN₂ ≤ rightN₁ := by
      have h_step : leftN₂ * P ≤ rightN₁ * P := Int.le_trans h_l2_le h_u_le_r1
      exact (Int.le_of_mul_le_mul_right (by linarith) hP_pos)
    have h_l1_le_r2 : leftN₁ ≤ rightN₂ := by
      have h_step : leftN₁ * P ≤ rightN₂ * P := Int.le_trans h_l1_le h_u_le_r2
      exact (Int.le_of_mul_le_mul_right (by linarith) hP_pos)
    -- Unfold leftN_i: |m₁ - m₂| ≤ 1 (since leftN_i ∈ {4m_i - 2, 4m_i - 1}, rightN_i = 4m_i + 2).
    -- We show m₁ = m₂ by ruling out m₁ ≠ m₂ via a parity argument.
    by_contra hm_ne
    -- Expand leftN values from h_l2_le_r1 and h_l1_le_r2.
    have h_l2_unfolded :
        (if isIrregular m₂ q₁ = true then 4 * (m₂ : Int) - 1 else 4 * (m₂ : Int) - 2)
          ≤ 4 * (m₁ : Int) + 2 := h_l2_le_r1
    have h_l1_unfolded :
        (if isIrregular m₁ q₁ = true then 4 * (m₁ : Int) - 1 else 4 * (m₁ : Int) - 2)
          ≤ 4 * (m₂ : Int) + 2 := h_l1_le_r2
    -- Derive m₁, m₂ close: |m₁ - m₂| ≤ 1.
    have h_close : (m₂ : Int) ≤ (m₁ : Int) + 1 ∧ (m₁ : Int) ≤ (m₂ : Int) + 1 := by
      refine ⟨?_, ?_⟩
      · by_cases h2_irreg : isIrregular m₂ q₁ = true
        · rw [if_pos h2_irreg] at h_l2_unfolded; omega
        · rw [if_neg h2_irreg] at h_l2_unfolded; omega
      · by_cases h1_irreg : isIrregular m₁ q₁ = true
        · rw [if_pos h1_irreg] at h_l1_unfolded; omega
        · rw [if_neg h1_irreg] at h_l1_unfolded; omega
    obtain ⟨h_m2_le, h_m1_le⟩ := h_close
    have h_diff : m₁ = m₂ + 1 ∨ m₂ = m₁ + 1 := by
      have hne_int : (m₁ : Int) ≠ (m₂ : Int) := by
        intro h; apply hm_ne; exact_mod_cast h
      omega
    -- WLOG m₂ = m₁ + 1 case (the other case is symmetric — swap pairs in the proof).
    -- We handle both cases inline.
    -- The key fact: leftN_other = rightN_self only when both are at the "boundary"
    -- 4m₁ + 2 = 4m₂ - 2 (regular pair 2, m₂ = m₁ + 1). Then U = (4m₁ + 2)·P,
    -- which forces both right-bracket of pair 1 and left-bracket of pair 2 to be tight,
    -- requiring m₁ even AND m₂ even — impossible since m₂ = m₁ + 1.
    rcases h_diff with hm | hm
    · -- m₁ = m₂ + 1. Same argument with roles swapped.
      -- Show isIrregular m₁ q₁ = false, since otherwise irreg gives leftN₁ = 4m₁ - 1
      -- and 4m₁ - 1 = 4m₂ + 3 > 4m₂ + 2 = rightN₂, contradicting h_l1_le_r2.
      have h1_reg : isIrregular m₁ q₁ = false := by
        by_contra h1_irr
        have h1_irr' : isIrregular m₁ q₁ = true := by
          cases hh : isIrregular m₁ q₁ with
          | false => exact absurd hh h1_irr
          | true => rfl
        rw [if_pos h1_irr'] at h_l1_unfolded
        omega
      -- So leftN₁ = 4m₁ - 2 = 4(m₂+1) - 2 = 4m₂ + 2 = rightN₂.
      -- Thus h_l1_le: (4m₂ + 2)*P ≤ U; h_u_le_r2: U ≤ (4m₂ + 2)*P.
      -- So U = (4m₂ + 2)*P, which means both equalities are tight.
      have h_leftN1_val : leftN₁ = 4 * (m₂ : Int) + 2 := by
        show (if isIrregular m₁ q₁ = true then 4 * (m₁ : Int) - 1 else 4 * (m₁ : Int) - 2)
                = 4 * (m₂ : Int) + 2
        rw [if_neg (by rw [h1_reg]; decide)]
        have : (m₁ : Int) = (m₂ : Int) + 1 := by exact_mod_cast hm
        omega
      have h_rightN2_val : rightN₂ = 4 * (m₂ : Int) + 2 := rfl
      -- Now U = leftN₁ * P = rightN₂ * P; specifically equalities:
      -- right of pair 1: U = rightN₁ * P = (4m₁ + 2)*P = (4m₂ + 6)*P. But U ≤ rightN₁*P
      -- and U ≥ leftN₁*P. With h_leftN1_val = 4m₂+2: leftN₁*P = (4m₂+2)*P.
      -- So (4m₂+2)*P ≤ U ≤ (4m₂+6)*P (using rightN₁ = 4m₁+2 = 4m₂+6).
      -- Combined with U ≤ rightN₂*P = (4m₂+2)*P, we get U = (4m₂+2)*P.
      -- Right of pair 2 at U: U = (4m₂+2)*P = rightN₂*P. From h_u_le_r2 it's = case,
      -- requires m₂ % 2 = 0.
      -- Left of pair 1 at U: leftN₁*P = U. From h_l1_le it's = case, requires m₁ % 2 = 0.
      -- Since m₁ = m₂ + 1, both even: contradiction.
      have hU_eq : U = (4 * (m₂ : Int) + 2) * P := by
        have h_LHS : (4 * (m₂ : Int) + 2) * P ≤ U := by
          rw [h_leftN1_val] at h_l1_le; exact h_l1_le
        have h_RHS : U ≤ (4 * (m₂ : Int) + 2) * P := by
          rw [h_rightN2_val] at h_u_le_r2; exact h_u_le_r2
        linarith
      -- From hU_eq and h₂ right bracket (= case requires m₂ even):
      have hm2_even : m₂ % 2 = 0 := by
        have ⟨_, h_r⟩ := h₂
        rcases h_r with hlt | ⟨_, heven⟩
        · rw [hU_eq_clear, hU_eq, hR2_eq, h_rightN2_val] at hlt
          exfalso; linarith
        · exact heven
      -- From hU_eq and h₁ left bracket (= case requires m₁ even):
      have hm1_even : m₁ % 2 = 0 := by
        have ⟨h_l, _⟩ := h₁
        rcases h_l with hlt | ⟨_, heven⟩
        · rw [hU_eq_clear, hU_eq, hL1_eq, h_leftN1_val] at hlt
          exfalso; linarith
        · exact heven
      -- m₁ = m₂ + 1 with both even: impossible.
      omega
    · -- m₂ = m₁ + 1. Symmetric.
      have h2_reg : isIrregular m₂ q₁ = false := by
        by_contra h2_irr
        have h2_irr' : isIrregular m₂ q₁ = true := by
          cases hh : isIrregular m₂ q₁ with
          | false => exact absurd hh h2_irr
          | true => rfl
        rw [if_pos h2_irr'] at h_l2_unfolded
        omega
      have h_leftN2_val : leftN₂ = 4 * (m₁ : Int) + 2 := by
        show (if isIrregular m₂ q₁ = true then 4 * (m₂ : Int) - 1 else 4 * (m₂ : Int) - 2)
                = 4 * (m₁ : Int) + 2
        rw [if_neg (by rw [h2_reg]; decide)]
        have : (m₂ : Int) = (m₁ : Int) + 1 := by exact_mod_cast hm
        omega
      have h_rightN1_val : rightN₁ = 4 * (m₁ : Int) + 2 := rfl
      have hU_eq : U = (4 * (m₁ : Int) + 2) * P := by
        have h_LHS : (4 * (m₁ : Int) + 2) * P ≤ U := by
          rw [h_leftN2_val] at h_l2_le; exact h_l2_le
        have h_RHS : U ≤ (4 * (m₁ : Int) + 2) * P := by
          rw [h_rightN1_val] at h_u_le_r1; exact h_u_le_r1
        linarith
      have hm1_even : m₁ % 2 = 0 := by
        have ⟨_, h_r⟩ := h₁
        rcases h_r with hlt | ⟨_, heven⟩
        · rw [hU_eq_clear, hU_eq, hR1_eq, h_rightN1_val] at hlt
          exfalso; linarith
        · exact heven
      have hm2_even : m₂ % 2 = 0 := by
        have ⟨h_l, _⟩ := h₂
        rcases h_l with hlt | ⟨_, heven⟩
        · rw [hU_eq_clear, hU_eq, hL2_eq, h_leftN2_val] at hlt
          exfalso; linarith
        · exact heven
      omega
  · -- q₁ ≠ q₂ case: WLOG q₁ < q₂ (handle q₁ > q₂ by swapping the pairs).
    exfalso
    rcases Int.lt_or_gt_of_ne hq_eq with h_lt | h_gt
    · exact inRoundingInterval_uniq_lt sig exp m₁ m₂ q₁ q₂ h_dec₁ h_dec₂ h₁ h₂ h_lt
    · -- q₁ > q₂: swap the pairs and apply the helper.
      exact inRoundingInterval_uniq_lt sig exp m₂ m₁ q₂ q₁ h_dec₂ h_dec₁ h₂ h₁ h_gt

end Srtfp

/- Clinger Decimal→Float correctness — runtime bridge (M4).

   This module discharges `DecodeOfDecimalBridge`: for a non-overflow
   nonzero `Decimal d`, `decode (ofDecimal d) = decodedAbs d.sign
   d.significand d.exponent`.

   The proof case-splits on the same if-tree as `ofDecimal` (= `decodedAbs`)
   and at each leaf applies the `fromBits_proj` axiom to recover the
   bit-field projections after the `Float.toBits_ofBits` round-trip.

   The case-split mirrors `decodedAbsAB`'s if-tree (see `Base.lean`). -/

import Srtfp.Proofs.Clinger.Base
import Srtfp.Proofs.Clinger.FindBinaryExp
import Srtfp.Float.RuntimeAxiom
import Srtfp.Tactics

namespace Srtfp.Clinger

open Srtfp.Float
open Srtfp

/-! ## Bit-range bounds -/

private theorem zero_lt_2pow52 : (0 : Nat) < 2 ^ 52 := by decide

private theorem one_shl_52_lt_2pow52_false : ¬ ((1 : Nat) <<< 52 < 2 ^ 52) := by decide

private theorem one_lt_2048 : (1 : Nat) < 2048 := by decide

/-! ## decode (fromBits ...) lemmas

These wrap the `fromBits_proj` axiom for the specific bit-field
shapes that `decimalToFloat` produces. -/

/-- `decode (fromBits sign biasedExp mantissa) = ⟨sign, mantissa, -1074⟩`
when `biasedExp = 0` (subnormal/zero). -/
private theorem decode_fromBits_zero
    (sign : Bool) (mantissa : Nat) (h_m : mantissa < 2 ^ 52) :
    decode (fromBits sign 0 mantissa) = ⟨sign, mantissa, -1074⟩ := by
  unfold decode
  obtain ⟨h_sign, h_be, h_man⟩ := fromBits_proj sign 0 mantissa (by decide) h_m (by omega)
  rw [h_sign, h_be, h_man]
  rfl

/-- `decode (fromBits sign biasedExp mantissa) = ⟨sign, mantissa + 2^52,
biasedExp - 1023 - 52⟩` when `biasedExp ≥ 1` (normal). -/
private theorem decode_fromBits_normal
    (sign : Bool) (biasedExp : Nat) (mantissa : Nat)
    (h_be_lo : 1 ≤ biasedExp) (h_be_hi : biasedExp < 2048) (h_m : mantissa < 2 ^ 52)
    (h_nan : biasedExp = 2047 → mantissa = 0) :
    decode (fromBits sign biasedExp mantissa)
      = ⟨sign, mantissa + (1 <<< 52), (biasedExp : Int) - 1023 - 52⟩ := by
  unfold decode
  obtain ⟨h_sign, h_be, h_man⟩ := fromBits_proj sign biasedExp mantissa h_be_hi h_m h_nan
  rw [h_sign, h_be, h_man]
  have h_ne : biasedExp ≠ 0 := by omega
  rw [if_neg h_ne]

/-! ## Inline reductions of `decimalToFloat` -/

/-- `infOfSign` reduces. -/
private theorem decode_infOfSign (sign : Bool) :
    decode (fromBits sign 2047 0) = ⟨sign, 0 + (1 <<< 52), (2047 : Int) - 1023 - 52⟩ :=
  decode_fromBits_normal sign 2047 0 (by decide) (by decide) zero_lt_2pow52 (by omega)

/-- `zeroOfSign` reduces. -/
private theorem decode_zeroOfSign (sign : Bool) :
    decode (fromBits sign 0 0) = ⟨sign, 0, -1074⟩ :=
  decode_fromBits_zero sign 0 zero_lt_2pow52

/-! ## Per-branch bridge lemmas

After fixing concrete `(a, b)` via `exp ≥ 0`, each leaf of
`decimalToFloat`'s if-tree produces a `fromBits` whose decode matches
the corresponding `decodedAbsAB` leaf. -/

/-- The normal no-carry leaf: `m < 2^53` and `decodedAbsAB` = `⟨sign, m,
e - 52⟩`. The Float-side produces `fromBits sign (e + 1023).toNat (m -
2^52)`. Their decodes match when `m ≥ 2^52` (which is guaranteed by
the rounding bounds — but we phrase the lemma to handle both regular
and irregular sub-cases.

For the regular case (m ≠ 2^52 ∨ q = -1074), `m ∈ [2^52, 2^53)` so
`m - 2^52 < 2^52` and `m = (m - 2^52) + 2^52`.

For the irregular no-carry case, `m = 2^52` exactly, so
`m - 2^52 = 0`. -/
private theorem decode_normal_leaf_eq
    (sign : Bool) (e : Int) (m : Nat)
    (h_m_lo : 2 ^ 52 ≤ m) (h_m_hi : m < 2 ^ 53)
    (h_e_lo : e ≥ -1022) (h_e_hi : e ≤ 1023) :
    decode (fromBits sign (e + 1023).toNat (m - 2 ^ 52))
      = ⟨sign, m, e - 52⟩ := by
  have h_be_lo : 1 ≤ (e + 1023).toNat := by
    have : 1 ≤ (e + 1023) := by omega
    omega
  have h_be_hi : (e + 1023).toNat < 2048 := by
    have h1 : (e + 1023) ≤ 2046 := by omega
    have h2 : (0 : Int) ≤ (e + 1023) := by omega
    omega
  have h_m_diff : m - 2 ^ 52 < 2 ^ 52 := by
    have : 2 * 2 ^ 52 = 2 ^ 53 := by decide
    omega
  rw [decode_fromBits_normal sign (e + 1023).toNat (m - 2 ^ 52) h_be_lo h_be_hi h_m_diff
      (by omega)]
  -- Need: ⟨sign, (m - 2^52) + 1 <<< 52, ((e + 1023).toNat : Int) - 1023 - 52⟩ = ⟨sign, m, e - 52⟩
  have h_m_eq : m - 2 ^ 52 + (1 <<< 52) = m := by
    have h_shl : (1 : Nat) <<< 52 = 2 ^ 52 := by decide
    rw [h_shl]
    omega
  have h_e_eq : ((e + 1023).toNat : Int) - 1023 - 52 = e - 52 := by
    have h1 : ((e + 1023).toNat : Int) = e + 1023 := by
      apply Int.toNat_of_nonneg
      omega
    omega
  rw [h_m_eq, h_e_eq]

/-- Carry leaf: `(2^52, e + 1 - 52)` via `fromBits sign (e' + 1023).toNat 0`. -/
private theorem decode_carry_leaf_eq
    (sign : Bool) (e : Int)
    (h_e_lo : e ≥ -1022) (h_e_hi : e + 1 ≤ 1023) :
    decode (fromBits sign ((e + 1) + 1023).toNat 0)
      = ⟨sign, 1 <<< 52, (e + 1) - 52⟩ := by
  have h_be_lo : 1 ≤ ((e + 1) + 1023).toNat := by
    have : 1 ≤ (e + 1 + 1023) := by omega
    omega
  have h_be_hi : ((e + 1) + 1023).toNat < 2048 := by
    have h1 : (e + 1 + 1023) ≤ 2046 := by omega
    have h2 : (0 : Int) ≤ (e + 1 + 1023) := by omega
    omega
  rw [decode_fromBits_normal sign ((e + 1) + 1023).toNat 0 h_be_lo h_be_hi zero_lt_2pow52
      (fun _ => rfl)]
  have h_e_eq : (((e + 1) + 1023).toNat : Int) - 1023 - 52 = (e + 1) - 52 := by
    have h1 : (((e + 1) + 1023).toNat : Int) = e + 1 + 1023 := by
      apply Int.toNat_of_nonneg
      omega
    omega
  rw [h_e_eq]
  simp []

/-- Subnormal `m ≥ 2^52` leaf: `fromBits sign 1 (m - 2^52)` decodes to
`⟨sign, m, -1074⟩` (which is correct because the normal exponent
`q = (1 : Int) - 1023 - 52 = -1074` matches the subnormal q). -/
private theorem decode_subnormal_normal_boundary_eq
    (sign : Bool) (m : Nat) (h_lo : 2 ^ 52 ≤ m) (h_hi : m < 2 ^ 53) :
    decode (fromBits sign 1 (m - 2 ^ 52)) = ⟨sign, m, -1074⟩ := by
  have h_m_diff : m - 2 ^ 52 < 2 ^ 52 := by
    have : 2 * 2 ^ 52 = 2 ^ 53 := by decide
    omega
  rw [decode_fromBits_normal sign 1 (m - 2 ^ 52) (by decide) (by decide) h_m_diff (by omega)]
  -- ⟨sign, m - 2^52 + 1 <<< 52, 1 - 1023 - 52⟩ = ⟨sign, m, -1074⟩
  have h_m_eq : m - 2 ^ 52 + (1 <<< 52) = m := by
    have h_shl : (1 : Nat) <<< 52 = 2 ^ 52 := by decide
    rw [h_shl]
    omega
  have h_e_eq : ((1 : Nat) : Int) - 1023 - 52 = -1074 := by decide
  rw [h_m_eq, h_e_eq]

/-- Subnormal `m < 2^52` leaf: `fromBits sign 0 m` decodes to `⟨sign, m,
-1074⟩`. -/
private theorem decode_subnormal_low_eq
    (sign : Bool) (m : Nat) (h_m : m < 2 ^ 52) :
    decode (fromBits sign 0 m) = ⟨sign, m, -1074⟩ :=
  decode_fromBits_zero sign m h_m

/-! ## Bound facts on `roundNearestEven` for the bridge

`roundNearestEven` is at least `num / denom`. In the normal no-carry
branch, `findBinaryExp` guarantees `2^52 · denom ≤ num`, so
`m_round ≥ 2^52`. The upper bound `m_round < 2^53` comes from the
`h_carry : ¬ m_round ≥ 2^53` hypothesis. -/

/-- Normal-branch lower bound: `m_round ≥ 2^52`. -/
private theorem normal_round_ge_2pow52
    (a b : Nat) (e : Int)
    (ha : 0 < a) (hb : 0 < b)
    (he_def : e = findBinaryExp a b) :
    2 ^ 52 ≤ roundNearestEven (scaleByPow2 a b (52 - e)).1
                              (scaleByPow2 a b (52 - e)).2 := by
  have h_leBy2e : leBy2e a b e = true := he_def ▸ findBinaryExp_le a b ha hb
  have h_bound := clinger_num_ge_2pow52_denom a b e ha hb h_leBy2e
  simp only at h_bound
  have hdenom_pos : 0 < (scaleByPow2 a b (52 - e)).2 := scaleByPow2_denom_pos hb
  have h_floor : 2 ^ 52 ≤ (scaleByPow2 a b (52 - e)).1 / (scaleByPow2 a b (52 - e)).2 := by
    rw [Nat.le_div_iff_mul_le hdenom_pos]
    exact h_bound
  exact Nat.le_trans h_floor
    (roundNearestEven_ge_floor (scaleByPow2 a b (52 - e)).1
                                (scaleByPow2 a b (52 - e)).2)

/-- Subnormal-branch upper bound: `m_round ≤ 2^52`.

In the subnormal branch (`e < -1022`), `findBinaryExp a b < -1022`,
so by `leBy2e (e+1)` we have `a < b · 2^(e+1)`. Scaling by 2^1074:
`num = a · 2^1074 ≤ ... · 2^(1074 + e + 1)`. With `e + 1 ≤ -1022`,
this gives `num < b · 2^52 = 2^52 · denom`. So `m_round ≤ num/denom + 1 ≤ 2^52`. -/
private theorem subnormal_round_le_2pow52
    (a b : Nat) (e : Int)
    (ha : 0 < a) (hb : 0 < b)
    (h_subnormal : ¬ e ≥ -1022)
    (he_def : e = findBinaryExp a b) :
    roundNearestEven (scaleByPow2 a b 1074).1 (scaleByPow2 a b 1074).2 ≤ 2 ^ 52 := by
  -- From findBinaryExp upper bound: a < b · 2^(e+1) (or equivalent form).
  have hupper := findBinaryExp_lt a b ha hb
  simp only at hupper
  rw [← he_def] at hupper
  have he_lt : e < -1022 := by omega
  have he1 : e + 1 ≤ -1022 := by omega
  have h_neg_e1_pos : -(e + 1) ≥ 1022 := by omega
  have h_neg_e1_nn : (0 : Int) ≤ -(e + 1) := by omega
  have h_e1_nn : ¬ (e + 1 ≥ 0) := by omega
  rw [if_neg h_e1_nn] at hupper
  -- hupper : a * 2 ^ (-(e + 1)).toNat < b
  -- We want: num ≤ 2^52 * denom, where num = (scaleByPow2 a b 1074).1, denom = .2.
  -- For scale 1074 ≥ 0 (since 1074 > 0), scaleByPow2 a b 1074 = (a * 2^1074, b).
  -- So num = a * 2^1074, denom = b.
  have h_scale : scaleByPow2 a b 1074 = (a * 2 ^ 1074, b) := by
    unfold scaleByPow2
    rw [if_pos (by decide : (1074 : Int) ≥ 0)]
    show ((a * 2 ^ (1074 : Int).toNat, b) : Nat × Nat) = (a * 2 ^ 1074, b)
    have : (1074 : Int).toNat = 1074 := by decide
    rw [this]
  rw [h_scale]
  show roundNearestEven (a * 2 ^ 1074) b ≤ 2 ^ 52
  -- num = a · 2^1074, want: num < 2^52 · b, i.e. a · 2^1074 < 2^52 · b.
  -- From hupper: a · 2^((-(e+1)).toNat) < b.
  -- Multiply both sides by 2^(1074 - (-(e+1)).toNat):
  -- a · 2^1074 = a · 2^((-(e+1)).toNat) · 2^(1074 - (-(e+1)).toNat) < b · 2^(1074 - (-(e+1)).toNat)
  -- Want: 2^(1074 - (-(e+1)).toNat) ≤ 2^52, i.e., 1074 - (-(e+1)).toNat ≤ 52, i.e., (-(e+1)).toNat ≥ 1022.
  have h_neg_e1_nat : (-(e + 1)).toNat ≥ 1022 := by
    have h1 : ((-(e + 1)).toNat : Int) = -(e + 1) := Int.toNat_of_nonneg h_neg_e1_nn
    omega
  -- Two cases on whether (-(e+1)).toNat ≤ 1074 or > 1074.
  have h_num_lt_2pow52 : a * 2 ^ 1074 < 2 ^ 52 * b := by
    by_cases h_le : (-(e + 1)).toNat ≤ 1074
    · -- Standard case: multiply hupper by 2^(1074 - (-(e+1)).toNat).
      have h_diff : 1074 - (-(e + 1)).toNat ≤ 52 := by omega
      have h_split : (1074 : Nat) = (-(e + 1)).toNat + (1074 - (-(e + 1)).toNat) := by omega
      have h_a2pow :
          a * 2 ^ 1074 = (a * 2 ^ (-(e + 1)).toNat) * 2 ^ (1074 - (-(e + 1)).toNat) := by
        have h1 :
            a * 2 ^ 1074 = a * 2 ^ ((-(e + 1)).toNat + (1074 - (-(e + 1)).toNat)) := by
          rw [← h_split]
        rw [h1, Nat.pow_add, ← Nat.mul_assoc]
      have h_num_lt : a * 2 ^ 1074 < b * 2 ^ (1074 - (-(e + 1)).toNat) := by
        rw [h_a2pow]
        exact (Nat.mul_lt_mul_right (Nat.pow_pos (by decide : 0 < (2 : Nat)))).mpr hupper
      have h_2pow_le : 2 ^ (1074 - (-(e + 1)).toNat) ≤ 2 ^ 52 :=
        Nat.pow_le_pow_right (by decide : 1 ≤ 2) h_diff
      have h_mul_le : b * 2 ^ (1074 - (-(e + 1)).toNat) ≤ b * 2 ^ 52 :=
        Nat.mul_le_mul_left b h_2pow_le
      have : b * 2 ^ 52 = 2 ^ 52 * b := Nat.mul_comm _ _
      omega
    · -- Pathological case: (-(e+1)).toNat > 1074. Then 2^((-(e+1)).toNat) > 2^1074.
      -- a * 2^1074 ≤ a * 2^((-(e+1)).toNat) < b ≤ 2^52 * b.
      have h_lt : 1074 < (-(e + 1)).toNat := Nat.lt_of_not_le h_le
      have h_le_1074 : (1074 : Nat) ≤ (-(e + 1)).toNat := Nat.le_of_lt h_lt
      have h_pow_le : (2 : Nat) ^ 1074 ≤ 2 ^ ((-(e + 1)).toNat) :=
        Nat.pow_le_pow_right (by decide : 1 ≤ 2) h_le_1074
      have h_lhs_le : a * 2 ^ 1074 ≤ a * 2 ^ ((-(e + 1)).toNat) :=
        Nat.mul_le_mul_left a h_pow_le
      have h_b_lt : a * 2 ^ ((-(e + 1)).toNat) < b := hupper
      have h_b_le_2pow52_b : b ≤ 2 ^ 52 * b := Nat.le_mul_of_pos_left _ (Nat.pow_pos (by decide))
      omega
  -- Now: m_round ≤ (a · 2^1074) / b + 1 ≤ ⌊(2^52 · b) / b⌋ + 1 = 2^52 + 1.
  -- Wait — but we need m_round ≤ 2^52, not 2^52 + 1. Need to show the +1 doesn't matter.
  -- Actually: roundNearestEven (a · 2^1074) b ≤ (a · 2^1074) / b + 1.
  -- We have (a · 2^1074) < 2^52 · b, so (a · 2^1074) / b ≤ 2^52 - 1, so m_round ≤ 2^52.
  have h_div : (a * 2 ^ 1074) / b ≤ 2 ^ 52 - 1 := by
    rw [Nat.div_le_iff_le_mul_add_pred hb]
    have : 2 ^ 52 * b = (2 ^ 52 - 1 + 1) * b := by
      have h1 : (2 ^ 52 - 1 + 1 : Nat) = 2 ^ 52 := by decide
      rw [h1]
    omega
  have h_ceil := roundNearestEven_le_ceil (a * 2 ^ 1074) b
  omega

/-! ## Decode of `decimalToFloat` matches `decodedAbsAB`

The bridge follows by walking the parallel if-trees in `decimalToFloat`
(producing a `Float`) and `decodedAbsAB` (producing a `Decoded`), and
applying the per-leaf `decode_*_eq` lemmas. -/

set_option maxHeartbeats 800000 in
/-- For nonzero `sig` and concrete `(a, b)`, `decode (decimalToFloat-body) =
decodedAbsAB`, conditional on `IsFiniteAbs` ruling out overflows. -/
private theorem bridge_AB
    (sign : Bool) (_sig : Nat) (_exp : Int) (a b : Nat)
    (ha_pos : 0 < a) (hb_pos : 0 < b)
    (h_finite : (decodedAbsAB sign a b).q ≤ 971) :
    decode
      (let e := findBinaryExp a b
       if e > 1023 then fromBits sign 2047 0
       else if e ≥ -1022 then
         let m := roundNearestEven (scaleByPow2 a b (52 - e)).1
                                    (scaleByPow2 a b (52 - e)).2
         if m ≥ 2 ^ 53 then
           let e' := e + 1
           if e' > 1023 then fromBits sign 2047 0
           else fromBits sign (e' + 1023).toNat 0
         else fromBits sign (e + 1023).toNat (m - 2 ^ 52)
       else
         let m := roundNearestEven (scaleByPow2 a b 1074).1
                                    (scaleByPow2 a b 1074).2
         if m = 0 then fromBits sign 0 0
         else if m ≥ 2 ^ 52 then fromBits sign 1 (m - 2 ^ 52)
         else fromBits sign 0 m)
    = decodedAbsAB sign a b := by
  -- Mirror the dispatch_AB structure.
  by_cases h_over : findBinaryExp a b > 1023
  · exfalso
    have h_eq : decodedAbsAB sign a b = (⟨sign, 0, 1024⟩ : Decoded) := by
      unfold decodedAbsAB; rw [if_pos h_over]
    rw [h_eq] at h_finite
    exact absurd (show (1024 : Int) ≤ 971 from h_finite) (by decide)
  · by_cases h_normal : findBinaryExp a b ≥ -1022
    · -- Normal branch.
      by_cases h_carry :
          roundNearestEven (scaleByPow2 a b (52 - findBinaryExp a b)).1
                            (scaleByPow2 a b (52 - findBinaryExp a b)).2 ≥ 2 ^ 53
      · -- Carry sub-branch.
        by_cases h_over2 : findBinaryExp a b + 1 > 1023
        · -- Carry-overflow: ruled out by h_finite.
          exfalso
          have h_eq : decodedAbsAB sign a b = (⟨sign, 0, 1024⟩ : Decoded) := by
            unfold decodedAbsAB
            rw [if_neg h_over, if_pos h_normal, if_pos h_carry, if_pos h_over2]
          rw [h_eq] at h_finite
          exact absurd (show (1024 : Int) ≤ 971 from h_finite) (by decide)
        · -- Carry-no-overflow leaf.
          have h_eq : decodedAbsAB sign a b =
              (⟨sign, 1 <<< 52, findBinaryExp a b + 1 - 52⟩ : Decoded) := by
            unfold decodedAbsAB
            rw [if_neg h_over, if_pos h_normal, if_pos h_carry, if_neg h_over2]
          rw [h_eq]
          simp only [if_neg h_over, if_pos h_normal, if_pos h_carry, if_neg h_over2]
          exact decode_carry_leaf_eq sign (findBinaryExp a b) h_normal (by omega)
      · -- No-carry leaf.
        have h_eq : decodedAbsAB sign a b =
            (⟨sign, roundNearestEven (scaleByPow2 a b (52 - findBinaryExp a b)).1
                                      (scaleByPow2 a b (52 - findBinaryExp a b)).2,
              findBinaryExp a b - 52⟩ : Decoded) := by
          unfold decodedAbsAB
          rw [if_neg h_over, if_pos h_normal, if_neg h_carry]
        rw [h_eq]
        simp only [if_neg h_over, if_pos h_normal, if_neg h_carry]
        -- Need decode (fromBits sign (e + 1023).toNat (m - 2^52)) = ⟨sign, m, e - 52⟩
        -- where m = roundNearestEven _ _, m ∈ [2^52, 2^53).
        have h_m_lo : 2 ^ 52 ≤ roundNearestEven (scaleByPow2 a b (52 - findBinaryExp a b)).1
                                                (scaleByPow2 a b (52 - findBinaryExp a b)).2 :=
          normal_round_ge_2pow52 a b _ ha_pos hb_pos rfl
        have h_m_hi : roundNearestEven (scaleByPow2 a b (52 - findBinaryExp a b)).1
                                        (scaleByPow2 a b (52 - findBinaryExp a b)).2 < 2 ^ 53 := by
          omega
        exact decode_normal_leaf_eq sign (findBinaryExp a b) _ h_m_lo h_m_hi h_normal
                (by omega)
    · -- Subnormal branch.
      by_cases h_zero : roundNearestEven (scaleByPow2 a b 1074).1
                                          (scaleByPow2 a b 1074).2 = 0
      · -- m = 0 leaf.
        have h_eq : decodedAbsAB sign a b = (⟨sign, 0, -1074⟩ : Decoded) := by
          unfold decodedAbsAB
          rw [if_neg h_over, if_neg h_normal, if_pos h_zero]
        rw [h_eq]
        simp only [if_neg h_over, if_neg h_normal, if_pos h_zero]
        exact decode_fromBits_zero sign 0 zero_lt_2pow52
      · by_cases h_nb : roundNearestEven (scaleByPow2 a b 1074).1
                                          (scaleByPow2 a b 1074).2 ≥ 2 ^ 52
        · -- m ≥ 2^52 leaf. From subnormal_round_le_2pow52, m_round ≤ 2^52, so m_round = 2^52.
          have h_eq : decodedAbsAB sign a b =
              (⟨sign, roundNearestEven (scaleByPow2 a b 1074).1
                                        (scaleByPow2 a b 1074).2, -1074⟩ : Decoded) := by
            unfold decodedAbsAB
            rw [if_neg h_over, if_neg h_normal, if_neg h_zero, if_pos h_nb]
          rw [h_eq]
          simp only [if_neg h_over, if_neg h_normal, if_neg h_zero, if_pos h_nb]
          have h_m_le : roundNearestEven (scaleByPow2 a b 1074).1
                                          (scaleByPow2 a b 1074).2 ≤ 2 ^ 52 :=
            subnormal_round_le_2pow52 a b _ ha_pos hb_pos h_normal rfl
          have h_m_hi : roundNearestEven (scaleByPow2 a b 1074).1
                                          (scaleByPow2 a b 1074).2 < 2 ^ 53 := by
            have : 2 ^ 52 < 2 ^ 53 := by decide
            omega
          exact decode_subnormal_normal_boundary_eq sign _ h_nb h_m_hi
        · -- m < 2^52 leaf.
          have h_eq : decodedAbsAB sign a b =
              (⟨sign, roundNearestEven (scaleByPow2 a b 1074).1
                                        (scaleByPow2 a b 1074).2, -1074⟩ : Decoded) := by
            unfold decodedAbsAB
            rw [if_neg h_over, if_neg h_normal, if_neg h_zero, if_neg h_nb]
          rw [h_eq]
          simp only [if_neg h_over, if_neg h_normal, if_neg h_zero, if_neg h_nb]
          have h_m_lt : roundNearestEven (scaleByPow2 a b 1074).1
                                          (scaleByPow2 a b 1074).2 < 2 ^ 52 := by omega
          exact decode_subnormal_low_eq sign _ h_m_lt

/-! ## The bridge -/

/-- **The runtime bridge** (`DecodeOfDecimalBridge`). -/
theorem decode_of_decimal_bridge : DecodeOfDecimalBridge := by
  intro d h_finite
  unfold ofDecimal decimalToFloat
  by_cases h_sig : d.significand = 0
  · -- Zero case.
    rw [if_pos h_sig]
    have h_decode : decodedAbs d.sign d.significand d.exponent = ⟨d.sign, 0, -1074⟩ := by
      rw [h_sig, decodedAbs_zero]
    rw [h_decode]
    show decode (fromBits d.sign 0 0) = ⟨d.sign, 0, -1074⟩
    exact decode_fromBits_zero d.sign 0 zero_lt_2pow52
  · -- Nonzero case.
    rw [if_neg h_sig]
    -- Now we need to mirror decodedAbs structure on `bridge_AB`.
    by_cases hexp : d.exponent ≥ 0
    · have h_pair :
          (if d.exponent ≥ 0 then (d.significand * 10 ^ d.exponent.toNat, 1)
            else (d.significand, 10 ^ (-d.exponent).toNat))
            = (d.significand * 10 ^ d.exponent.toNat, 1) := if_pos hexp
      rw [h_pair]
      have ha_pos : 0 < d.significand * 10 ^ d.exponent.toNat :=
        Nat.mul_pos (Nat.pos_of_ne_zero h_sig)
                    (Nat.pow_pos (by decide : 0 < (10 : Nat)))
      have hb_pos : (0 : Nat) < 1 := by decide
      have h_decode_eq : decodedAbs d.sign d.significand d.exponent =
                          decodedAbsAB d.sign (d.significand * 10 ^ d.exponent.toNat) 1 :=
        decodedAbs_eq_decodedAbsAB_pos d.sign d.significand d.exponent h_sig hexp
      rw [h_decode_eq]
      rw [h_decode_eq] at h_finite
      exact bridge_AB d.sign d.significand d.exponent _ _ ha_pos hb_pos h_finite
    · have hexp' : d.exponent < 0 := Int.not_le.mp hexp
      have h_pair :
          (if d.exponent ≥ 0 then (d.significand * 10 ^ d.exponent.toNat, 1)
            else (d.significand, 10 ^ (-d.exponent).toNat))
            = (d.significand, 10 ^ (-d.exponent).toNat) := if_neg hexp
      rw [h_pair]
      have ha_pos : 0 < d.significand := Nat.pos_of_ne_zero h_sig
      have hb_pos : 0 < (10 : Nat) ^ (-d.exponent).toNat :=
        Nat.pow_pos (by decide : 0 < (10 : Nat))
      have h_decode_eq : decodedAbs d.sign d.significand d.exponent =
                          decodedAbsAB d.sign d.significand (10 ^ (-d.exponent).toNat) :=
        decodedAbs_eq_decodedAbsAB_neg d.sign d.significand d.exponent h_sig hexp
      rw [h_decode_eq]
      rw [h_decode_eq] at h_finite
      exact bridge_AB d.sign d.significand d.exponent _ _ ha_pos hb_pos h_finite


/-! ## Overflow ⇒ `±∞`, and `IsFiniteAbs` from a finite round-trip

The bridge above handles the *finite* leaves. The complementary fact —
an overflow (`¬ IsFiniteAbs`) lands exactly on the `±∞` bit pattern —
lets any statement that assumes a bit-level round-trip to a *finite*
float drop its `IsFiniteAbs` side conditions entirely
(`isFiniteAbs_of_roundtrip`). -/

/-- An overflow (`¬ IsFiniteAbs`) sends the `decimalToFloat` body to `±∞`. -/
private theorem overflow_AB
    (sign : Bool) (a b : Nat)
    (h_not : ¬ ((decodedAbsAB sign a b).q ≤ 971)) :
    (let e := findBinaryExp a b
     if e > 1023 then fromBits sign 2047 0
     else if e ≥ -1022 then
       let m := roundNearestEven (scaleByPow2 a b (52 - e)).1
                                  (scaleByPow2 a b (52 - e)).2
       if m ≥ 2 ^ 53 then
         let e' := e + 1
         if e' > 1023 then fromBits sign 2047 0
         else fromBits sign (e' + 1023).toNat 0
       else fromBits sign (e + 1023).toNat (m - 2 ^ 52)
     else
       let m := roundNearestEven (scaleByPow2 a b 1074).1
                                  (scaleByPow2 a b 1074).2
       if m = 0 then fromBits sign 0 0
       else if m ≥ 2 ^ 52 then fromBits sign 1 (m - 2 ^ 52)
       else fromBits sign 0 m)
    = fromBits sign 2047 0 := by
  by_cases h_over : findBinaryExp a b > 1023
  · simp only [if_pos h_over]
  · by_cases h_normal : findBinaryExp a b ≥ -1022
    · by_cases h_carry : roundNearestEven (scaleByPow2 a b (52 - findBinaryExp a b)).1
                          (scaleByPow2 a b (52 - findBinaryExp a b)).2 ≥ 2 ^ 53
      · by_cases h_over2 : findBinaryExp a b + 1 > 1023
        · simp only [if_neg h_over, if_pos h_normal, if_pos h_carry, if_pos h_over2]
        · exfalso
          apply h_not
          have h_eq : decodedAbsAB sign a b
              = (⟨sign, 1 <<< 52, findBinaryExp a b + 1 - 52⟩ : Decoded) := by
            unfold decodedAbsAB
            rw [if_neg h_over, if_pos h_normal, if_pos h_carry, if_neg h_over2]
          rw [h_eq]
          show findBinaryExp a b + 1 - 52 ≤ 971
          omega
      · exfalso
        apply h_not
        have h_eq : decodedAbsAB sign a b
            = (⟨sign, roundNearestEven (scaleByPow2 a b (52 - findBinaryExp a b)).1
                                        (scaleByPow2 a b (52 - findBinaryExp a b)).2,
                findBinaryExp a b - 52⟩ : Decoded) := by
          unfold decodedAbsAB
          rw [if_neg h_over, if_pos h_normal, if_neg h_carry]
        rw [h_eq]
        show findBinaryExp a b - 52 ≤ 971
        omega
    · -- Subnormal branch: every leaf has `q = -1074`.
      exfalso
      apply h_not
      by_cases h_zero : roundNearestEven (scaleByPow2 a b 1074).1 (scaleByPow2 a b 1074).2 = 0
      · have h_eq : decodedAbsAB sign a b = (⟨sign, 0, -1074⟩ : Decoded) := by
          unfold decodedAbsAB
          rw [if_neg h_over, if_neg h_normal, if_pos h_zero]
        rw [h_eq]
        show (-1074 : Int) ≤ 971
        omega
      · by_cases h_nb : roundNearestEven (scaleByPow2 a b 1074).1 (scaleByPow2 a b 1074).2 ≥ 2 ^ 52
        · have h_eq : decodedAbsAB sign a b
              = (⟨sign, roundNearestEven (scaleByPow2 a b 1074).1 (scaleByPow2 a b 1074).2,
                  -1074⟩ : Decoded) := by
            unfold decodedAbsAB
            rw [if_neg h_over, if_neg h_normal, if_neg h_zero, if_pos h_nb]
          rw [h_eq]
          show (-1074 : Int) ≤ 971
          omega
        · have h_eq : decodedAbsAB sign a b
              = (⟨sign, roundNearestEven (scaleByPow2 a b 1074).1 (scaleByPow2 a b 1074).2,
                  -1074⟩ : Decoded) := by
            unfold decodedAbsAB
            rw [if_neg h_over, if_neg h_normal, if_neg h_zero, if_neg h_nb]
          rw [h_eq]
          show (-1074 : Int) ≤ 971
          omega

/-- Overflowing inputs produce exactly `±∞`. -/
theorem decimalToFloat_overflow_inf (sign : Bool) (sig : Nat) (exp : Int)
    (h_sig : sig ≠ 0)
    (h_not : ¬ IsFiniteAbs sign sig exp) :
    decimalToFloat sign sig exp = fromBits sign 2047 0 := by
  unfold IsFiniteAbs at h_not
  unfold decimalToFloat
  rw [if_neg h_sig]
  by_cases hexp : exp ≥ 0
  · rw [decodedAbs_eq_decodedAbsAB_pos sign sig exp h_sig hexp] at h_not
    have h_pair : (if exp ≥ 0 then (sig * 10 ^ exp.toNat, 1)
        else (sig, 10 ^ (-exp).toNat)) = (sig * 10 ^ exp.toNat, 1) := if_pos hexp
    rw [h_pair]
    exact overflow_AB sign _ _ h_not
  · rw [decodedAbs_eq_decodedAbsAB_neg sign sig exp h_sig hexp] at h_not
    have h_pair : (if exp ≥ 0 then (sig * 10 ^ exp.toNat, 1)
        else (sig, 10 ^ (-exp).toNat)) = (sig, 10 ^ (-exp).toNat) := if_neg hexp
    rw [h_pair]
    exact overflow_AB sign _ _ h_not

/-- `±∞` is not finite, at the bit level. -/
theorem isFiniteBits_fromBits_inf (sign : Bool) :
    isFiniteBits (fromBits sign 2047 0) = false := by
  obtain ⟨_, h_be, _⟩ := fromBits_proj sign 2047 0 (by decide) (by decide) (fun _ => rfl)
  unfold isFiniteBits
  rw [h_be]
  decide

/-- **`IsFiniteAbs` is implied by a bit-level round-trip to a finite float**:
if `Clinger.ofDecimal d` has the same bits as some finite `f`, the abstract
decode cannot have overflowed (overflow produces `±∞`, whose biased exponent
`2047` cannot match a finite bit pattern). This removes `IsFiniteAbs` side
conditions from any statement that already assumes the round-trip. -/
theorem isFiniteAbs_of_roundtrip (d : Decimal) (f : _root_.Float)
    (h_sig : d.significand ≠ 0)
    (h_fin : isFiniteBits f = true)
    (h_rt : (ofDecimal d).toBits = f.toBits) :
    IsFiniteAbs d.sign d.significand d.exponent := by
  by_contra h_not
  have h_inf : ofDecimal d = fromBits d.sign 2047 0 :=
    decimalToFloat_overflow_inf d.sign d.significand d.exponent h_sig h_not
  have h_fb : isFiniteBits (ofDecimal d) = isFiniteBits f := by
    unfold isFiniteBits biasedExpBits
    rw [h_rt]
  rw [h_inf, isFiniteBits_fromBits_inf, h_fin] at h_fb
  exact absurd h_fb (by decide)

/-! ## `Clinger.ofDecimal` never produces a NaN bit pattern

Every leaf of `decimalToFloat`'s if-tree is `fromBits sign be m` with either
`m = 0` (zero / infinity / carry-overflow leaves) or `be < 2047` (normal /
subnormal leaves), so none can encode a NaN payload
(`be = 2047 ∧ m ≠ 0`). This lets `ofDecimal`'s output feed the restricted
`Float.toBits_ofBits` axiom unconditionally, without any finiteness
hypothesis. -/

/-- The `(a, b)`-body mirrored by `bridge_AB` / `overflow_AB` never produces
a NaN bit pattern, for any positive `a, b` (no finiteness hypothesis
needed: even the overflow leaf `fromBits sign 2047 0` has mantissa `0`,
hence is `±∞`, not NaN). -/
private theorem not_nanPattern_AB
    (sign : Bool) (a b : Nat) (ha_pos : 0 < a) (hb_pos : 0 < b) :
    _root_.Float.isNaNPattern
      ((let e := findBinaryExp a b
        if e > 1023 then fromBits sign 2047 0
        else if e ≥ -1022 then
          let m := roundNearestEven (scaleByPow2 a b (52 - e)).1
                                     (scaleByPow2 a b (52 - e)).2
          if m ≥ 2 ^ 53 then
            let e' := e + 1
            if e' > 1023 then fromBits sign 2047 0
            else fromBits sign (e' + 1023).toNat 0
          else fromBits sign (e + 1023).toNat (m - 2 ^ 52)
        else
          let m := roundNearestEven (scaleByPow2 a b 1074).1
                                     (scaleByPow2 a b 1074).2
          if m = 0 then fromBits sign 0 0
          else if m ≥ 2 ^ 52 then fromBits sign 1 (m - 2 ^ 52)
          else fromBits sign 0 m).toBits) = false := by
  by_cases h_over : findBinaryExp a b > 1023
  · simp only [if_pos h_over]
    exact fromBits_toBits_isNaNPattern_false sign 2047 0 (by decide) (by decide)
      (fun _ => rfl)
  · by_cases h_normal : findBinaryExp a b ≥ -1022
    · by_cases h_carry : roundNearestEven (scaleByPow2 a b (52 - findBinaryExp a b)).1
                          (scaleByPow2 a b (52 - findBinaryExp a b)).2 ≥ 2 ^ 53
      · by_cases h_over2 : findBinaryExp a b + 1 > 1023
        · simp only [if_neg h_over, if_pos h_normal, if_pos h_carry, if_pos h_over2]
          exact fromBits_toBits_isNaNPattern_false sign 2047 0 (by decide)
            (by decide) (fun _ => rfl)
        · simp only [if_neg h_over, if_pos h_normal, if_pos h_carry, if_neg h_over2]
          have h_be_hi : (findBinaryExp a b + 1 + 1023).toNat < 2048 := by omega
          exact fromBits_toBits_isNaNPattern_false sign _ 0 h_be_hi
            zero_lt_2pow52 (fun _ => rfl)
      · simp only [if_neg h_over, if_pos h_normal, if_neg h_carry]
        have h_be_hi : (findBinaryExp a b + 1023).toNat < 2048 := by omega
        have h_m_diff :
            roundNearestEven (scaleByPow2 a b (52 - findBinaryExp a b)).1
                              (scaleByPow2 a b (52 - findBinaryExp a b)).2 - 2 ^ 52 < 2 ^ 52 := by
          omega
        exact fromBits_toBits_isNaNPattern_false sign _ _ h_be_hi h_m_diff
          (fun _ => by omega)
    · by_cases h_zero : roundNearestEven (scaleByPow2 a b 1074).1 (scaleByPow2 a b 1074).2 = 0
      · simp only [if_neg h_over, if_neg h_normal, if_pos h_zero]
        exact fromBits_toBits_isNaNPattern_false sign 0 0 (by decide) (by decide)
          (fun _ => rfl)
      · by_cases h_nb : roundNearestEven (scaleByPow2 a b 1074).1 (scaleByPow2 a b 1074).2 ≥ 2 ^ 52
        · simp only [if_neg h_over, if_neg h_normal, if_neg h_zero, if_pos h_nb]
          have h_m_le := subnormal_round_le_2pow52 a b _ ha_pos hb_pos h_normal rfl
          have h_m_diff :
              roundNearestEven (scaleByPow2 a b 1074).1 (scaleByPow2 a b 1074).2 - 2 ^ 52
                < 2 ^ 52 := by
            have h2 : 2 * 2 ^ 52 = 2 ^ 53 := by decide
            omega
          exact fromBits_toBits_isNaNPattern_false sign 1 _ (by decide) h_m_diff
            (fun _ => by omega)
        · simp only [if_neg h_over, if_neg h_normal, if_neg h_zero, if_neg h_nb]
          have h_m_lt : roundNearestEven (scaleByPow2 a b 1074).1 (scaleByPow2 a b 1074).2
              < 2 ^ 52 := by omega
          exact fromBits_toBits_isNaNPattern_false sign 0 _ (by decide) h_m_lt
            (fun _ => by omega)

/-- **`Clinger.ofDecimal` never produces a NaN bit pattern**, for any
`Decimal` (zero, finite nonzero, or overflowing to `±∞` — none of the
leaves of `decimalToFloat`'s if-tree can encode a NaN payload). -/
theorem ofDecimal_toBits_not_nanPattern (d : Decimal) :
    _root_.Float.isNaNPattern (ofDecimal d).toBits = false := by
  show _root_.Float.isNaNPattern (decimalToFloat d.sign d.significand d.exponent).toBits = false
  unfold decimalToFloat
  by_cases h_sig : d.significand = 0
  · rw [if_pos h_sig]
    exact fromBits_toBits_isNaNPattern_false d.sign 0 0 (by decide) (by decide)
      (fun _ => rfl)
  · rw [if_neg h_sig]
    by_cases hexp : d.exponent ≥ 0
    · have h_pair :
          (if d.exponent ≥ 0 then (d.significand * 10 ^ d.exponent.toNat, 1)
            else (d.significand, 10 ^ (-d.exponent).toNat))
            = (d.significand * 10 ^ d.exponent.toNat, 1) := if_pos hexp
      rw [h_pair]
      have ha_pos : 0 < d.significand * 10 ^ d.exponent.toNat :=
        Nat.mul_pos (Nat.pos_of_ne_zero h_sig)
                    (Nat.pow_pos (by decide : 0 < (10 : Nat)))
      exact not_nanPattern_AB d.sign _ 1 ha_pos (by decide)
    · have h_pair :
          (if d.exponent ≥ 0 then (d.significand * 10 ^ d.exponent.toNat, 1)
            else (d.significand, 10 ^ (-d.exponent).toNat))
            = (d.significand, 10 ^ (-d.exponent).toNat) := if_neg hexp
      rw [h_pair]
      have hb_pos : 0 < (10 : Nat) ^ (-d.exponent).toNat :=
        Nat.pow_pos (by decide : 0 < (10 : Nat))
      exact not_nanPattern_AB d.sign _ _ (Nat.pos_of_ne_zero h_sig) hb_pos

end Srtfp.Clinger

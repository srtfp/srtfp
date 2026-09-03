/- Rational readings of the cleared comparisons, the sign/magnitude
   split of `toRat` and `wordVal`, and the word/decode bridges. Moved
   here unchanged from the old printer proof stack (`TieBreak.lean`,
   `RoundTrip.lean`) for the reader proofs. Retired by the reader rewrite. -/
import Srtfp.Proofs.CorrectnessSpec
import Srtfp.Proofs.Clinger.Bridge
import Srtfp.Proofs.Clinger.NatInterval
import Srtfp.Proofs.Bits
import Srtfp.Tactics

open Srtfp.Compat

namespace Srtfp

open Srtfp.Schubfach
open Srtfp.Float
open Srtfp.Clinger

namespace Schubfach

/-- The common positive denominator-clearing factor for scale `(q,k)`:
`2^{max(-q,0)} · 10^{max(-k,0)}` as a rational. -/
private noncomputable def clearFactor (q k : Int) : ℚ :=
  (2 : ℚ) ^ (if q < 0 then (-q).toNat else 0)
    * (10 : ℚ) ^ (if k < 0 then (-k).toNat else 0)

theorem clearFactor_pos (q k : Int) : 0 < clearFactor q k := by
  unfold clearFactor
  apply Rat.mul_pos <;> (apply Rat.pow_pos; decide)

/-- `b^q · b^{max(-q,0)} = b^{max(q,0)}` as rationals, for nonzero `b`. -/
theorem zpow_split_gen (b : ℚ) (hb : b ≠ 0) (q : Int) :
    b ^ q * b ^ (if q < 0 then (-q).toNat else 0)
      = b ^ (if q ≥ 0 then q.toNat else 0) := by
  by_cases hq : q < 0
  · rw [if_pos hq, if_neg (by omega : ¬ q ≥ 0)]
    rw [← Rat.zpow_natCast b (-q).toNat, Int.toNat_of_nonneg (by omega : (0:Int) ≤ -q),
        ← Rat.zpow_add hb]
    rw [show q + -q = 0 from by omega, Rat.zpow_zero]
    exact (Rat.pow_zero b).symm
  · rw [if_neg hq, if_pos (by omega : q ≥ 0)]
    rw [← Rat.zpow_natCast b q.toNat, Int.toNat_of_nonneg (by omega : (0:Int) ≤ q)]
    simp

/-- `2^q · 2^{max(-q,0)} = 2^{max(q,0)}` as rationals. -/
theorem zpow_two_split (q : Int) :
    (2 : ℚ) ^ q * (2 : ℚ) ^ (if q < 0 then (-q).toNat else 0)
      = (2 : ℚ) ^ (if q ≥ 0 then q.toNat else 0) :=
  zpow_split_gen 2 (by grind) q

/-- `10^k · 10^{max(-k,0)} = 10^{max(k,0)}` as rationals. -/
theorem zpow_ten_split (k : Int) :
    (10 : ℚ) ^ k * (10 : ℚ) ^ (if k < 0 then (-k).toNat else 0)
      = (10 : ℚ) ^ (if k ≥ 0 then k.toNat else 0) :=
  zpow_split_gen 10 (by grind) k

/-- Multiplying `(a:ℚ)·2^q` by the clearing factor yields `(lhs : ℚ)`. -/
theorem lhs_eq_clear (a : Int) (q k : Int) :
    (cmpScaledMixed.lhs a q k : ℚ)
      = ((a : ℚ) * (2 : ℚ) ^ q) * clearFactor q k := by
  unfold cmpScaledMixed.lhs clearFactor
  push_cast
  have h2 := zpow_two_split q
  calc (a : ℚ) * (2 : ℚ) ^ (if q ≥ 0 then q.toNat else 0)
          * (10 : ℚ) ^ (if k < 0 then (-k).toNat else 0)
      = (a : ℚ) * ((2 : ℚ) ^ q * (2 : ℚ) ^ (if q < 0 then (-q).toNat else 0))
          * (10 : ℚ) ^ (if k < 0 then (-k).toNat else 0) := by rw [h2]
    _ = (a : ℚ) * (2 : ℚ) ^ q
          * ((2 : ℚ) ^ (if q < 0 then (-q).toNat else 0)
             * (10 : ℚ) ^ (if k < 0 then (-k).toNat else 0)) := by grind

/-- Multiplying `(b:ℚ)·10^k` by the clearing factor yields `(rhs : ℚ)`. -/
theorem rhs_eq_clear (b : Int) (q k : Int) :
    (cmpScaledMixed.rhs b q k : ℚ)
      = ((b : ℚ) * (10 : ℚ) ^ k) * clearFactor q k := by
  unfold cmpScaledMixed.rhs clearFactor
  push_cast
  have h10 := zpow_ten_split k
  calc (b : ℚ) * (10 : ℚ) ^ (if k ≥ 0 then k.toNat else 0)
          * (2 : ℚ) ^ (if q < 0 then (-q).toNat else 0)
      = (b : ℚ) * ((10 : ℚ) ^ k * (10 : ℚ) ^ (if k < 0 then (-k).toNat else 0))
          * (2 : ℚ) ^ (if q < 0 then (-q).toNat else 0) := by rw [h10]
    _ = (b : ℚ) * (10 : ℚ) ^ k
          * ((2 : ℚ) ^ (if q < 0 then (-q).toNat else 0)
             * (10 : ℚ) ^ (if k < 0 then (-k).toNat else 0)) := by grind

/-- **(A) ℚ bridge, `<` direction.** The integer cleared comparison equals
the rational comparison `(a:ℚ)·2^q < (b:ℚ)·10^k`. -/
theorem cmpScaledMixed_lhs_lt_rhs_iff_rat (a : Int) (q : Int) (b : Int) (k : Int) :
    cmpScaledMixed.lhs a q k < cmpScaledMixed.rhs b q k
      ↔ (a : ℚ) * (2 : ℚ) ^ q < (b : ℚ) * (10 : ℚ) ^ k := by
  rw [show (cmpScaledMixed.lhs a q k < cmpScaledMixed.rhs b q k)
        ↔ (cmpScaledMixed.lhs a q k : ℚ) < (cmpScaledMixed.rhs b q k : ℚ) from
        Int.cast_lt.symm]
  rw [lhs_eq_clear, rhs_eq_clear]
  exact mul_lt_mul_iff_of_pos_right (clearFactor_pos q k)

/-- **(A) ℚ bridge, `=` direction.** -/
theorem cmpScaledMixed_lhs_eq_rhs_iff_rat (a : Int) (q : Int) (b : Int) (k : Int) :
    cmpScaledMixed.lhs a q k = cmpScaledMixed.rhs b q k
      ↔ (a : ℚ) * (2 : ℚ) ^ q = (b : ℚ) * (10 : ℚ) ^ k := by
  rw [show (cmpScaledMixed.lhs a q k = cmpScaledMixed.rhs b q k)
        ↔ (cmpScaledMixed.lhs a q k : ℚ) = (cmpScaledMixed.rhs b q k : ℚ) from
        Int.cast_inj.symm]
  rw [lhs_eq_clear, rhs_eq_clear]
  exact mul_left_inj' (Rat.ne_of_gt (clearFactor_pos q k))

/-- **(A) ℚ bridge, `>` direction.** -/
theorem cmpScaledMixed_lhs_gt_rhs_iff_rat (a : Int) (q : Int) (b : Int) (k : Int) :
    cmpScaledMixed.lhs a q k > cmpScaledMixed.rhs b q k
      ↔ (a : ℚ) * (2 : ℚ) ^ q > (b : ℚ) * (10 : ℚ) ^ k := by
  rw [gt_iff_lt, gt_iff_lt]
  rw [show (cmpScaledMixed.rhs b q k < cmpScaledMixed.lhs a q k)
        ↔ (cmpScaledMixed.rhs b q k : ℚ) < (cmpScaledMixed.lhs a q k : ℚ) from
        Int.cast_lt.symm]
  rw [lhs_eq_clear, rhs_eq_clear]
  exact mul_lt_mul_iff_of_pos_right (clearFactor_pos q k)

/-- The rational value of the decimal grid point `s · 10^k`. -/
def gridVal (s : Nat) (k : Int) : ℚ := (s : ℚ) * (10 : ℚ) ^ k

/-- Equidistance iff exactly at the midpoint. -/
theorem abs_eq_abs_iff_two_eq (v u w : ℚ) (h : u < w) :
    |v - u| = |v - w| ↔ 2 * v = u + w := by
  rw [abs_eq_iff_mul_self_eq]
  have hwu : w - u ≠ 0 := by grind
  constructor
  · intro hsq
    have hfact : (2 * v - (u + w)) * (w - u) = 0 := by grind
    rcases Rat.mul_eq_zero.mp hfact with h1 | h1
    · grind
    · exact absurd h1 hwu
  · intro hmid; grind

/-- `signFactor s = (-1)^s` as a rational. -/
def signFactor (s : Bool) : ℚ := if s then -1 else 1

theorem toRat_eq_signFactor_gridVal (d : Decimal) :
    d.toRat = signFactor d.sign * gridVal d.significand d.exponent := by
  unfold Decimal.toRat signFactor gridVal; grind

/-- `wordVal w = signFactor (Word.decode w).sign · magVal …`. -/
theorem wordVal_eq_signFactor_magVal (w : UInt64) :
    wordVal w = signFactor (Srtfp.Float.Word.decode w).sign
        * magVal (Srtfp.Float.Word.decode w).m (Srtfp.Float.Word.decode w).q := by
  unfold wordVal signFactor; rfl

/-- `|±1·a - ±1·b| = |a - b|`: the shared sign factors out of the distance. -/
theorem abs_signFactor_sub (sgn : Bool) (a b : ℚ) :
    |signFactor sgn * a - signFactor sgn * b| = |a - b| := by
  unfold signFactor
  cases sgn
  · simp
  · -- (-1)*a - (-1)*b = -(a-b); |-(a-b)| = |a-b|.
    rw [show ((if true then -1 else 1 : ℚ)) = -1 from rfl]
    rw [show (-1 : ℚ) * a - (-1) * b = -(a - b) from by grind, abs_neg]

/-- **Signed-distance reduction.** For a decimal `d'` whose sign matches
`(Srtfp.Float.Word.decode w).sign`, the signed clause-(3) distance reduces to the
unsigned grid distance against `v = magVal (Srtfp.Float.Word.decode w).m (Srtfp.Float.Word.decode
w).q`. -/
theorem toRat_dist_eq_grid_dist (d' : Decimal) (w : UInt64)
    (h_sign : d'.sign = (Srtfp.Float.Word.decode w).sign) :
    |Decimal.toRat d' - wordVal w|
      = |magVal (Srtfp.Float.Word.decode w).m (Srtfp.Float.Word.decode w).q
         - gridVal d'.significand d'.exponent| := by
  rw [toRat_eq_signFactor_gridVal, wordVal_eq_signFactor_magVal, h_sign]
  rw [show signFactor (Srtfp.Float.Word.decode w).sign
            * gridVal d'.significand d'.exponent
          - signFactor (Srtfp.Float.Word.decode w).sign
            * magVal (Srtfp.Float.Word.decode w).m (Srtfp.Float.Word.decode w).q
        = signFactor (Srtfp.Float.Word.decode w).sign
            * (gridVal d'.significand d'.exponent
               - magVal (Srtfp.Float.Word.decode w).m (Srtfp.Float.Word.decode w).q) from by
        grind]
  rw [show signFactor (Srtfp.Float.Word.decode w).sign
            * (gridVal d'.significand d'.exponent
               - magVal (Srtfp.Float.Word.decode w).m (Srtfp.Float.Word.decode w).q)
        = signFactor (Srtfp.Float.Word.decode w).sign * gridVal d'.significand d'.exponent
          - signFactor (Srtfp.Float.Word.decode w).sign
            * magVal (Srtfp.Float.Word.decode w).m (Srtfp.Float.Word.decode w).q from by grind]
  rw [abs_signFactor_sub, abs_sub_comm]

end Schubfach

/-- `decodedAbsAB sign a b` has `.sign = sign`. -/
theorem decodedAbsAB_sign (sign : Bool) (a b : Nat) :
    (decodedAbsAB sign a b).sign = sign := by
  unfold decodedAbsAB
  simp only
  split
  · rfl
  · split
    · split
      · split <;> rfl
      · rfl
    · split
      · rfl
      · split <;> rfl

/-- `decodedAbs sign sig exp` has `.sign = sign` (every leaf of the if-tree
    preserves the input sign). -/
theorem decodedAbs_sign (sign : Bool) (sig : Nat) (exp : Int) :
    (decodedAbs sign sig exp).sign = sign := by
  by_cases h_sig : sig = 0
  · subst h_sig
    rw [decodedAbs_zero]
  · by_cases hexp : exp ≥ 0
    · rw [decodedAbs_eq_decodedAbsAB_pos sign sig exp h_sig hexp]
      exact decodedAbsAB_sign _ _ _
    · rw [decodedAbs_eq_decodedAbsAB_neg sign sig exp h_sig hexp]
      exact decodedAbsAB_sign _ _ _

/-- A float is recovered from its bit-field decomposition via `Word.pack`,
    provided `f` is not NaN. This uses the restricted `Float.toBits_ofBits`
    and pure UInt64/Nat algebra: the three bit fields are disjoint, so their
    OR is a sum (`or_or_eq_add'`) and `omega` reassembles the word. -/
theorem pack_decode_eq (w : UInt64) (_h : Word.isNaN w = false) :
    Word.pack (Word.signBit w) (Word.biasedExp w) (Word.mantissa w) = w := by
  unfold Word.pack Word.signBit Word.biasedExp Word.mantissa
  -- Goal: (signBit branch ||| biasedExp shifted ||| mantissa masked) = w.
  -- Pure UInt64 fact: OR of disjoint bit-field projections recovers W.
  generalize w = W
  -- Reduce the .toNat in biasedExpBits and mantissaBits casts.
  show (if decide (W >>> 63 ≠ 0) = true then (1 : UInt64) <<< 63 else 0) |||
       (UInt64.ofNat (((W >>> 52) &&& 0x7FF).toNat) &&& 0x7FF) <<< 52 |||
       UInt64.ofNat ((W &&& 0x000F_FFFF_FFFF_FFFF).toNat) &&& 0x000F_FFFF_FFFF_FFFF = W
  -- UInt64.ofNat ∘ UInt64.toNat = id on `< 2^64` values; all here are.
  have h1 : UInt64.ofNat (((W >>> 52) &&& 0x7FF).toNat) = (W >>> 52) &&& 0x7FF :=
    UInt64.toNat_inj.1 (Nat.mod_eq_of_lt (UInt64.toNat_lt _))
  have h2 : UInt64.ofNat ((W &&& 0x000F_FFFF_FFFF_FFFF).toNat) = W &&& 0x000F_FFFF_FFFF_FFFF :=
    UInt64.toNat_inj.1 (Nat.mod_eq_of_lt (UInt64.toNat_lt _))
  rw [h1, h2]
  -- Compare at the Nat level, where each field is a div/mod expression.
  rw [← UInt64.toNat_inj, UInt64.toNat_or, UInt64.toNat_or]
  have ha : W.toNat < 2 ^ 64 := UInt64.toNat_lt _
  -- biased-exponent field value
  have hbe : (((W >>> 52 &&& 2047) &&& 2047) <<< 52).toNat
      = (W.toNat / 2 ^ 52 % 2048) * 2 ^ 52 := by
    rw [UInt64.toNat_shiftLeft, UInt64.toNat_and, UInt64.toNat_and, UInt64.toNat_shiftRight,
        show ((52 : UInt64)).toNat % 64 = 52 by decide,
        show ((2047 : UInt64)).toNat = 2 ^ 11 - 1 by decide,
        Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod,
        Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  -- mantissa field value
  have hmnt : ((W &&& 4503599627370495) &&& 4503599627370495).toNat = W.toNat % 2 ^ 52 := by
    rw [UInt64.toNat_and, UInt64.toNat_and,
        show ((4503599627370495 : UInt64)).toNat = 2 ^ 52 - 1 by decide,
        Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod]
    omega
  rw [hbe, hmnt]
  by_cases hsgn : W >>> 63 = 0
  · have hz : W.toNat / 2 ^ 63 = 0 := by
      have := congrArg UInt64.toNat hsgn
      rwa [UInt64.toNat_shiftRight, show ((63 : UInt64)).toNat % 64 = 63 by decide,
           Nat.shiftRight_eq_div_pow] at this
    simp only [hsgn, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, if_false]
    rw [or_or_eq_add' (Or.inl (by decide)) ⟨_, by omega, rfl⟩ (by omega),
        show ((0 : UInt64)).toNat = 0 by decide]
    omega
  · have hz : W.toNat / 2 ^ 63 = 1 := by
      have h0 : (W >>> 63).toNat ≠ 0 := fun h => hsgn (UInt64.toNat_inj.1 (by simpa using h))
      rw [UInt64.toNat_shiftRight, show ((63 : UInt64)).toNat % 64 = 63 by decide,
          Nat.shiftRight_eq_div_pow] at h0
      omega
    simp only [hsgn, ne_eq, not_false_eq_true, decide_true, if_true]
    rw [show ((1 : UInt64) <<< 63).toNat = 2 ^ 63 by decide]
    rw [or_or_eq_add' (Or.inr rfl) ⟨_, by omega, rfl⟩ (by omega)]
    omega

/-- For two finite floats `f₁, f₂` decoding to the same `(sign, m, q)`,
    their bits agree. -/
theorem toBits_eq_of_decode_eq
    (w₁ w₂ : UInt64)
    (h_fin₁ : Word.isFinite w₁ = true)
    (h_fin₂ : Word.isFinite w₂ = true)
    (h_sign : Word.signBit w₁ = Word.signBit w₂)
    (h_m : (Word.decode w₁).m = (Word.decode w₂).m)
    (h_q : (Word.decode w₁).q = (Word.decode w₂).q) :
    w₁ = w₂ := by
  -- The bit fields are determined by signBit, biasedExpBits, mantissaBits.
  -- We have h_sign (signBit). We need (biasedExpBits, mantissaBits) equality.
  -- From decode: m and q determine (biasedExpBits, mantissaBits) when the bits are canonical.
  -- Strategy: use the Word.pack inverse to reassemble.
  -- Goal: w₁ = w₂.
  -- We'll show via pack_decode_eq that w = (assembled bits from (sign, be, mb)).
  -- Then comparing the assembled bits gives equality.
  -- decode determines biasedExpBits and mantissaBits:
  --   If biasedExpBits = 0: m = mantissaBits, q = -1074.
  --   Else: m = mantissaBits + 2^52, q = be - 1023 - 52.
  -- The encoding of (m, q) into (be, mb) is unique given m, q.
  have hm₁ := h_m
  have hq₁ := h_q
  -- We need Word.biasedExp w₁ = Word.biasedExp w₂ and Word.mantissa w₁ = Word.mantissa w₂.
  -- Get them by case analysis on (Word.biasedExp w₁ = 0) vs not, comparing to f₂'s.
  have h_be_eq : Word.biasedExp w₁ = Word.biasedExp w₂ := by
    by_cases he₁ : Word.biasedExp w₁ = 0
    · -- f₁ subnormal: q₁ = -1074, m₁ = Word.mantissa w₁ < 2^52.
      have hq_eq₁ : (Word.decode w₁).q = -1074 := by unfold Word.decode; rw [if_pos he₁]
      -- f₂'s decode q equals -1074 (by h_q).
      have hq_eq₂ : (Word.decode w₂).q = -1074 := by rw [← h_q]; exact hq_eq₁
      -- This forces f₂ to also be subnormal (biasedExp = 0).
      by_contra h_ne
      -- Then biasedExp f₂ ≥ 1, so q = be₂ - 1023 - 52 ≥ -1074 with equality iff be₂ = 1.
      -- But mantissaBits would differ, so m would differ. Wait, we need a contradiction.
      have he₂ : Word.biasedExp w₂ ≠ 0 := by
        intro h
        apply h_ne
        rw [he₁, h]
      have hq₂_def : (Word.decode w₂).q = (Word.biasedExp w₂ : Int) - 1023 - 52 := by
        unfold Word.decode; rw [if_neg he₂]
      rw [hq₂_def] at hq_eq₂
      -- (be₂ : Int) - 1023 - 52 = -1074 → be₂ = 1.
      have hbe₂_one : Word.biasedExp w₂ = 1 := by
        have : (Word.biasedExp w₂ : Int) = 1 := by omega
        exact_mod_cast this
      -- Then m₂ = Word.mantissa w₂ + 2^52 ≥ 2^52.
      have hm₂_def : (Word.decode w₂).m = Word.mantissa w₂ + (1 <<< 52) := by
        unfold Word.decode; rw [if_neg he₂]
      have h_shl : (1 : Nat) <<< 52 = 2 ^ 52 := by decide
      have h_m₂_ge : 2^52 ≤ (Word.decode w₂).m := by rw [hm₂_def, h_shl]; omega
      -- But m₁ = Word.mantissa w₁ < 2^52.
      have hm₁_def : (Word.decode w₁).m = Word.mantissa w₁ := by unfold Word.decode; rw [if_pos he₁]
      have hmb₁_lt : Word.mantissa w₁ < 2 ^ 52 := by
        unfold Word.mantissa
        rw [UInt64.toNat_and]
        have hmask : ((0x000F_FFFF_FFFF_FFFF : UInt64).toNat) = 4503599627370495 := by decide
        rw [hmask]
        have hle : w₁.toNat &&& 4503599627370495 ≤ 4503599627370495 := Nat.and_le_right
        have hpow : (2 : Nat) ^ 52 = 4503599627370496 := by decide
        omega
      rw [hm₁_def] at h_m
      rw [h_m] at hmb₁_lt
      omega
    · -- f₁ normal.
      by_cases he₂ : Word.biasedExp w₂ = 0
      · -- Mirror of above.
        exfalso
        have hq_eq₂ : (Word.decode w₂).q = -1074 := by unfold Word.decode; rw [if_pos he₂]
        have hq_eq₁ : (Word.decode w₁).q = -1074 := by rw [h_q]; exact hq_eq₂
        have hq₁_def : (Word.decode w₁).q = (Word.biasedExp w₁ : Int) - 1023 - 52 := by
          unfold Word.decode; rw [if_neg he₁]
        rw [hq₁_def] at hq_eq₁
        have hbe₁_one : Word.biasedExp w₁ = 1 := by
          have : (Word.biasedExp w₁ : Int) = 1 := by omega
          exact_mod_cast this
        have hm₁_def : (Word.decode w₁).m = Word.mantissa w₁ + (1 <<< 52) := by
          unfold Word.decode; rw [if_neg he₁]
        have h_shl : (1 : Nat) <<< 52 = 2 ^ 52 := by decide
        have h_m₁_ge : 2^52 ≤ (Word.decode w₁).m := by rw [hm₁_def, h_shl]; omega
        have hm₂_def : (Word.decode w₂).m = Word.mantissa w₂ := by unfold Word.decode; rw [if_pos he₂]
        have hmb₂_lt : Word.mantissa w₂ < 2 ^ 52 := by
          unfold Word.mantissa
          rw [UInt64.toNat_and]
          have hmask : ((0x000F_FFFF_FFFF_FFFF : UInt64).toNat) = 4503599627370495 := by decide
          rw [hmask]
          have hle : w₂.toNat &&& 4503599627370495 ≤ 4503599627370495 := Nat.and_le_right
          have hpow : (2 : Nat) ^ 52 = 4503599627370496 := by decide
          omega
        rw [hm₂_def] at h_m
        rw [← h_m] at hmb₂_lt
        omega
      · -- Both normal: q determines biasedExp.
        have hq₁_def : (Word.decode w₁).q = (Word.biasedExp w₁ : Int) - 1023 - 52 := by
          unfold Word.decode; rw [if_neg he₁]
        have hq₂_def : (Word.decode w₂).q = (Word.biasedExp w₂ : Int) - 1023 - 52 := by
          unfold Word.decode; rw [if_neg he₂]
        rw [hq₁_def, hq₂_def] at h_q
        have : (Word.biasedExp w₁ : Int) = (Word.biasedExp w₂ : Int) := by omega
        exact_mod_cast this
  have h_mb_eq : Word.mantissa w₁ = Word.mantissa w₂ := by
    by_cases he₁ : Word.biasedExp w₁ = 0
    · have he₂ : Word.biasedExp w₂ = 0 := by rw [← h_be_eq]; exact he₁
      have hm₁_def : (Word.decode w₁).m = Word.mantissa w₁ := by unfold Word.decode; rw [if_pos he₁]
      have hm₂_def : (Word.decode w₂).m = Word.mantissa w₂ := by unfold Word.decode; rw [if_pos he₂]
      rw [hm₁_def, hm₂_def] at h_m; exact h_m
    · have he₂ : Word.biasedExp w₂ ≠ 0 := by rw [← h_be_eq]; exact he₁
      have hm₁_def : (Word.decode w₁).m = Word.mantissa w₁ + (1 <<< 52) := by
        unfold Word.decode; rw [if_neg he₁]
      have hm₂_def : (Word.decode w₂).m = Word.mantissa w₂ + (1 <<< 52) := by
        unfold Word.decode; rw [if_neg he₂]
      rw [hm₁_def, hm₂_def] at h_m; omega
  -- Now use pack_decode_eq to recover both f₁ and f₂ (neither is NaN,
  -- since both are finite).
  have h_be_lt₁ : Word.biasedExp w₁ < 2047 := by unfold Word.isFinite at h_fin₁; simpa using h_fin₁
  have h_be_lt₂ : Word.biasedExp w₂ < 2047 := by unfold Word.isFinite at h_fin₂; simpa using h_fin₂
  have h_nan₁ : Word.isNaN w₁ = false := by
    unfold Word.isNaN
    have : ¬ Word.biasedExp w₁ = 2047 := by omega
    simp [this]
  have h_nan₂ : Word.isNaN w₂ = false := by
    unfold Word.isNaN
    have : ¬ Word.biasedExp w₂ = 2047 := by omega
    simp [this]
  have hf₁ := pack_decode_eq w₁ h_nan₁
  have hf₂ := pack_decode_eq w₂ h_nan₂
  rw [h_sign, h_be_eq, h_mb_eq] at hf₁
  exact hf₁.symm.trans hf₂

/-- `Word.signBit w = (Word.decode w).sign`. -/
theorem signBit_eq_decode_sign (w : UInt64) :
    Word.signBit w = (Word.decode w).sign := by
  unfold Word.decode
  by_cases he : Word.biasedExp w = 0
  · simp [he]
  · simp [he]

end Srtfp

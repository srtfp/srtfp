/- Round-trip theorem: `Clinger.ofDecimal (Schubfach.toDecimalBits w) = f` at
   the bit level.

   This chains:
     * M3.8 Schubfach correctness (`toDecimal_in_Rv`): the decimal produced
       has `(sig, exp)` in the rounding interval of `Word.decode w`.
     * M4 Clinger correctness (`ofDecimal_in_Rv`): for finite nonzero
       Decimal d, `decode (ofDecimal d)` has `(sig, exp)` in its rounding
       interval.
     * Disjointness (`inRoundingInterval_uniq`): two canonical IEEE pairs
       sharing a rounding-interval point must be equal.

   ## Statement (.toBits level)

   For finite f with `(Word.decode w).m ≠ 0`, there exists `d : Decimal` with
   `Schubfach.toDecimalBits w = .ok d ∧ Clinger.ofDecimalBits d = w`.

   ## Why `.toBits` level?

   Going to the `Float` level requires a new axiom `Float.ofBits_toBits`,
   which is dual to the existing `Float.toBits_ofBits`. We keep the
   theorem at `.toBits` level so it consumes only the existing axiom
   budget; JSON's `floatLiteralStrict` consumes `.toBits` directly. -/

import Srtfp.Proofs.Disjointness
import Srtfp.Proofs.Decimal
import Srtfp.Proofs.Schubfach.ToDecimal
import Srtfp.Proofs.Schubfach.Shortest
import Srtfp.Proofs.Clinger
import Srtfp.Float.Bits
import Srtfp.Tactics

namespace Srtfp

open Srtfp.Schubfach
open Srtfp.Float
open Srtfp.Clinger

/-! ## Sign of the Clinger output -/

/-- `decodedAbsAB sign a b` has `.sign = sign`. -/
private theorem decodedAbsAB_sign (sign : Bool) (a b : Nat) :
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

/-! ## Decode is injective at the bit level for finite canonical pairs

The Word.decode wunction `Float → (sign, m, q)` is injective on finite floats
because the underlying bit pattern is uniquely determined by these
three quantities (`Word.pack` is the inverse). This lemma lifts that fact:
if two finite floats decode to the same triple, their bits agree. -/

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

/-! ## Sign equality for `Word.decode (ofDecimalBits d)` -/

/-- `Word.decode (ofDecimalBits d)` has sign `d.sign`, provided the value
is in finite range. -/
theorem decode_ofDecimal_sign (d : Decimal)
    (h_finite : IsFiniteAbs d.sign d.significand d.exponent) :
    (Word.decode (Clinger.ofDecimalBits d)).sign = d.sign := by
  rw [Clinger.decode_of_decimal_bridge_bits d h_finite]
  exact decodedAbs_sign d.sign d.significand d.exponent

/-! ## SignBit lemmas -/

/-- `Word.signBit w = (Word.decode w).sign`. -/
theorem signBit_eq_decode_sign (w : UInt64) :
    Word.signBit w = (Word.decode w).sign := by
  unfold Word.decode
  by_cases he : Word.biasedExp w = 0
  · simp [he]
  · simp [he]

/-! ## IsFiniteAbs from inRoundingInterval witness -/

/-! ## The round-trip theorem -/

/-! ## The round-trip theorem -/

/-- Helper: `d.significand · 10^d.exponent = sig · 10^exp` (as Nat × Int values)
    when `d = Decimal.mk' sign sig exp`. -/
private theorem mk'_value_eq (sign : Bool) (sig : Nat) (exp : Int) (h_sig : sig ≠ 0) :
    let d := Decimal.mk' sign sig exp
    d.significand * 10 ^ ((d.exponent - exp).toNat : Nat) = sig
    ∧ exp ≤ d.exponent := by
  have ⟨_, _, _, hexp_le, hval⟩ := mk_pos_props sign sig exp h_sig
  exact ⟨hval, hexp_le⟩

/-- Helper: `inRoundingInterval` for the raw `(sig, exp)` equals that for the
    canonical `(d.significand, d.exponent)` where `d = Decimal.mk' sign sig exp`. -/
private theorem inRoundingInterval_mk'_eq (sign : Bool) (sig : Nat) (exp : Int)
    (m : Nat) (q : Int) (irreg : Bool) (h_sig : sig ≠ 0) :
    let d := Decimal.mk' sign sig exp
    inRoundingInterval sig exp m q irreg
      = inRoundingInterval d.significand d.exponent m q irreg := by
  simp only
  obtain ⟨hval, hexp_le⟩ := mk'_value_eq sign sig exp h_sig
  set d := Decimal.mk' sign sig exp
  set k : Nat := (d.exponent - exp).toNat
  -- Use scale10_pow: inRoundingInterval (d.significand · 10^k) (d.exponent - k) m q
  --                = inRoundingInterval d.significand d.exponent m q.
  have h_invariance := inRoundingInterval_scale10_pow d.significand d.exponent m q irreg k
  -- We have sig = d.significand · 10^k, and exp = d.exponent - k.
  have hk_pos : (k : Int) = d.exponent - exp := by
    show ((d.exponent - exp).toNat : Int) = d.exponent - exp
    exact Int.toNat_of_nonneg (by omega)
  have hsig_eq : sig = d.significand * 10^k := hval.symm
  have hexp_eq : exp = d.exponent - (k : Int) := by grind
  rw [hsig_eq, hexp_eq]
  exact h_invariance

/-! ## Sorry D: `(decode (Clinger.ofDecimal d)).m ≠ 0` helper -/

/-- If `(Word.decode v).m = 0`, then `g` is in the subnormal-zero bit branch:
    `Word.biasedExp v = 0`, hence `(Word.decode v).q = -1074`. The normal branch
    produces `m = mantissaBits + 2^52 ≥ 2^52 > 0`, ruling it out. -/
private theorem decode_m_zero_q (v : UInt64) (h_m : (Word.decode v).m = 0) :
    (Word.decode v).q = -1074 := by
  by_cases he : Word.biasedExp v = 0
  · unfold Word.decode; rw [if_pos he]
  · exfalso
    have hm_def : (Word.decode v).m = Word.mantissa v + (1 <<< 52) := by
      unfold Word.decode; rw [if_neg he]
    have h_shl : (1 : Nat) <<< 52 = 2 ^ 52 := by decide
    rw [hm_def, h_shl] at h_m
    have hpow : (2 : Nat) ^ 52 = 4503599627370496 := by decide
    omega

/-- The key obligation for Sorry D: under the canonical witness `h_rv_canonical`
    for the legal IEEE pair `(m_f, q_f)`, and the Clinger witness `h_rv_clinger`
    sharing the same `(d.sig, d.exp)`, if `m' = 0` and `q' = -1074` we obtain
    a contradiction.

    Strategy: bracket inequalities. From the Clinger witness, the right bracket
    gives `fourU(-1074) ≤ fourVR_0 = 2·10^kNeg`. From the canonical witness,
    the left bracket gives `fourVL_f ≤ fourU_f`. We bridge `fourU_f · 2^D
    = fourU(-1074)` where `D = 1074 - max(-q_f, 0) ≥ 0`. Combining,
    `fourVL_f · 2^D ≤ 2·10^kNeg`. We then show `fourVL_f · 2^D ≥ 2·10^kNeg`
    with equality only at `(m_f, q_f, irreg_f) = (1, -1074, false)`. In the
    equality case `m_f = 1` is odd, contradicting the parity-equality leg of
    the canonical left bracket. -/
private theorem clinger_decode_m_ne_zero_aux
    (d : Decimal)
    (m_f : Nat) (q_f : Int)
    (h_legal_f : LegalIEEE m_f q_f)
    (m' : Nat) (q' : Int)
    (h_rv_canonical : inRoundingInterval d.significand d.exponent
                        m_f q_f (isIrregular m_f q_f) = true)
    (h_rv_clinger : inRoundingInterval d.significand d.exponent
                      m' q' (isIrregular m' q') = true)
    (h_m_zero : m' = 0) (h_q_neg1074 : q' = -1074) : False := by
  subst h_m_zero
  subst h_q_neg1074
  -- `isIrregular 0 (-1074) = false`.
  have h_irreg_zero : isIrregular 0 (-1074) = false := by
    unfold isIrregular minNormalSignificand minBinaryExp
    decide
  rw [h_irreg_zero] at h_rv_clinger
  -- Reify both witnesses.
  rw [inRoundingInterval_iff] at h_rv_canonical h_rv_clinger
  -- LegalIEEE consequences: m_f ≥ 1, q_f ≥ -1074.
  have hmf_pos : 1 ≤ m_f := by
    rcases h_legal_f with ⟨h, _, _⟩ | ⟨h, _, _, _⟩
    · exact h
    · have : (2 : Nat) ^ 52 ≥ 1 := by decide
      omega
  have hqf_lo : -1074 ≤ q_f := by
    rcases h_legal_f with ⟨_, _, hq⟩ | ⟨_, _, hq, _⟩
    · omega
    · exact hq
  have hmf_pos_Int : (1 : Int) ≤ (m_f : Int) := by exact_mod_cast hmf_pos
  -- Abbreviate the recurring power expressions.
  let kNeg : Nat := if d.exponent < 0 then (-d.exponent).toNat else 0
  let kPos : Nat := if d.exponent ≥ 0 then d.exponent.toNat else 0
  let qfPos : Nat := if q_f ≥ 0 then q_f.toNat else 0
  let qfNeg : Nat := if q_f < 0 then (-q_f).toNat else 0
  -- Compute the relevant cleared values directly.
  -- fourU d.sig (-1074) d.exp = 4 d.sig · 10^kPos · 2^1074
  have h_clinger_U_eq :
      fourU d.significand (-1074) d.exponent
        = 4 * (d.significand : Int) * (10 : Int)^kPos * (2 : Int)^1074 := by
    show (4 * (d.significand : Int))
            * ((10 : Int) ^ (if d.exponent ≥ 0 then d.exponent.toNat else 0))
            * ((2 : Int) ^ (if (-1074 : Int) < 0 then ((-(-1074 : Int)).toNat) else 0))
          = 4 * (d.significand : Int) * (10 : Int)^kPos * (2 : Int)^1074
    show (4 * (d.significand : Int))
            * ((10 : Int) ^ kPos)
            * ((2 : Int) ^ (if (-1074 : Int) < 0 then ((-(-1074 : Int)).toNat) else 0))
          = 4 * (d.significand : Int) * (10 : Int)^kPos * (2 : Int)^1074
    have h1 : (if (-1074 : Int) < 0 then ((-(-1074 : Int)).toNat) else 0) = 1074 := by decide
    rw [h1]
  -- fourVR 0 (-1074) d.exp = 2 · 10^kNeg
  have h_clinger_VR_eq :
      fourVR 0 (-1074) d.exponent = 2 * (10 : Int)^kNeg := by
    show (4 * (0 : Int) + 2)
            * ((2 : Int) ^ (if ((-1074 : Int) ≥ 0) then ((-1074 : Int).toNat) else 0))
            * ((10 : Int) ^ (if d.exponent < 0 then (-d.exponent).toNat else 0))
          = 2 * (10 : Int)^kNeg
    show (4 * (0 : Int) + 2)
            * ((2 : Int) ^ (if ((-1074 : Int) ≥ 0) then ((-1074 : Int).toNat) else 0))
            * ((10 : Int) ^ kNeg)
          = 2 * (10 : Int)^kNeg
    have h_qpos : (if ((-1074 : Int) ≥ 0) then ((-1074 : Int).toNat) else 0) = 0 := by decide
    rw [h_qpos]; grind
  -- Right bracket from the Clinger witness: fourU(-1074) ≤ 2·10^kNeg.
  have h_fourU0_le :
      4 * (d.significand : Int) * (10 : Int)^kPos * (2 : Int)^1074
        ≤ 2 * (10 : Int)^kNeg := by
    obtain ⟨_, hright⟩ := h_rv_clinger
    rw [h_clinger_U_eq, h_clinger_VR_eq] at hright
    rcases hright with hlt | ⟨heq, _⟩
    · exact Int.le_of_lt hlt
    · exact Int.le_of_eq heq
  -- Canonical left bracket: fourVL_f ≤ fourU_f, plus parity if equality.
  -- fourVL m_f q_f d.exp irreg_f = leftN_f · 2^qfPos · 10^kNeg
  -- fourU d.sig q_f d.exp = 4 d.sig · 10^kPos · 2^qfNeg
  have h_canon_VL_eq :
      fourVL m_f q_f d.exponent (isIrregular m_f q_f)
        = (if isIrregular m_f q_f then 4 * (m_f : Int) - 1 else 4 * (m_f : Int) - 2)
            * (2 : Int)^qfPos * (10 : Int)^kNeg := by
    rfl
  have h_canon_U_eq :
      fourU d.significand q_f d.exponent
        = 4 * (d.significand : Int) * (10 : Int)^kPos * (2 : Int)^qfNeg := by
    rfl
  -- Extract left bracket.
  obtain ⟨h_left, _⟩ := h_rv_canonical
  rw [h_canon_VL_eq, h_canon_U_eq] at h_left
  -- Useful bound: 2^qfNeg · 2^D = 2^1074 where D = 1074 - qfNeg.
  have h_qfNeg_le : qfNeg ≤ 1074 := by
    show (if q_f < 0 then (-q_f).toNat else 0) ≤ 1074
    by_cases h : q_f < 0
    · rw [if_pos h]
      have : (-q_f).toNat ≤ 1074 := by omega
      exact this
    · rw [if_neg h]; omega
  let D : Nat := 1074 - qfNeg
  have hD_add : qfNeg + D = 1074 := by show qfNeg + (1074 - qfNeg) = 1074; omega
  have hD_def_unfold : D = 1074 - qfNeg := rfl
  have h_pow_split : (2 : Int)^qfNeg * (2 : Int)^D = (2 : Int)^1074 := by
    rw [← Int.pow_add, hD_add]
  -- α := qfPos + D
  let α : Nat := qfPos + D
  have hα_def : α = qfPos + D := rfl
  have h_pow_combine : (2 : Int)^qfPos * (2 : Int)^D = (2 : Int)^α := by
    rw [← Int.pow_add]
  -- α = 0 ↔ q_f = -1074.
  have hα_eq_iff : α = 0 ↔ q_f = -1074 := by
    constructor
    · intro h
      -- α = qfPos + D = qfPos + 1074 - qfNeg = 0
      have hqfPos_zero : qfPos = 0 := by
        show (if q_f ≥ 0 then q_f.toNat else 0) = 0
        have hsum : qfPos + D = 0 := h
        have hqfPos_le : qfPos = 0 := by omega
        show (if q_f ≥ 0 then q_f.toNat else 0) = 0
        exact hqfPos_le
      have hqfNeg_1074 : qfNeg = 1074 := by
        have hsum : qfPos + D = 0 := h
        have : qfPos = 0 := hqfPos_zero
        omega
      -- qfNeg = 1074 forces q_f < 0 ∧ (-q_f).toNat = 1074 ∧ thus q_f = -1074.
      have hqfNeg_unfold : (if q_f < 0 then (-q_f).toNat else 0) = 1074 := hqfNeg_1074
      by_cases h_neg : q_f < 0
      · rw [if_pos h_neg] at hqfNeg_unfold
        have : -q_f = 1074 := by omega
        omega
      · rw [if_neg h_neg] at hqfNeg_unfold
        exact absurd hqfNeg_unfold (by decide)
    · intro h
      -- q_f = -1074: qfPos = 0, qfNeg = 1074, D = 0, α = 0.
      have hqfPos_zero : qfPos = 0 := by
        show (if q_f ≥ 0 then q_f.toNat else 0) = 0
        rw [h]; decide
      have hqfNeg_eq : qfNeg = 1074 := by
        show (if q_f < 0 then (-q_f).toNat else 0) = 1074
        rw [h]; decide
      have hD_eq : D = 0 := by show 1074 - qfNeg = 0; omega
      show qfPos + D = 0
      omega
  -- The leftN_f ≥ 2 bound.
  have hleftN_ge_two :
      (2 : Int) ≤ (if isIrregular m_f q_f then 4 * (m_f : Int) - 1 else 4 * (m_f : Int) - 2) := by
    by_cases hi : isIrregular m_f q_f
    · rw [if_pos hi]
      grind
    · rw [if_neg hi]
      grind
  have hpow_α_ge_one : (1 : Int) ≤ (2 : Int)^α := one_le_pow_of_le (by decide : (1:Int) ≤ 2) _
  have hpow_D_pos : (0 : Int) < (2 : Int)^D := Int.pow_pos (by decide)
  -- Combine the brackets. Multiply left bracket by 2^D.
  -- LHS (after multiplication): leftN_f · 2^qfPos · 10^kNeg · 2^D = leftN_f · 2^α · 10^kNeg.
  -- RHS: 4 d.sig · 10^kPos · 2^qfNeg · 2^D = 4 d.sig · 10^kPos · 2^1074.
  -- So we get: leftN_f · 2^α · 10^kNeg ≤ 4 d.sig · 10^kPos · 2^1074 ≤ 2 · 10^kNeg.
  -- I.e., leftN_f · 2^α · 10^kNeg ≤ 2 · 10^kNeg.
  -- Dividing by 10^kNeg > 0: leftN_f · 2^α ≤ 2. But leftN_f ≥ 2 and 2^α ≥ 1, so ... = 2.
  set L : Int := (if isIrregular m_f q_f then 4 * (m_f : Int) - 1 else 4 * (m_f : Int) - 2)
    with hL_def
  set X10 : Int := (10 : Int)^kNeg with hX10_def
  set Y10 : Int := (10 : Int)^kPos with hY10_def
  set A2 : Int := (2 : Int)^qfPos with hA2_def
  set B2 : Int := (2 : Int)^qfNeg with hB2_def
  set DPow : Int := (2 : Int)^D with hDPow_def
  set α2 : Int := (2 : Int)^α with hα2_def
  have hX10_pos : (0 : Int) < X10 := Int.pow_pos (by decide)
  have hY10_pos : (0 : Int) < Y10 := Int.pow_pos (by decide)
  have hA2_pos : (0 : Int) < A2 := Int.pow_pos (by decide)
  have hB2_pos : (0 : Int) < B2 := Int.pow_pos (by decide)
  have hDPow_pos : (0 : Int) < DPow := Int.pow_pos (by decide)
  have hα2_pos : (0 : Int) < α2 := Int.pow_pos (by decide)
  -- Restate the hypotheses in these names.
  have h_left_named :
      L * A2 * X10 < 4 * (d.significand : Int) * Y10 * B2 ∨
      L * A2 * X10 = 4 * (d.significand : Int) * Y10 * B2 ∧ m_f % 2 = 0 := h_left
  have h_right_named :
      4 * (d.significand : Int) * Y10 * (2 : Int)^1074 ≤ 2 * X10 := h_fourU0_le
  -- Bridge B2 · DPow = 2^1074, A2 · DPow = α2.
  have h_bridge_BD : B2 * DPow = (2 : Int)^1074 := h_pow_split
  have h_bridge_AD : A2 * DPow = α2 := h_pow_combine
  -- Multiply left bracket by DPow ≥ 0:
  --   L * A2 * X10 * DPow vs 4·sig · Y10 · B2 · DPow.
  --   RHS = 4·sig · Y10 · (B2 · DPow) = 4·sig · Y10 · 2^1074.
  --   LHS = L · (A2 · DPow) · X10 = L · α2 · X10.
  have h_chainLHS : L * A2 * X10 * DPow = L * α2 * X10 := by
    calc L * A2 * X10 * DPow
        = L * (A2 * DPow) * X10 := by grind
      _ = L * α2 * X10 := by rw [h_bridge_AD]
  have h_chainRHS :
      4 * (d.significand : Int) * Y10 * B2 * DPow
        = 4 * (d.significand : Int) * Y10 * (2 : Int)^1074 := by
    calc 4 * (d.significand : Int) * Y10 * B2 * DPow
        = 4 * (d.significand : Int) * Y10 * (B2 * DPow) := by grind
      _ = 4 * (d.significand : Int) * Y10 * (2 : Int)^1074 := by rw [h_bridge_BD]
  -- L · α2 · X10 ≤ 4·sig · Y10 · 2^1074 ≤ 2 · X10. So L · α2 · X10 ≤ 2 · X10.
  have h_combined : L * α2 * X10 ≤ 2 * X10 := by
    rcases h_left_named with hstrict | ⟨heq, _⟩
    · -- Strict version: L·A2·X10 < 4·sig·Y10·B2. Multiply by DPow > 0.
      have h_step : L * A2 * X10 * DPow ≤ 4 * (d.significand : Int) * Y10 * B2 * DPow :=
        Int.mul_le_mul_of_nonneg_right (Int.le_of_lt hstrict) (Int.le_of_lt hDPow_pos)
      have h1 : L * α2 * X10 ≤ 4 * (d.significand : Int) * Y10 * (2 : Int)^1074 := by
        rw [← h_chainLHS, ← h_chainRHS]; exact h_step
      grind
    · -- Equality version: L·A2·X10 = 4·sig·Y10·B2. Multiply by DPow.
      have h_step : L * A2 * X10 * DPow = 4 * (d.significand : Int) * Y10 * B2 * DPow := by
        rw [heq]
      have h1 : L * α2 * X10 = 4 * (d.significand : Int) * Y10 * (2 : Int)^1074 := by
        rw [← h_chainLHS, h_step, h_chainRHS]
      grind
  -- Divide by X10 > 0: L · α2 ≤ 2.
  have h_prod_le : L * α2 ≤ 2 :=
    Int.le_of_mul_le_mul_right (by grind : (L * α2) * X10 ≤ 2 * X10) hX10_pos
  -- And L · α2 ≥ 2.
  have h_prod_ge : (2 : Int) ≤ L * α2 := by
    have hL_pos : (0 : Int) < L := by grind
    calc (2 : Int) = 2 * 1 := by grind
      _ ≤ L * 1 := by grind
      _ ≤ L * α2 := Int.mul_le_mul_of_nonneg_left hpow_α_ge_one (Int.le_of_lt hL_pos)
  -- L · α2 = 2.
  have h_prod_eq : L * α2 = 2 := le_antisymm h_prod_le h_prod_ge
  -- L ≥ 2 and α2 ≥ 1, and product = 2. So L = 2 and α2 = 1.
  have hL_eq_2 : L = 2 := by
    by_contra hne
    have h_gt : L > 2 := by
      have h2 : (2 : Int) ≤ L := by grind
      omega
    have hα2_pos' : (0 : Int) < α2 := hα2_pos
    have : L * α2 > 2 * 1 := by
      have : L * α2 ≥ L * 1 := by
        have hL_pos : (0 : Int) < L := by grind
        exact Int.mul_le_mul_of_nonneg_left hpow_α_ge_one (Int.le_of_lt hL_pos)
      have : L * α2 ≥ L := by grind
      grind
    grind
  have hα2_eq_1 : α2 = 1 := by
    have h := h_prod_eq
    rw [hL_eq_2] at h
    grind
  -- α2 = 1 ⟹ α = 0.
  have hα_zero : α = 0 := by
    by_contra hne
    have hpos : 0 < α := Nat.pos_of_ne_zero hne
    have h2pow_ge_2 : (2 : Int) ≤ (2 : Int)^α := by
      calc (2 : Int) = (2 : Int)^1 := by grind
        _ ≤ (2 : Int)^α := by
            apply pow_le_pow_right₀ (by decide) hpos
    rw [← hα2_def] at h2pow_ge_2
    grind
  -- So q_f = -1074.
  have hqf_eq : q_f = -1074 := hα_eq_iff.mp hα_zero
  -- L = 2 forces ¬isIrregular m_f q_f and m_f = 1.
  have hirreg_false : isIrregular m_f q_f = false := by
    by_cases hi : isIrregular m_f q_f
    · rw [hL_def, if_pos hi] at hL_eq_2
      -- 4·m_f - 1 = 2 ⟹ 4 m_f = 3, contradiction with m_f ≥ 1.
      have : (4 : Int) * (m_f : Int) = 3 := by grind
      grind
    · cases h_val : isIrregular m_f q_f with
      | true => exact absurd h_val hi
      | false => rfl
  have hmf_eq : m_f = 1 := by
    rw [hL_def, hirreg_false, if_neg (by decide : ¬ (false = true))] at hL_eq_2
    have : (4 : Int) * (m_f : Int) = 4 := by grind
    have : (m_f : Int) = 1 := by grind
    exact_mod_cast this
  -- Now use the right bracket (or left bracket) parity: in the equality case
  -- we need m_f % 2 = 0, but m_f = 1 is odd.
  -- The left bracket case-split: it's either strict or equality with parity.
  -- We don't directly know which case fired in h_left_named at this point.
  -- However: from h_prod_eq = 2 we deduced L · α2 · X10 = 2 · X10, hence
  -- L · A2 · X10 · DPow = 4 · sig · Y10 · B2 · DPow, and cancelling DPow > 0:
  -- L · A2 · X10 = 4 · sig · Y10 · B2. So the equality case must have fired.
  have h_chain_eq : L * A2 * X10 = 4 * (d.significand : Int) * Y10 * B2 := by
    rcases h_left_named with hstrict | ⟨heq, _⟩
    · exfalso
      -- strict case: L · A2 · X10 < 4·sig·Y10·B2. Multiply by DPow > 0:
      --   L · A2 · X10 · DPow < 4·sig·Y10·B2·DPow.
      -- LHS = L · α2 · X10 = 2 · X10 (from h_combined being equality)
      -- RHS = 4·sig·Y10·2^1074
      -- Combined with h_fourU0_le: 4·sig·Y10·2^1074 ≤ 2·X10.
      -- So L · α2 · X10 < ... ≤ 2 · X10. But L · α2 · X10 = 2 · X10. Contradiction.
      have h_eq_LHS : L * α2 * X10 = 2 * X10 := by
        have h1 : L * α2 * X10 ≤ 2 * X10 := h_combined
        have h2 : (2 : Int) ≤ L * α2 := h_prod_ge
        have h3 : (L * α2) * X10 ≥ 2 * X10 := by
          have hX10_nn : (0 : Int) ≤ X10 := Int.le_of_lt hX10_pos
          exact Int.mul_le_mul_of_nonneg_right h2 hX10_nn
        grind
      -- Multiply hstrict by DPow > 0:
      have h_step_strict : L * A2 * X10 * DPow < 4 * (d.significand : Int) * Y10 * B2 * DPow :=
        Int.mul_lt_mul_of_pos_right hstrict hDPow_pos
      rw [h_chainLHS, h_chainRHS] at h_step_strict
      grind
    · exact heq
  -- Get the parity from the equality case directly.
  rcases h_left_named with hstrict | ⟨heq, h_parity⟩
  · exfalso
    -- Contradicts h_chain_eq.
    grind
  · -- h_parity : m_f % 2 = 0. But m_f = 1, contradiction.
    rw [hmf_eq] at h_parity
    exact absurd h_parity (by decide)

/-! ## Sorry C: `IsFiniteAbs` from `inRoundingInterval` witness

Given the canonical Schubfach output `(d.sig, d.exp)` and the legal IEEE pair
`(m_f, q_f)` whose rounding interval it falls in, the abstract Clinger decode
`decodedAbs d.sign d.sig d.exp` cannot hit the overflow branch.

We extract a uniform right-bracket bound: in cleared form,
`4·sig·10^kPos·2^qfNeg ≤ (4·m_f + 2)·2^qfPos·10^kNeg`. This is `<` unless
`m_f` is even. We use this to rule out both the direct overflow branch and
the normal-with-carry-to-overflow branch. -/

/-- Cleared-form right bracket from `inRoundingInterval`, in `a, b` form
where `a = sig · 10^kPos` and `b = 10^kNeg`. -/
private theorem rv_right_bracket_int
    (sig : Nat) (exp : Int) (m_f : Nat) (q_f : Int)
    (h_rv : inRoundingInterval sig exp m_f q_f (isIrregular m_f q_f) = true) :
    let kPos : Nat := if exp ≥ 0 then exp.toNat else 0
    let kNeg : Nat := if exp < 0 then (-exp).toNat else 0
    let qfPos : Nat := if q_f ≥ 0 then q_f.toNat else 0
    let qfNeg : Nat := if q_f < 0 then (-q_f).toNat else 0
    (4 * (sig : Int) * (10 : Int) ^ kPos * (2 : Int) ^ qfNeg <
       (4 * (m_f : Int) + 2) * (2 : Int) ^ qfPos * (10 : Int) ^ kNeg)
    ∨ (4 * (sig : Int) * (10 : Int) ^ kPos * (2 : Int) ^ qfNeg =
         (4 * (m_f : Int) + 2) * (2 : Int) ^ qfPos * (10 : Int) ^ kNeg ∧ m_f % 2 = 0) := by
  rw [inRoundingInterval_iff] at h_rv
  obtain ⟨_, h_right⟩ := h_rv
  -- The right bracket is in fourU, fourVR form. Unfold these.
  simp only [fourU, fourVR, cmpScaledMixed.lhs, cmpScaledMixed.rhs] at h_right
  exact h_right

/-- Discrete bound on `(4·m_f + 2)·2^qfPos`: at most `(2^55 - 2)·2^971`. -/
private theorem rhs_bound_basic (m_f : Nat) (q_f : Int) (h_legal_f : LegalIEEE m_f q_f) :
    let qfPos : Nat := if q_f ≥ 0 then q_f.toNat else 0
    (4 * (m_f : Int) + 2) * (2 : Int) ^ qfPos ≤
      ((2 : Int) ^ 55 - 2) * (2 : Int) ^ 971 := by
  simp only
  -- m_f < 2^53.
  have hmf_lt : m_f < 2 ^ 53 := by
    rcases h_legal_f with ⟨_, hm, _⟩ | ⟨_, hm, _, _⟩
    · have h52 : (2 : Nat) ^ 52 ≤ 2 ^ 53 := by decide
      omega
    · exact hm
  have hmf_lt_Int : (m_f : Int) < (2 : Int) ^ 53 := by exact_mod_cast hmf_lt
  -- q_f ≤ 971.
  have hqf_le : q_f ≤ 971 := by
    rcases h_legal_f with ⟨_, _, hq⟩ | ⟨_, _, _, hq⟩
    · omega
    · exact hq
  set qfPos : Nat := if q_f ≥ 0 then q_f.toNat else 0 with hqfPos_def
  have hqfPos_le : qfPos ≤ 971 := by
    rw [hqfPos_def]
    by_cases h : q_f ≥ 0
    · rw [if_pos h]
      omega
    · rw [if_neg h]; omega
  -- (4 m_f + 2) ≤ 2^55 - 2 (since m_f ≤ 2^53 - 1).
  have h_4mf_le : 4 * (m_f : Int) + 2 ≤ (2 : Int) ^ 55 - 2 := by
    have h53eq : (2 : Int) ^ 53 = 9007199254740992 := by decide
    have h55eq : (2 : Int) ^ 55 = 36028797018963968 := by decide
    have h_step : (m_f : Int) ≤ 2 ^ 53 - 1 := by grind
    grind
  have h_4mf_nn : (0 : Int) ≤ 4 * (m_f : Int) + 2 := by
    have : (0 : Int) ≤ (m_f : Int) := Int.natCast_nonneg _
    grind
  -- (2^qfPos) ≤ 2^971.
  have h_2qfPos_le : (2 : Int) ^ qfPos ≤ (2 : Int) ^ 971 :=
    pow_le_pow_right₀ (by decide) hqfPos_le
  -- (2^971) > 0.
  have h_2_971_pos : (0 : Int) < (2 : Int) ^ 971 := Int.pow_pos (by decide)
  -- Chain: (4 m_f + 2)·2^qfPos ≤ (4 m_f + 2)·2^971 ≤ (2^55 - 2)·2^971.
  have h_step1 : (4 * (m_f : Int) + 2) * (2 : Int) ^ qfPos
                  ≤ (4 * (m_f : Int) + 2) * (2 : Int) ^ 971 :=
    Int.mul_le_mul_of_nonneg_left h_2qfPos_le h_4mf_nn
  have h_step2 : (4 * (m_f : Int) + 2) * (2 : Int) ^ 971
                  ≤ ((2 : Int) ^ 55 - 2) * (2 : Int) ^ 971 :=
    Int.mul_le_mul_of_nonneg_right h_4mf_le (Int.le_of_lt h_2_971_pos)
  exact Int.le_trans h_step1 h_step2

/-- Discrete bound on `(4·m_f + 2)·2^qfPos` when `m_f` is even: at most
`(2^55 - 6)·2^971` (since `m_f ≤ 2^53 - 2`). -/
private theorem rhs_bound_even (m_f : Nat) (q_f : Int)
    (h_legal_f : LegalIEEE m_f q_f) (h_m_even : m_f % 2 = 0) :
    let qfPos : Nat := if q_f ≥ 0 then q_f.toNat else 0
    (4 * (m_f : Int) + 2) * (2 : Int) ^ qfPos ≤
      ((2 : Int) ^ 55 - 6) * (2 : Int) ^ 971 := by
  simp only
  -- m_f < 2^53.
  have hmf_lt : m_f < 2 ^ 53 := by
    rcases h_legal_f with ⟨_, hm, _⟩ | ⟨_, hm, _, _⟩
    · have h52 : (2 : Nat) ^ 52 ≤ 2 ^ 53 := by decide
      omega
    · exact hm
  -- m_f even ⟹ m_f ≠ 2^53 - 1, so m_f ≤ 2^53 - 2.
  have hmf_le_strict : m_f ≤ 2 ^ 53 - 2 := by
    have hodd : (2 ^ 53 - 1 : Nat) % 2 = 1 := by decide
    by_contra hne
    push_neg at hne
    have hmf_eq : m_f = 2 ^ 53 - 1 := by omega
    rw [hmf_eq] at h_m_even
    omega
  have hmf_le_strict_Int : (m_f : Int) ≤ (2 : Int) ^ 53 - 2 := by
    have h53eq : (2 : Int) ^ 53 = 9007199254740992 := by decide
    have : ((m_f : Nat) : Int) ≤ ((2 ^ 53 - 2 : Nat) : Int) := by exact_mod_cast hmf_le_strict
    have h_rhs : ((2 ^ 53 - 2 : Nat) : Int) = (2 : Int) ^ 53 - 2 := by
      have : (2 : Nat) ^ 53 = 9007199254740992 := by decide
      omega
    grind
  -- q_f ≤ 971.
  have hqf_le : q_f ≤ 971 := by
    rcases h_legal_f with ⟨_, _, hq⟩ | ⟨_, _, _, hq⟩
    · omega
    · exact hq
  set qfPos : Nat := if q_f ≥ 0 then q_f.toNat else 0 with hqfPos_def
  have hqfPos_le : qfPos ≤ 971 := by
    rw [hqfPos_def]
    by_cases h : q_f ≥ 0
    · rw [if_pos h]
      omega
    · rw [if_neg h]; omega
  -- (4 m_f + 2) ≤ 2^55 - 6.
  have h_4mf_le_strict : 4 * (m_f : Int) + 2 ≤ (2 : Int) ^ 55 - 6 := by
    have h53eq : (2 : Int) ^ 53 = 9007199254740992 := by decide
    have h55eq : (2 : Int) ^ 55 = 36028797018963968 := by decide
    grind
  have h_4mf_nn : (0 : Int) ≤ 4 * (m_f : Int) + 2 := by
    have : (0 : Int) ≤ (m_f : Int) := Int.natCast_nonneg _
    grind
  -- (2^qfPos) ≤ 2^971.
  have h_2qfPos_le : (2 : Int) ^ qfPos ≤ (2 : Int) ^ 971 :=
    pow_le_pow_right₀ (by decide) hqfPos_le
  have h_2_971_pos : (0 : Int) < (2 : Int) ^ 971 := Int.pow_pos (by decide)
  have h_step1 : (4 * (m_f : Int) + 2) * (2 : Int) ^ qfPos
                  ≤ (4 * (m_f : Int) + 2) * (2 : Int) ^ 971 :=
    Int.mul_le_mul_of_nonneg_left h_2qfPos_le h_4mf_nn
  have h_step2 : (4 * (m_f : Int) + 2) * (2 : Int) ^ 971
                  ≤ ((2 : Int) ^ 55 - 6) * (2 : Int) ^ 971 :=
    Int.mul_le_mul_of_nonneg_right h_4mf_le_strict (Int.le_of_lt h_2_971_pos)
  exact Int.le_trans h_step1 h_step2

/-- Identity: `(2^55 - 2) · 2^971 = 2^1026 - 2^972`. -/
private theorem pow_identity_basic :
    ((2 : Int) ^ 55 - 2) * (2 : Int) ^ 971 = (2 : Int) ^ 1026 - (2 : Int) ^ 972 := by
  have h1 : (2 : Int) ^ 55 * (2 : Int) ^ 971 = (2 : Int) ^ 1026 := by
    rw [← Int.pow_add]
  have h2 : (2 : Int) ^ 972 = 2 * (2 : Int) ^ 971 := by
    rw [show (972 : Nat) = 971 + 1 from rfl, Int.pow_succ]; grind
  have : ((2 : Int) ^ 55 - 2) * (2 : Int) ^ 971
          = (2 : Int) ^ 55 * (2 : Int) ^ 971 - 2 * (2 : Int) ^ 971 := by grind
  rw [this, h1, ← h2]

/-- Identity: `(2^55 - 6) · 2^971 < 2^1026 - 2^972`. -/
private theorem pow_identity_strict :
    ((2 : Int) ^ 55 - 6) * (2 : Int) ^ 971 < (2 : Int) ^ 1026 - (2 : Int) ^ 972 := by
  have h1 : (2 : Int) ^ 55 * (2 : Int) ^ 971 = (2 : Int) ^ 1026 := by
    rw [← Int.pow_add]
  have h2 : (2 : Int) ^ 972 = 2 * (2 : Int) ^ 971 := by
    rw [show (972 : Nat) = 971 + 1 from rfl, Int.pow_succ]; grind
  have h_2_971_pos : (0 : Int) < (2 : Int) ^ 971 := Int.pow_pos (by decide)
  -- (2^55 - 6) · 2^971 = 2^1026 - 6·2^971.
  -- 2^1026 - 2^972 = 2^1026 - 2·2^971.
  -- (2^1026 - 6·2^971) < (2^1026 - 2·2^971) ⟺ -6·2^971 < -2·2^971 ⟺ 2·2^971 < 6·2^971, true.
  have h_eq1 : ((2 : Int) ^ 55 - 6) * (2 : Int) ^ 971
          = (2 : Int) ^ 1026 - 6 * (2 : Int) ^ 971 := by
    have : ((2 : Int) ^ 55 - 6) * (2 : Int) ^ 971
            = (2 : Int) ^ 55 * (2 : Int) ^ 971 - 6 * (2 : Int) ^ 971 := by grind
    rw [this, h1]
  rw [h_eq1, h2]
  -- Goal: 2^1026 - 6 · 2^971 < 2^1026 - 2 · 2^971. Need 6·2^971 > 2·2^971.
  set X := (2 : Int) ^ 971 with hX_def
  have hX_pos : (0 : Int) < X := Int.pow_pos (by decide)
  -- Goal: 2^1026 - 6 * X < 2^1026 - 2 * X.
  omega

/-- **Sorry C closure**: from the `inRoundingInterval` witness on a legal IEEE
pair, `IsFiniteAbs` holds.

We prove the equivalent: `(decodedAbs d.sign d.sig d.exp).q ≤ 971`. The
`decodedAbs` branches are:
* zero sig: q = -1074 (ruled out by `d.sig ≠ 0`, but harmless if it fired)
* overflow `e > 1023`: q = 1024 (must rule out)
* normal no-carry: q = e - 52, with `e ≤ 1023` ⟹ q ≤ 971 ✓
* normal with carry, `e ≤ 1022`: q = e - 51 ≤ 971 ✓
* normal with carry, `e = 1023`: q = 1024 (must rule out)
* subnormal: q = -1074 ✓

The two failing branches both require `4·a·2^qfNeg ≥ b·(2^1026 - 2^972)`,
which contradicts the right-bracket bound
`4·a·2^qfNeg ≤ (4 m_f + 2)·2^qfPos·b ≤ (2^1026 - 2^972)·b` since `b > 0` and
either we have strict (m_f odd) or m_f even forces a tighter `(2^1026 -
6·2^971)·b` bound. -/
-- Emits one benign `exponentiation.threshold` warning (deduped from many sites in this proof).
-- Do not silence by raising the threshold: `push_cast`/`simp` then evaluate `2^1024` literals
-- and overflow the stack.
theorem isFiniteAbs_of_rv
    (d : Decimal) (m_f : Nat) (q_f : Int)
    (h_legal_f : LegalIEEE m_f q_f)
    (h_d_sig_ne : d.significand ≠ 0)
    (h_rv : inRoundingInterval d.significand d.exponent m_f q_f (isIrregular m_f q_f) = true) :
    IsFiniteAbs d.sign d.significand d.exponent := by
  -- Extract the right bracket in (a, b)-form.
  have h_bracket := rv_right_bracket_int d.significand d.exponent m_f q_f h_rv
  simp only at h_bracket
  -- Abbreviate the kPos, kNeg, qfPos, qfNeg.
  set kPos : Nat := if d.exponent ≥ 0 then d.exponent.toNat else 0 with hkPos_def
  set kNeg : Nat := if d.exponent < 0 then (-d.exponent).toNat else 0 with hkNeg_def
  set qfPos : Nat := if q_f ≥ 0 then q_f.toNat else 0 with hqfPos_def
  set qfNeg : Nat := if q_f < 0 then (-q_f).toNat else 0 with hqfNeg_def
  -- Define a, b as Nat.
  set a : Nat := d.significand * 10 ^ kPos with ha_def
  set b : Nat := 10 ^ kNeg with hb_def
  -- Cast lemmas.
  have h_a_cast : (a : Int) = (d.significand : Int) * (10 : Int) ^ kPos := by
    rw [ha_def]; push_cast; rfl
  have h_b_cast : (b : Int) = (10 : Int) ^ kNeg := by
    rw [hb_def]; push_cast; rfl
  -- Reshape h_bracket: 4·d.sig·10^kPos·2^qfNeg = 4·a·2^qfNeg (using h_a_cast).
  --                    (4·m_f+2)·2^qfPos·10^kNeg = (4·m_f+2)·2^qfPos·b (using h_b_cast).
  have h_bracket' :
      (4 * (a : Int) * (2 : Int) ^ qfNeg <
         (4 * (m_f : Int) + 2) * (2 : Int) ^ qfPos * (b : Int))
      ∨ (4 * (a : Int) * (2 : Int) ^ qfNeg =
           (4 * (m_f : Int) + 2) * (2 : Int) ^ qfPos * (b : Int) ∧ m_f % 2 = 0) := by
    rcases h_bracket with h | ⟨h, hm⟩
    · left; rw [h_a_cast, h_b_cast]; grind
    · right
      refine ⟨?_, hm⟩
      rw [h_a_cast, h_b_cast]; grind
  -- Positivity.
  have ha_pos : 0 < a := by
    rw [ha_def]
    exact Nat.mul_pos (Nat.pos_of_ne_zero h_d_sig_ne) (Nat.pow_pos (by decide))
  have hb_pos : 0 < b := by rw [hb_def]; exact Nat.pow_pos (by decide)
  have ha_pos_Int : (0 : Int) < (a : Int) := by exact_mod_cast ha_pos
  have hb_pos_Int : (0 : Int) < (b : Int) := by exact_mod_cast hb_pos
  -- Bound on RHS: (4 m_f + 2)·2^qfPos ≤ (2^55 - 2)·2^971.
  have h_rhs_basic : (4 * (m_f : Int) + 2) * (2 : Int) ^ qfPos
                      ≤ ((2 : Int) ^ 55 - 2) * (2 : Int) ^ 971 := by
    have := rhs_bound_basic m_f q_f h_legal_f
    exact this
  -- Bound on RHS · b: (4 m_f + 2)·2^qfPos·b ≤ ((2^55-2)·2^971)·b = (2^1026-2^972)·b.
  have h_rhs_b_le : (4 * (m_f : Int) + 2) * (2 : Int) ^ qfPos * (b : Int)
                     ≤ ((2 : Int) ^ 1026 - (2 : Int) ^ 972) * (b : Int) := by
    have h_b_nn : (0 : Int) ≤ (b : Int) := Int.le_of_lt hb_pos_Int
    have h_step : (4 * (m_f : Int) + 2) * (2 : Int) ^ qfPos * (b : Int)
                    ≤ (((2 : Int) ^ 55 - 2) * (2 : Int) ^ 971) * (b : Int) :=
      Int.mul_le_mul_of_nonneg_right h_rhs_basic h_b_nn
    rw [pow_identity_basic] at h_step
    exact h_step
  -- Bound on LHS: 4·a·2^qfNeg ≤ (2^1026-2^972)·b.
  have h_lhs_le : 4 * (a : Int) * (2 : Int) ^ qfNeg
                    ≤ ((2 : Int) ^ 1026 - (2 : Int) ^ 972) * (b : Int) := by
    rcases h_bracket' with h_strict | ⟨h_eq, _⟩
    · exact Int.le_trans (Int.le_of_lt h_strict) h_rhs_b_le
    · exact Int.le_trans (Int.le_of_eq h_eq) h_rhs_b_le
  -- Set up Y := 2^qfNeg, Z := 2^971, W := 2^1026 - 2^972 = 2^1026 - 2*Z.
  -- Eventually we want to translate "a ≥ b · 2^1024" (overflow case)
  -- or "2 a ≥ b · (2^1025 - 2^971)" (carry case)
  -- into a contradiction with h_lhs_le.
  -- Unfold IsFiniteAbs and decodedAbs.
  unfold IsFiniteAbs
  rw [decodedAbs_nonzero d.sign d.significand d.exponent h_d_sig_ne]
  -- Branch structure. Use `show` to match.
  show (let (a', b') : Nat × Nat :=
        if d.exponent ≥ 0 then (d.significand * 10 ^ d.exponent.toNat, 1)
        else (d.significand, 10 ^ (-d.exponent).toNat)
        let e := findBinaryExp a' b'
        if e > 1023 then ({ sign := d.sign, m := 0, q := 1024 } : Decoded)
        else if e ≥ -1022 then
          let (num, denom) := scaleByPow2 a' b' (52 - e)
          let m := roundNearestEven num denom
          if m ≥ 2 ^ 53 then
            let e' := e + 1
            if e' > 1023 then ({ sign := d.sign, m := 0, q := 1024 } : Decoded)
            else { sign := d.sign, m := 1 <<< 52, q := e' - 52 }
          else { sign := d.sign, m := m, q := e - 52 }
        else
          let (num, denom) := scaleByPow2 a' b' 1074
          let m := roundNearestEven num denom
          if m = 0 then { sign := d.sign, m := 0, q := -1074 }
          else if m ≥ 2 ^ 52 then { sign := d.sign, m := m, q := -1074 }
          else { sign := d.sign, m := m, q := -1074 }).q ≤ 971
  -- The (a', b') match in the goal needs to be reduced to (a, b).
  have h_ab_eq : (if d.exponent ≥ 0 then (d.significand * 10 ^ d.exponent.toNat, 1)
                  else (d.significand, 10 ^ (-d.exponent).toNat)) = (a, b) := by
    by_cases h_e : d.exponent ≥ 0
    · rw [if_pos h_e]
      have h_kP : kPos = d.exponent.toNat := by
        rw [hkPos_def, if_pos h_e]
      have h_kN : kNeg = 0 := by
        rw [hkNeg_def, if_neg (by omega : ¬ d.exponent < 0)]
      have ha_eq : a = d.significand * 10 ^ d.exponent.toNat := by
        rw [ha_def, h_kP]
      have hb_eq : b = 1 := by
        rw [hb_def, h_kN, Nat.pow_zero]
      rw [ha_eq, hb_eq]
    · rw [if_neg h_e]
      have h_kP : kPos = 0 := by
        rw [hkPos_def, if_neg h_e]
      have h_kN : kNeg = (-d.exponent).toNat := by
        rw [hkNeg_def, if_pos (by omega : d.exponent < 0)]
      have ha_eq : a = d.significand := by
        rw [ha_def, h_kP, Nat.pow_zero, Nat.mul_one]
      have hb_eq : b = 10 ^ (-d.exponent).toNat := by
        rw [hb_def, h_kN]
      rw [ha_eq, hb_eq]
  rw [h_ab_eq]
  simp only
  set e := findBinaryExp a b with he_def
  -- The two "bad" branches are (a) e > 1023 and (b) e = 1023 with carry.
  -- We'll show contradiction in both.
  -- KEY: derive contradiction from h_lhs_le and a lower bound on 4·a·2^qfNeg
  -- (provided by either overflow lower bound or carry lower bound).
  -- Helper: `4·c·2^qfNeg ≤ W·b` for any c ≥ b·2^1024 (then derive `4·b·2^1024·2^qfNeg ≤ W·b`,
  -- yielding `4·2^1024·2^qfNeg ≤ W`, hence `4·2^1024 ≤ W`, contradiction).
  -- Bound: 4·2^1024 = 2^1026 > 2^1026 - 2^972 = W. So contradiction.
  by_cases h_over : e > 1023
  · -- Overflow case. e > 1023 ⟹ b · 2^1024 ≤ a.
    exfalso
    have h_fb_le_bool := findBinaryExp_le a b ha_pos hb_pos
    rw [leBy2e_eq_true_iff] at h_fb_le_bool
    have h_e_nn : e ≥ 0 := by rw [he_def]; omega
    rw [if_pos h_e_nn] at h_fb_le_bool
    have h_e_toNat_ge : e.toNat ≥ 1024 := by
      have h1024 : (1024 : Int) ≤ e := by grind
      omega
    have h_b_1024_le_a : b * 2 ^ 1024 ≤ a := by
      have h_pow_le : b * 2 ^ 1024 ≤ b * 2 ^ e.toNat :=
        Nat.mul_le_mul_left b (Nat.pow_le_pow_right (by decide) h_e_toNat_ge)
      have : b * 2 ^ e.toNat ≤ a := by
        rw [← he_def] at h_fb_le_bool
        exact h_fb_le_bool
      omega
    have h_b_1024_le_a_Int : (b : Int) * (2 : Int) ^ 1024 ≤ (a : Int) := by
      have := h_b_1024_le_a
      have h_cast : ((b * 2 ^ 1024 : Nat) : Int) = (b : Int) * (2 : Int) ^ 1024 := by
        push_cast; rfl
      have h_le_Int : ((b * 2 ^ 1024 : Nat) : Int) ≤ (a : Int) := by exact_mod_cast this
      grind
    -- Multiply by 4·2^qfNeg > 0.
    have h_2qfNeg_pos : (0 : Int) < (2 : Int) ^ qfNeg := Int.pow_pos (by decide)
    have h_4_2qfNeg_pos : (0 : Int) < 4 * (2 : Int) ^ qfNeg := by
      have : (0 : Int) < 4 := by decide
      exact Int.mul_pos this h_2qfNeg_pos
    have h_lhs_lower : 4 * (b : Int) * (2 : Int) ^ 1024 * (2 : Int) ^ qfNeg
                        ≤ 4 * (a : Int) * (2 : Int) ^ qfNeg := by
      have h_b_1024_4 : 4 * ((b : Int) * (2 : Int) ^ 1024) ≤ 4 * (a : Int) := by grind
      have h_step : (4 * ((b : Int) * (2 : Int) ^ 1024)) * (2 : Int) ^ qfNeg
                      ≤ (4 * (a : Int)) * (2 : Int) ^ qfNeg :=
        Int.mul_le_mul_of_nonneg_right h_b_1024_4 (Int.le_of_lt h_2qfNeg_pos)
      have h_eq1 : 4 * (b : Int) * (2 : Int) ^ 1024 * (2 : Int) ^ qfNeg
                    = (4 * ((b : Int) * (2 : Int) ^ 1024)) * (2 : Int) ^ qfNeg := by grind
      have h_eq2 : 4 * (a : Int) * (2 : Int) ^ qfNeg
                    = (4 * (a : Int)) * (2 : Int) ^ qfNeg := by grind
      grind
    -- Combine: 4·b·2^1024·2^qfNeg ≤ 4·a·2^qfNeg ≤ ((2^1026 - 2^972)·b).
    have h_chain : 4 * (b : Int) * (2 : Int) ^ 1024 * (2 : Int) ^ qfNeg
                    ≤ ((2 : Int) ^ 1026 - (2 : Int) ^ 972) * (b : Int) :=
      Int.le_trans h_lhs_lower h_lhs_le
    -- Divide by b: 4·2^1024·2^qfNeg ≤ (2^1026 - 2^972).
    have h_lhs_b_factored : 4 * (b : Int) * (2 : Int) ^ 1024 * (2 : Int) ^ qfNeg
                              = (4 * (2 : Int) ^ 1024 * (2 : Int) ^ qfNeg) * (b : Int) := by grind
    rw [h_lhs_b_factored] at h_chain
    have h_div_b : 4 * (2 : Int) ^ 1024 * (2 : Int) ^ qfNeg
                    ≤ (2 : Int) ^ 1026 - (2 : Int) ^ 972 :=
      Int.le_of_mul_le_mul_right h_chain hb_pos_Int
    -- 4·2^1024 = 2^1026.
    have h_4_2pow : 4 * (2 : Int) ^ 1024 = (2 : Int) ^ 1026 := by
      have h_eq : (4 : Int) = (2 : Int) ^ 2 := by decide
      rw [h_eq, ← Int.pow_add]
    rw [h_4_2pow] at h_div_b
    -- 2^1026 · 2^qfNeg ≥ 2^1026 (qfNeg ≥ 0). Combined with bound: 2^1026 ≤ 2^1026 - 2^972. Contradiction.
    have h_2qfNeg_ge_one : (1 : Int) ≤ (2 : Int) ^ qfNeg :=
      one_le_pow_of_le (by decide : (1 : Int) ≤ 2) _
    have h_2_1026_pos : (0 : Int) < (2 : Int) ^ 1026 := Int.pow_pos (by decide)
    have h_2_1026_mul : (2 : Int) ^ 1026 ≤ (2 : Int) ^ 1026 * (2 : Int) ^ qfNeg := by
      calc (2 : Int) ^ 1026 = (2 : Int) ^ 1026 * 1 := by grind
        _ ≤ (2 : Int) ^ 1026 * (2 : Int) ^ qfNeg :=
            Int.mul_le_mul_of_nonneg_left h_2qfNeg_ge_one (Int.le_of_lt h_2_1026_pos)
    have h_2_972_pos : (0 : Int) < (2 : Int) ^ 972 := Int.pow_pos (by decide)
    -- We have: h_div_b : 2^1026 * 2^qfNeg ≤ 2^1026 - 2^972 AND h_2_1026_mul : 2^1026 ≤ 2^1026 * 2^qfNeg.
    -- Combined: 2^1026 ≤ 2^1026 - 2^972. With h_2_972_pos: 2^972 > 0 ⟹ 2^1026 - 2^972 < 2^1026.
    -- Use omega with set aliases.
    set P := (2 : Int) ^ 1026
    set Q := (2 : Int) ^ 972
    set R := (2 : Int) ^ qfNeg
    omega
  · push_neg at h_over
    -- e ≤ 1023.
    by_cases h_normal_range : e ≥ -1022
    · simp only [if_neg (by grind : ¬ e > 1023), if_pos h_normal_range]
      -- m_round case.
      by_cases h_carry : roundNearestEven (scaleByPow2 a b (52 - e)).1
                                          (scaleByPow2 a b (52 - e)).2 ≥ 2 ^ 53
      · simp only [if_pos h_carry]
        by_cases h_carry_over : e + 1 > 1023
        · -- e = 1023 ∧ carry: contradiction.
          exfalso
          have h_e_eq : e = 1023 := by grind
          -- The carry inequality: 2·a ≥ b·(2^1025 - 2^971).
          have h_scale_eq : scaleByPow2 a b (52 - e) = (a, b * 2 ^ 971) := by
            rw [h_e_eq]
            show scaleByPow2 a b (52 - 1023) = (a, b * 2 ^ 971)
            unfold scaleByPow2
            have h_neg : ¬ ((52 - 1023 : Int) ≥ 0) := by decide
            rw [if_neg h_neg]
            have h_to : (-(52 - 1023 : Int)).toNat = 971 := by decide
            rw [h_to]
          have h_m_round : roundNearestEven a (b * 2 ^ 971) ≥ 2 ^ 53 := by
            rw [h_scale_eq] at h_carry; exact h_carry
          have h_denom_pos : 0 < b * 2 ^ 971 := Nat.mul_pos hb_pos (Nat.pow_pos (by decide))
          obtain ⟨_, h_round_high⟩ := roundNearestEven_cleared_bound a (b * 2 ^ 971) h_denom_pos
          -- h_round_high : 2·(m_round)·(b·2^971) ≤ 2·a + (b·2^971).
          have h_m_round_Int : ((2 ^ 53 : Nat) : Int)
                                ≤ (roundNearestEven a (b * 2 ^ 971) : Int) := by
            exact_mod_cast h_m_round
          have h_2_53_cast : ((2 ^ 53 : Nat) : Int) = (2 : Int) ^ 53 := by omega
          rw [h_2_53_cast] at h_m_round_Int
          have h_b_2_971_cast : ((b * 2 ^ 971 : Nat) : Int) = (b : Int) * (2 : Int) ^ 971 := by
            push_cast; rfl
          -- 2·2^53·(b·2^971) ≤ 2·m_round·(b·2^971).
          have h_b_2_971_Int_pos : (0 : Int) < (b : Int) * (2 : Int) ^ 971 := by
            exact Int.mul_pos hb_pos_Int (Int.pow_pos (by decide))
          have h_b_2_971_Int_nn : (0 : Int) ≤ (b : Int) * (2 : Int) ^ 971 :=
            Int.le_of_lt h_b_2_971_Int_pos
          have h_step1 : 2 * (2 : Int) ^ 53 * ((b : Int) * (2 : Int) ^ 971)
                        ≤ 2 * (roundNearestEven a (b * 2 ^ 971) : Int)
                          * ((b : Int) * (2 : Int) ^ 971) := by
            have h_2_step : 2 * (2 : Int) ^ 53 ≤ 2 * (roundNearestEven a (b * 2 ^ 971) : Int) := by
              grind
            exact Int.mul_le_mul_of_nonneg_right h_2_step h_b_2_971_Int_nn
          have h_round_high_recast :
              2 * (roundNearestEven a (b * 2 ^ 971) : Int) * ((b : Int) * (2 : Int) ^ 971)
                ≤ 2 * (a : Int) + (b : Int) * (2 : Int) ^ 971 := by
            have := h_round_high
            rw [h_b_2_971_cast] at this
            exact this
          have h_carry_ineq :
              2 * (2 : Int) ^ 53 * ((b : Int) * (2 : Int) ^ 971)
                ≤ 2 * (a : Int) + (b : Int) * (2 : Int) ^ 971 :=
            Int.le_trans h_step1 h_round_high_recast
          -- Rearrange: (2·2^53 - 1)·(b·2^971) ≤ 2·a. I.e., (2^54 - 1)·b·2^971 ≤ 2a.
          have h_2_54 : (2 : Int) ^ 54 = 2 * (2 : Int) ^ 53 := by
            rw [show (54 : Nat) = 53 + 1 from rfl, Int.pow_succ]; grind
          have h_carry_2a : ((2 : Int) ^ 54 - 1) * ((b : Int) * (2 : Int) ^ 971)
                              ≤ 2 * (a : Int) := by
            have h_expand : ((2 : Int) ^ 54 - 1) * ((b : Int) * (2 : Int) ^ 971)
                            = 2 * (2 : Int) ^ 53 * ((b : Int) * (2 : Int) ^ 971)
                              - ((b : Int) * (2 : Int) ^ 971) := by
              rw [h_2_54]; grind
            grind
          -- Multiply by 2: (2^55 - 2)·b·2^971 ≤ 4a.
          have h_carry_4a : ((2 : Int) ^ 55 - 2) * ((b : Int) * (2 : Int) ^ 971)
                              ≤ 4 * (a : Int) := by
            have h_2_55 : (2 : Int) ^ 55 = 2 * (2 : Int) ^ 54 := by
              rw [show (55 : Nat) = 54 + 1 from rfl, Int.pow_succ]; grind
            have h_double : ((2 : Int) ^ 55 - 2) = 2 * ((2 : Int) ^ 54 - 1) := by grind
            calc ((2 : Int) ^ 55 - 2) * ((b : Int) * (2 : Int) ^ 971)
                = 2 * (((2 : Int) ^ 54 - 1) * ((b : Int) * (2 : Int) ^ 971)) := by
                    rw [h_double]; grind
              _ ≤ 2 * (2 * (a : Int)) := by grind
              _ = 4 * (a : Int) := by grind
          -- (2^55 - 2)·2^971·b ≤ 4a, hence (2^1026 - 2^972)·b ≤ 4a.
          have h_carry_4a_pow : ((2 : Int) ^ 1026 - (2 : Int) ^ 972) * (b : Int)
                                  ≤ 4 * (a : Int) := by
            have h_pow_eq := pow_identity_basic
            calc ((2 : Int) ^ 1026 - (2 : Int) ^ 972) * (b : Int)
                = (((2 : Int) ^ 55 - 2) * (2 : Int) ^ 971) * (b : Int) := by rw [h_pow_eq]
              _ = ((2 : Int) ^ 55 - 2) * ((b : Int) * (2 : Int) ^ 971) := by grind
              _ ≤ 4 * (a : Int) := h_carry_4a
          -- Multiply by 2^qfNeg ≥ 1: ((2^1026 - 2^972)·b)·2^qfNeg ≤ (4a)·2^qfNeg.
          have h_2qfNeg_pos : (0 : Int) < (2 : Int) ^ qfNeg := Int.pow_pos (by decide)
          have h_2qfNeg_ge_one : (1 : Int) ≤ (2 : Int) ^ qfNeg :=
            one_le_pow_of_le (by decide : (1 : Int) ≤ 2) _
          -- Now we use h_lhs_le: 4·a·2^qfNeg ≤ (2^1026-2^972)·b.
          have h_b_nn : (0 : Int) ≤ (b : Int) := Int.le_of_lt hb_pos_Int
          have h_diff_pos : (0 : Int) < (2 : Int) ^ 1026 - (2 : Int) ^ 972 := by
            have h1 : (2 : Int) ^ 972 < (2 : Int) ^ 1026 :=
              pow_lt_pow_right₀ (by decide) (by decide)
            omega
          have h_diff_b_nn : (0 : Int) ≤ ((2 : Int) ^ 1026 - (2 : Int) ^ 972) * (b : Int) := by
            exact Int.mul_nonneg (Int.le_of_lt h_diff_pos) h_b_nn
          have h_combine : ((2 : Int) ^ 1026 - (2 : Int) ^ 972) * (b : Int) * (2 : Int) ^ qfNeg
                            ≤ 4 * (a : Int) * (2 : Int) ^ qfNeg := by
            exact Int.mul_le_mul_of_nonneg_right h_carry_4a_pow (Int.le_of_lt h_2qfNeg_pos)
          -- Combine with h_lhs_le: 4·a·2^qfNeg ≤ (2^1026 - 2^972)·b.
          -- We have h_carry_4a_pow · 2^qfNeg ≤ 4·a·2^qfNeg ≤ (2^1026-2^972)·b.
          -- So ((2^1026 - 2^972)·b)·2^qfNeg ≤ (2^1026-2^972)·b. So 2^qfNeg ≤ 1 (if b > 0 and difference > 0).
          -- Hence qfNeg = 0.
          have h_qfNeg_zero : qfNeg = 0 := by
            -- ((2^1026-2^972)·b)·2^qfNeg ≤ (2^1026-2^972)·b.
            have h_chain : ((2 : Int) ^ 1026 - (2 : Int) ^ 972) * (b : Int) * (2 : Int) ^ qfNeg
                            ≤ ((2 : Int) ^ 1026 - (2 : Int) ^ 972) * (b : Int) :=
              Int.le_trans h_combine h_lhs_le
            -- Since b > 0 and diff > 0, divide.
            have h_lhs_pos : (0 : Int) < ((2 : Int) ^ 1026 - (2 : Int) ^ 972) * (b : Int) :=
              Int.mul_pos h_diff_pos hb_pos_Int
            have h_2qfNeg_le_one : (2 : Int) ^ qfNeg ≤ 1 := by
              -- From h_chain : ((2^1026-2^972)·b) · 2^qfNeg ≤ ((2^1026-2^972)·b).
              -- Rewrite as ((2^1026-2^972)·b) · 2^qfNeg ≤ ((2^1026-2^972)·b) · 1.
              have h_step : ((2 : Int) ^ 1026 - (2 : Int) ^ 972) * (b : Int) * (2 : Int) ^ qfNeg
                              ≤ ((2 : Int) ^ 1026 - (2 : Int) ^ 972) * (b : Int) * 1 := by
                rw [Int.mul_one]; exact h_chain
              -- Cancel ((2^1026-2^972)·b) > 0 from left.
              exact Int.le_of_mul_le_mul_left h_step h_lhs_pos

            -- 2^qfNeg ≤ 1 and 2^qfNeg ≥ 1. So = 1. So qfNeg = 0.
            have h_eq_one : (2 : Int) ^ qfNeg = 1 := le_antisymm h_2qfNeg_le_one h_2qfNeg_ge_one
            by_contra h_ne
            have h_pos_q : 0 < qfNeg := Nat.pos_of_ne_zero h_ne
            have h_ge_two : (2 : Int) ≤ (2 : Int) ^ qfNeg := by
              calc (2 : Int) = (2 : Int) ^ 1 := by grind
                _ ≤ (2 : Int) ^ qfNeg := pow_le_pow_right₀ (by decide) h_pos_q
            grind
          rw [h_qfNeg_zero, Int.pow_zero, Int.mul_one] at h_lhs_le
          -- Clean up h_combine: ... * 2^qfNeg → ... * 1 = ...
          have h_combine' : ((2 : Int) ^ 1026 - (2 : Int) ^ 972) * (b : Int) ≤ 4 * (a : Int) := by
            have h_step := h_combine
            rw [h_qfNeg_zero, Int.pow_zero, Int.mul_one, Int.mul_one] at h_step
            exact h_step
          -- Now: 4·a ≤ (2^1026 - 2^972)·b AND (2^1026 - 2^972)·b ≤ 4·a.
          -- So equality. With h_bracket' (strict if m_f odd, eq if even),
          -- we need to derive a contradiction.
          -- Abstract heavy terms.
          set LO : Int := ((2 : Int) ^ 1026 - (2 : Int) ^ 972) * (b : Int) with hLO_def
          set MID : Int := 4 * (a : Int) with hMID_def
          set HI : Int := (4 * (m_f : Int) + 2) * (2 : Int) ^ qfPos * (b : Int) with hHI_def
          -- We have: LO ≤ MID (from h_combine'), MID ≤ LO (from h_lhs_le), HI ≤ LO (from h_rhs_b_le).
          rcases h_bracket' with h_strict | ⟨h_eq, h_m_even⟩
          · -- Strict case. With qfNeg = 0: 4·a < HI, i.e., MID < HI.
            rw [h_qfNeg_zero, Int.pow_zero, Int.mul_one] at h_strict
            -- MID < HI ≤ LO, MID ≥ LO. Contradiction.
            change MID < HI at h_strict
            change MID ≤ LO at h_lhs_le
            change HI ≤ LO at h_rhs_b_le
            change LO ≤ MID at h_combine'
            omega
          · -- Equality case with m_f even.
            rw [h_qfNeg_zero, Int.pow_zero, Int.mul_one] at h_eq
            -- h_eq: MID = HI.
            change MID = HI at h_eq
            change MID ≤ LO at h_lhs_le
            change LO ≤ MID at h_combine'
            -- Strict bound on HI from rhs_bound_even.
            have h_rhs_even := rhs_bound_even m_f q_f h_legal_f h_m_even
            simp only at h_rhs_even
            set EVENB : Int := ((2 : Int) ^ 55 - 6) * (2 : Int) ^ 971 * (b : Int) with hEVENB_def
            have h_rhs_even_b : HI ≤ EVENB := by
              rw [hHI_def, hEVENB_def]
              exact Int.mul_le_mul_of_nonneg_right h_rhs_even h_b_nn
            have h_strict_b : EVENB < LO := by
              rw [hEVENB_def, hLO_def]
              exact Int.mul_lt_mul_of_pos_right pow_identity_strict hb_pos_Int
            -- MID = HI ≤ EVENB < LO and MID ≥ LO. Contradiction.
            omega
        · -- e + 1 ≤ 1023.
          push_neg at h_carry_over
          simp only [if_neg (by grind : ¬ e + 1 > 1023)]
          show e + 1 - 52 ≤ 971
          omega
      · simp only [if_neg h_carry]
        show e - 52 ≤ 971
        omega
    · -- Subnormal branch.
      push_neg at h_normal_range
      simp only [if_neg (by grind : ¬ e > 1023), if_neg (by grind : ¬ e ≥ -1022)]
      by_cases h_m_zero : roundNearestEven (scaleByPow2 a b 1074).1 (scaleByPow2 a b 1074).2 = 0
      · simp only [if_pos h_m_zero]; decide
      · by_cases h_m_52 : roundNearestEven (scaleByPow2 a b 1074).1 (scaleByPow2 a b 1074).2 ≥ 2 ^ 52
        · simp only [if_neg h_m_zero, if_pos h_m_52]; decide
        · simp only [if_neg h_m_zero, if_neg h_m_52]; decide

set_option maxHeartbeats 1600000 in
/-- **`R_v` membership characterises the round-trip.** Any decimal `c` with
    nonzero significand, the same sign as a finite nonzero `f`, and
    `(c.significand, c.exponent)` inside `f`'s rounding interval reads back
    to exactly `f`'s bits through `Clinger.ofDecimal`.

    This is the Clinger-side assembly (M4 + the disjointness lemma
    `inRoundingInterval_uniq`), independent of how the witness decimal was
    produced; `ofDecimal_toDecimal_eq_bits` instantiates it with the
    Schubfach output. -/
theorem ofDecimal_eq_bits_of_rv
    (w : UInt64) (c : Decimal)
    (h_fin : Word.isFinite w = true)
    (h_nonzero : (Word.decode w).m ≠ 0)
    (h_c_sig_ne : c.significand ≠ 0)
    (h_c_sign : c.sign = (Word.decode w).sign)
    (h_rv : inRoundingInterval c.significand c.exponent
              (Word.decode w).m (Word.decode w).q
              (isIrregular (Word.decode w).m (Word.decode w).q) = true) :
    Clinger.ofDecimalBits c = w := by
  set decoded_f := Word.decode w with h_decoded_f
  have h_legal_for_finite : LegalIEEE decoded_f.m decoded_f.q :=
    decode_legalIEEE_bits w h_fin h_nonzero
  have h_finite_abs : IsFiniteAbs c.sign c.significand c.exponent :=
    isFiniteAbs_of_rv c decoded_f.m decoded_f.q h_legal_for_finite h_c_sig_ne h_rv
  have h_rv_clinger :
      inRoundingInterval c.significand c.exponent
        (Word.decode (Clinger.ofDecimalBits c)).m (Word.decode (Clinger.ofDecimalBits c)).q
        (isIrregular (Word.decode (Clinger.ofDecimalBits c)).m (Word.decode (Clinger.ofDecimalBits c)).q) = true :=
    Clinger.ofDecimalBits_in_Rv c h_c_sig_ne h_finite_abs
  have h_bridge := Clinger.decode_of_decimal_bridge_bits c h_finite_abs
  have h_fin_clinger : Word.isFinite (Clinger.ofDecimalBits c) = true := by
    unfold Word.isFinite
    have h_dec_q : (Word.decode (Clinger.ofDecimalBits c)).q ≤ 971 := by
      rw [h_bridge]; exact h_finite_abs
    by_cases he : Word.biasedExp (Clinger.ofDecimalBits c) = 0
    · simp [he]
    · have h_q_def : (Word.decode (Clinger.ofDecimalBits c)).q
                   = (Word.biasedExp (Clinger.ofDecimalBits c) : Int) - 1023 - 52 := by
        unfold Word.decode; rw [if_neg he]
      rw [h_q_def] at h_dec_q
      have h_be_le : (Word.biasedExp (Clinger.ofDecimalBits c) : Int) ≤ 2046 := by omega
      have h_be_le_nat : Word.biasedExp (Clinger.ofDecimalBits c) ≤ 2046 := by omega
      have : Word.biasedExp (Clinger.ofDecimalBits c) < 2047 := by omega
      simpa using this
  have h_decoded_clinger_legal : LegalIEEE (Word.decode (Clinger.ofDecimalBits c)).m
                                            (Word.decode (Clinger.ofDecimalBits c)).q := by
    apply decode_legalIEEE_bits _ h_fin_clinger
    intro h_m_zero
    have h_q_eq : (Word.decode (Clinger.ofDecimalBits c)).q = -1074 :=
      decode_m_zero_q (Clinger.ofDecimalBits c) h_m_zero
    exact clinger_decode_m_ne_zero_aux c
      decoded_f.m decoded_f.q h_legal_for_finite
      (Word.decode (Clinger.ofDecimalBits c)).m (Word.decode (Clinger.ofDecimalBits c)).q
      h_rv h_rv_clinger h_m_zero h_q_eq
  rw [h_bridge] at h_rv_clinger
  obtain ⟨hm_eq, hq_eq⟩ := inRoundingInterval_uniq
    c.significand c.exponent
    decoded_f.m (Clinger.decodedAbs c.sign c.significand c.exponent).m
    decoded_f.q (Clinger.decodedAbs c.sign c.significand c.exponent).q
    h_legal_for_finite
    (by rw [← h_bridge]; exact h_decoded_clinger_legal)
    h_rv
    h_rv_clinger
  have h_sign_eq : Word.signBit w = Word.signBit (Clinger.ofDecimalBits c) := by
    rw [signBit_eq_decode_sign w, signBit_eq_decode_sign]
    rw [h_bridge, decodedAbs_sign c.sign c.significand c.exponent]
    rw [← h_c_sign]
  apply (toBits_eq_of_decode_eq (Clinger.ofDecimalBits c) w h_fin_clinger h_fin
    h_sign_eq.symm ?_ ?_)
  · rw [h_bridge]; exact hm_eq.symm
  · rw [h_bridge]; exact hq_eq.symm

set_option maxHeartbeats 1600000 in
/-- **Round-trip theorem (bits level, axiom-free).** For a finite, nonzero
    binary64 word `w`, printing then reading recovers `w` exactly:
    `Clinger.ofDecimalBits (Schubfach.toDecimalBits w) = w`.

    Chains M3.8 (Schubfach correctness) and M4 (Clinger correctness)
    through the disjointness lemma `inRoundingInterval_uniq`. -/
theorem ofDecimal_toDecimal_eq_bits
    (w : UInt64)
    (h_fin : Word.isFinite w = true)
    (h_nonzero : (Word.decode w).m ≠ 0) :
    ∃ d, Schubfach.toDecimalBits w = .ok d ∧
         Clinger.ofDecimalBits d = w := by
  -- Step 1: Apply M3.8 to get the Schubfach output and its witness.
  obtain ⟨d, hd_eq, sig, exp, hd_mk, h_rv_raw⟩ := toDecimalBits_in_Rv w h_fin h_nonzero
  refine ⟨d, hd_eq, ?_⟩
  set decoded_f := Word.decode w with h_decoded_f
  -- Step 2: From the M3.8 witness, the rounding interval claim is for the raw (sig, exp).
  -- We need it for d.significand, d.exponent (canonical). The values match, so we use
  -- `inRoundingInterval_mk'_eq`.
  have h_sig_ne : sig ≠ 0 := by
    -- If sig = 0, h_rv_raw says inRoundingInterval 0 exp decoded_f.m decoded_f.q ... = true,
    -- but `inRoundingInterval_zero_eq_false` says it's false (since decoded_f.m ≥ 1).
    intro h_sig_zero
    rw [h_sig_zero] at h_rv_raw
    have h_m_pos : 1 ≤ decoded_f.m := Nat.one_le_iff_ne_zero.mpr h_nonzero
    have h_false := inRoundingInterval_zero_eq_false exp decoded_f.m decoded_f.q
                      (isIrregular decoded_f.m decoded_f.q) h_m_pos
    rw [h_false] at h_rv_raw
    exact Bool.false_ne_true h_rv_raw
  -- Step 3: Convert M3.8 witness to canonical form.
  have h_d_sign : d.sign = (Word.decode w).sign := by
    rw [← hd_mk]; exact mk_pos_props _ _ _ h_sig_ne |>.1
  have h_d_sig_ne : d.significand ≠ 0 := by
    rw [← hd_mk]; exact mk_pos_props _ _ _ h_sig_ne |>.2.1
  have h_rv_canonical : inRoundingInterval d.significand d.exponent
                          decoded_f.m decoded_f.q (isIrregular decoded_f.m decoded_f.q) = true := by
    have h_eq := inRoundingInterval_mk'_eq (Word.decode w).sign sig exp decoded_f.m decoded_f.q
                  (isIrregular decoded_f.m decoded_f.q) h_sig_ne
    simp only at h_eq
    rw [← hd_mk]
    rw [← h_eq]
    exact h_rv_raw
  -- Steps 4-6: the Clinger-side assembly, factored into `ofDecimal_eq_bits_of_rv`.
  exact ofDecimal_eq_bits_of_rv w d h_fin h_nonzero h_d_sig_ne h_d_sign h_rv_canonical

end Srtfp

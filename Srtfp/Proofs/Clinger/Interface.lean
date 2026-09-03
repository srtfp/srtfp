module
/- The one fact the printer proof needs from the reader: a decimal reads
   back to the finite nonzero word `w` iff it carries `w`'s sign and its
   magnitude lies in the rounding interval `R_w` (Giulietti §3.2.1, the
   assumption about `round`). Derived here from the existing reader
   results; a reader rewrite replaces this file and nothing else. -/
public import Srtfp.Proofs.Clinger
public import Srtfp.Proofs.Clinger.NatIntervalRat
public import Srtfp.Proofs.Disjointness
public import Srtfp.Proofs.ReaderCorrectness
public import Srtfp.Proofs.Printer.Interval

@[expose] public section

open Srtfp.Compat

namespace Srtfp.Printer

open Srtfp Srtfp.Float Srtfp.Schubfach Srtfp.Clinger

variable {m : Nat} {q : Int} {w : UInt64} {d : Decimal}

/-! ## The old cleared-form membership test is the new rational one -/

theorem isIrregular_iff : isIrregular m q = true ↔ (m = 2 ^ 52 ∧ q > -1074) := by
  unfold isIrregular minNormalSignificand minBinaryExp
  simp [decide_eq_true_eq]

theorem inRoundingInterval_iff_InRv (sig : Nat) (exp : Int) (m : Nat) (q : Int) :
    inRoundingInterval sig exp m q (isIrregular m q) = true
      ↔ InRv m q ((sig : ℚ) * (10 : ℚ) ^ exp) = true := by
  rw [inRoundingInterval_iff]
  unfold fourVL fourU fourVR
  have hgt : ∀ a b : Int, (cmpScaledMixed.rhs b q exp < cmpScaledMixed.lhs a q exp)
      ↔ ((b : ℚ) * (10 : ℚ) ^ exp < (a : ℚ) * (2 : ℚ) ^ q) :=
    fun a b => cmpScaledMixed_lhs_gt_rhs_iff_rat a q b exp
  have heq' : ∀ a b : Int, (cmpScaledMixed.rhs b q exp = cmpScaledMixed.lhs a q exp)
      ↔ ((b : ℚ) * (10 : ℚ) ^ exp = (a : ℚ) * (2 : ℚ) ^ q) :=
    fun a b => ⟨fun h => ((cmpScaledMixed_lhs_eq_rhs_iff_rat a q b exp).mp h.symm).symm,
                fun h => ((cmpScaledMixed_lhs_eq_rhs_iff_rat a q b exp).mpr h.symm).symm⟩
  rw [cmpScaledMixed_lhs_lt_rhs_iff_rat, cmpScaledMixed_lhs_eq_rhs_iff_rat, hgt, heq']
  unfold InRv vl vr
  have h2 := two_zpow_pos q
  have h10 := ten_zpow_pos exp
  by_cases hirr : isIrregular m q = true
  · rw [if_pos hirr, if_pos (isIrregular_iff.mp hirr)]
    push_cast
    split <;> simp <;> grind
  · rw [if_neg hirr, if_neg (fun h => hirr (isIrregular_iff.mpr h))]
    push_cast
    split <;> simp <;> grind

/-! ## Words -/

theorem word_of_decode_zero (hw : Word.isFinite w = true) (hm : (Word.decode w).m = 0) :
    w = Word.pack (Word.decode w).sign 0 0 := by
  have hpack := pack_decode_eq w (word_isNaN_false_of_isFinite w hw)
  have hsign := signBit_eq_decode_sign w
  have he : Word.biasedExp w = 0 := by
    rcases Nat.eq_zero_or_pos (Word.biasedExp w) with he | he
    · exact he
    · exfalso
      unfold Word.decode at hm
      simp only [show Word.biasedExp w ≠ 0 by omega, if_false] at hm
      omega
  have hmb : Word.mantissa w = 0 := by
    unfold Word.decode at hm
    simpa [he] using hm
  calc w = Word.pack (Word.signBit w) (Word.biasedExp w) (Word.mantissa w) := hpack.symm
    _ = Word.pack (Word.decode w).sign 0 0 := by rw [hsign, he, hmb]

theorem decode_pack_zero (sign : Bool) : Word.decode (Word.pack sign 0 0) = ⟨sign, 0, -1074⟩ := by
  obtain ⟨hs, hb, hmn⟩ := pack_proj sign 0 0 (by decide) (by decide)
  unfold Word.decode
  rw [hs, hb, hmn]; rfl

theorem zero_reads_to_zero (sign : Bool) :
    Clinger.ofDecimalBits ⟨sign, 0, 0⟩ = Word.pack sign 0 0 := rfl

theorem isFinite_pack_inf (sign : Bool) : Word.isFinite (Word.pack sign 2047 0) = false := by
  obtain ⟨_, hb, _⟩ := pack_proj sign 2047 0 (by decide) (by decide)
  unfold Word.isFinite; rw [hb]; decide

/-- A decimal with significand `0` reads to the zero word of its sign. -/
theorem ofDecimalBits_of_sig_zero (h : d.significand = 0) :
    Clinger.ofDecimalBits d = Word.pack d.sign 0 0 := by
  unfold Clinger.ofDecimalBits Clinger.decimalToFloatBits
  rw [if_pos h]; rfl

/-- Reading back to any finite word carries the decimal's sign. -/
theorem sign_of_reads_to (hw : Word.isFinite w = true)
    (h : Clinger.ofDecimalBits d = w) : d.sign = (Word.decode w).sign := by
  by_cases hsig : d.significand = 0
  · rw [← h, ofDecimalBits_of_sig_zero hsig, decode_pack_zero]
  by_cases hfin : IsFiniteAbs d.sign d.significand d.exponent
  · rw [← h, decode_of_decimal_bridge_bits d hfin, decodedAbs_sign]
  · exfalso
    have := decimalToFloatBits_overflow_inf d.sign d.significand d.exponent hsig hfin
    rw [show w = Clinger.ofDecimalBits d from h.symm] at hw
    unfold Clinger.ofDecimalBits at hw
    rw [this, isFinite_pack_inf] at hw
    exact Bool.false_ne_true hw

/-! ## The interface lemma -/

/-- Membership in `R_w` for a nonzero `w` excludes the zero word's interval:
    everything in `R_w` exceeds `2^{-1075}`, the top of `R_0`. -/
theorem not_InRv_zero_of_InRv (h : LegalIEEE m q) {x : ℚ} (hx : InRv m q x = true) :
    InRv 0 (-1074) x = false := by
  have hm1n : 1 ≤ m := by unfold LegalIEEE at h; omega
  have hq : -1074 ≤ q := by unfold LegalIEEE at h; omega
  have hm1 : (1 : ℚ) ≤ m := by exact_mod_cast hm1n
  have h2neg : (2 : ℚ) ^ (-1074 : Int) = ((2 : ℚ) ^ (1074 : ℕ))⁻¹ := by
    rw [Rat.zpow_neg]; rfl
  -- keep `2^{-1074}` symbolic so no tactic tries to evaluate it
  generalize hT : ((2 : ℚ) ^ (1074 : ℕ))⁻¹ = t at h2neg
  have h2q : t ≤ (2 : ℚ) ^ q := by
    rw [← h2neg]; exact zpow_le_zpow_right₀ (by decide) hq
  have h2pos : (0 : ℚ) < t := by rw [← h2neg]; exact two_zpow_pos _
  have h2posq := two_zpow_pos q
  -- everything in `R_w` lies strictly above `2^{-1075}`: `(m - 1/2)·2^q ≥ 2^{-1075}` with
  -- equality only at `m = 1, q = -1074`, where `m` is odd and the endpoint is excluded
  have hlow : (1/2 : ℚ) * t < x := by
    unfold InRv vl at hx
    have hhalf : (1/2 : ℚ) * (2 : ℚ) ^ q ≤ ((m : ℚ) - 1/2) * (2 : ℚ) ^ q :=
      Rat.mul_le_mul_of_nonneg_right (by grind) (le_of_lt h2posq)
    have hhalf' : (1/2 : ℚ) * t ≤ (1/2 : ℚ) * (2 : ℚ) ^ q :=
      Rat.mul_le_mul_of_nonneg_left h2q (by grind)
    by_cases hev : m % 2 = 0
    · have hm2 : (2 : ℚ) ≤ m := by exact_mod_cast (show 2 ≤ m by omega)
      have h32 : (3/2 : ℚ) * (2 : ℚ) ^ q ≤ ((m : ℚ) - 1/2) * (2 : ℚ) ^ q :=
        Rat.mul_le_mul_of_nonneg_right (by grind) (le_of_lt h2posq)
      rw [if_pos hev] at hx
      simp only [decide_eq_true_eq] at hx
      split at hx <;> grind
    · rw [if_neg hev] at hx
      simp only [decide_eq_true_eq] at hx
      split at hx <;> grind
  unfold InRv vr
  simp only [Nat.zero_mod, if_true, decide_eq_false_iff_not]
  rintro ⟨_, hxr⟩
  rw [h2neg] at hxr
  have hz : ((0 : ℕ) : ℚ) = 0 := rfl
  grind

/-- The value of a decimal in `R_w` is below the overflow threshold. -/
theorem lt_threshold_of_InRv (hw : Word.isFinite w = true) (hm : 1 ≤ (Word.decode w).m)
    (sig : Nat) (exp : Int)
    (h : InRv (Word.decode w).m (Word.decode w).q ((sig : ℚ) * (10 : ℚ) ^ exp) = true) :
    (sig : ℚ) * (10 : ℚ) ^ exp < (2 : ℚ) ^ (1024 : ℕ) - (2 : ℚ) ^ (970 : ℕ) :=
  gridVal_lt_bound_of_rv sig exp _ _
    (Or.inr (decode_legalIEEE_bits w hw (Nat.pos_iff_ne_zero.mp hm)))
    ((inRoundingInterval_iff_InRv _ _ _ _).mpr h)

/-- **The interface.** Reading a decimal back yields the finite nonzero
    word `w` iff the decimal is nonzero, carries `w`'s sign, and its
    magnitude lies in `R_w`. -/
theorem reads_to_iff (hw : Word.isFinite w = true) (hm : 1 ≤ (Word.decode w).m) (d : Decimal) :
    Clinger.ofDecimalBits d = w ↔
      (d.significand ≠ 0 ∧ d.sign = (Word.decode w).sign
        ∧ InRv (Word.decode w).m (Word.decode w).q
            ((d.significand : ℚ) * (10 : ℚ) ^ d.exponent) = true) := by
  constructor
  · intro h
    have hsig : d.significand ≠ 0 := by
      intro h0
      have := congrArg (fun w => (Word.decode w).m) (h ▸ ofDecimalBits_of_sig_zero h0)
      simp only [decode_pack_zero] at this
      omega
    have hfin := isFiniteAbs_of_roundtrip_bits d w hsig hw h
    refine ⟨hsig, ?_, ?_⟩
    · rw [← h, decode_of_decimal_bridge_bits d hfin, decodedAbs_sign]
    · have := ofDecimalBits_in_Rv d hsig hfin
      simp only at this
      rw [h] at this
      exact (inRoundingInterval_iff_InRv _ _ _ _).mp this
  · rintro ⟨hsig, hsign, hmem⟩
    -- the decimal is in range, so the reader produces a finite word `w'`
    have hfin : IsFiniteAbs d.sign d.significand d.exponent := by
      by_contra hnot
      have h1 := bound_le_gridVal_of_not_finite d.sign d.significand d.exponent hsig hnot
      have h2 := lt_threshold_of_InRv hw hm d.significand d.exponent hmem
      unfold gridVal at h1
      exact absurd (lt_of_le_of_lt h1 h2) (lt_irrefl _)
    have hw' : Word.isFinite (Clinger.ofDecimalBits d) = true := isFiniteBits_ofDecimal d hfin
    have hmem' := ofDecimalBits_in_Rv d hsig hfin
    simp only at hmem'
    rw [inRoundingInterval_iff_InRv] at hmem'
    -- `w'` is not the zero word: its interval lies below `R_w`
    have hlegal := decode_legalIEEE_bits w hw (by omega)
    have hm' : (Word.decode (Clinger.ofDecimalBits d)).m ≠ 0 := by
      intro h0
      have hq0 : (Word.decode (Clinger.ofDecimalBits d)).q = -1074 := by
        unfold Word.decode at h0 ⊢
        by_cases he : Word.biasedExp (Clinger.ofDecimalBits d) = 0
        · simp [he]
        · exfalso; simp only [he, if_false] at h0; omega
      rw [h0, hq0] at hmem'
      rw [not_InRv_zero_of_InRv hlegal hmem] at hmem'
      exact Bool.false_ne_true hmem'
    have hlegal' := decode_legalIEEE_bits _ hw' hm'
    obtain ⟨hmeq, hqeq⟩ := inRoundingInterval_uniq d.significand d.exponent _ _ _ _ hlegal hlegal'
      ((inRoundingInterval_iff_InRv _ _ _ _).mpr hmem)
      ((inRoundingInterval_iff_InRv _ _ _ _).mpr hmem')
    have hsign' : (Word.decode (Clinger.ofDecimalBits d)).sign = d.sign := by
      rw [decode_of_decimal_bridge_bits d hfin, decodedAbs_sign]
    apply toBits_eq_of_decode_eq _ _ hw' hw
    · rw [signBit_eq_decode_sign, signBit_eq_decode_sign, hsign', hsign]
    · exact hmeq.symm
    · exact hqeq.symm

end Srtfp.Printer

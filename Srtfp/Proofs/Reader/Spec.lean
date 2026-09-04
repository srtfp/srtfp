module
/- The reader meets `Srtfp/Spec.lean`: a function is a correct reader iff
   it is `Clinger.ofDecimalBits`. Also the one fact the printer proof uses
   about the reader, `reads_to_iff`: a decimal reads back to a finite
   nonzero word iff it carries the word's sign and its magnitude lies in
   the word's rounding interval (Giulietti §3.2.1). -/
public import Srtfp.Proofs.Reader.Compute
public import Srtfp.Proofs.Reader.Nearest

@[expose] public section

open Srtfp.Compat

namespace Srtfp.Clinger

open Srtfp.Float Srtfp.Printer

theorem abs_toRat (d : Decimal) :
    |Spec.toRat d| = (d.significand : Rat) * (10 : Rat) ^ d.exponent := by
  show |(if d.sign then -1 else 1 : Rat) * _| = _
  rw [sign_mul_abs, abs_of_nonneg (mag_nonneg d)]

theorem ofDecimalBits_eq (d : Decimal) :
    ofDecimalBits d = decimalToFloatBits d.sign d.significand d.exponent := rfl

/-- Every value in `R_w` is below the overflow threshold: the largest
interval's right endpoint is the threshold, excluded because `2^53 - 1` is odd. -/
theorem lt_threshold_of_InRv {m : Nat} {q : Int} {x : Rat} (h : Legal m q) (hx : InRv m q x = true) :
    x < 2 ^ 1024 - 2 ^ 970 := by
  have hr := (le_of_InRv hx).2
  have hev := even_of_eq_vr hx
  unfold vr at hr hev
  have hm : (m : Rat) + 1 ≤ 2 ^ 53 := by exact_mod_cast (show m + 1 ≤ 2 ^ 53 by have := h.1; omega)
  rw [threshold_eq]
  rcases Int.lt_or_le q 971 with hq | hq
  · have hp := two_zpow_pos q
    have h1 : (2 : Rat) ^ q ≤ 2 ^ (970 : Int) := zpow_le_zpow_right₀ (by decide) (by omega)
    have h2 : (2 : Rat) ^ (971 : Int) = 2 ^ (970 : Int) * 2 := by
      rw [← Rat.zpow_add_one (by decide)]; rfl
    have h3 : ((m : Rat) + 1/2) * 2 ^ q < 2 ^ 53 * 2 ^ q := Rat.mul_lt_mul_of_pos_right (by grind) hp
    have h4 : (2 : Rat) ^ 53 * 2 ^ q ≤ 2 ^ 53 * 2 ^ (970 : Int) :=
      Rat.mul_le_mul_of_nonneg_left h1 (by grind)
    generalize (2 : Rat) ^ (970 : Int) = P at *
    generalize (2 : Rat) ^ q = Q at *
    grind
  · have hq' : q = 971 := by have := h.2.2.1; omega
    subst hq'
    have hle : ((m : Rat) + 1/2) * 2 ^ (971 : Int) ≤ (2 ^ 53 - 1/2) * 2 ^ (971 : Int) :=
      Rat.mul_le_mul_of_nonneg_right (by grind) (le_of_lt (two_zpow_pos _))
    by_cases heq : x = ((m : Rat) + 1/2) * 2 ^ (971 : Int)
    · have he := hev heq
      have hm2 : (m : Rat) + 2 ≤ 2 ^ 53 := by
        exact_mod_cast (show m + 2 ≤ 2 ^ 53 by have := h.1; omega)
      rw [heq]; exact Rat.mul_lt_mul_of_pos_right (by grind) (two_zpow_pos _)
    · exact lt_of_lt_of_le (lt_of_le_of_ne hr heq) hle

/-- An infinity word is the packed infinity of its sign. -/
theorem eq_pack_inf {w : UInt64} (hi : Word.isInf w = true) :
    w = Word.pack (Word.signBit w) 2047 0 := by
  unfold Word.isInf at hi
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hi
  conv => lhs; rw [← pack_decode_eq w]
  rw [hi.1, hi.2]

theorem isFinite_pack_inf (sign : Bool) : Word.isFinite (Word.pack sign 2047 0) = false := by
  obtain ⟨-, hb, -⟩ := pack_proj sign 2047 0 (by decide) (by decide)
  unfold Word.isFinite; rw [hb]; decide

/-! ## The reader theorem -/

/-- `Clinger.ofDecimalBits` is a correct reader. -/
theorem correctReader_ofDecimalBits : Spec.CorrectReader ofDecimalBits where
  inRange d hd := by
    rw [abs_toRat] at hd
    obtain ⟨hfin, hs, hmem⟩ := (decimalToFloatBits_spec d.sign d.significand d.exponent).1 hd
    exact nearestWord_of_InRv hfin hs hmem
  overflow d hd := by
    rw [abs_toRat] at hd
    rw [ofDecimalBits_eq, (decimalToFloatBits_spec d.sign d.significand d.exponent).2 hd]
    obtain ⟨hs, hb, hm⟩ := pack_proj d.sign 2047 0 (by decide) (by decide)
    refine (unpack_eq_inf_iff _ _).mpr ⟨?_, by rw [hs]⟩
    unfold Word.isInf; rw [hb, hm]; decide

/-- **The reader theorem.** A function is a correct reader iff it is
`Clinger.ofDecimalBits`. -/
theorem correctReader_iff_ofDecimal (p : Decimal → UInt64) :
    Spec.CorrectReader p ↔ ∀ d : Decimal, p d = ofDecimalBits d := by
  constructor
  · intro h d
    rcases lt_or_ge |Spec.toRat d| (2 ^ 1024 - 2 ^ 970) with hd | hd
    · have hn := h.inRange d hd
      rw [abs_toRat] at hd
      obtain ⟨hfin, hs, hmem⟩ := (decimalToFloatBits_spec d.sign d.significand d.exponent).1 hd
      exact eq_of_nearestWord hn hfin hs hmem
    · obtain ⟨hi, hs⟩ := (unpack_eq_inf_iff _ _).mp (h.overflow d hd)
      rw [abs_toRat] at hd
      rw [ofDecimalBits_eq, (decimalToFloatBits_spec d.sign d.significand d.exponent).2 hd,
        eq_pack_inf hi, sign_inj hs]
  · intro h
    have : p = ofDecimalBits := funext h
    subst this
    exact correctReader_ofDecimalBits

/-- `d` reads back to `w` under every correct reader iff under ours. -/
theorem readsTo_iff (d : Decimal) (w : UInt64) : Spec.ReadsTo d w ↔ ofDecimalBits d = w := by
  constructor
  · intro h; exact h _ correctReader_ofDecimalBits
  · intro h p hp; rw [(correctReader_iff_ofDecimal p).mp hp d, h]

/-! ## The interface to the printer proof -/

/-- Reading back to a finite word carries the decimal's sign. -/
theorem sign_of_reads_to {w : UInt64} (hw : Word.isFinite w = true) {d : Decimal}
    (h : ofDecimalBits d = w) : d.sign = (Word.decode w).sign := by
  rw [ofDecimalBits_eq] at h
  have hspec := decimalToFloatBits_spec d.sign d.significand d.exponent
  rcases lt_or_ge ((d.significand : Rat) * (10 : Rat) ^ d.exponent) (2 ^ 1024 - 2 ^ 970) with hd | hd
  · rw [← h]; exact (hspec.1 hd).2.1.symm
  · exfalso
    rw [hspec.2 hd] at h
    rw [← h, isFinite_pack_inf] at hw
    exact Bool.false_ne_true hw

/-- Reading a decimal back yields the finite nonzero word `w` iff the
decimal is nonzero, carries `w`'s sign, and its magnitude lies in `R_w`. -/
theorem reads_to_iff {w : UInt64} (hw : Word.isFinite w = true) (hm : 1 ≤ (Word.decode w).m)
    (d : Decimal) :
    ofDecimalBits d = w ↔
      (d.significand ≠ 0 ∧ d.sign = (Word.decode w).sign
        ∧ InRv (Word.decode w).m (Word.decode w).q
            ((d.significand : Rat) * (10 : Rat) ^ d.exponent) = true) := by
  have hspec := decimalToFloatBits_spec d.sign d.significand d.exponent
  rw [ofDecimalBits_eq]
  constructor
  · intro h
    rcases lt_or_ge ((d.significand : Rat) * (10 : Rat) ^ d.exponent) (2 ^ 1024 - 2 ^ 970) with hd | hd
    · obtain ⟨-, hs, hmem⟩ := hspec.1 hd
      rw [h] at hs hmem
      refine ⟨fun h0 => ?_, hs.symm, hmem⟩
      -- a zero significand reads to the zero word, whose `m` is `0`
      have hz : decimalToFloatBits d.sign d.significand d.exponent = Word.pack d.sign 0 0 := by
        unfold decimalToFloatBits; rw [if_pos h0]; rfl
      rw [hz] at h
      rw [← h, decode_pack d.sign (by decide) (by decide), if_pos rfl] at hm
      exact absurd hm (by simp)
    · exfalso
      rw [hspec.2 hd] at h
      rw [← h, isFinite_pack_inf] at hw
      exact Bool.false_ne_true hw
  · rintro ⟨-, hs, hmem⟩
    have hd := lt_threshold_of_InRv (decode_legal hw) hmem
    obtain ⟨hfin, hs', hmem'⟩ := hspec.1 hd
    exact (eq_of_nearestWord (nearestWord_of_InRv hw hs.symm hmem) hfin hs' hmem').symm

end Srtfp.Clinger

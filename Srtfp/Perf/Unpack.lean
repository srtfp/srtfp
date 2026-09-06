module
/- Lean's model reads a word as our `Word.decode` does. The specification
   speaks through `Float.Model.UnpackedFloat.unpack` (`Srtfp/Spec.lean`);
   the implementation and its proofs use the bit fields of
   `Srtfp/Float/Bits.lean`. This file relates the two, field by field. -/
public import Srtfp.Spec
public import Srtfp.Perf.BitsLemmas
public import Srtfp.Proofs.Printer.Vocab
public import Srtfp.Perf.Word
public import Srtfp.Proofs.Model

@[expose] public section

namespace Srtfp.Float

open Float.Model Float.Model.UnpackedFloat

/-! ## The three fields -/

theorem unpackExponent_toNat (w : UInt64) :
    (@unpackExponent Format.binary64 w.toBitVec).toNat = Word.biasedExp w := by
  unfold unpackExponent Word.biasedExp
  simp only [BitVec.toNat_cast, BitVec.extractLsb, BitVec.extractLsb'_toNat]
  rw [UInt64.toNat_and, UInt64.toNat_shiftRight, show (2047 : UInt64).toNat = 2 ^ 11 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod, show (52 : UInt64).toNat % 64 = 52 by decide]
  rfl

theorem unpackMantissa_toNat (w : UInt64) :
    (@unpackMantissa Format.binary64 w.toBitVec).toNat = Word.mantissa w := by
  unfold unpackMantissa Word.mantissa
  simp only [BitVec.toNat_cast, BitVec.extractLsb, BitVec.extractLsb'_toNat]
  rw [UInt64.toNat_and, show (4503599627370495 : UInt64).toNat = 2 ^ 52 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod]
  rfl

theorem unpackSign_eq (w : UInt64) :
    Sign.ofBitVec (@unpackSign Format.binary64 w.toBitVec) = Word.signBit w := by
  have h1 : (@unpackSign Format.binary64 w.toBitVec).toNat = w.toNat >>> 63 := by
    unfold unpackSign
    simp only [BitVec.toNat_cast, BitVec.extractLsb, BitVec.extractLsb'_toNat]
    show w.toNat >>> 63 % 2 ^ 1 = _
    have := w.toNat_lt
    rw [Nat.shiftRight_eq_div_pow]; exact Nat.mod_eq_of_lt (by omega)
  have h : (@unpackSign Format.binary64 w.toBitVec = 0#1) ↔ (w >>> 63 = 0) := by
    rw [BitVec.toNat_eq, h1, BitVec.toNat_ofNat]; word
  unfold Sign.ofBitVec Word.signBit
  simp only [h]

/-! ## `unpack`, in terms of the fields -/

/-- Lean's `unpack` of a word, case by case on its fields. -/
theorem unpack_eq (w : UInt64) :
    Spec.unpack w =
      if Word.biasedExp w = 2047 then
        (if Word.mantissa w = 0 then .infinity (Word.signBit w) else .notANumber)
      else if Word.biasedExp w = 0 then
        (if h : Word.mantissa w = 0 then .zero (Word.signBit w)
         else .finite (Word.signBit w) (Word.mantissa w) (-1074) (Nat.pos_of_ne_zero h))
      else
        .finite (Word.signBit w) (Word.mantissa w + 2 ^ 52)
          ((Word.biasedExp w : Int) - 1075) (by omega) := by
  show UnpackedFloat.unpack Format.binary64 w.toBitVec = _
  rw [← Model.packComponents_unpack w.toBitVec, Model.unpack_packComponents,
    unpackExponent_toNat, unpackSign_eq]
  simp only [unpackMantissa_toNat]

/-! ## Consequences the proofs use -/

end Srtfp.Float

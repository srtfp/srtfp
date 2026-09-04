module
/- Lean's model reads a word as our `Word.decode` does. The specification
   speaks through `Float.Model.UnpackedFloat.unpack` (`Srtfp/Spec.lean`);
   the implementation and its proofs use the bit fields of
   `Srtfp/Float/Bits.lean`. This file relates the two, field by field. -/
public import Srtfp.Spec
public import Srtfp.Proofs.Bits
public import Srtfp.Proofs.Printer.Vocab

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
    Sign.ofBitVec (@unpackSign Format.binary64 w.toBitVec) = Spec.sign (Word.signBit w) := by
  unfold Sign.ofBitVec Spec.sign Word.signBit
  have hlt := w.toNat_lt
  have h1 : (@unpackSign Format.binary64 w.toBitVec).toNat = w.toNat >>> 63 := by
    unfold unpackSign
    simp only [BitVec.toNat_cast, BitVec.extractLsb, BitVec.extractLsb'_toNat]
    show w.toNat >>> 63 % 2 ^ 1 = _
    rw [Nat.shiftRight_eq_div_pow]
    have : w.toNat / 2 ^ 63 < 2 := by omega
    exact Nat.mod_eq_of_lt (by omega)
  have h2 : (w >>> 63).toNat = w.toNat >>> 63 := by
    rw [UInt64.toNat_shiftRight, show (63 : UInt64).toNat % 64 = 63 by decide]
  by_cases h0 : w.toNat >>> 63 = 0
  · rw [if_pos (BitVec.eq_of_toNat_eq (by rw [h1, h0]; rfl))]
    have : w >>> 63 = 0 := UInt64.toNat_inj.mp (by rw [h2, h0]; rfl)
    simp [this]
  · rw [if_neg (fun h => h0 (by have := congrArg BitVec.toNat h; rw [h1] at this; exact this))]
    have : w >>> 63 ≠ 0 := fun h => h0 (by have := congrArg UInt64.toNat h; rw [h2] at this; exact this)
    simp [this]

/-! ## `unpack`, in terms of the fields -/

theorem exponentBias_eq : Format.binary64.exponentBias = 1023 := rfl

/-- Lean's `unpack` of a word, case by case on its fields. -/
theorem unpack_eq (w : UInt64) :
    Spec.unpack w =
      if Word.biasedExp w = 2047 then
        (if Word.mantissa w = 0 then .infinity (Spec.sign (Word.signBit w)) else .notANumber)
      else if Word.biasedExp w = 0 then
        (if h : Word.mantissa w = 0 then .zero (Spec.sign (Word.signBit w))
         else .finite (Spec.sign (Word.signBit w)) (Word.mantissa w) (-1074) (Nat.pos_of_ne_zero h))
      else
        .finite (Spec.sign (Word.signBit w)) (Word.mantissa w + 2 ^ 52)
          ((Word.biasedExp w : Int) - 1075) (by omega) := by
  have hE := unpackExponent_toNat w
  have hM := unpackMantissa_toNat w
  have hS := unpackSign_eq w
  have hMlt : (@unpackMantissa Format.binary64 w.toBitVec).toNat < 2 ^ 52 :=
    (@unpackMantissa Format.binary64 w.toBitVec).isLt
  unfold Spec.unpack UnpackedFloat.unpack
  simp only [hS, exponentBias_eq]
  have hE' : (@unpackExponent Format.binary64 w.toBitVec = -1#_) ↔ Word.biasedExp w = 2047 := by
    rw [← hE]; exact ⟨fun h => by rw [h]; rfl, fun h => BitVec.eq_of_toNat_eq (by rw [h]; rfl)⟩
  have hZ' : (@unpackExponent Format.binary64 w.toBitVec = 0#_) ↔ Word.biasedExp w = 0 := by
    rw [← hE]; exact ⟨fun h => by rw [h]; rfl, fun h => BitVec.eq_of_toNat_eq (by rw [h]; rfl)⟩
  have hM' : (@unpackMantissa Format.binary64 w.toBitVec = 0#_) ↔ Word.mantissa w = 0 := by
    rw [← hM]; exact ⟨fun h => by rw [h]; rfl, fun h => BitVec.eq_of_toNat_eq (by rw [h]; rfl)⟩
  have hcat : ((1#1 : BitVec 1) ++ @unpackMantissa Format.binary64 w.toBitVec).toNat
      = Word.mantissa w + 2 ^ 52 := by
    have h2 := Nat.two_pow_add_eq_or_of_lt hMlt 1
    rw [Nat.mul_one] at h2
    rw [BitVec.toNat_append]
    show 1 <<< 52 ||| _ = _
    rw [Nat.shiftLeft_eq, Nat.one_mul, ← h2, hM]
    omega
  by_cases h1 : Word.biasedExp w = 2047
  · rw [if_pos (hE'.mpr h1), if_pos h1]
    by_cases h2 : Word.mantissa w = 0
    · rw [if_pos (hM'.mpr h2), if_pos h2]
    · rw [if_neg (fun h => h2 (hM'.mp h)), if_neg h2]
  · rw [if_neg (fun h => h1 (hE'.mp h)), if_neg h1]
    by_cases h2 : Word.biasedExp w = 0
    · rw [if_pos (hZ'.mpr h2), if_pos h2]
      by_cases h3 : Word.mantissa w = 0
      · rw [dif_pos (hM'.mpr h3), dif_pos h3]
      · rw [dif_neg (fun h => h3 (hM'.mp h)), dif_neg h3]
        simp only [UnpackedFloat.finite.injEq, hM, hE, h2, true_and]
        omega
    · rw [if_neg (fun h => h2 (hZ'.mp h)), if_neg h2]
      simp only [UnpackedFloat.finite.injEq, hcat, hE, true_and]
      omega

/-! ## Consequences the proofs use -/

theorem negative_sign (b : Bool) : Spec.negative (Spec.sign b) = b := by
  cases b <;> rfl

theorem sign_inj {a b : Bool} (h : Spec.sign a = Spec.sign b) : a = b := by
  cases a <;> cases b <;> simp_all [Spec.sign]

theorem isFinite_iff (w : UInt64) : (Spec.unpack w).isFinite = true ↔ Word.isFinite w = true := by
  have hb := word_biasedExp_lt w
  rw [unpack_eq]; unfold Word.isFinite
  split
  · split <;> simp [UnpackedFloat.isFinite] <;> omega
  · split
    · split <;> simp [UnpackedFloat.isFinite] <;> omega
    · simp [UnpackedFloat.isFinite]; omega

theorem unpack_eq_nan_iff (w : UInt64) : Spec.unpack w = .notANumber ↔ Word.isNaN w = true := by
  rw [unpack_eq]; unfold Word.isNaN
  split
  · split <;> simp_all
  · split
    · split <;> simp_all
    · simp_all

theorem unpack_eq_inf_iff (w : UInt64) (s : Sign) :
    Spec.unpack w = .infinity s ↔ Word.isInf w = true ∧ s = Spec.sign (Word.signBit w) := by
  rw [unpack_eq]; unfold Word.isInf
  split
  · split <;> simp_all [eq_comm]
  · split
    · split <;> simp_all
    · simp_all

theorem wordSign_eq {w : UInt64} (hw : Word.isFinite w = true) :
    Spec.wordSign w = Word.signBit w := by
  unfold Word.isFinite at hw; simp only [decide_eq_true_eq] at hw
  unfold Spec.wordSign; rw [unpack_eq, if_neg (by omega)]
  by_cases h0 : Word.biasedExp w = 0
  · rw [if_pos h0]
    by_cases hm : Word.mantissa w = 0
    · rw [dif_pos hm]; exact negative_sign _
    · rw [dif_neg hm]; exact negative_sign _
  · rw [if_neg h0]; exact negative_sign _

theorem wordVal_eq {w : UInt64} (hw : Word.isFinite w = true) :
    Spec.wordVal w = (if (Word.decode w).sign then -1 else 1 : Rat)
      * Printer.v (Word.decode w).m (Word.decode w).q := by
  unfold Word.isFinite at hw; simp only [decide_eq_true_eq] at hw
  have he : (Word.biasedExp w : Int) - 1023 - 52 = (Word.biasedExp w : Int) - 1075 := by omega
  unfold Spec.wordVal Word.decode Printer.v; rw [unpack_eq, if_neg (by omega)]
  by_cases h0 : Word.biasedExp w = 0
  · rw [if_pos h0]
    by_cases hm : Word.mantissa w = 0
    · rw [dif_pos hm]; simp [h0, hm]
    · rw [dif_neg hm]; simp [h0, Spec.val, negative_sign]
  · rw [if_neg h0]; simp [h0, Spec.val, negative_sign, Nat.shiftLeft_eq, he]

theorem wordSig_mod_two {w : UInt64} (hw : Word.isFinite w = true) :
    Spec.wordSig w % 2 = (Word.decode w).m % 2 := by
  unfold Word.isFinite at hw; simp only [decide_eq_true_eq] at hw
  unfold Spec.wordSig Word.decode; rw [unpack_eq, if_neg (by omega)]
  by_cases h0 : Word.biasedExp w = 0
  · rw [if_pos h0]
    by_cases hm : Word.mantissa w = 0
    · rw [dif_pos hm]; simp [h0, hm]
    · rw [dif_neg hm]; simp [h0]
  · rw [if_neg h0]; simp [h0, Nat.shiftLeft_eq]

end Srtfp.Float

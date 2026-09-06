module
/- The entry points over the kernel: `toDecimalBits` and `toDecimal`
   (`Float → Decimal`) and `floatToString`, each equal to the reference and
   registered as its `@[csimp]` replacement. -/

public import Srtfp.Perf.Schubfach.Kernel
public import Srtfp.Perf.StringFast
public import Srtfp.Perf.DecimalFast
public import Srtfp.Perf.Unpack

@[expose] public section

open Srtfp.Compat
open Float.Model.UnpackedFloat (Sign)

namespace Srtfp.Schubfach

open Srtfp Srtfp.Float Srtfp.Printer

variable {m : Nat} {q : Int}

/-! ## The finite case is the reference scan -/

/-- `mk'` keeps the value. -/
theorem mk'_value (s : Sign) {n : Nat} (hn : n ≠ 0) (i : Int) :
    ((Decimal.mk' s n i).significand : Rat) * (10 : Rat) ^ (Decimal.mk' s n i).exponent
      = (n : Rat) * (10 : Rat) ^ i := by
  obtain ⟨-, -, -, hle, hv⟩ := mk_pos_props s n i hn
  generalize Decimal.mk' s n i = d at *
  rw [← hv]
  push_cast
  rw [← Rat.zpow_natCast, Int.toNat_of_nonneg (by omega), Rat.mul_assoc,
    ← Rat.zpow_add (by decide), show d.exponent - i + i = d.exponent by omega]

/-- The kernel's canonicalised decimal is the scan's. -/
theorem finite_eq (sb : Sign) (h : InRange m q) :
    Decimal.mk' sb (Exact.shortest m q).1 (Exact.shortest m q).2
      = ⟨sb, (Printer.shortest m q).1, (Printer.shortest m q).2⟩ := by
  obtain ⟨hpos, hval⟩ := Exact.shortest_spec h
  rcases hr : Exact.shortest m q with ⟨n', k'⟩
  rcases ho : Printer.shortest m q with ⟨n, i⟩
  have hn := (scan_spec h ho).1
  have h10 := out_ten h ho
  rw [hr, ho] at hval; rw [hr] at hpos
  simp only at hval hpos
  obtain ⟨hsign, hne, -, -, -⟩ := mk_pos_props sb n' k' (by omega)
  exact canonical_eq_of_value_eq (d := Decimal.mk' sb n' k') (d' := ⟨sb, n, i⟩)
    (Decimal.canonical_isCanonical ⟨sb, n', k'⟩)
    (Or.inr ⟨Nat.pos_iff_ne_zero.mp hn, h10⟩) hsign (Nat.pos_of_ne_zero hne) hn
    (by rw [mk'_value sb (by omega)]; exact hval)

/-! ## `Float → Decimal` -/

/-- The `Decimal` of `(c, q)` from the kernel (`mU = c`, `qB = q + 1074`). -/
@[inline] def decimalTail (sign : Sign) (mU qB : UInt64) : Decimal :=
  if mU = 0 then ⟨sign, 0, 0⟩
  else
    let r := kernel mU qB
    Decimal.mk' sign r.1.toNat ((r.2.toNat : Int) - 324)

theorem decimalTail_eq (sign : Sign) (mU qB : UInt64) (h : InRange m q) (hm : mU.toNat = m)
    (hq : (qB.toNat : Int) = q + 1074) :
    decimalTail sign mU qB = ⟨sign, (Printer.shortest m q).1, (Printer.shortest m q).2⟩ := by
  have hm0 : mU ≠ 0 := fun hc => by
    have := h.1; rw [← hm, hc] at this; exact absurd this (by decide)
  unfold decimalTail
  rw [if_neg hm0, ← finite_eq sign h, ← kernel_eq h mU qB hm hq]

/-- The shortest round-trip `Decimal` of a binary64 bit pattern; `none` for
    a NaN or an infinity. -/
def toDecimalBits (w : UInt64) : Option Decimal :=
  let expBits : UInt64 := (w >>> 52) &&& 0x7FF
  let mantBits : UInt64 := w &&& 0x000F_FFFF_FFFF_FFFF
  if expBits = 0x7FF then none
  else
    some (decimalTail (if w >>> 63 = 0 then .positive else .negative)
      (if expBits = 0 then mantBits else mantBits + 4503599627370496)
      (if expBits = 0 then 0 else expBits - 1))

/-- The shortest round-trip `Decimal` of a `Float`; `none` for a NaN or an
    infinity. -/
def toDecimal (f : _root_.Float) : Option Decimal := toDecimalBits f.toBits

/-! The reference printer on each shape of the unpacked word. Stated over
variables so that no tactic ever reduces `shortest` at concrete arguments
(the elaborator and the kernel would try to evaluate it). -/

theorem printer_nan {w : UInt64} (hu : Spec.unpack w = .notANumber) :
    Printer.toDecimalBits w = none := by
  unfold Printer.toDecimalBits; rw [hu]

theorem printer_inf {w : UInt64} {s : Sign} (hu : Spec.unpack w = .infinity s) :
    Printer.toDecimalBits w = none := by
  unfold Printer.toDecimalBits; rw [hu]

theorem printer_zero {w : UInt64} {s : Sign} (hu : Spec.unpack w = .zero s) :
    Printer.toDecimalBits w = some ⟨s, 0, 0⟩ := by
  unfold Printer.toDecimalBits; rw [hu]

theorem printer_finite {w : UInt64} {s : Sign} {m : Nat} {q : Int} {h : 0 < m}
    (hu : Spec.unpack w = .finite s m q h) :
    Printer.toDecimalBits w = some ⟨s, (Printer.shortest m q).1, (Printer.shortest m q).2⟩ := by
  unfold Printer.toDecimalBits; rw [hu]

theorem toDecimalBits_eq (w : UInt64) : toDecimalBits w = Printer.toDecimalBits w := by
  have hu := unpack_eq w
  have hexp : ((w >>> 52) &&& 0x7FF : UInt64).toNat = Word.biasedExp w := rfl
  have hmant : (w &&& 0x000F_FFFF_FFFF_FFFF : UInt64).toNat = Word.mantissa w := rfl
  have hsign : (if w >>> 63 = 0 then Sign.positive else Sign.negative) = Word.signBit w := rfl
  have hb := word_biasedExp_lt w
  have hmlt := word_mantissa_lt w
  unfold toDecimalBits
  rw [hsign]
  -- the fields as atoms: no tactic below may unfold a bit operation on `w`
  generalize ((w >>> 52) &&& 0x7FF : UInt64) = expBits at *
  generalize (w &&& 0x000F_FFFF_FFFF_FFFF : UInt64) = mantBits at *
  generalize Word.biasedExp w = E at *
  by_cases h7 : expBits = 0x7FF
  · have hE : E = 2047 := by rw [← hexp, h7]; rfl
    rw [if_pos h7]
    rw [if_pos hE] at hu
    by_cases hm : Word.mantissa w = 0
    · rw [if_pos hm] at hu; rw [printer_inf hu]
    · rw [if_neg hm] at hu; rw [printer_nan hu]
  · have hE : E ≠ 2047 := fun hc => h7 (UInt64.toNat_inj.mp (by rw [hexp, hc]; rfl))
    rw [if_neg h7]
    rw [if_neg hE] at hu
    by_cases h0 : expBits = 0
    · have hE0 : E = 0 := by rw [← hexp, h0]; rfl
      rw [if_pos h0, if_pos h0]
      rw [if_pos hE0] at hu
      by_cases hm : mantBits = 0
      · have hM0 : Word.mantissa w = 0 := by rw [← hmant, hm]; rfl
        rw [dif_pos hM0] at hu
        rw [printer_zero hu]
        unfold decimalTail
        rw [if_pos hm]
      · have hM0 : Word.mantissa w ≠ 0 := fun hc => hm (UInt64.toNat_inj.mp (by rw [hmant, hc]; rfl))
        rw [dif_neg hM0] at hu
        rw [printer_finite hu, decimalTail_eq (Word.signBit w) mantBits 0 (m := Word.mantissa w)
          (q := -1074) ⟨Nat.pos_of_ne_zero hM0, by omega, by omega, by omega, fun h => absurd rfl h⟩
          hmant rfl]
    · have hE0 : E ≠ 0 := fun hc => h0 (UInt64.toNat_inj.mp (by rw [hexp, hc]; rfl))
      rw [if_neg h0, if_neg h0]
      rw [if_neg hE0] at hu
      have h1 : (1 : UInt64) ≤ expBits :=
        UInt64.le_iff_toNat_le.mpr (by simp only [show (1 : UInt64).toNat = 1 from rfl, hexp]; omega)
      rw [printer_finite hu, decimalTail_eq (Word.signBit w) (mantBits + 4503599627370496) (expBits - 1)
        (m := Word.mantissa w + 2 ^ 52) (q := (E : Int) - 1075)
        ⟨by omega, by omega, by omega, by omega, fun _ => by omega⟩
        (by simp only [UInt64.toNat_add, hmant, show (4503599627370496 : UInt64).toNat = 2 ^ 52 from rfl]
            exact Nat.mod_eq_of_lt (by omega))
        (by simp only [UInt64.toNat_sub_of_le _ _ h1, show (1 : UInt64).toNat = 1 from rfl, hexp]; omega)]

theorem toDecimal_eq (f : _root_.Float) : toDecimal f = Printer.toDecimal f := toDecimalBits_eq f.toBits

/-- The live `Float → Decimal` registration (`CsimpPin.lean` asserts it is
    in force). -/
@[csimp]
theorem printer_toDecimal_csimp : @Printer.toDecimal = @toDecimal := by
  funext f; exact (toDecimal_eq f).symm

/-! ## `Float → String` -/

/-- `emitChecked` with the exponent's table index supplied directly. -/
@[inline] def emitIdx (sign : Sign) (sig : Nat) (idx : Nat) : String :=
  if h : idx ≤ 616 then
    withSign sign (toString sig ++ expTable[idx]'(by rw [expTable_size]; omega))
  else
    withSign sign (toString sig ++ "e" ++ intToStrRef ((idx : Int) - 324))

theorem emitIdx_eq (sign : Sign) (sig : Nat) (idx : Nat) :
    emitIdx sign sig idx = emitChecked sign sig ((idx : Int) - 324) := by
  rw [emitChecked_eq]
  unfold emitIdx
  split
  · rename_i h
    rw [show expTable[idx]'(by rw [expTable_size]; omega) = "e" ++ intToStrRef ((idx : Int) - 324)
        from by simp [expTable], String.append_assoc]
  · rfl

/-- The string of `decimalTail`, without building the `Decimal`. -/
@[inline] def emitTail (sign : Sign) (mU qB : UInt64) : String :=
  if mU = 0 then withSign sign "0"
  else
    let r := kernel mU qB
    if r.1 % 10 ≠ 0 then emitIdx sign r.1.toNat r.2.toNat
    else
      let (sig', exp') := Decimal.canonicaliseAux r.1.toNat ((r.2.toNat : Int) - 324)
      if sig' = 0 then withSign sign "0" else emitChecked sign sig' exp'

theorem emitTail_eq (sign : Sign) (mU qB : UInt64) :
    emitTail sign mU qB = decimalToStrRef (decimalTail sign mU qB) := by
  unfold emitTail decimalTail
  by_cases h0 : mU = 0
  · rw [if_pos h0, if_pos h0]; rfl
  rw [if_neg h0, if_neg h0]
  generalize kernel mU qB = r
  obtain ⟨sU, kB⟩ := r
  dsimp only
  rw [decimalToStrRef_mk', emitIdx_eq, emitChecked_eq]
  have hmod : (sU % 10 = 0) ↔ (sU.toNat % 10 = 0) := by
    rw [← UInt64.toNat_inj, UInt64.toNat_mod]; rfl
  by_cases hs0 : sU.toNat = 0
  · rw [if_pos hs0]
    have hm0 : ¬ (sU % 10 ≠ 0) := fun hc => hc (hmod.mpr (by rw [hs0]))
    rw [if_neg hm0, hs0, Decimal.canonicaliseAux_zero]
    simp
  · rw [if_neg hs0]
    by_cases hm : sU.toNat % 10 ≠ 0
    · rw [if_pos hm, if_pos (fun hc => hm (hmod.mp hc))]
    · rw [if_neg hm, if_neg (fun hc => hm (fun hc' => hc (hmod.mpr hc')))]
      rcases Decimal.canonicaliseAux sU.toNat ((kB.toNat : Int) - 324) with ⟨sig', exp'⟩
      simp only [emitChecked_eq]

/-- The shortest round-trip decimal string of a `Float`, and `"NaN"`,
    `"Infinity"`, `"-Infinity"`. -/
@[inline] def floatToString (f : _root_.Float) : String :=
  let bits := f.toBits
  let expBits : UInt64 := (bits >>> 52) &&& 0x7FF
  let mantBits : UInt64 := bits &&& 0x000F_FFFF_FFFF_FFFF
  if expBits = 0x7FF then
    if mantBits ≠ 0 then "NaN"
    else if (bits >>> 63) ≠ 0 then "-Infinity" else "Infinity"
  else
    emitTail (if bits >>> 63 = 0 then .positive else .negative)
      (if expBits = 0 then mantBits else mantBits + 4503599627370496)
      (if expBits = 0 then 0 else expBits - 1)

theorem floatToString_eq (f : _root_.Float) : floatToString f = floatToStrRef f := by
  unfold floatToStrRef
  rw [Printer.toDecimal_eq_bits, ← toDecimalBits_eq]
  unfold floatToString toDecimalBits
  have hexp : ((f.toBits >>> 52) &&& 0x7FF : UInt64).toNat = biasedExpBits f := rfl
  have hmant : (f.toBits &&& 0x000F_FFFF_FFFF_FFFF : UInt64).toNat = mantissaBits f := rfl
  by_cases h7 : ((f.toBits >>> 52) &&& 0x7FF : UInt64) = 0x7FF
  · rw [if_pos h7, if_pos h7]
    have hbE : biasedExpBits f = 2047 := by rw [← hexp, h7]; rfl
    by_cases hm : (f.toBits &&& 0x000F_FFFF_FFFF_FFFF : UInt64) = 0
    · have hm0 : mantissaBits f = 0 := by rw [← hmant, hm]; rfl
      have hNaN : ¬ isNaNBits f = true := by simp [isNaNBits, hbE, hm0]
      rw [if_neg (by simp [hm])]
      simp only [hNaN, Bool.false_eq_true, if_false, signBit, withSign]
      split <;> simp_all
    · have hm0 : mantissaBits f ≠ 0 := by
        intro hc
        exact hm (UInt64.toNat_inj.mp (by rw [hmant, hc]; rfl))
      have hNaN : isNaNBits f = true := by simp [isNaNBits, hbE, hm0]
      rw [if_pos hm]
      simp [hNaN]
  · rw [if_neg h7, if_neg h7]
    exact emitTail_eq _ _ _

/-- The live `Float → String` registration (`CsimpPin.lean` asserts it is
    in force). -/
@[csimp]
theorem floatToStrRef_csimp : @floatToStrRef = @floatToString := by
  funext f; exact (floatToString_eq f).symm

end Srtfp.Schubfach

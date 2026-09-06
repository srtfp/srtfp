module
/- The reference `Float → String` shape the fast string kernel is proven
   against (`floatToStrRef`), the exponent-suffix table, and the
   `Decimal.mk'`-to-string identity every emitter proof ends in. -/

public import Srtfp.Printer
public import Srtfp.Perf.Bits

@[expose] public section

open Float.Model.UnpackedFloat (Sign)

namespace Srtfp.Schubfach

open Srtfp.Float
open Srtfp.Decimal (canonicaliseAux)

/-! ## Reference strings -/

/-- Reference `Int → String`.  Byte-identical to `toString : Int → String`
    (whose `ToString` instance routes through the OPAQUE
    `String.Internal.append`, making it unusable as a proof target);
    this spelling uses `++` so emitters can be proven against it. -/
def intToStrRef (e : Int) : String :=
  match e with
  | .ofNat m => toString m
  | .negSucc m => "-" ++ toString (m + 1)

/-- `s` with the sign in front: `"-" ++ s` for a negative sign. -/
@[inline]
def withSign (sign : Sign) (s : String) : String :=
  match sign with | .negative => "-" ++ s | .positive => s

/-- Reference Decimal → String emit (shape from `BenchFloatToString.lean`). -/
def decimalToStrRef (d : _root_.Srtfp.Decimal) : String :=
  if d.significand = 0 then withSign d.sign "0"
  else
    withSign d.sign (toString d.significand ++ "e" ++ intToStrRef d.exponent)

/-- Reference `Float → String`: the body of `floatToStr` in `BenchFloatToString.lean`. -/
def floatToStrRef (f : _root_.Float) : String :=
  match Printer.toDecimal f with
  | some d => decimalToStrRef d
  | none => if isNaNBits f then "NaN" else withSign (signBit f) "Infinity"

/-! ## The exponent suffix table -/

/-- `"e-324"`, `"e-323"`, ..., `"e292"`: every canonical binary64
    shortest-decimal exponent, with the `'e'` pre-attached. -/
def expTable : Array String :=
  Array.ofFn (fun i : Fin 617 => "e" ++ intToStrRef ((i.val : Int) - 324))

theorem expTable_size : expTable.size = 617 := by
  simp [expTable]

/-- Fast emit when `exp` is in the canonical binary64 range (always, for
    Schubfach outputs), reference emit otherwise. -/
@[inline]
def emitChecked (sign : Sign) (sig : Nat) (exp : Int) : String :=
  if h : -324 ≤ exp ∧ exp ≤ 292 then
    let core := toString sig ++
      expTable[(exp + 324).toNat]'(by rw [expTable_size]; omega)
    withSign sign core
  else
    withSign sign (toString sig ++ "e" ++ intToStrRef exp)

theorem emitChecked_eq (sign : Sign) (sig : Nat) (exp : Int) :
    emitChecked sign sig exp =
      withSign sign (toString sig ++ "e" ++ intToStrRef exp) := by
  unfold emitChecked
  split
  · rename_i h
    rw [show expTable[(exp + 324).toNat]'(by rw [expTable_size]; omega)
          = "e" ++ intToStrRef (((exp + 324).toNat : Int) - 324) from by
      simp [expTable]]
    rw [show (((exp + 324).toNat : Int) - 324) = exp from by omega]
    rw [String.append_assoc]
  · rfl

/-! ## `Decimal.mk'` as a string -/

theorem decimalToStrRef_mk' (sign : Sign) (sig : Nat) (exp : Int) :
    decimalToStrRef (_root_.Srtfp.Decimal.mk' sign sig exp)
      = (if sig = 0 then withSign sign "0"
        else if sig % 10 ≠ 0 then
          withSign sign (toString sig ++ "e" ++ intToStrRef exp)
        else
          let (sig', exp') := canonicaliseAux sig exp
          if sig' = 0 then withSign sign "0"
          else
            withSign sign (toString sig' ++ "e" ++ intToStrRef exp')) := by
  unfold decimalToStrRef _root_.Srtfp.Decimal.mk' _root_.Srtfp.Decimal.canonical
  by_cases hs0 : sig = 0
  · simp [hs0]
  simp only [hs0, if_false]
  by_cases hsmod : sig % 10 ≠ 0
  · have hCanon : canonicaliseAux sig exp = (sig, exp) := by
      unfold canonicaliseAux
      simp [hs0, hsmod]
    rw [hCanon, if_pos hsmod]
    simp [hs0]
  · rw [if_neg hsmod]

end Srtfp.Schubfach

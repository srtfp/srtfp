module
/- The exponent-suffix table and emitter identities for the compact
   string reference in Srtfp.Text.Float. -/

public import Srtfp.Text.Float
public import Srtfp.Decimal

@[expose] public section

open Float.Model.UnpackedFloat (Sign)

namespace Srtfp.Schubfach

open Srtfp.Text (withSign decimalToString)
open Srtfp.Decimal (canonicaliseAux)

/-! ## The exponent suffix table -/

/-- `"e-324"`, `"e-323"`, ..., `"e292"`: every canonical binary64
    shortest-decimal exponent, with the `'e'` pre-attached. -/
def expTable : Array String :=
  Array.ofFn (fun i : Fin 617 => "e" ++ toString ((i.val : Int) - 324))

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
    withSign sign (toString sig ++ "e" ++ toString exp)

theorem emitChecked_eq (sign : Sign) (sig : Nat) (exp : Int) :
    emitChecked sign sig exp =
      withSign sign (toString sig ++ "e" ++ toString exp) := by
  unfold emitChecked
  split
  · rename_i h
    rw [show expTable[(exp + 324).toNat]'(by rw [expTable_size]; omega)
          = "e" ++ toString (((exp + 324).toNat : Int) - 324) from by
      simp [expTable]]
    rw [show (((exp + 324).toNat : Int) - 324) = exp from by omega]
    rw [String.append_assoc]
  · rfl

/-! ## `Decimal.mk'` as a string -/

theorem decimalToString_mk' (sign : Sign) (sig : Nat) (exp : Int) :
    decimalToString (_root_.Srtfp.Decimal.mk' sign sig exp)
      = (if sig = 0 then withSign sign "0"
        else if sig % 10 ≠ 0 then
          withSign sign (toString sig ++ "e" ++ toString exp)
        else
          let (sig', exp') := canonicaliseAux sig exp
          if sig' = 0 then withSign sign "0"
          else
            withSign sign (toString sig' ++ "e" ++ toString exp')) := by
  unfold decimalToString _root_.Srtfp.Decimal.mk' _root_.Srtfp.Decimal.canonical
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
    split <;> simp_all

end Srtfp.Schubfach

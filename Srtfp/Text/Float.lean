module
/- The compact Float string reference. Its numerical choices are certified
   by Srtfp.Correctness; special values use Lean's binary64 model. -/
public import Srtfp.Printer
public import Init.Data.Int.ToString

@[expose] public section

namespace Srtfp.Text

/-- Prefix a minus sign exactly for a negative value. -/
@[inline] def withSign (sign : Float.Model.UnpackedFloat.Sign) (s : String) : String :=
  match sign with | .negative => "-" ++ s | .positive => s

/-- Signed zero, or the significand followed by `e` and the signed exponent. -/
def decimalToString (d : Decimal) : String :=
  withSign d.sign (if d.significand = 0 then "0"
    else toString d.significand ++ "e" ++ toString d.exponent)

/-- The shortest decimal in the compact format, or `NaN` / signed `Infinity`. -/
def floatToString (f : Float) : String :=
  match Printer.toDecimal f with
  | some d => decimalToString d
  | none => match Spec.unpack f.toBits with
    | .infinity sign => withSign sign "Infinity"
    | _ => "NaN"

end Srtfp.Text

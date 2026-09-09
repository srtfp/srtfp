module
/- The decimal text grammar and its canonical value.
   This specification imports no parsing, formatting, or canonicalisation code. -/
public import Srtfp.Spec
public import Srtfp.DecimalSyntax
public import Init.Data.Nat.ToString

@[expose] public section

namespace Srtfp.Text.Spec

open Float.Model.UnpackedFloat (Sign)

/-- The spelling of a mantissa or exponent sign. -/
def SignChars (allowPlus : Bool) (cs : List Char) (sign : Sign) : Prop :=
  match sign with
  | .negative => cs = ['-']
  | .positive => cs = [] ∨ (allowPlus = true ∧ cs = ['+'])

/-- An omitted exponent means zero; a written exponent needs at least one digit. -/
def Exponent (cs : List Char) (e : Int) : Prop :=
  (cs = [] ∧ e = 0) ∨ ∃ marker pre sign ds,
    (marker = 'e' ∨ marker = 'E') ∧ SignChars true pre sign ∧
    ds ≠ [] ∧ ds.all Char.isDigit = true ∧ cs = marker :: (pre ++ ds) ∧
    e = (match sign with
      | .negative => -(Nat.ofDigitChars 10 ds 0 : Int)
      | .positive => Nat.ofDigitChars 10 ds 0)

/-- Allowed mantissa digits and decimal point, independently of any scanner. -/
def Mantissa (opts : DecimalSyntax) (intD fracD : List Char) (dot : Bool) : Prop :=
  intD.all Char.isDigit = true ∧ fracD.all Char.isDigit = true ∧
  (intD ≠ [] ∨ fracD ≠ []) ∧
  (intD = [] → opts.allowLeadingDot = true) ∧
  (dot = true → fracD = [] → opts.allowTrailingDot = true) ∧
  (dot = false → fracD = []) ∧
  (opts.requireDot = true → dot = true) ∧
  (2 ≤ intD.length → intD.head? = some '0' → opts.allowLeadingZeros = true)

/-- Canonicalisation preserves the sign and moves only trailing zeros into the exponent. -/
def Normalizes (sign : Sign) (sig : Nat) (exp : Int) (d : Decimal) : Prop :=
  d.IsCanonical ∧ d.sign = sign ∧
  ((sig = 0 ∧ d.significand = 0) ∨
    ∃ zeros : Nat, sig = d.significand * 10 ^ zeros ∧ d.exponent = exp + zeros)

/-- The complete decimal grammar and its canonical value. No whitespace or other suffix is allowed. -/
def Parses (opts : DecimalSyntax) (s : String) (d : Decimal) : Prop :=
  ∃ pre sign intD fracD dot tail exp,
    SignChars opts.allowExplicitMantissaPlus pre sign ∧ Mantissa opts intD fracD dot ∧
    Exponent tail exp ∧
    s.toList = pre ++ intD ++ (if dot then '.' :: fracD else []) ++ tail ∧
    Normalizes sign (Nat.ofDigitChars 10 (intD ++ fracD) 0) (exp - fracD.length) d

end Srtfp.Text.Spec

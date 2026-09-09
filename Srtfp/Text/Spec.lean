module
/- Decimal text grammar, canonical values, and exact presentation.
   This specification imports no parsing, formatting, or canonicalisation code. -/
public import Srtfp.Spec
public import Srtfp.Text.FormatOptions
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

/-- Exact decimal presentation. `point` counts digits before the decimal point;
    positions outside the significand are filled with zeros. -/
def Formats (opts : FormatOptions) (d : Decimal) (s : String) : Prop :=
  let ds := Nat.toDigits 10 d.significand
  let leading : Int := d.exponent + ds.length - 1
  let scientific := opts.mode.scientificAt leading
  let point : Int := if scientific then 1 else leading + 1
  let intD := if point ≤ 0 then ['0'] else
    ds.take point.toNat ++ List.replicate (point.toNat - ds.length) '0'
  let frac := List.replicate (-point).toNat '0' ++ ds.drop point.toNat
  let minFrac := if scientific then opts.sciMinFracDigits else opts.minFracDigits
  let fracD := frac ++ List.replicate (minFrac - frac.length) '0'
  let expD := Nat.toDigits 10 leading.natAbs
  let suffix := if scientific then
    (if opts.upperExp then 'E' else 'e') ::
      (if leading < 0 then ['-'] else if opts.expPlus then ['+'] else []) ++
      List.replicate (opts.expMinDigits - expD.length) '0' ++ expD
    else []
  s.toList = (match d.sign with | .negative => ['-'] | .positive => []) ++
    intD ++ (if fracD = [] then [] else '.' :: fracD) ++ suffix

/-- A formatter obeys the presentation rules on every decimal. -/
def CorrectFormatter (opts : FormatOptions) (p : Decimal → String) : Prop :=
  ∀ d, Formats opts d (p d)

end Srtfp.Text.Spec

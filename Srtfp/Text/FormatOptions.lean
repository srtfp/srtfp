module
/- Presentation choices, independent of the formatter and parser. -/
public import Srtfp.DecimalSyntax

@[expose] public section

namespace Srtfp.Text

/-- When to use exponent notation. `pointExp` is the decimal
    exponent of the leading significant digit (`1.5e3` has `pointExp = 3`,
    `0.05` has `pointExp = -2`). -/
inductive ExpMode where
  /-- Never use an exponent (Rust `Display` style). -/
  | positional
  /-- Always use an exponent (C `%e` style). -/
  | scientific
  /-- Positional iff `lo < pointExp < hi` (shortest-style windows:
      Python `repr` uses `(-5, 16)`, JavaScript `(-7, 21)`,
      Java `(-4, 7)`). -/
  | window (lo hi : Int)
  deriving Repr, DecidableEq, Inhabited

/-- How to render a `Decimal`. All options are value-preserving: padding
    only ever adds zeros, never rounds. -/
structure FormatOptions where
  /-- Positional vs exponent notation. -/
  mode : ExpMode := .window (-5) 16
  /-- Minimum digits after the decimal point in positional notation;
      `0` omits the point when there is no fractional part (`"2"`),
      `1` forces `"2.0"`. -/
  minFracDigits : Nat := 0
  /-- Minimum digits after the decimal point in exponent notation
      (`1` forces `"1.0e-7"`; Python's `repr` uses `0`: `"1e-05"`). -/
  sciMinFracDigits : Nat := 0
  /-- Print `'+'` on non-negative exponents (`"1e+21"`). -/
  expPlus : Bool := false
  /-- Zero-pad the exponent magnitude to this many digits (`2` gives
      `"1e-05"`). -/
  expMinDigits : Nat := 1
  /-- `'E'` instead of `'e'`. -/
  upperExp : Bool := false
  deriving Repr, DecidableEq, Inhabited

/-- The formatter emits a decimal point whenever the parsing dialect requires one. -/
def FormatOptions.CompatibleWith (fopts : FormatOptions) (popts : DecimalSyntax) : Prop :=
  popts.requireDot = true → 1 ≤ fopts.minFracDigits ∧ 1 ≤ fopts.sciMinFracDigits

namespace FormatOptions

/-- Python `repr`: the `(-5, 16)` window, positional `.0`, bare
    scientific mantissa, and
    `'+'`-signed two-digit exponents (`"2.0"`, `"1e+21"`, `"1e-05"`). -/
def python : FormatOptions := { minFracDigits := 1, expPlus := true, expMinDigits := 2 }

/-- JavaScript `String(x)`: wider window, integers without a dot
    (`"2"`, `"1e+21"`, `"1e-7"`). -/
def js : FormatOptions := { mode := .window (-7) 21, expPlus := true }

/-- Java `Double.toString`: narrow window, forced `.0`, uppercase bare
    exponent (`"2.0"`, `"1.0E7"`). -/
def java : FormatOptions :=
  { mode := .window (-4) 7, minFracDigits := 1, sciMinFracDigits := 1, upperExp := true }

/-- C `%e` shape without the rounding: always scientific, six fraction
    digits minimum, signed two-digit exponent (`"2.000000e+00"`). -/
def cScientific : FormatOptions :=
  { mode := .scientific, sciMinFracDigits := 6, expPlus := true, expMinDigits := 2 }

end FormatOptions

/-- Whether `mode` puts a value with leading-digit exponent `pointExp`
    in exponent notation. -/
def ExpMode.scientificAt : ExpMode → Int → Bool
  | .positional, _ => false
  | .scientific, _ => true
  | .window lo hi, pe => decide (pe ≤ lo) || decide (hi ≤ pe)

end Srtfp.Text

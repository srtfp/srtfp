module
/- Decimal ↔ String: a dialect-parameterized formatter and parser.

   `Srtfp`'s verified core stops at the `Decimal` record; this module is
   the shared text layer so that consumers (MLIR, JSON, YAML, ...)
   don't each hand-roll literal printing and parsing. The lexical shape a
   dialect *accepts* is a `DecimalSyntax` (`Srtfp/DecimalSyntax.lean`);
   the shape a printer *emits* is a `FormatOptions` below. One engine,
   per-dialect instantiation; `Srtfp/Text/Roundtrip.lean` proves
   `parse (format d) = some d` once, for every compatible pair.

   Format-specific specials stay out: YAML's `.inf`/`.nan` tokens and
   MLIR's `0x...` raw-bits form are not decimal literals and belong to
   the consumer. Truncating presentations (C's `%.6e` rounding a longer
   significand) are likewise excluded — every option here is
   value-preserving, which is what makes the round-trip theorem
   unconditional on the value. -/

public import Srtfp.Decimal
public import Srtfp.DecimalSyntax

@[expose] public section

namespace Srtfp.Text

/-! ## Presentation options -/

/-- When to use exponent notation. `pointExp` below is the decimal
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

/-! ## Digits -/

def digitChar (d : Nat) : Char := Char.ofNat (48 + d)

def digitVal (c : Char) : Nat := c.toNat - 48

def isDigitChar (c : Char) : Bool := 48 ≤ c.toNat && c.toNat ≤ 57

/-- Decimal digits of `n`, most significant first, prepended to `acc`. -/
def natCharsAux (n : Nat) (acc : List Char) : List Char :=
  if h : n < 10 then digitChar n :: acc
  else natCharsAux (n / 10) (digitChar (n % 10) :: acc)
  termination_by n
  decreasing_by exact Nat.div_lt_self (by omega) (by decide)

/-- Decimal digits of `n`, most significant first (`natChars 0 = ['0']`). -/
def natChars (n : Nat) : List Char := natCharsAux n []

/-- Value of a digit string, most significant first. -/
def charsVal (ds : List Char) : Nat := ds.foldl (fun a c => 10 * a + digitVal c) 0

/-! ## Formatting -/

/-- Whether `mode` puts a value with leading-digit exponent `pointExp`
    in exponent notation. -/
def ExpMode.scientificAt : ExpMode → Int → Bool
  | .positional, _ => false
  | .scientific, _ => true
  | .window lo hi, pe => decide (pe ≤ lo) || decide (hi ≤ pe)

/-- `".frac"`, with `frac` zero-padded to `minFrac` digits; empty when
    both are empty. -/
def dotFrac (minFrac : Nat) (frac : List Char) : List Char :=
  let frac := frac ++ List.replicate (minFrac - frac.length) '0'
  if frac.isEmpty then [] else '.' :: frac

/-- Exponent suffix `"e<exp>"` per the options. -/
def expChars (opts : FormatOptions) (e : Int) : List Char :=
  (if opts.upperExp then 'E' else 'e')
    :: (if e < 0 then ['-'] else if opts.expPlus then ['+'] else [])
    ++ (List.replicate (opts.expMinDigits - (natChars e.natAbs).length) '0'
        ++ natChars e.natAbs)

/-- Render an unsigned `(significand digits, exponent)` pair. -/
def formatMag (opts : FormatOptions) (ds : List Char) (exp : Int) : List Char :=
  let pointExp : Int := exp + ds.length - 1
  if opts.mode.scientificAt pointExp then
    ds.take 1 ++ dotFrac opts.sciMinFracDigits (ds.drop 1) ++ expChars opts pointExp
  else if 0 ≤ exp then
    ds ++ List.replicate exp.toNat '0' ++ dotFrac opts.minFracDigits []
  else if (ds.length : Int) + exp ≤ 0 then
    '0' :: dotFrac opts.minFracDigits
      (List.replicate (-((ds.length : Int) + exp)).toNat '0' ++ ds)
  else
    let whole := ((ds.length : Int) + exp).toNat
    ds.take whole ++ dotFrac opts.minFracDigits (ds.drop whole)

/-- Render a `Decimal` as a character list. -/
def formatChars (opts : FormatOptions) (d : Decimal) : List Char :=
  (if d.sign then ['-'] else []) ++ formatMag opts (natChars d.significand) d.exponent

/-- Render a `Decimal` as a `String`. -/
def format (opts : FormatOptions) (d : Decimal) : String :=
  String.ofList (formatChars opts d)

/-! ## Parsing -/

/-- Parse a nonempty all-digit run as the (possibly negated) exponent
    value, requiring end of input. -/
def parseExpDigits (neg : Bool) (rest : List Char) : Option Int :=
  let ds := rest.takeWhile isDigitChar
  if ds.isEmpty ∨ ¬ (rest.dropWhile isDigitChar).isEmpty then none
  else some (if neg then -(charsVal ds : Int) else (charsVal ds : Int))

/-- Parse the optional exponent suffix and require end of input.
    Returns the exponent value (`0` when absent). -/
def parseExpTail (cs : List Char) : Option Int :=
  if cs.isEmpty then some 0
  else if cs.head? = some 'e' ∨ cs.head? = some 'E' then
    if cs.tail.head? = some '-' then parseExpDigits true cs.tail.tail
    else if cs.tail.head? = some '+' then parseExpDigits false cs.tail.tail
    else parseExpDigits false cs.tail
  else none

/-- Parse the digits-and-dot mantissa body (no sign), returning the
    integer-part and fraction-part digit strings and the remainder. -/
def parseMantissa (opts : DecimalSyntax) (cs : List Char) :
    Option (List Char × List Char × List Char) :=
  let intD := cs.takeWhile isDigitChar
  let rest := cs.dropWhile isDigitChar
  if intD.isEmpty ∧ ¬ opts.allowLeadingDot then none
  else if ¬ opts.allowLeadingZeros ∧ 2 ≤ intD.length ∧ intD.head? = some '0' then none
  else if rest.head? = some '.' then
    let fracD := rest.tail.takeWhile isDigitChar
    if fracD.isEmpty ∧ intD.isEmpty then none
    else if fracD.isEmpty ∧ ¬ opts.allowTrailingDot then none
    else some (intD, fracD, rest.tail.dropWhile isDigitChar)
  else if opts.requireDot ∨ intD.isEmpty then none
  else some (intD, [], rest)

/-- Parse a decimal literal under dialect `opts`, given the sign
    separately (for callers whose lexer already consumed it). The result
    is canonical (`Decimal.mk'`). -/
def parseMag (opts : DecimalSyntax) (sign : Bool) (cs : List Char) : Option Decimal :=
  (parseMantissa opts cs).bind fun (intD, fracD, rest) =>
    (parseExpTail rest).map fun e =>
      Decimal.mk' sign (charsVal (intD ++ fracD)) (e - fracD.length)

/-- Parse a decimal literal (with optional leading sign) under dialect
    `opts`. The result is canonical (`Decimal.mk'`). -/
def parseChars (opts : DecimalSyntax) (cs : List Char) : Option Decimal :=
  if cs.head? = some '-' then parseMag opts true cs.tail
  else if cs.head? = some '+' then
    if opts.allowExplicitMantissaPlus then parseMag opts false cs.tail else none
  else parseMag opts false cs

/-- Parse a decimal literal from a `String`. -/
def parse (opts : DecimalSyntax) (s : String) : Option Decimal :=
  parseChars opts s.toList

end Srtfp.Text

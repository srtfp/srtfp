module
/- Decimal ↔ String: a dialect-parameterized formatter and parser.

   `Srtfp`'s verified core stops at the `Decimal` record; this module is
   the shared text layer so that consumers (MLIR, JSON, YAML, ...)
   don't each hand-roll literal printing and parsing. The lexical shape a
   dialect *accepts* is a `DecimalSyntax` (`Srtfp/DecimalSyntax.lean`);
   the shape a printer *emits* is a `FormatOptions` below. One engine,
   per-dialect instantiation; `Srtfp/Proofs/Text.lean` proves
   `parse (format d) = some d` once, for every compatible pair.

   Both directions go through the `Lexeme`: the skeleton
   `[-]int[.frac][e exp]` of a literal, as digit lists.

     format = render ∘ place        parse = value ∘ lex

   `place` chooses positional or scientific layout and pads; `render`
   prints a lexeme; `lex` is the dialect grammar; `value` reads a
   lexeme's digits back into a canonical `Decimal`. The round trip is
   then two independent facts — `lex` inverts `render` on well-formed
   lexemes, and `value` inverts `place` on canonical decimals — glued by
   `place` only ever producing well-formed lexemes.

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

open Float.Model.UnpackedFloat (Sign)

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

/-- Decimal digits of `n`, most significant first (`natChars 0 = ['0']`). -/
def natChars (n : Nat) : List Char :=
  if n < 10 then [digitChar n] else natChars (n / 10) ++ [digitChar (n % 10)]
decreasing_by omega

/-- Value of a digit string, most significant first. -/
def charsVal (ds : List Char) : Nat := ds.foldl (fun a c => 10 * a + digitVal c) 0

/-! ## Lexemes -/

/-- The skeleton `[-]int[.frac][e exp]` of a decimal literal: digit lists
    (most significant first) and the exponent when one is written. -/
structure Lexeme where
  sign : Sign
  intD : List Char
  fracD : List Char
  exp : Option Int
  deriving Repr

/-- The decimal a lexeme denotes, canonicalised. -/
def Lexeme.value (l : Lexeme) : Decimal :=
  Decimal.mk' l.sign (charsVal (l.intD ++ l.fracD)) (l.exp.getD 0 - l.fracD.length)

/-! ## Formatting -/

/-- Whether `mode` puts a value with leading-digit exponent `pointExp`
    in exponent notation. -/
def ExpMode.scientificAt : ExpMode → Int → Bool
  | .positional, _ => false
  | .scientific, _ => true
  | .window lo hi, pe => decide (pe ≤ lo) || decide (hi ≤ pe)

/-- `ds` right-padded with zeros to at least `n` digits. -/
def padTo (n : Nat) (ds : List Char) : List Char :=
  ds ++ List.replicate (n - ds.length) '0'

/-- The lexeme whose digits are `D` with the point after the first `w`
    of them, fraction padded to `n` digits. -/
def Lexeme.split (sign : Sign) (D : List Char) (w n : Nat) (exp : Option Int) : Lexeme :=
  ⟨sign, D.take w, padTo n (D.drop w), exp⟩

/-- Lay out the significand digits `ds` (nonempty) and exponent `exp`
    per `opts`. Scientific keeps one digit before the point and writes
    the exponent; positional writes the digits with the point `(-exp)⁺`
    places from their right end, zeros filling whatever positions the
    significand does not cover (`⟨5, -4⟩` becomes `0.0005`,
    `⟨15, 2⟩` becomes `1500`). -/
def place (opts : FormatOptions) (sign : Sign) (ds : List Char) (exp : Int) : Lexeme :=
  let pointExp : Int := exp + ds.length - 1
  if opts.mode.scientificAt pointExp then
    .split sign ds 1 opts.sciMinFracDigits (some pointExp)
  else
    let D := List.replicate (-pointExp).toNat '0' ++ ds ++ List.replicate exp.toNat '0'
    .split sign D (D.length - (-exp).toNat) opts.minFracDigits none

/-- `|e|` zero-padded on the left to at least `n` digits. -/
def expDigits (n : Nat) (e : Int) : List Char :=
  List.replicate (n - (natChars e.natAbs).length) '0' ++ natChars e.natAbs

/-- Exponent suffix `e<exp>` per the options. -/
def expChars (opts : FormatOptions) (e : Int) : List Char :=
  (if opts.upperExp then 'E' else 'e')
    :: (if e < 0 then ['-'] else if opts.expPlus then ['+'] else [])
    ++ expDigits opts.expMinDigits e

/-- Print a lexeme: sign, integer digits, `.frac` when there is a
    fraction, the exponent suffix when there is an exponent. -/
def render (opts : FormatOptions) (l : Lexeme) : List Char :=
  (match l.sign with | .negative => ['-'] | .positive => [])
    ++ l.intD
    ++ (if l.fracD = [] then [] else '.' :: l.fracD)
    ++ (match l.exp with | some e => expChars opts e | none => [])

/-- Render a `Decimal` as a `String`. -/
def format (opts : FormatOptions) (d : Decimal) : String :=
  String.ofList (render opts (place opts d.sign (natChars d.significand) d.exponent))

/-! ## Parsing -/

/-- An optional leading sign; `'+'` only when `allowPlus`. -/
def lexSign (allowPlus : Bool) (cs : List Char) : Option (Sign × List Char) :=
  if cs.head? = some '-' then some (.negative, cs.tail)
  else if cs.head? = some '+' then (if allowPlus then some (.positive, cs.tail) else none)
  else some (.positive, cs)

/-- `[+-]?digits`, to end of input, as an exponent value. -/
def lexExp (cs : List Char) : Option Int :=
  (lexSign true cs).bind fun (s, ds) =>
    if ds = [] ∨ ¬ ds.all Char.isDigit then none
    else some (match s with | .negative => -(charsVal ds : Int) | .positive => charsVal ds)

/-- The optional exponent suffix, then end of input. -/
def lexExpTail : List Char → Option (Option Int)
  | [] => some none
  | c :: cs => if c = 'e' ∨ c = 'E' then (lexExp cs).map some else none

/-- The digits-and-dot body under dialect `opts`: the integer and
    fraction digit runs and the unconsumed remainder. -/
def lexMantissa (opts : DecimalSyntax) (cs : List Char) :
    Option (List Char × List Char × List Char) :=
  let intD := cs.takeWhile Char.isDigit
  let rest := cs.dropWhile Char.isDigit
  if intD = [] ∧ ¬ opts.allowLeadingDot then none
  else if ¬ opts.allowLeadingZeros ∧ 2 ≤ intD.length ∧ intD.head? = some '0' then none
  else if rest.head? = some '.' then
    let fracD := rest.tail.takeWhile Char.isDigit
    if fracD = [] ∧ (intD = [] ∨ ¬ opts.allowTrailingDot) then none
    else some (intD, fracD, rest.tail.dropWhile Char.isDigit)
  else if opts.requireDot ∨ intD = [] then none
  else some (intD, [], rest)

/-- Lex a decimal literal under dialect `opts`. -/
def lex (opts : DecimalSyntax) (cs : List Char) : Option Lexeme := do
  let (sign, cs) ← lexSign opts.allowExplicitMantissaPlus cs
  let (intD, fracD, rest) ← lexMantissa opts cs
  let exp ← lexExpTail rest
  pure ⟨sign, intD, fracD, exp⟩

/-- Parse a decimal literal from a `String`. The result is canonical
    (`Decimal.mk'`). -/
def parse (opts : DecimalSyntax) (s : String) : Option Decimal :=
  (lex opts s.toList).map Lexeme.value

end Srtfp.Text

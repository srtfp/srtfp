module
/- The lexical shape of a decimal literal a dialect accepts.

   `Srtfp.Text.parse` is parameterised by this record so JSON, YAML,
   MLIR and friends share one parser and one round-trip proof
   (`Srtfp/Text/Roundtrip.lean`). The baseline with every flag off is
   the strict RFC 8259 grammar

     [-]?(0|[1-9][0-9]*)(\.[0-9]+)?([eE][+-]?[0-9]+)?

   and each flag admits one more form. Two of the flags describe tokens
   that are not decimal literals at all (`.nan`, `0x..`); `Text.parse`
   never consults them and a consumer handles those tokens itself. -/

@[expose] public section

namespace Srtfp

/-- Options describing the permitted shape of a decimal literal. All
    fields default to `false` (strict JSON); dialect presets below flip
    the relevant flags. -/
structure DecimalSyntax where
  /-- Allow a leading `.` with no integer-part digit, e.g. `".5"`. JSON: no. YAML: yes. -/
  allowLeadingDot : Bool := false
  /-- Allow a trailing `.` with no fractional-part digit, e.g. `"5."`. JSON: no. YAML: yes. -/
  allowTrailingDot : Bool := false
  /-- Allow an explicit `'+'` mantissa sign, e.g. `"+5"`. JSON: no. YAML: yes. -/
  allowExplicitMantissaPlus : Bool := false
  /-- Permit `.nan` / `.inf` / `-.inf` literals. JSON: no — non-finite
      values have no JSON syntax. YAML: yes (canonical forms). Not a
      decimal literal, so `Text.parse` does not consult this flag. -/
  allowNonFiniteLiterals : Bool := false
  /-- Permit hexadecimal / octal / binary integer literals (`0x...`,
      `0o...`, `0b...`). JSON: no. YAML 1.1: yes, YAML 1.2: no for octal,
      yes for the others under specific tags. Not a decimal literal, so
      `Text.parse` does not consult this flag. -/
  allowAlternativeBases : Bool := false
  /-- Require the decimal point: a bare integer literal like `"2"` is not
      a float. JSON: no (integers are floats). MLIR: yes. -/
  requireDot : Bool := false
  /-- Allow redundant leading zeros on the integer part, e.g. `"007.5"`.
      JSON: no. MLIR: yes (`[0-9]+` digits). -/
  allowLeadingZeros : Bool := false
  deriving Repr, DecidableEq, Inhabited

namespace DecimalSyntax

/-- Strict RFC 8259 JSON: no permissive features. -/
def jsonStrict : DecimalSyntax := {}

/-- YAML 1.2 "core schema" floats: permits leading/trailing `.`, explicit
    `+` on the mantissa, and the non-finite literals. Hex literals are
    NOT in the core schema (they require the explicit `!!int` tag). -/
def yamlCore : DecimalSyntax :=
  { allowLeadingDot          := true
  , allowTrailingDot         := true
  , allowExplicitMantissaPlus := true
  , allowNonFiniteLiterals    := true
  , allowAlternativeBases     := false }

/-- YAML 1.1 extended: like `yamlCore` plus hex/octal/binary integers
    (which several YAML 1.1 emitters still produce in the wild). -/
def yaml11 : DecimalSyntax :=
  { yamlCore with allowAlternativeBases := true }

/-- MLIR float literals: `[0-9]+ '.' [0-9]* ([eE][+-]?[0-9]+)?`. The dot
    is mandatory, may dangle (`"2."`), and leading zeros are allowed
    (`"007.5"`). The mantissa sign is lexed separately in MLIR, so `'+'`
    stays disallowed here. -/
def mlir : DecimalSyntax :=
  { requireDot        := true
  , allowTrailingDot  := true
  , allowLeadingZeros := true }

end DecimalSyntax

end Srtfp

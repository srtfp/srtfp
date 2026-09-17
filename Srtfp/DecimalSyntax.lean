module
/- The lexical shape of a decimal literal a dialect accepts.

   `Srtfp.Text.parse` is parameterised by this record so JSON, YAML,
   MLIR and friends share one parser, certified against the grammar in
   `Srtfp/Text/Spec.lean`. The baseline with every flag off is
   the strict RFC 8259 grammar

     [-]?(0|[1-9][0-9]*)(\.[0-9]+)?([eE][+-]?[0-9]+)?

   The flags adjust this grammar. Non-finite tokens (`.nan`, `.inf`)
   and alternative bases (`0x...`, `0o...`, `0b...`) belong to the
   consuming parser; this record describes decimal literals only. -/

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

/-- YAML-style decimal floats: permits leading/trailing `.` and explicit
    `+` on the mantissa. This describes decimal syntax, not a complete
    YAML schema. -/
def yamlCore : DecimalSyntax :=
  { allowLeadingDot          := true
  , allowTrailingDot         := true
  , allowExplicitMantissaPlus := true }

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

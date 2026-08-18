module
/- M7 milestone: extensibility audit for the upcoming JSON ↔ YAML bridge.

   `decimalNumber` (M2.3) accepts the strict RFC 8259 number grammar:

     [-]?(0|[1-9][0-9]*)(\.[0-9]+)?([eE][+-]?[0-9]+)?

   YAML 1.2 is more permissive — leading `.`, trailing `.`, explicit `+`
   on the mantissa sign, and the special tokens `.nan` / `.inf` / `-.inf`
   are all valid. This file documents the **option surface** for
   parameterising the decimal biparser so that future code can instantiate
   it for JSON-strict, YAML-permissive, or any intermediate dialect
   without forking the implementation.

   The implementation parameterisation is intentionally NOT in this file —
   the M2 biparser is already pulling its weight on JSON; pulling the
   options record through every combinator would be a large refactor for
   no immediate user. This module captures the *design contract* so the
   refactor (when actually needed for the YAML port) has a clear target.

   See also: dissertation §6 for the JSON-↔-YAML bridge plan. -/

@[expose] public section

namespace Srtfp

/-- Options describing the permitted shape of a decimal literal. The
    JSON-strict instance is currently embedded in `decimalNumber`; a
    parameterised `decimalNumberWith` taking a `DecimalSyntax` argument
    would consult these fields when assembling its choice tree.

    All fields default to `false` (strict JSON). YAML instances should
    flip the relevant flags. -/
structure DecimalSyntax where
  /-- Allow a leading `.` with no integer-part digit, e.g. `".5"`. JSON: no. YAML: yes. -/
  allowLeadingDot : Bool := false
  /-- Allow a trailing `.` with no fractional-part digit, e.g. `"5."`. JSON: no. YAML: yes. -/
  allowTrailingDot : Bool := false
  /-- Allow an explicit `'+'` mantissa sign, e.g. `"+5"`. JSON: no. YAML: yes. -/
  allowExplicitMantissaPlus : Bool := false
  /-- Permit `.nan` / `.inf` / `-.inf` literals (mapping to the obvious
      `Float` values). JSON: no — non-finite values have no JSON syntax.
      YAML: yes (canonical forms). -/
  allowNonFiniteLiterals : Bool := false
  /-- Permit hexadecimal / octal / binary integer literals (`0x...`,
      `0o...`, `0b...`). JSON: no. YAML 1.1: yes, YAML 1.2: no for octal,
      yes for the others under specific tags. -/
  allowAlternativeBases : Bool := false
  /-- Require the decimal point: a bare integer literal like `"2"` is not
      a float. JSON: no (integers are floats). MLIR: yes. -/
  requireDot : Bool := false
  /-- Allow redundant leading zeros on the integer part, e.g. `"007.5"`.
      JSON: no. MLIR: yes (`[0-9]+` digits). -/
  allowLeadingZeros : Bool := false
  deriving Repr, DecidableEq, Inhabited

namespace DecimalSyntax

/-- Strict RFC 8259 JSON: no permissive features. This is the dialect
    `Srtfp.decimalNumber` already implements. -/
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

/-! ## Refactor sketch (decided not worth pursuing)

Originally this section sketched parameterising every component of
`decimalNumber` (mantissa sign, int part, frac part, exp part, etc.) over
the `DecimalSyntax` record so that `decimalNumberWith yamlCore` and
`decimalNumberWith yaml11` would each produce a syntax-specific parser
rather than dispatching through the union parser `decimalNumberPermissive`.

That refactor is **not worth doing** for the M7-scoped flags
(`allowLeadingDot`, `allowTrailingDot`, `allowExplicitMantissaPlus`), and
this note documents why so a future reader doesn't reattempt it.

### Reason: proof coupling

`IsQuad decimalNumberPermissive` and `IsQuad (decimalNumberWith yamlCore /
yaml11)` are proven in `Srtfp/Proofs/DecimalWith/IsoWith.lean`
(≈4000 lines). Those proofs are structured around a single fixed iso
`mkDecimalNumberIsoWith` whose `bwd` case-splits on `DecimalFormat` and
whose `fwd` is a closed-form function of the four parsed components.
Each per-constructor lemma (e.g. `mkDNIw_semiRev_plusInteger`) reduces
the iso symbolically.

Genuinely parameterising the components over `cfg` would require either:

* threading `cfg` through `mkDecimalNumberIsoWith` (making the iso
  dependent on `cfg`), forcing every per-constructor lemma to take
  `cfg` and re-prove its reduction under each flag combination, OR
* splitting the iso into multiple per-cfg isos and re-proving each one
  from scratch.

Either path multiplies the proof surface several-fold. The cleanup is
cosmetic; the cost is "re-prove the whole IsoWith file", which violates
the rule-of-thumb that refactors should adapt existing proofs via
`unfold` / `simp` rather than rebuild them.

### Current architecture is already direct

`decimalNumberWith cfg` dispatches in one step:

* If no M7 permissive flag is set ⇒ `decimalNumber` (strict).
* Otherwise ⇒ `decimalNumberPermissive` (union of all M7 forms).

`decimalNumberPermissive` accepts everything `decimalNumber` accepts plus
the leading-dot / trailing-dot / explicit-plus variants, and records the
syntactic shape in `DecimalFormat`. For the M7 flags this *is* the
syntax-specific behaviour for `yamlCore` and `yaml11` (they enable the
same union of forms and so legitimately share the same parser). The
dispatch is already as direct as it can be without splitting the iso.

### Sketches for the un-implemented flags

If the future M8+ work for `allowNonFiniteLiterals` and
`allowAlternativeBases` does proceed, those flags would each warrant a
new dispatch branch in `decimalNumberWith`. They would NOT extend
`decimalNumberPermissive` — they require new `DecimalFormat`
constructors and probably a new value type (`Decimal` can't represent
`nan`/`inf`/non-decimal bases). For reference, the original sketches:

* **Non-finite literals**: add a first-priority `.nan` / `.inf` / `-.inf`
  branch; extends the value type past `Decimal` so this is a different
  biparser, not a permissive variant of `decimalNumber`.
* **Alternative bases**: add hex/oct/bin branches with a base-conversion
  iso; the complement extends with a base tag.

Each would land as its own named biparser (e.g.
`decimalOrSpecialFloat` / `decimalOrAltBase`) with its own proof file,
and `decimalNumberWith` would dispatch to it when the relevant flag is
set. Both have a much larger scope than the M7 refactor and would
plausibly justify their own milestone, not a refactor of the existing
dispatch. -/

end Srtfp

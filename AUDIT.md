# Audit guide

Read the specification definitions and certifying theorem statements for the
APIs you use, then inspect the shared checks below. Lean checks the local
implementation and proof bodies; they are outside the manual review boundary.
The pinned Lean kernel, compiler, and upstream runtime implementations are trusted.

## API contracts

| API | Definitions to review | Certifying statements |
| --- | --- | --- |
| `Printer.toDecimalBits`, `Printer.toDecimal` | [Srtfp/Spec.lean](Srtfp/Spec.lean) | [Srtfp/Correctness.lean](Srtfp/Correctness.lean): `correct_iff_toDecimal`, `shortest_decimal_exists_unique`, `toDecimal_spec` |
| `Reader.ofDecimalBits`, `Reader.ofDecimal` | `Decimal.toModel` in `Srtfp/Spec.lean` and the two direct wrappers in [Srtfp/Reader.lean](Srtfp/Reader.lean) | Definitional equality with the signed upstream conversion |
| `Decimal` canonicalisation, constructors, scientific literals, constants, negation | `Decimal`, `IsCanonical`, `Normalizes` in `Srtfp/Spec.lean` | [Srtfp/Decimal/Correctness.lean](Srtfp/Decimal/Correctness.lean) |
| `Text.parse` | [Srtfp/DecimalSyntax.lean](Srtfp/DecimalSyntax.lean), the grammar in [Srtfp/Text/Spec.lean](Srtfp/Text/Spec.lean), and `Decimal.Normalizes` | [Srtfp/Text/Correctness.lean](Srtfp/Text/Correctness.lean): `parse_spec`, `correct_iff_parse` |
| `Text.format` | [Srtfp/Text/FormatOptions.lean](Srtfp/Text/FormatOptions.lean), `Formats` and `CorrectFormatter` in `Srtfp/Text/Spec.lean` | `Srtfp/Text/Correctness.lean`: `format_spec`, `correct_iff_format`, `format_parses` |
| `Text.floatToString` | The three definitions in [Srtfp/Text/Float.lean](Srtfp/Text/Float.lean), plus the numerical specification | `Srtfp/Correctness.lean`: `toDecimal_spec`; [Srtfp/Perf/Schubfach/Entry.lean](Srtfp/Perf/Schubfach/Entry.lean): `floatToString_eq` |

The numerical contract covers every binary64 bit pattern, both signs of zero,
and arbitrary decimal significands and exponents. It delegates decimal rounding
to upstream `Float.Model.ofScientific`; there is no local rounding algorithm or
overflow threshold in the specification. The printer's biconditional establishes
both correctness and uniqueness. Runtime `Float` results satisfy the same
specification through `.toBits`.

The text parser contract includes rejection and canonicalisation. Formatting
specifies the exact spelling even for noncanonical decimals. For canonical inputs,
parsing that spelling recovers the input when `FormatOptions.CompatibleWith` holds.
The dialect flags define the certified grammar; external JSON, YAML, or MLIR
standards are not themselves formalised. Non-finite tokens and alternative bases
belong to a consuming parser. `Text.floatToString` is separate from `Text.format`.

## Shared checks

Inspect [Test/Audit.lean](Test/Audit.lean), the pinned
[lean-toolchain](lean-toolchain), and the package options and audit target in
[lakefile.lean](lakefile.lean). Run:

```sh
lake build Test.Audit
lake test
```

The audit uses upstream `Lean.collectAxioms` and selects declarations by their
defining module, including private helpers and declarations outside the `Srtfp`
namespace. It permits only `propext`, `Quot.sound`, and `Classical.choice`.
It rejects `sorryAx`, native proof axioms, local partial or unsafe definitions,
and unchecked `@[extern]` or `@[implemented_by]` replacements. Fast paths use
kernel-checked equality proofs via `@[csimp]`.

The audit covers both implementation tiers and also runs in a default `lake build`.
[Test/AuditTests.lean](Test/AuditTests.lean) checks its rejection behavior;
[Srtfp/Perf/CsimpPin.lean](Srtfp/Perf/CsimpPin.lean) pins the compiler replacements.
[Test/SpecImports.lean](Test/SpecImports.lean) ensures specification modules import
only upstream Lean and other specification modules.

`Rat` and its arithmetic come from Lean. The lemmas in
[Srtfp/Rat.lean](Srtfp/Rat.lean) and tactics in
[Srtfp/Perf/Tactics.lean](Srtfp/Perf/Tactics.lean) are local proof helpers, not
verbatim Mathlib copies. They are covered by the audit and excluded from the
specification imports.

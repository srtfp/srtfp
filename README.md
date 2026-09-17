# srtfp: a verified shortest round-trip float printer

A Lean 4 library providing, for IEEE-754 binary64:

- a **shortest round-trip printer**, as a dead-simple reference plus a
  verified fast path (the [Schubfach
  algorithm](https://drive.google.com/file/d/1IEeATSVnEE6TkrHlCYNY2GjaraBjOT4f/view)),
- a **correctly rounded parser**, and
- a machine-checked certification connecting them.

## Specification

The flagship theorems guarantee that, for every 64-bit float, the
printer:

1. rejects NaN and ±∞ with `none`, and otherwise returns a decimal
   that
2. **round-trips**: reading the decimal back yields the original float,
   bit for bit;
3. is **shortest**: no other round-tripping decimal has fewer
   significant digits;
4. is **closest**: among equally short candidates, it is nearest the
   float's exact value; and
5. **breaks ties to even**: at equal distance, it has the even
   significand.

These properties uniquely determine the printer's behavior, and
likewise the parser's: a function is a correct shortest-decimal printer iff it is
`Printer.toDecimalBits`, and a correct round-to-nearest reader iff it
is `Reader.ofDecimalBits`. For the exact statements, see
[`Srtfp/Correctness.lean`](Srtfp/Correctness.lean).

The library has two implementation tiers, each a separate import:

- **Reference (`import Srtfp`, the default)**: the specification made
  effective, in exact rational arithmetic over Lean's own model of the
  format. The printer walks the decimal grids from coarse to fine and
  tests the two grid neighbours of the value against its rounding
  interval; the reader rounds the value to the binary64 grid around it
  and packs the result with core's `Float.Model.pack`. Plus the proofs
  and certification of both the `UInt64` and runtime `Float` entry points
  against the same specification over raw IEEE-754 bit patterns.
  Uses nothing beyond Lean's three standard axioms (`propext`,
  `Quot.sound`, `Classical.choice`); a build-time audit enforces this.
- **Performance (`import Srtfp.Perf`, opt-in)**: Giulietti's Schubfach
  printer on 64-bit words, written to follow the paper and proven
  result by result (`Srtfp/Perf/Schubfach/`), and an Eisel–Lemire
  kernel with an exact big-integer fallback for reading, each proven
  equal to the reference and registered as a `@[csimp]` rewrite, so
  compiled code runs the fast path while the proofs still speak about
  the reference. Same axiom budget as the reference tier. Deleting
  `Srtfp/Perf/` leaves the library working, only slower.

## Reading the code

Review the specification definitions and the certifying theorem statements
for the APIs you use, plus the shared checks below. Lean checks the proofs;
the implementation and proof bodies need no manual review.

| API | Specification to read | Certifying statements |
| --- | --- | --- |
| `Reader.ofDecimalBits`, `Printer.toDecimalBits`, and their `Float` wrappers | [`Srtfp/Spec.lean`](Srtfp/Spec.lean) | [`Srtfp/Correctness.lean`](Srtfp/Correctness.lean): `correct_iff_ofDecimal`, `correct_iff_toDecimal`, `ofDecimal_spec`, `toDecimal_spec` |
| `Decimal` canonicalisation, constructors, scientific literals, constants, and negation | `Decimal`, `IsCanonical`, and `Normalizes` in `Srtfp/Spec.lean` | [`Srtfp/Decimal/Correctness.lean`](Srtfp/Decimal/Correctness.lean) |
| `Text.parse` | [`Srtfp/DecimalSyntax.lean`](Srtfp/DecimalSyntax.lean) and the grammar in [`Srtfp/Text/Spec.lean`](Srtfp/Text/Spec.lean), using `Decimal.Normalizes` | [`Srtfp/Text/Correctness.lean`](Srtfp/Text/Correctness.lean): `parse_spec`, `correct_iff_parse` |
| `Text.format` | [`Srtfp/Text/FormatOptions.lean`](Srtfp/Text/FormatOptions.lean) and `Formats` / `CorrectFormatter` in `Srtfp/Text/Spec.lean` | `Srtfp/Text/Correctness.lean`: `format_spec`, `correct_iff_format`; `format_parses` for canonical inputs and compatible options |
| `Text.floatToString` and its fast emitter | The three definitions in [`Srtfp/Text/Float.lean`](Srtfp/Text/Float.lean), plus the numerical specification above | `Srtfp/Correctness.lean`: `toDecimal_spec`; [`Srtfp/Perf/Schubfach/Entry.lean`](Srtfp/Perf/Schubfach/Entry.lean): `floatToString_eq` |

The numerical specification uses upstream `Float.Model.UnpackedFloat.unpack`,
`Rat`, and `Nat.toDigits`. Its biconditionals establish both correctness and
uniqueness. In particular, existence of a correct reader makes the printer's
“under every correct reader” condition non-vacuous. The runtime `Float` APIs
satisfy the same word specification through `.toBits`.

Here “shortest” counts **significand digits**, not rendered characters.
The specification preserves both signs of zero, accepts arbitrary decimal
significands and exponents, and rounds overflow to signed infinity at
`2^1024 - 2^970`.

`Decimal.Normalizes` specifies the unique canonical decimal obtained by
moving trailing significand zeros into the exponent, preserving the sign.
The constructor theorems and text grammar share this rule. Negation reverses
the sign even at zero; `ofInt 0` and the named `zero` are positive.

The text parser theorem includes rejection as well as accepted strings and
canonical values. The formatting theorem fixes the exact spelling on every
`Decimal`, including noncanonical inputs. For canonical inputs, parsing that
spelling recovers the input when `FormatOptions.CompatibleWith` holds. The certified
grammar is defined by the dialect flags; conformance to external JSON, YAML,
or MLIR standards is not established.

`DecimalSyntax` controls decimal literals only. Non-finite tokens and
alternative bases belong to the consuming parser; the unused
`allowNonFiniteLiterals` and `allowAlternativeBases` fields have been removed.
`yaml11` remains a compatibility alias for `yamlCore`.

The compact `Text.floatToString` format prints zero as `"0"` or `"-0"`,
nonzero finite values as signed `significand ++ "e" ++ exponent`, and
special values as `"NaN"` or signed `"Infinity"`. It uses upstream integer
printing and the same binary64 model. It is separate from the configurable
`Text.format`; importing `Srtfp.Perf` compiles it to the certified fast emitter.

For every review, also inspect [`Test/Audit.lean`](Test/Audit.lean), the pinned
[`lean-toolchain`](lean-toolchain), and the package options and audit target in
[`lakefile.lean`](lakefile.lean). Run `lake build Test.Audit` on the checkout.
The audit uses upstream `Lean.collectAxioms` and selects declarations by their
defining module, covering private helpers and declarations outside the `Srtfp`
namespace. Only `propext`, `Quot.sound`, and `Classical.choice` are allowed;
there is no exception for `sorryAx` or native proofs. It also rejects local
partial or unsafe definitions and unchecked `@[extern]` or `@[implemented_by]`
replacements. The fast paths use equality proofs via `@[csimp]`.

This audit covers both implementation tiers and runs in `lake build` and
`lake test`; its regression fixtures are in
[`Test/AuditTests.lean`](Test/AuditTests.lean). Lean's kernel, compiler, and
upstream runtime implementations are trusted.

The implementation itself is two short modules of exact arithmetic,
worth reading to understand the algorithms; both import only the
specification:

| Module | Contents |
| --- | --- |
| [`Srtfp/Printer.lean`](Srtfp/Printer.lean) | the printer, `toDecimalBits`: the rounding interval and the scan over decimal grids |
| [`Srtfp/Reader.lean`](Srtfp/Reader.lean) | the reader, `ofDecimalBits`: round to the binary64 grid, pack with core's model |

Everything else is proof (`Srtfp/Proofs/`; `Proofs/Model.lean` relates
core's `pack` and `unpack`, `Proofs/Reader/` and `Proofs/Printer/` are the
two correctness proofs), operations on `Decimal`
(`Srtfp/Decimal.lean`), the text layer (`Srtfp/Text.lean`, `Decimal` ↔
`String` for JSON, YAML, MLIR, …), or the performance tier (`Srtfp/Perf/`,
where the bit-field arithmetic of the fast kernels also lives).

Zero dependencies beyond the Lean toolchain: no mathlib, and the test
suite runs on a small in-repo harness (`Test/Harness.lean`). CI builds
and tests the library on Lean v4.33.0 (the pinned toolchain and the
floor: core's `Float.Model` arrived in v4.33).
The proofs' small compatibility layer (Mathlib's lemma names over core's
`Rat`, the `|·|` bars) lives in the `Srtfp.Compat` namespace with scoped
notation, so srtfp and Mathlib can be imported in the same file without
collisions.

## Build

```
lake build           # all library tiers and the audit
lake test            # audit, import-boundary checks, and the test suite
make                 # same as lake build
make test            # same as lake test (make check is an alias)
make benchmarks      # build benchmark and differential-test helpers
```

## Extra tests

Differential testing against C++'s `std::to_chars` and CPython's `repr`
found no unexplained differences out of 100 billion tested values. (The
one explained difference: `to_chars` prints large integers verbatim
rather than shortest, e.g. `784169164648129232896` instead of
`7.841691646481292e+20`.)

```
python3 benches/difftest_ryu.py   # cross-check the printer vs C++ to_chars (Ryu) and Python repr
```

## Performance

![Time per conversion (ns/call, lower is better) for the verified
printer against C++ std::to_chars, JDK Schubfach, and CPython repr,
on three input distributions](benches/perf.svg)

3–10× faster than CPython's `repr` (depending on the corpus), within
2× of C++'s `std::to_chars` and the JDK's Schubfach on *nice* and
*uniform* inputs, and ahead of the JDK on the *adversarial* corpus.
The three corpora probe different regimes: *nice* mirrors a typical
JSON payload, *uniform* draws random finite doubles, and *adversarial*
is a stress set containing the finite values from Ryū's test suite.
Each bar is the best of several runs' medians (`plot.py --runs 4`),
which filters the machine's clock-state noise.

The reader (`Decimal → Float`) runs an Eisel–Lemire kernel over the same
128-bit table, with the exact big-integer reader as its fallback;
`lake exe benchDecimalToFloat` times it, and `benches/bench_ref
from_chars|strtod` gives the C++ parsers for scale (those also lex the
text, which the Lean reader has already done).

```
benches/run.sh                     # time the printer against C++/Java/Python baselines
python3 benches/plot.py --replot   # regenerate the comparison plot
lake exe benchDecimalToFloat nice  # time the reader (nice | uniform | adversarial)
```

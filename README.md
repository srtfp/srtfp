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

The numerical audit surface is [`Srtfp/Spec.lean`](Srtfp/Spec.lean) and
the theorem statements in [`Srtfp/Correctness.lean`](Srtfp/Correctness.lean).
The specification is self-contained: it defines the `Decimal` type and
its canonical form, reads binary64 words through Lean's own model of
the format (`Float.Model.UnpackedFloat.unpack`), and otherwise uses
only core Lean (`Rat`, `Rat.abs`, `Nat.toDigits`). The two
`correct_iff_*` theorems are biconditionals: a function satisfies the
specification *if and only if* it is the library's function. So the
specification has exactly one model, and the implementation never
needs to be inspected. The reader theorem also establishes existence,
so the specification's “under every correct reader” is not vacuous.
`ofDecimal_spec` and `toDecimal_spec` certify the runtime `Float` entry
points against this same specification through `.toBits`.

Here “shortest” counts **significand digits**, not characters in a
rendered string. The specification preserves both signs of zero,
accepts arbitrary decimal significands and exponents, and rounds
overflow to signed infinity at the stated threshold.

The build checks this boundary in [`Test/Audit.lean`](Test/Audit.lean),
using upstream `Lean.collectAxioms`. It checks declarations by their
defining module, including private helpers and declarations outside the
`Srtfp` namespace, and permits only `propext`, `Quot.sound`, and
`Classical.choice`. There is no exception for `sorryAx` or native proofs.
It also rejects local partial or unsafe definitions and unchecked
`@[extern]` and `@[implemented_by]` replacements;
the fast paths use equality proofs via `@[csimp]`.
This single audit covers the reference and performance tiers
and runs in both `lake build` and `lake test`.
Its regression fixtures live in [`Test/AuditTests.lean`](Test/AuditTests.lean).
As usual, the Lean kernel, compiler, and
upstream runtime implementations are trusted.

For a numerical review, also check the pinned [`lean-toolchain`](lean-toolchain)
and the package options and audit target in [`lakefile.lean`](lakefile.lean).
Run `lake build Test.Audit` on the checkout being reviewed. The numerical
theorems certify `Reader.ofDecimalBits`, `Printer.toDecimalBits`,
`Reader.ofDecimal`, and `Printer.toDecimal`; string rendering, text parsing,
and the other `Decimal` operations have the additional review requirements below.

For decimal text, additionally read [`Srtfp/DecimalSyntax.lean`](Srtfp/DecimalSyntax.lean),
[`Srtfp/Text/Spec.lean`](Srtfp/Text/Spec.lean), and the theorem statements in
[`Srtfp/Text/Correctness.lean`](Srtfp/Text/Correctness.lean).
`parse_spec` characterizes every accepted string and its canonical value;
`correct_iff_parse` says these requirements determine the parser uniquely,
including rejection. The specification describes signs, digit runs, the
decimal point, the exponent, and removal of trailing significand zeros.
It uses upstream digit conversion and imports no parser or canonicalisation
implementation. Those implementations do not need manual review.

`format_spec` guarantees that formatting a canonical decimal produces a
permitted spelling of the same value, for compatible options. To review
that condition and the exact presentation choices (notation windows,
padding, exponent case), also read `FormatOptions`, `CompatibleWith`, and
the formatting definitions in [`Srtfp/Text.lean`](Srtfp/Text.lean).
The certified grammar is defined by the dialect flags; it does not establish
conformance to an external JSON, YAML, or MLIR standard.
Other `Decimal` constructors, literal instances, and negation still require
reviewing [`Srtfp/Decimal.lean`](Srtfp/Decimal.lean) when used.

The performance tier's `Schubfach.floatToString` has a separate reference
format: zero as `"0"` or `"-0"`, nonzero finite values as signed
`significand ++ "e" ++ exponent`, and `"NaN"` / signed `"Infinity"`.
Its extra audit surface is the four reference string definitions at the start
of [`Srtfp/Perf/StringFast.lean`](Srtfp/Perf/StringFast.lean), their
`signBit`, `biasedExpBits`, `mantissaBits`, and `isNaNBits` helpers in
[`Srtfp/Perf/Bits.lean`](Srtfp/Perf/Bits.lean), and the `floatToString_eq`
statement in [`Srtfp/Perf/Schubfach/Entry.lean`](Srtfp/Perf/Schubfach/Entry.lean).
This string function is not covered by `Text.format_spec`.

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

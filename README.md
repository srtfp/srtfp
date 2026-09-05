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

1. rejects NaN and ±∞ with an error, and otherwise returns a decimal
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

The library is three tiers, each a separate import:

- **Reference (`import Srtfp`, the default)**: the specification made
  effective, in exact rational arithmetic over Lean's own model of the
  format. The printer walks the decimal grids from coarse to fine and
  tests the two grid neighbours of the value against its rounding
  interval; the reader rounds the value to the binary64 grid around it
  and packs the result with core's `Float.Model.pack`. Plus the proofs
  and the theorems above stated on raw IEEE-754 bit patterns (`UInt64`).
  Uses nothing beyond Lean's three standard axioms (`propext`,
  `Quot.sound`, `Classical.choice`); a build-time audit enforces this.
- **Performance (`import Srtfp.Perf`, opt-in)**: the Schubfach
  algorithm and its fixed-width `UInt64` kernels and precomputed
  tables for printing, and an Eisel–Lemire kernel with an exact
  big-integer fallback for reading, each proven equal to the reference
  and registered as a `@[csimp]` rewrite, so compiled code runs the fast
  path while the proofs still speak about the reference. Same axiom
  budget as the reference tier. Deleting `Srtfp/Perf/` leaves the
  library working, only slower.
- **Float (`import Srtfp.Bridge`, opt-in)**: the same theorems attached
  to the runtime `Float` type, across the bit round-trip
  `Float.toBits_ofBits` (constructing a non-NaN `Float` from bits and
  reading it back gives the same bits), proven over core's `Float.Model`
  in `Srtfp/Bridge/Basic.lean`. No axiom; what is trusted is that the
  compiled `Float.ofBits` and `Float.toBits` implement their definitions,
  the `@[extern]` contract every primitive type carries.

## Reading the code

To trust the result, read [`Srtfp/Spec.lean`](Srtfp/Spec.lean) and
[`Srtfp/Correctness.lean`](Srtfp/Correctness.lean) and nothing else.
The specification is self-contained: it defines the `Decimal` type and
its canonical form, reads binary64 words through Lean's own model of
the format (`Float.Model.UnpackedFloat.unpack`), and otherwise uses
only core Lean (`Rat`, `Rat.abs`, `Nat.toDigits`). Both theorems in
`Correctness.lean` are biconditionals: a function satisfies the
specification *if and only if* it is the library's function. So the
specification has exactly one model, and the implementation never
needs to be inspected.

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
`String` for JSON, YAML, MLIR, …), the performance tier (`Srtfp/Perf/`,
where the bit-field arithmetic of the fast kernels also lives), or the
`Float` bridge (`Srtfp/Bridge/`).

Zero dependencies beyond the Lean toolchain: no mathlib, and the test
suite runs on a small in-repo harness (`SrtfpTest/Spec.lean`). CI builds
and tests the library on Lean v4.33.0 (the pinned toolchain and the
floor: core's `Float.Model` arrived in v4.33).
The proofs' small compatibility layer (Mathlib's lemma names over core's
`Rat`, the `|·|` bars) lives in the `Srtfp.Compat` namespace with scoped
notation, so srtfp and Mathlib can be imported in the same file without
collisions.

## Build

```
lake build           # the library
lake test            # build, axiom-check, and run the test suite
make                 # helper binaries (benchmarks, difftest)
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

2–7× faster than CPython's `repr` (depending on the corpus) and within
3× of C++'s `std::to_chars` and the JDK's Schubfach on non-adversarial
inputs. The three corpora probe different regimes: *nice* mirrors a
typical JSON payload, *uniform* draws random finite doubles, and
*adversarial* is a stress set containing the finite values from Ryū's
test suite.

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

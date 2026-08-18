# srtfp — a verified shortest round-trip float printer

A Lean 4 library providing, for IEEE-754 binary64:

- a **shortest round-trip printer** (the [Schubfach
  algorithm](https://drive.google.com/file/d/1IEeATSVnEE6TkrHlCYNY2GjaraBjOT4f/view)),
- a **correctly rounded parser** (Clinger-style), and
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

These properties uniquely determine the printer's behavior — and the
parser's: a function is a correct shortest-decimal printer iff it is
`Schubfach.toDecimalBits`, and a correct round-to-nearest reader iff it
is `Clinger.ofDecimalBits`. For the exact statements, see
[`Srtfp/Correctness.lean`](Srtfp/Correctness.lean).

The certification is two-tier:

- **Bits tier (`import Srtfp`, the default)** — the theorems stated on
  raw IEEE-754 bit patterns (`UInt64`). Uses nothing beyond Lean's
  three standard axioms (`propext`, `Quot.sound`, `Classical.choice`);
  a build-time audit enforces this.
- **Float tier (`import Srtfp.Bridge`, opt-in)** — the same theorems
  attached to the runtime `Float` type. This tier depends on exactly
  one extra axiom, `Float.toBits_ofBits`: constructing a non-NaN
  `Float` from bits and reading it back gives the same bits — the
  implementation contract of Lean's opaque `Float`, not provable
  within Lean.

No `sorry` anywhere.

Factored out of QuadParsers, a biparser library with proven
round-trip properties.

Zero dependencies beyond the Lean toolchain — no mathlib, and the test
suite runs on a small in-repo harness (`SrtfpTest/Spec.lean`). CI builds
and tests the library on Lean v4.27.0, v4.32.2 (the pinned toolchain),
and v4.33.0.
The vendored compatibility surface (`abs_nonneg`, `Nat.log`, the `ℚ`/`|·|`/`∃!`
notations, …) lives in the `Srtfp.Compat` namespace with scoped notation, so
srtfp and Mathlib can be imported in the same file without collisions.

## Build

```
lake build           # the library
lake test            # build, axiom-check, and run the test suite
make                 # helper binaries (benchmarks, difftest)
```

## Extra tests

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

```
benches/run.sh                     # time the printer against C++/Java/Python baselines
python3 benches/plot.py --replot   # regenerate the comparison plot
```

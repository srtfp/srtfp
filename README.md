# srtfp — a verified shortest round-trip float printer

A Lean 4 library providing, for IEEE-754 binary64:

- a **shortest round-trip printer** (the [Schubfach
  algorithm](https://drive.google.com/file/d/1IEeATSVnEE6TkrHlCYNY2GjaraBjOT4f/view)),
- a **correctly rounded parser** (Clinger-style), and
- a machine-checked, **fully axiom-free certification** connecting them
  on raw binary64 bit patterns (`UInt64` words).

The certification is two-tier:

- **Bits tier (`import Srtfp`, the default)** — the flagship theorems in
  [`Srtfp/Correctness.lean`](Srtfp/Correctness.lean): a function is a
  correct shortest-decimal printer iff it is `Schubfach.toDecimalBits`,
  and a correct round-to-nearest reader iff it is
  `Clinger.ofDecimalBits`, both stated on words. Every declaration in
  this tier depends on **nothing beyond `propext`, `Quot.sound`,
  `Classical.choice`** — no assumption about the runtime `Float` type is
  ever made. Enforced at build time by `SrtfpBitsAxiomCheck.lean` (an
  environment-level transitive axiom audit) and
  `tools/check_axiom_free_imports.py` (a source-level import walk).
- **Float tier (`import Srtfp.Bridge`, opt-in)** — the same theorems
  attached to the runtime `Float` type
  ([`Srtfp/Bridge/Correctness.lean`](Srtfp/Bridge/Correctness.lean)).
  This tier admits exactly one extra axiom: the restricted runtime
  round-trip `Float.toBits_ofBits`
  ([`Srtfp/Float/RuntimeAxiom.lean`](Srtfp/Float/RuntimeAxiom.lean)) —
  `(Float.ofBits x).toBits = x` for non-NaN patterns `x`, the IEEE-754
  implementation contract of Lean's opaque `Float`, not derivable in
  pure Lean. `SrtfpTest/RuntimeAxiomProbe.lean` demonstrates empirically
  that the runtime canonicalises NaN payloads, which is exactly why the
  axiom carries its non-NaN restriction. `SrtfpAxiomCheck.lean` audits
  this closure against the four-axiom budget.

No `sorry` anywhere.

Factored out of QuadParsers, a biparser library with proven
round-trip properties.

Zero dependencies beyond the Lean toolchain — no mathlib, and the test
suite runs on a small in-repo harness (`SrtfpTest/Spec.lean`). CI builds
and tests the library on Lean v4.27.0, v4.32.2 (the pinned toolchain),
and v4.33.0.
One caveat: the library vendors a few root-level compatibility lemmas
(`abs_nonneg`, `Nat.log`, …) that Mathlib also declares, so a file
cannot import both srtfp and Mathlib. Packages can depend on both as
long as no single file imports both.

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

## Benchmarks

```
benches/run.sh                     # time the printer against C++/Java/Python baselines
python3 benches/plot.py --replot   # regenerate the comparison plot
```

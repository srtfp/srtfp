# srtfp — a verified shortest round-trip float printer

A Lean 4 library providing, for IEEE-754 binary64:

- a **shortest round-trip printer** (the [Schubfach
  algorithm](https://drive.google.com/file/d/1IEeATSVnEE6TkrHlCYNY2GjaraBjOT4f/view)),
- a **correctly rounded parser** (Clinger-style), and
- a machine-checked **round-trip theorem** connecting them at the
  `Float.toBits` level.

The specification and top-level correctness theorems are in
[`Srtfp/Correctness.lean`](Srtfp/Correctness.lean).

Axiom budget: `propext`, `Quot.sound`, `Classical.choice`, plus one
quarantined runtime axiom about the `Float.toBits`/`Float.ofBits`
intrinsics ([`Srtfp/Float/RuntimeAxiom.lean`](Srtfp/Float/RuntimeAxiom.lean));
the round-trip theorem is stated at the `.toBits` level so the
bit-level results are axiom-free. Enforced by `SrtfpAxiomCheck.lean` at
build time. No `sorry`.

Factored out of QuadParsers, a biparser library with proven
round-trip properties.

## Build

```
lake exe cache get   # download the prebuilt mathlib (skip only for a multi-hour from-source build)
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

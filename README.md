# srtfp: a verified shortest round-trip float printer

A Lean 4 library for IEEE-754 binary64 printing, decimal-to-float conversion,
and decimal text parsing and formatting. It uses only the pinned Lean toolchain;
there are no external dependencies.

For every finite float, the printer returns a canonical decimal that:

- converts back to the same bits through Lean's signed `Float.Model.ofScientific`;
- has the fewest significand digits;
- is closest to the float among equally short candidates, with ties to even.

These rules uniquely determine the result, including both signs of zero.
NaN and infinities return `none`. “Shortest” counts significand digits, not
rendered characters.

## Use

```lean
import Srtfp       -- reference implementations and correctness theorems
import Srtfp.Perf  -- optional, proved compiler replacements for fast execution
```

The fast tier provides a Schubfach printer and an Eisel–Lemire converter with
an exact integer fallback. Equality proofs connect them to the reference
operations, including upstream `Float.Model.ofScientific`, via `@[csimp]`.

The main APIs are `Printer.toDecimal`, `Reader.ofDecimal`, `Text.parse`, and
`Text.format`, in the `Srtfp` namespace. `Text.floatToString` provides a compact
float renderer; `Text.format` provides configurable decimal formatting.

## Audit

Start with [the numerical specification](Srtfp/Spec.lean) and
[the correctness and uniqueness statements](Srtfp/Correctness.lean).
The [audit guide](AUDIT.md) lists the complete review boundary for each API
and the checks that enforce it. Lean checks the implementation and proof bodies;
manual review focuses on the specification and theorem statements.

## Build and test

```sh
lake build  # all library tiers and the mandatory audit
lake test   # runtime tests, audit regressions, and specification import checks
```

`make` and `make test` run the same commands. See
[benches/README.md](benches/README.md) for benchmarks, recorded results, and
differential testing.

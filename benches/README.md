# Float→String cross-implementation benchmarks

Compares this repo's verified Schubfach implementation against the
standard fast float-to-string libraries, on three input distributions.

## Run

```bash
./benches/run.sh        # text table (lean / to_chars / snprintf / python)
python3 benches/plot.py # build + checksum-gate + bar chart -> benches/perf.png
```

`run.sh` builds everything (lake + g++), pins to core 0, prints a summary
table. `plot.py` additionally builds the JDK Schubfach reference, gates on
bit-identical checksums, and writes `perf.png` + `results.csv`
(both regenerable, so gitignored). Useful flags: `--corpus uniform`
(restrict), `--snprintf` (add libc), `--no-build`.

## Implementations measured

| Name        | What                                              |
|-------------|---------------------------------------------------|
| `lean`      | `Schubfach.toDecimal` + `Decimal.toStr` (this repo) |
| `JDK`       | `Double.toString` — the reference Schubfach (Giulietti, JDK 19+) |
| `chars`     | `std::to_chars` — libstdc++ shortest-decimal (Ryu) |
| `snprintf`  | libc `printf("%.17g", f)`                          |
| `python`    | CPython 3 `repr(f)`                                |

The JDK row is the canonical *reference Schubfach*: since JDK 19,
`Double.toString` is Raffaello Giulietti's Schubfach — the same algorithm
this repo implements in Lean — so it is the most direct apples-to-apples
comparison. (`plot.py` only; `run.sh` omits it.)

## Corpora

| Corpus        | Size  | Description                                                   |
|---------------|------:|---------------------------------------------------------------|
| `adversarial` |   225 | Hand-picked + Ryu edge cases + ulp boundaries + 0.1+0.2 family |
| `nice`        |  1024 | Stratified JSON-style mix: ints, currency, lat/long, timestamps, constants |
| `uniform`     |  1024 | Random finite binary64 (uniform sign / biased exp / mantissa) |

All inputs are generated deterministically from a fixed seed by
`Corpora.lean` when the Lean benches load. For the other harnesses,
`lake exe genCorpora` writes the same values to `corpora/<name>.u64` as
IEEE-754 u64 bit patterns (one per line); each impl reconstructs floats
via `std::bit_cast<double>` / `struct.unpack` / `longBitsToDouble`, so
every harness sees byte-for-byte identical arrays. The checksum step in
`run.sh` aborts if this invariant ever drifts. To draw a fresh random
corpus, change `Corpora.seed`.

## Methodology

- 1000 iterations × ~1024 inputs × 5 runs per (impl, corpus) (~5M emit calls).
- XOR-sink the result length so the optimiser can't elide the call.
- `taskset -c 0` to suppress migration noise.
- Report median of the 5 runs.
- 50-iter warmup before timing (~50k emit calls).

Numbers vary ±5–10% with thermal state and load (much tighter than the
prior 23-input runs); re-run for stability. Relative ratios between
implementations stay constant.

## Files

- `Corpora.lean` — the corpus generator (fixed seed, SplitMix64).
- `GenCorpora.lean` — `lake exe genCorpora`, writes `corpora/*.u64`.
- `bench_ref.cpp` — `std::to_chars` + `snprintf` in one binary.
- `bench_py.py`   — Python `repr` reference.
- `bench_java/Bench.java` — JDK `Double.toString` (reference Schubfach).
- `run.sh`        — build + sanity-check + run + summarise (text table).
- `plot.py`       — build + checksum-gate + timing + bar chart (`perf.png`).

The Lean bench itself is `./BenchFloatToString.lean`.

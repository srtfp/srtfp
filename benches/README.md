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
| `adversarial` |  ~130 | Hand-picked + Ryu edge cases + ulp boundaries + 0.1+0.2 family |
| `nice`        |  1024 | Stratified JSON-style mix: ints, currency, lat/long, timestamps, constants |
| `uniform`     |  1024 | Random finite binary64 (uniform sign / biased exp / mantissa) |

All inputs are generated deterministically (`SEED = 0xDEADBEEF`) by
`gen_corpora.py` and serialised as IEEE-754 u64 bit patterns; each impl
reconstructs floats via `Float.ofBits` / `std::bit_cast<double>` /
`struct.unpack`, so the three bench harnesses see byte-for-byte identical
arrays. The checksum step in `run.sh` aborts if this invariant ever drifts.

## Regenerating the corpora

```bash
python3 benches/gen_corpora.py
```

Re-emits `Corpora.lean`, `corpora.h`, `corpora.cpp`. The emitted files
are committed; users don't need to run the generator to build or bench.

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

- `gen_corpora.py` — corpus generator + Python bench data source.
- `Corpora.lean` — generated Lean corpus (committed).
- `corpora.h` / `corpora.cpp` — generated C++ corpus (committed).
- `bench_ref.cpp` — `std::to_chars` + `snprintf` in one binary.
- `bench_py.py`   — Python `repr` reference.
- `bench_java/Bench.java` — JDK `Double.toString` (reference Schubfach).
- `bench_java/Corpora.java` — generated Java corpus (committed).
- `run.sh`        — build + sanity-check + run + summarise (text table).
- `plot.py`       — build + checksum-gate + timing + bar chart (`perf.png`).

The Lean bench itself is `./BenchFloatToString.lean`.

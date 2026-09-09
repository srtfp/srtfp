import Lake
open Lake DSL

package srtfp where
  version := v!"0.1.0"
  testDriver := "test"
  -- A bare unknown identifier in a signature must be an error, never a
  -- silently auto-bound implicit: with Mathlib gone, a stray `ℚ` would
  -- otherwise generalize a theorem statement without complaint.
  leanOptions := #[⟨`autoImplicit, false⟩]
  -- Per-process build memory guard (`lean -M`, in MB). This counts Lean's
  -- allocator accounting, which runs above resident RSS. Elaboration memory
  -- accumulates across a module's declarations on ≥4.32 toolchains, so the
  -- heavy proofs are split one-per-module (the Result 20 kernel sweeps,
  -- `Perf/Schubfach/NadezhinSweep*`, at ~2.5 GB each and everything else
  -- below that). 8 GB covers the worst with allocator headroom yet aborts a
  -- runaway proof with `memory_exception` instead of OOM-ing the machine;
  -- the library parallel-builds comfortably in 16 GB.
  -- `weakLeanArgs` so the limit applies on every build but never enters the
  -- trace hash.
  weakLeanArgs := #["-M", "8192"]

@[default_target]
lean_lib Srtfp where
  roots := #[`Srtfp]

-- The performance tier: verified `@[csimp]` fast paths (`Srtfp/Perf.lean`
-- and below). Opt-in for clients; built by default so the equivalence
-- proofs and the axiom audit always cover it.
@[default_target]
lean_lib SrtfpPerf where
  roots := #[`Srtfp.Perf]

-- Validation lives under Test/. Runtime suites are imported by Test.Main.
lean_lib Test where
  globs := #[.submodules `Test]

-- The audit remains mandatory in the default build; the test runner also imports it.
@[default_target]
lean_lib Audit where
  roots := #[`Test.Audit]

-- The bench corpora (`benches/Corpora.lean`), generated at load time from a
-- fixed seed. `lake exe genCorpora` writes them out for the other harnesses.
lean_lib Corpora where
  srcDir := "benches"
  roots := #[`Corpora]

lean_exe genCorpora where
  srcDir := "benches"
  root := `GenCorpora

-- The test runner lives in `Test/Main.lean` alongside the corpus modules.
lean_exe test where
  root := `Test.Main

-- Schubfach Float→Decimal kernel microbench (no String emit).
lean_exe benchToDecimal where
  srcDir := "benches"
  root := `BenchToDecimal

-- Decimal→Float: the live reader (fast kernel + exact fallback) and its fallback.
lean_exe benchDecimalToFloat where
  srcDir := "benches"
  root := `BenchDecimalToFloat

-- Canonical end-to-end Float→String bench. Driven by `benches/run.sh`.
lean_exe benchFloatToString where
  srcDir := "benches"
  root := `BenchFloatToString

-- Functional sanity check: fast2 paths agree with reference.

-- Profiling tools (out-of-the-way; see benches/profiling/).
-- Stage-breakdown profiler (decode|kernel|canon|int→string|emit|full).
lean_exe benchProfile where
  srcDir := "benches/profiling"
  root := `BenchProfile

-- callgrind driver (live toStringFast over uniform).
lean_exe benchCG where
  srcDir := "benches/profiling"
  root := `BenchCG

lean_exe benchCGK where
  srcDir := "benches/profiling"
  root := `BenchCGK

lean_exe benchSpec where
  srcDir := "benches/profiling"
  root := `BenchSpec

-- Differential-testing dumper: prints our verified printer's output per
-- bit pattern, for comparison against the Ryu oracle (benches/difftest_ryu.*).
lean_exe diffDump where
  srcDir := "benches/profiling"
  root := `DiffDump


lean_exe benchReadCG where
  srcDir := "benches/profiling"
  root := `BenchReadCG

lean_lib EmitProto where
  srcDir := "benches/profiling"
  roots := #[`EmitProto]

lean_exe benchEmitCG where
  srcDir := "benches/profiling"
  root := `BenchEmitCG

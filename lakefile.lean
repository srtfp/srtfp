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
  -- allocator accounting, which runs above resident RSS. The heaviest module
  -- is KernelV13Flip3 (~7.5 GB peak cgroup memory for the single flip3 spec
  -- proof; shrinking it further means restructuring that proof); KernelV6
  -- and TableInvariant peak ~3.5-4 GB, everything else ≤ ~2 GB — the heavy
  -- modules were split (KernelV13{Resid,Flip3,WReg}, R20Band*Sweep*)
  -- precisely so peaks stay per-process and the sweeps parallelize. 10 GB
  -- leaves margin for Flip3 yet aborts a runaway proof with
  -- `memory_exception` instead of OOM-ing the machine. `weakLeanArgs` so the
  -- limit applies on every build but never enters the trace hash.
  weakLeanArgs := #["-M", "10240"]

@[default_target]
lean_lib Srtfp where
  roots := #[`Srtfp]

-- The Float tier: everything in `Srtfp` plus the runtime-axiom bridge
-- (`Srtfp/Bridge.lean` and below). Importing it admits Float.toBits_ofBits.
@[default_target]
lean_lib SrtfpBridge where
  roots := #[`Srtfp.Bridge]

lean_lib SrtfpAxiomCheck where
  roots := #[`SrtfpAxiomCheck]

-- Axiom linter for the axiom-free tier: `import Srtfp` alone must need
-- only propext / Quot.sound / Classical.choice.
lean_lib SrtfpBitsAxiomCheck where
  roots := #[`SrtfpBitsAxiomCheck]

-- Test corpus modules (e.g. `SrtfpTest.Ryu`). The `test` exe imports from this
-- library; new corpora go in `SrtfpTest/*.lean` and are picked up automatically.
lean_lib SrtfpTest where
  globs := #[.submodules `SrtfpTest]

-- Auto-generated bench corpus (`benches/Corpora.lean`). Regenerate via
-- `python3 benches/gen_corpora.py`; the generated file is committed.
lean_lib Corpora where
  srcDir := "benches"
  roots := #[`Corpora]

-- The test runner lives in `SrtfpTest/Main.lean` alongside the corpus modules.
lean_exe test where
  root := `SrtfpTest.Main

-- Schubfach Float→Decimal kernel microbench (no String emit).
lean_exe benchToDecimal where
  srcDir := "benches"
  root := `BenchToDecimal

-- Canonical end-to-end Float→String bench. Driven by `benches/run.sh`.
lean_exe benchFloatToString where
  srcDir := "benches"
  root := `BenchFloatToString

-- Functional sanity check: fast2 paths agree with reference.
lean_exe benchVerify where
  srcDir := "benches"
  root := `BenchVerify

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

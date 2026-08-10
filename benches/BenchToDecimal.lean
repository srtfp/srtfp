/- End-to-end microbenchmark for `Schubfach.toDecimal`.

   Build & run:
     lake exe benchToDecimal
-/

import Srtfp.Schubfach
import Srtfp.Schubfach.Perf.Orchestration
import Srtfp.Schubfach.Perf.Uint64Bridge
import Srtfp.Schubfach.Perf.Kernel192Correctness
import Srtfp.Schubfach.Perf.KernelV6 -- live toDecimal @[csimp]
open Srtfp.Schubfach

/-- 23 representative `Float` inputs spanning normals, subnormals, edges,
    and irregular cases. Same set used in the dispatch plan. -/
def testInputs : Array Float :=
  #[
    1.0, 2.0, 0.1, 0.2, 0.3, 0.1 + 0.2,
    1e10, 1e-10, 1.7976931348623157e308, 5e-324,
    3.14159265358979, 2.718281828459045,
    1.0/3.0, 1.0/7.0, 1.0/11.0,
    42.0, 100.0, 1000.0, 999999.999999,
    1.5, 2.5, 3.5, 4.5
  ]

def doOne (iters : Nat) : IO Nat := do
  let n := testInputs.size
  let start ← IO.monoNanosNow
  -- IMPORTANT: reset accumulator each outer iteration so it stays
  -- small (GMP-style Nat addition cost grows with magnitude).  This
  -- mirrors `BenchPacked`'s pattern.  Previously the running total
  -- grew over 1.15M iterations and added ~100 ns/call of GMP overhead.
  let mut grand : Nat := 0
  for _ in [:iters] do
    let mut t : Nat := 0
    for f in testInputs do
      match toDecimal f with
      | .ok d => t := t + d.significand
      | .error _ => pure ()
    if t = 99 then grand := grand + 1
  let stop ← IO.monoNanosNow
  IO.println s!"  (suppress: {grand})"
  pure ((stop - start) / (iters * n))

def runMany (label : String) (iters : Nat) : IO Unit := do
  -- Warmup
  let _ ← doOne 100
  let mut times : Array Nat := #[]
  for _ in [:5] do
    times := times.push (← doOne iters)
  let sorted := (times.toList.toArray).qsort (· < ·)
  IO.println s!"{label}: times={times} median={sorted[2]!}ns/call"

def main : IO Unit := do
  runMany "toDecimal" 50000

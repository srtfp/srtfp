import Srtfp.Schubfach
import Srtfp.Decimal
import Srtfp.Schubfach.Perf.Orchestration
import Srtfp.Schubfach.Perf.Uint64Bridge
import Srtfp.Schubfach.Perf.Kernel192Correctness
import Srtfp.Schubfach.Perf.DigitsFast
import Srtfp.Schubfach.Perf.KernelV13
import Corpora

open Srtfp

/-- Reference shape used by the bench; rewritten via `@[csimp]` to
    `Srtfp.Schubfach.toStringFast` at compile time. -/
def floatToStr (f : Float) : String := Srtfp.Schubfach.floatToStrRef f

/-- Sum of IEEE bit patterns (mod 2^64). Lets `run.sh` verify that Lean,
    C++, and Python iterate over byte-identical arrays. -/
def corpusChecksum (xs : Array Float) : UInt64 :=
  xs.foldl (init := 0) (fun acc f => acc + f.toBits)

def main (args : List String) : IO Unit := do
  let label := args.headD "adversarial"
  let testInputs :=
    match label with
    | "nice"    => Corpora.nice
    | "uniform" => Corpora.uniform
    | _         => Corpora.adversarial
  let chk := corpusChecksum testInputs
  if args.contains "--checksum" then
    IO.println s!"{label}: n={testInputs.size} sum_bits={chk}"
    return
  IO.println s!"# corpus: {label}, inputs: {testInputs.size}, sum_bits={chk}"
  let N : Nat := 1000
  let M : Nat := 5
  for _ in [0:50] do
    for f in testInputs do
      let _ := floatToStr f
      pure ()
  let mut times : Array Nat := #[]
  for _ in [0:M] do
    let t0 ← IO.monoNanosNow
    let mut sink : Nat := 0
    for _ in [0:N] do
      for f in testInputs do
        sink := sink ^^^ (floatToStr f).length
    let t1 ← IO.monoNanosNow
    let nsPerCall := (t1 - t0) / (N * testInputs.size)
    times := times.push nsPerCall
    if sink == 12345 then IO.println ""
  let sorted := times.qsort (· < ·)
  let median := sorted[M/2]!
  IO.println s!"Lean Schubfach (Float→String):  median = {median} ns/call  (runs: {times.toList})"

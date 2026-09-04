/- Float → Decimal microbenchmark (no String emit): times the live
   `Printer.toDecimal` (`@[csimp]`-rewritten to the Schubfach kernel) over
   the shared corpora, with the same methodology as `BenchFloatToString`
   (50 warm-up passes, 1000 passes × 5 runs, median). The sink folds the
   significand into a `UInt64` so the accumulator never grows into a
   bignum.

     lake exe benchToDecimal <adversarial|nice|uniform> [--checksum] -/

import Srtfp.Perf
import Corpora
open Srtfp

def corpusOf (label : String) : Array Float :=
  match label with
  | "nice" => Corpora.nice
  | "uniform" => Corpora.uniform
  | _ => Corpora.adversarial

/-- The public entry point; compiled callers run the live kernel. -/
def toDec (f : Float) : Except String Decimal := Printer.toDecimal f

def main (args : List String) : IO Unit := do
  let label := args.headD "adversarial"
  let xs := corpusOf label
  let chk := xs.foldl (init := (0 : UInt64)) (fun acc f => acc + f.toBits)
  if args.contains "--checksum" then
    IO.println s!"{label}: n={xs.size} sum_bits={chk}"
    return
  IO.println s!"# corpus: {label}, inputs: {xs.size}, sum_bits={chk}"
  let N : Nat := 1000
  let M : Nat := 5
  for _ in [0:50] do
    for f in xs do
      let _ := toDec f
      pure ()
  let mut times : Array Nat := #[]
  for _ in [0:M] do
    let t0 ← IO.monoNanosNow
    let mut sink : UInt64 := 0
    for _ in [0:N] do
      for f in xs do
        sink := sink ^^^ (match toDec f with
          | .ok d => UInt64.ofNat d.significand
          | .error _ => 0)
    let t1 ← IO.monoNanosNow
    -- tenths of a ns, so sub-100ns paths keep a digit of precision
    times := times.push ((t1 - t0) * 10 / (N * xs.size))
    if sink == 12345 then IO.println ""
  let sorted := times.qsort (· < ·)
  let med := sorted[M/2]!
  IO.println s!"Lean toDecimal ({label}): median = {med / 10}.{med % 10} ns/call  (runs: {times.toList.map fun t => s!"{t / 10}.{t % 10}"})"

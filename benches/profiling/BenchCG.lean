import Srtfp.Schubfach
import Srtfp.Schubfach.Perf.Orchestration
import Srtfp.Schubfach.Perf.Uint64Bridge
import Srtfp.Schubfach.Perf.Kernel192Correctness
import Srtfp.Schubfach.Perf.DigitsFast
import Srtfp.Schubfach.Perf.KernelV13
import Corpora
open Srtfp Srtfp.Schubfach
def main : IO Unit := do
  let c := Corpora.uniform
  let mut sink : Nat := 0
  for _ in [0:1000] do
    for f in c do sink := sink ^^^ (toStringFast9 f).length
  IO.println s!"{sink}"

import Srtfp.Perf.Schubfach
import Srtfp.Perf.Orchestration
import Srtfp.Perf.Uint64Bridge
import Srtfp.Perf.Kernel192Correctness
import Srtfp.Perf.DigitsFast
import Srtfp.Perf.KernelV13
import Corpora
open Srtfp Srtfp.Schubfach
def main : IO Unit := do
  let c := Corpora.uniform
  let mut sink : Nat := 0
  for _ in [0:1000] do
    for f in c do sink := sink ^^^ (toStringFast9 f).length
  IO.println s!"{sink}"

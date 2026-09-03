import Srtfp.Perf.Schubfach
import Srtfp.Perf.Orchestration
import Srtfp.Perf.KernelV6
import Srtfp.Perf.Kernel192Correctness
import Srtfp.Perf.StringFast
import Corpora
open Srtfp Srtfp.Schubfach Srtfp.Float
def main : IO Unit := do
  let c := Corpora.uniform
  let mut sink : Nat := 0
  for _ in [0:300] do
    for f in c do sink := sink ^^^ (shortestUnsigned_v7 (decode f).m (decode f).q).1
  IO.println s!"{sink}"

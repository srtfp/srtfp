import Srtfp.Schubfach
import Srtfp.Schubfach.Perf.Orchestration
import Srtfp.Schubfach.Perf.KernelV6
import Srtfp.Schubfach.Perf.Kernel192Correctness
import Srtfp.Schubfach.Perf.StringFast
import Corpora
open Srtfp Srtfp.Schubfach Srtfp.Float
def main : IO Unit := do
  let c := Corpora.uniform
  let mut sink : Nat := 0
  for _ in [0:300] do
    for f in c do sink := sink ^^^ (shortestUnsigned_v7 (decode f).m (decode f).q).1
  IO.println s!"{sink}"

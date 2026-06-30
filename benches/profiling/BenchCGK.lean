import Srtfp.Numeric.Schubfach
import Srtfp.Numeric.Schubfach.Perf.Orchestration
import Srtfp.Numeric.Schubfach.Perf.KernelV6
import Srtfp.Numeric.Schubfach.Perf.Kernel192Correctness
import Srtfp.Numeric.Schubfach.Perf.StringFast
import Corpora
open PP.Numeric PP.Numeric.Schubfach PP.Numeric.Float
def main : IO Unit := do
  let c := Corpora.uniform
  let mut sink : Nat := 0
  for _ in [0:300] do
    for f in c do sink := sink ^^^ (shortestUnsigned_v7 (decode f).m (decode f).q).1
  IO.println s!"{sink}"

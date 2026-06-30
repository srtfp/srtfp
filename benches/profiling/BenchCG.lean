import Srtfp.Numeric.Schubfach
import Srtfp.Numeric.Schubfach.Perf.Orchestration
import Srtfp.Numeric.Schubfach.Perf.Uint64Bridge
import Srtfp.Numeric.Schubfach.Perf.Kernel192Correctness
import Srtfp.Numeric.Schubfach.Perf.DigitsFast
import Srtfp.Numeric.Schubfach.Perf.KernelV9
import Srtfp.Numeric.Schubfach.Perf.KernelV10
import Srtfp.Numeric.Schubfach.Perf.KernelV11
import Srtfp.Numeric.Schubfach.Perf.KernelV12
import Srtfp.Numeric.Schubfach.Perf.KernelV13
import Corpora
open PP.Numeric PP.Numeric.Schubfach
def main : IO Unit := do
  let c := Corpora.uniform
  let mut sink : Nat := 0
  for _ in [0:1000] do
    for f in c do sink := sink ^^^ (toStringFast9 f).length
  IO.println s!"{sink}"

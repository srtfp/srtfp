/- Profiler driver (callgrind / perf): the live `toStringFast9` over the
   uniform corpus, `N` passes (default 1000; pass a number to run longer,
   e.g. 20000 for a perf record with enough samples). No timing, no
   warm-up: just the work. -/
import Srtfp.Perf.Schubfach
import Srtfp.Perf.Orchestration
import Srtfp.Perf.Uint64Bridge
import Srtfp.Perf.Kernel192Correctness
import Srtfp.Perf.DigitsFast
import Srtfp.Perf.KernelV13
import Srtfp.Perf.KernelV14
import Corpora
open Srtfp Srtfp.Schubfach
/-- `benchCG [N] [v14]`: a second argument `v14` runs the unverified v14
    prototype (`toStringFast10`) instead of the live path. -/
def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 1000
  let c := Corpora.uniform
  let mut sink : Nat := 0
  if args.contains "v14" then
    for _ in [0:n] do
      for f in c do sink := sink ^^^ (toStringFast10 f).length
  else
    for _ in [0:n] do
      for f in c do sink := sink ^^^ (toStringFast9 f).length
  IO.println s!"{sink}"

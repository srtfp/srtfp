/- Profiler driver (callgrind / perf): the live `floatToString` over the
   uniform corpus, `N` passes (default 1000; pass a number to run longer,
   e.g. 20000 for a perf record with enough samples). No timing, no
   warm-up: just the work. -/
import Srtfp.Perf
import Corpora
open Srtfp Srtfp.Schubfach
/-- `benchCG [N]`. -/
def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 1000
  let c := Corpora.uniform
  let mut sink : Nat := 0
  for _ in [0:n] do
    for f in c do sink := sink ^^^ (floatToString f).length
  IO.println s!"{sink}"

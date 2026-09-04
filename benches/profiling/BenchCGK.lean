/- Profiler driver (callgrind / perf) for the live Float → Decimal path:
   `Printer.toDecimal` (`@[csimp]`-rewritten to the live kernel) over the
   uniform corpus, `N` passes (default 1000). The sink folds the
   significand into a `UInt64` so nothing grows into a bignum. -/
import Srtfp.Perf
import Corpora
open Srtfp
def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 1000
  let c := Corpora.uniform
  let mut sink : UInt64 := 0
  for _ in [0:n] do
    for f in c do
      sink := sink ^^^ (match Printer.toDecimal f with
        | .ok d => UInt64.ofNat d.significand
        | .error _ => 0)
  IO.println s!"{sink}"

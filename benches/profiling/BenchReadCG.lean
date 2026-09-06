/- Profiler driver (callgrind / perf): the live reader over the decimals
   the printer produces for the uniform corpus, `N` passes (default 200).
   No timing, no warm-up: just the work. -/
import Srtfp.Perf
import Corpora
open Srtfp

def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 200
  let decs : Array Decimal := Corpora.uniform.filterMap fun f => Printer.toDecimal f
  let mut sink : UInt64 := 0
  -- `init := i` keeps the fold from being a closed term (which Lean would
  -- hoist out of the loop and evaluate once).
  for i in [0:n] do
    sink := sink ^^^ decs.foldl (init := UInt64.ofNat i) fun a d => a ^^^ Reader.ofDecimalBits d
  IO.println s!"{sink}"

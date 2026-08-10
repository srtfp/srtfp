/- Stage-breakdown profiler for the Schubfach Float→String pipeline.
   Isolates: decode | kernel (shortestUnsigned) | canonicalise (toDecimal)
   | int→string (toString sig) | emit/append | full.  Run: lake exe benchProfile -/
import Srtfp.Schubfach
import Srtfp.Schubfach.Perf.Orchestration
import Srtfp.Schubfach.Perf.Uint64Bridge
import Srtfp.Schubfach.Perf.Kernel192Correctness
import Srtfp.Schubfach.Perf.DigitsFast
import Srtfp.Schubfach.Perf.KernelV9
import Srtfp.Schubfach.Perf.KernelV10
import Srtfp.Schubfach.Perf.KernelV11
import Srtfp.Schubfach.Perf.KernelV12
import Srtfp.Schubfach.Perf.KernelV13
import Corpora
open Srtfp Srtfp.Schubfach Srtfp.Float

/-- Time `g` over `xs`, `N` outer reps, median of 5. -/
def timeIt (label : String) (N : Nat) (sz : Nat) (body : Unit → Nat) : IO Unit := do
  for _ in [0:50] do let _ := body (); pure ()
  let mut times : Array Nat := #[]
  for _ in [0:5] do
    let t0 ← IO.monoNanosNow
    let mut sink : Nat := 0
    for _ in [0:N] do sink := sink ^^^ body ()
    let t1 ← IO.monoNanosNow
    times := times.push ((t1 - t0) / (N * sz))
    if sink == 999999999 then IO.println ""
  let s := times.qsort (· < ·)
  IO.println s!"  {label}: median={s[2]!}ns  runs={times.toList}"

def main : IO Unit := do
  let corpus := Corpora.uniform
  let sz := corpus.size
  let N : Nat := 1000
  -- Precompute decoded (sign,sig,exp) so emit stages don't re-run the kernel.
  let decs : Array (Bool × Nat × Int) := corpus.filterMap (fun f =>
    match toDecimal f with | .ok d => some (d.sign, d.significand, d.exponent) | _ => none)
  let sigs : Array Nat := decs.map (fun t => t.2.1)
  IO.println s!"# uniform corpus: {sz} floats, {decs.size} decoded"
  -- 1. loop/decode baseline (fold in UInt64: a Nat accumulator would
  -- heap-allocate a GMP limb for every toBits value ≥ 2^63)
  timeIt "1 baseline (toBits)"       N sz (fun _ => (corpus.foldl (init := (0 : UInt64)) (fun a f => a ^^^ f.toBits)).toNat)
  timeIt "2 decode (Float→m,q)"      N sz (fun _ => corpus.foldl (init := 0) (fun a f => a ^^^ (decode f).m))
  -- v8 from the bit fields is what the live toStringFast4 path runs
  -- (bare shortestUnsigned csimp-rewrites to the older v3 chain)
  timeIt "3 kernel (shortestUnsigned_v8)" N sz (fun _ => corpus.foldl (init := 0) (fun a f =>
      let bits : UInt64 := f.toBits
      let expBits : UInt64 := (bits >>> 52) &&& 0x7FF
      let mantBits : UInt64 := bits &&& 0x000F_FFFF_FFFF_FFFF
      let mU := if expBits = 0 then mantBits else mantBits + 4503599627370496
      let qB := if expBits = 0 then 0 else expBits - 1
      a ^^^ (shortestUnsigned_v8 mU qB).1))
  timeIt "4 toDecimal (kernel+canon)" N sz (fun _ => corpus.foldl (init := 0) (fun a f => a ^^^ (match toDecimal f with | .ok d => d.significand | _ => 0)))
  -- emit stages over precomputed decimals
  timeIt "5 int→string (toString sig)" N decs.size (fun _ => sigs.foldl (init := 0) (fun a s => a ^^^ (toString s).length))
  timeIt "6 full emit (sign++sig++e++exp)" N decs.size (fun _ => decs.foldl (init := 0) (fun a t =>
      let signStr := if t.1 then "-" else ""
      a ^^^ (signStr ++ toString t.2.1 ++ "e" ++ toString t.2.2).length))
  timeIt "6b full emit (emitChecked)" N decs.size (fun _ => decs.foldl (init := 0) (fun a t =>
      a ^^^ (emitChecked t.1 t.2.1 t.2.2).length))
  timeIt "7 FULL toStringFast4"       N sz (fun _ => corpus.foldl (init := 0) (fun a f => a ^^^ (toStringFast4 f).length))

/- Decimal → Float bench: `Reader.ofDecimalBits` (compiled to the fast
   kernel with the exact fallback) over the decimals the printer produces
   for a corpus, against the exact fallback alone and the reference.

     lake exe benchDecimalToFloat [nice|uniform|adversarial] [--reference]

   `--reference` also times the `Rat` reference, which is slow. -/
import Srtfp.Perf
import Corpora

open Srtfp

def main (args : List String) : IO Unit := do
  let label := args.headD "nice"
  let corpus := match label with
    | "uniform" => Corpora.uniform
    | "adversarial" => Corpora.adversarial
    | _ => Corpora.nice
  let decs : Array Decimal := corpus.filterMap fun f =>
    match Printer.toDecimal f with | .ok d => some d | .error _ => none
  let fastHits := decs.foldl (init := 0) fun a d => if (Reader.readFast d).isSome then a + 1 else a
  IO.println s!"# {label} corpus: {decs.size} decimals, {fastHits} on the fast path"
  let N : Nat := 300
  let M : Nat := 5
  let timeIt (name : String) (body : Unit → UInt64) : IO Unit := do
    for _ in [0:20] do let _ := body (); pure ()
    let mut times : Array Nat := #[]
    for _ in [0:M] do
      let t0 ← IO.monoNanosNow
      let mut sink : UInt64 := 0
      for _ in [0:N] do
        sink := sink ^^^ body ()
      let t1 ← IO.monoNanosNow
      times := times.push ((t1 - t0) / (N * decs.size))
      if sink == 12345 then IO.println ""
    let sorted := times.qsort (· < ·)
    IO.println s!"{name}: median = {sorted[M / 2]!} ns/call (runs: {times.toList})"
  timeIt "live reader (readFast + readExact fallback)" fun _ =>
    decs.foldl (init := 0) fun a d => a ^^^ Reader.ofDecimalBits d
  timeIt "readExact alone" fun _ =>
    decs.foldl (init := 0) fun a d => a ^^^ (Float.Model.pack (Reader.readExact d)).toBits
  if args.contains "--reference" then
    let N := 3
    let t0 ← IO.monoNanosNow
    let mut sink : UInt64 := 0
    for _ in [0:N] do
      sink := sink ^^^ decs.foldl (init := 0) fun a d => a ^^^ (Float.Model.pack (Reader.read d)).toBits
    let t1 ← IO.monoNanosNow
    IO.println s!"reference (Rat): {(t1 - t0) / (N * decs.size)} ns/call"
    if sink == 12345 then IO.println ""

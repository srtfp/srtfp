import Srtfp.Perf
import Corpora

open Srtfp

/-- Reference shape used by the bench; rewritten via `@[csimp]` to
    `Srtfp.Schubfach.toStringFast` at compile time. -/
def floatToStr (f : Float) : String := Srtfp.Schubfach.floatToStrRef f

/-- Sum of IEEE bit patterns (mod 2^64). Lets `run.sh` verify that Lean,
    C++, and Python iterate over byte-identical arrays. -/
def corpusChecksum (xs : Array Float) : UInt64 :=
  xs.foldl (init := 0) (fun acc f => acc + f.toBits)

def main (args : List String) : IO Unit := do
  let label := args.headD "adversarial"
  let testInputs :=
    match label with
    | "nice"    => Corpora.nice
    | "uniform" => Corpora.uniform
    | _         => Corpora.adversarial
  let chk := corpusChecksum testInputs
  if args.contains "--checksum" then
    IO.println s!"{label}: n={testInputs.size} sum_bits={chk}"
    return
  IO.println s!"# corpus: {label}, inputs: {testInputs.size}, sum_bits={chk}"
  -- `--baseline`: same loop with a trivial body, to measure the harness
  -- (IO for-in, XOR sink) overhead that every Lean number below includes.
  let baseline := args.contains "--baseline"
  -- `--keep`: keep the last 64 results alive in a ring, so each call frees a
  -- string allocated 64 calls earlier instead of the one it just made. In
  -- the default loop every object dies immediately, which empties the
  -- allocator's pages each iteration (mimalloc's page-retire bookkeeping
  -- then costs ~20 ns per size class per call, see the profile); this mode
  -- shows the cost with a warm heap, as in a real workload.
  let keep := args.contains "--keep"
  let N : Nat := 1000
  let M : Nat := 5
  for _ in [0:50] do
    for f in testInputs do
      let _ := floatToStr f
      pure ()
  let mut times : Array Nat := #[]
  let mut ring : Array String := Array.replicate 64 ""
  for _ in [0:M] do
    let t0 ← IO.monoNanosNow
    let mut sink : Nat := 0
    if baseline then
      for _ in [0:N] do
        for f in testInputs do
          sink := sink ^^^ (f.toBits >>> 58).toNat
    else if keep then
      let mut i : Nat := 0
      for _ in [0:N] do
        for f in testInputs do
          let s := floatToStr f
          sink := sink ^^^ s.length
          ring := ring.set! (i % 64) s
          i := i + 1
    else
      for _ in [0:N] do
        for f in testInputs do
          sink := sink ^^^ (floatToStr f).length
    let t1 ← IO.monoNanosNow
    let nsPerCall := (t1 - t0) / (N * testInputs.size)
    times := times.push nsPerCall
    if sink == 12345 then IO.println ""
  let sorted := times.qsort (· < ·)
  let median := sorted[M/2]!
  IO.println s!"Lean Schubfach (Float→String):  median = {median} ns/call  (runs: {times.toList})"

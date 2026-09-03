/- "Ours WITHOUT the @[csimp] kernel layer" bench: the exact-rational
   grid-scan reference `Printer.toDecimalBits`, which never gets a csimp
   registration, so this measures the reference as written. Slow by
   design; use a small BENCH_N. Directly comparable in shape to
   `benchFloatToString`.

     lake exe benchSpec <adversarial|nice|uniform> [--checksum]   (BENCH_N env) -/
import Srtfp.Printer
import Corpora

open Srtfp

/-- Verbatim copy of `Schubfach.decimalToStrRef`. -/
def decimalToStrSpec (d : Decimal) : String :=
  if d.significand = 0 then (if d.sign then "-0" else "0")
  else
    let signStr := if d.sign then "-" else ""
    signStr ++ toString d.significand ++ "e" ++ toString d.exponent

/-- The shape of `Schubfach.floatToStrRef`, over the grid-scan reference. -/
def floatToStrSpec (f : Float) : String :=
  match Printer.toDecimalBits f.toBits with
  | .ok d => decimalToStrSpec d
  | .error e => e

def corpusOf (label : String) : Array Float :=
  match label with
  | "nice" => Corpora.nice
  | "uniform" => Corpora.uniform
  | _ => Corpora.adversarial

def main (args : List String) : IO Unit := do
  let label := args.headD "adversarial"
  let xs := corpusOf label
  if args.contains "--checksum" then
    let s := xs.foldl (fun a f => a + f.toBits) (0 : UInt64)
    IO.println s!"{label}: n={xs.size} sum_bits={s.toNat}"
    return
  let N := (← IO.getEnv "BENCH_N").bind String.toNat? |>.getD 200
  let M := 5
  let mut sink := 0
  for _ in [0:5] do
    for f in xs do sink := sink ^^^ (floatToStrSpec f).length
  let mut times : Array Nat := #[]
  for _ in [0:M] do
    sink := 0
    let t0 ← IO.monoNanosNow
    for _ in [0:N] do
      for f in xs do sink := sink ^^^ (floatToStrSpec f).length
    let t1 ← IO.monoNanosNow
    times := times.push ((t1 - t0) / (N * xs.size))
    if sink == 12345 then IO.println ""
  let sorted := times.qsort (· < ·)
  IO.println s!"spec/{label}: median = {sorted[M/2]!} ns/call (runs: {sorted.toList})"

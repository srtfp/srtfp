/- "Ours WITHOUT the @[csimp] kernel layer" bench.

   Imports only the spec module `Srtfp.Schubfach` (and `Corpora`), NOT the
   `Schubfach/Perf/*` kernel modules. The kernel `@[csimp]` redirects
   (`shiftedSig`→fast, `toDecimal`→v7, `floatToStrRef`→`toStringFast9`, …) all
   live under `Perf/`, so they are out of scope here and the pure-Nat spec
   `toDecimal` runs. This measures the float→string path with the dominant
   csimp layer disabled — directly comparable to `benchFloatToString`.

   Caveat: `Schubfach.lean` itself imports `Decimal.Perf.Fast`, so Decimal
   *canonicalisation* stays fast; only the (dominant) Schubfach arithmetic
   kernel is de-optimised. The body below is a verbatim copy of
   `Schubfach.floatToStrRef` / `decimalToStrRef`.

     lake exe benchSpec <adversarial|nice|uniform> [--checksum]   (BENCH_N env) -/
import Srtfp.Schubfach
import Corpora

open Srtfp Srtfp.Schubfach

/-- Verbatim copy of `Schubfach.decimalToStrRef`. -/
def decimalToStrSpec (d : Decimal) : String :=
  if d.significand = 0 then (if d.sign then "-0" else "0")
  else
    let signStr := if d.sign then "-" else ""
    signStr ++ toString d.significand ++ "e" ++ toString d.exponent

/-- Verbatim copy of `Schubfach.floatToStrRef` — but compiled here with no
    kernel csimp in scope, so `toDecimal` is the spec. -/
def floatToStrSpec (f : Float) : String :=
  match toDecimal f with
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

/- Callgrind driver for the emitters: `benchEmitCG live|set [N]`. -/
import Srtfp.Perf
import Corpora
import EmitProto
open Srtfp Srtfp.Schubfach

def main (args : List String) : IO Unit := do
  let mode := args.headD "live"
  let n := ((args.drop 1).head? >>= String.toNat?).getD 200
  let decs : Array (Float.Model.UnpackedFloat.Sign × Nat × Int) := Corpora.uniform.filterMap fun f =>
    (Printer.toDecimal f).map fun d => (d.sign, d.significand, d.exponent)
  let mut sink : Nat := 0
  for i in [0:n] do
    sink := sink ^^^ (decs.foldl (init := i) fun a t =>
      a ^^^ (match mode with
        | "set" => (emitSet t.1 (UInt64.ofNat t.2.1) t.2.2).length
        | _ => (emitChecked t.1 t.2.1 t.2.2).length))
  IO.println s!"{sink}"

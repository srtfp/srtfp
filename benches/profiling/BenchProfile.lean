/- Stage-breakdown profiler for the Schubfach Float→String pipeline.
   Isolates: decode | kernel (v13, v14 live) | toDecimal | int→string
   | emit variants | full (v14 live, v13 previous).
   Run: lake exe benchProfile [adversarial|nice|uniform]   (default uniform) -/
import Srtfp.Perf
import Srtfp.Perf.KernelV14
import Corpora
open Srtfp Srtfp.Schubfach Srtfp.Float

-- `main` inlines five copies of the (large) kernels; the LCNF compiler
-- needs more than the default heartbeat budget for that.
set_option maxHeartbeats 4000000

/-- Time `body`, `N` outer reps, median of 5 (tenths of ns). -/
def timeIt (label : String) (N : Nat) (sz : Nat) (body : Unit → Nat) : IO Unit := do
  for _ in [0:50] do let _ := body (); pure ()
  let mut times : Array Nat := #[]
  for _ in [0:5] do
    let t0 ← IO.monoNanosNow
    let mut sink : Nat := 0
    for _ in [0:N] do sink := sink ^^^ body ()
    let t1 ← IO.monoNanosNow
    times := times.push ((t1 - t0) * 10 / (N * sz))
    if sink == 999999999 then IO.println ""
  let s := times.qsort (· < ·)
  IO.println s!"  {label}: median={s[2]! / 10}.{s[2]! % 10}ns  runs={times.toList.map fun t => s!"{t / 10}.{t % 10}"}"

/-- One heap object per call (a two-field constructor the compiler cannot
    scalar-replace across the `noinline` boundary): measures the cost of a
    single allocate-then-free in a tight loop. -/
@[noinline] def mkPair (x : UInt64) : UInt64 × UInt64 := (x, x + 1)

/-- Two heap objects per call (`Except.ok` around a pair). -/
@[noinline] def mkExceptPair (x : UInt64) : Except String (UInt64 × UInt64) := .ok (x, x + 1)

/-- Decimal digits of `n`, appended to `b` (fuel-bounded; 20 digits suffice). -/
def pushDigits : Nat → ByteArray → UInt64 → ByteArray
  | 0, b, _ => b
  | fuel + 1, b, n =>
    if n < 10 then b.push (48 + n.toUInt8)
    else (pushDigits fuel b (n / 10)).push (48 + (n % 10).toUInt8)

/-- UNVERIFIED emit alternative for measurement: digits written into a
    `ByteArray` (one out-of-line `lean_byte_array_push` per byte), then one
    `String.fromUTF8!` (runtime validation + copy). -/
def emitBA (sign : Float.Model.UnpackedFloat.Sign) (sU : UInt64) (exp : Int) : String :=
  let b := ByteArray.emptyWithCapacity 32
  let b := match sign with | .negative => b.push 45 | .positive => b
  let b := pushDigits 20 b sU
  let b := b.push 101
  let b := if exp < 0 then pushDigits 20 (b.push 45) (UInt64.ofNat (-exp).toNat)
           else pushDigits 20 b (UInt64.ofNat exp.toNat)
  String.fromUTF8! b

/-- UNVERIFIED emit alternative: `String.push` per character on the
    `toString sig` string (exclusive after the first realloc). -/
def emitPush (sign : Float.Model.UnpackedFloat.Sign) (sig : Nat) (exp : Int) : String :=
  let core := toString sig
  let core := core.push 'e'
  let core := if exp < 0 then (core.push '-') ++ toString (-exp).toNat else core ++ toString exp.toNat
  match sign with | .negative => "-" ++ core | .positive => core

def main (args : List String) : IO Unit := do
  let label := args.headD "uniform"
  let corpus := match label with
    | "nice" => Corpora.nice
    | "adversarial" => Corpora.adversarial
    | _ => Corpora.uniform
  let sz := corpus.size
  let N : Nat := 1000
  let decs : Array (Float.Model.UnpackedFloat.Sign × Nat × Int) := corpus.filterMap (fun f =>
    (Printer.toDecimal f).map fun d => (d.sign, d.significand, d.exponent))
  let sigs : Array Nat := decs.map (fun t => t.2.1)
  IO.println s!"# {label} corpus: {sz} floats, {decs.size} decoded"
  timeIt "1 baseline (toBits, foldl)"  N sz (fun _ => (corpus.foldl (init := (0 : UInt64)) (fun a f => a ^^^ f.toBits)).toNat)
  timeIt "1b one alloc/free per call (noinline pair)" N sz (fun _ => (corpus.foldl (init := (0 : UInt64)) (fun a f => a ^^^ (mkPair f.toBits).1)).toNat)
  timeIt "1c two allocs/frees per call (Except.ok pair)" N sz (fun _ => (corpus.foldl (init := (0 : UInt64)) (fun a f =>
      a ^^^ (match mkExceptPair f.toBits with | .ok p => p.1 | .error _ => 0))).toNat)
  timeIt "2 decode (Float→m,q)"      N sz (fun _ => corpus.foldl (init := 0) (fun a f => a ^^^ (decode f).m))
  timeIt "3 kernel v13 (previous, from bit fields)" N sz (fun _ => (corpus.foldl (init := (0 : UInt64)) (fun a f =>
      let bits : UInt64 := f.toBits
      let expBits : UInt64 := (bits >>> 52) &&& 0x7FF
      let mantBits : UInt64 := bits &&& 0x000F_FFFF_FFFF_FFFF
      let mU := if expBits = 0 then mantBits else mantBits + 4503599627370496
      let qB := if expBits = 0 then 0 else expBits - 1
      a ^^^ UInt64.ofNat (shortestUnsigned_v13 mU qB).1)).toNat)
  timeIt "3b kernel v14 (live, unboxed)" N sz (fun _ => (corpus.foldl (init := (0 : UInt64)) (fun a f =>
      let bits : UInt64 := f.toBits
      let expBits : UInt64 := (bits >>> 52) &&& 0x7FF
      let mantBits : UInt64 := bits &&& 0x000F_FFFF_FFFF_FFFF
      let mU := if expBits = 0 then mantBits else mantBits + 4503599627370496
      let qB := if expBits = 0 then 0 else expBits - 1
      a ^^^ (shortestUnsigned_v14 mU qB).1)).toNat)
  timeIt "4 toDecimal (Printer.toDecimal, live)" N sz (fun _ => (corpus.foldl (init := (0 : UInt64)) (fun a f =>
      a ^^^ (match Printer.toDecimal f with | some d => UInt64.ofNat d.significand | _ => 0))).toNat)
  timeIt "5 int→string (toString sig)" N decs.size (fun _ => sigs.foldl (init := 0) (fun a s => a ^^^ (toString s).length))
  timeIt "6 emit: sign++sig++e++exp" N decs.size (fun _ => decs.foldl (init := 0) (fun a t =>
      let signStr := match t.1 with | .negative => "-" | .positive => ""
      a ^^^ (signStr ++ toString t.2.1 ++ "e" ++ toString t.2.2).length))
  timeIt "6b emit: emitChecked (live)" N decs.size (fun _ => decs.foldl (init := 0) (fun a t =>
      a ^^^ (emitChecked t.1 t.2.1 t.2.2).length))
  timeIt "6c emit: ByteArray.push + fromUTF8! (unverified)" N decs.size (fun _ => decs.foldl (init := 0) (fun a t =>
      a ^^^ (emitBA t.1 (UInt64.ofNat t.2.1) t.2.2).length))
  timeIt "6d emit: String.push (unverified)" N decs.size (fun _ => decs.foldl (init := 0) (fun a t =>
      a ^^^ (emitPush t.1 t.2.1 t.2.2).length))
  timeIt "7 FULL floatToStrRef (live: toStringFast10/v14)" N sz (fun _ => corpus.foldl (init := 0) (fun a f => a ^^^ (floatToStrRef f).length))
  timeIt "7b FULL toStringFast9 (previous v13)" N sz (fun _ => corpus.foldl (init := 0) (fun a f => a ^^^ (toStringFast9 f).length))

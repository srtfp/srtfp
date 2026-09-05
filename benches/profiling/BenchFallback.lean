/- The cost of the live printer's fallback: the values of the bench corpora
   on which a 128-bit verdict is ambiguous, timed through the fast kernel
   (which returns `none` for them), the fallback `shortestUnsignedN`, and
   the exact comparison it may reach. `lake exe benchFallback`. -/
import Srtfp.Perf
import Corpora
open Srtfp Srtfp.Schubfach

def fields (f : Float) : UInt64 × UInt64 :=
  let bits := f.toBits
  let expBits : UInt64 := (bits >>> 52) &&& 0x7FF
  let mantBits : UInt64 := bits &&& 0x000F_FFFF_FFFF_FFFF
  ((if expBits = 0 then mantBits else mantBits + 4503599627370496),
   (if expBits = 0 then 0 else expBits - 1))

def finiteNonzero (f : Float) : Bool :=
  ((f.toBits >>> 52) &&& 0x7FF) != 0x7FF && (fields f).1 != 0

def fallsBack (f : Float) : Bool :=
  finiteNonzero f && (shortestUnsigned_u64_opt_v14 (fields f).1 (fields f).2).isNone

def timeIt (name : String) (n : Nat) (per : Nat) (body : Unit → UInt64) : IO Unit := do
  for _ in [0:5] do let _ := body (); pure ()
  let t0 ← IO.monoNanosNow
  let mut sink : UInt64 := 0
  for _ in [0:n] do sink := sink ^^^ body ()
  let t1 ← IO.monoNanosNow
  IO.println s!"{name}: {(t1 - t0) / (n * per)} ns/call{if sink == 1 then " " else ""}"

/-- The interval endpoints and midpoint comparison of a value, as the
    fallback would compare them. -/
def cmpArgs (fb : Array Float) : Array (Nat × Int × Nat × Int) := Id.run do
  let mut out := #[]
  for f in fb do
    let (mU, qB) := fields f
    let m := mU.toNat; let q : Int := (qB.toNat : Int) - 1074
    let k := kOfMQ m q
    let s := shiftedSig m q k
    out := out.push (4 * m - 2, q, 4 * (s / 10), k + 1)
    out := out.push (4 * m + 2, q, 4 * (s / 10 + 1), k + 1)
    out := out.push (2 * m, q, 2 * s + 1, k)
  return out

def main : IO Unit := do
  let fb : Array Float := (Corpora.uniform ++ Corpora.adversarial).filter fallsBack
  let ordinary := Corpora.uniform.filter finiteNonzero
  IO.println s!"# {fb.size} fallback values in the uniform + adversarial corpora"
  timeIt "fast kernel on fallback values (returns none)" 20000 fb.size fun _ => fb.foldl (init := 0) fun a f =>
    let (mU, qB) := fields f
    a ^^^ (match shortestUnsigned_u64_opt_v14 mU qB with | some p => p.1 | none => 7)
  timeIt "shortestUnsignedN on fallback values" 20000 fb.size fun _ => fb.foldl (init := 0) fun a f =>
    let (mU, qB) := fields f
    a ^^^ UInt64.ofNat (shortestUnsignedN mU.toNat ((qB.toNat : Int) - 1074)).1
  timeIt "shortestUnsignedN on uniform values" 200 ordinary.size fun _ => ordinary.foldl (init := 0) fun a f =>
    let (mU, qB) := fields f
    a ^^^ UInt64.ofNat (shortestUnsignedN mU.toNat ((qB.toNat : Int) - 1074)).1
  let args := cmpArgs fb
  timeIt "cmpExact on fallback endpoints" 20000 args.size fun _ =>
    args.foldl (init := 0) fun acc (a, q, b, k) => acc ^^^ (cmpExact a q b k).toNat.toUInt64
  timeIt "live toDecimal on adversarial" 2000 Corpora.adversarial.size fun _ =>
    Corpora.adversarial.foldl (init := 0) fun a f =>
      a ^^^ (match Printer.toDecimal f with | some d => UInt64.ofNat d.significand | none => 0)

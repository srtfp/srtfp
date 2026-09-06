/- Measurement-only emitter prototypes, UNVERIFIED and not part of the
   library. They answer whether a byte-level emitter could beat the live
   `Nat.repr ++ expTable` path on Lean's runtime; it cannot (2026-09-06):
   per string, callgrind gives the live path ~1000 instructions and this
   pre-sized `set!` writer ~1760, of which the digit loop is ~370,
   `fromUTF8!` validation ~400 and the UTF-8 length scan every string
   construction pays ~175. An unchecked `uset` variant measured ~10%
   faster than `set!` and was still 1.8× the live path. -/
import Srtfp.Perf
open Srtfp Srtfp.Schubfach

/-- UNVERIFIED emit alternative for measurement: one pre-sized buffer
    (`copySlice` from a blank), in-place `set!` writes two digits per
    step from a pair table, one `fromUTF8!`. -/
def blank32 : ByteArray := ⟨Array.replicate 32 48⟩

def digitPairs : ByteArray :=
  "00010203040506070809101112131415161718192021222324252627282930313233343536373839404142434445464748495051525354555657585960616263646566676869707172737475767778798081828384858687888990919293949596979899".toUTF8

@[inline] def ndigitsU (n : UInt64) : Nat :=
  if n < 10 then 1 else if n < 100 then 2 else if n < 1000 then 3 else if n < 10000 then 4
  else if n < 100000 then 5 else if n < 1000000 then 6 else if n < 10000000 then 7
  else if n < 100000000 then 8 else if n < 1000000000 then 9 else if n < 10000000000 then 10
  else if n < 100000000000 then 11 else if n < 1000000000000 then 12
  else if n < 10000000000000 then 13 else if n < 100000000000000 then 14
  else if n < 1000000000000000 then 15 else if n < 10000000000000000 then 16
  else if n < 100000000000000000 then 17 else if n < 1000000000000000000 then 18
  else if n < 10000000000000000000 then 19 else 20

/-- Digits of `n` written to end at position `last`, two per step. -/
def writeDigits : Nat → ByteArray → Nat → UInt64 → ByteArray
  | 0, b, _, _ => b
  | fuel + 1, b, last, n =>
    if n < 10 then b.set! last (48 + n.toUInt8)
    else if n < 100 then
      let r := (2 * n).toNat
      (b.set! (last - 1) (digitPairs.get! r)).set! last (digitPairs.get! (r + 1))
    else
      let r := (2 * (n % 100)).toNat
      let b := (b.set! (last - 1) (digitPairs.get! r)).set! last (digitPairs.get! (r + 1))
      writeDigits fuel b (last - 2) (n / 100)

def emitSet (sign : Float.Model.UnpackedFloat.Sign) (sU : UInt64) (exp : Int) : String :=
  let neg := match sign with | .negative => true | .positive => false
  let nd := ndigitsU sU
  let eNeg := exp < 0
  let eAbs : UInt64 := UInt64.ofNat (if eNeg then (-exp).toNat else exp.toNat)
  let ne := ndigitsU eAbs
  let len := (if neg then 1 else 0) + nd + 1 + (if eNeg then 1 else 0) + ne
  let b := blank32.copySlice 0 (ByteArray.emptyWithCapacity len) 0 len
  let b := if neg then b.set! 0 45 else b
  let p := if neg then 1 else 0
  let b := writeDigits 20 b (p + nd - 1) sU
  let p := p + nd
  let b := b.set! p 101
  let p := p + 1
  let b := if eNeg then b.set! p 45 else b
  let p := p + (if eNeg then 1 else 0)
  let b := writeDigits 20 b (p + ne - 1) eAbs
  String.fromUTF8! b

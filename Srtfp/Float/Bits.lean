/- IEEE-754 binary64 bit-level decomposition.

   This file extracts the sign / biased-exponent / mantissa fields from a
   `Float` via `Float.toBits`, and lifts them to an "integer significand
   × power-of-two" representation suitable for the Schubfach printer
   (M3) and the Clinger parser (M4).

   For a finite binary64 value `f`:

     f = (-1)^sign × m × 2^q

   where:
     - `sign` is the top bit
     - `biasedExp` is the next 11 bits, `0 ≤ biasedExp ≤ 2047`
     - `mantissaBits` is the bottom 52 bits, `0 ≤ mantissaBits < 2^52`
     - The integer significand `m` and binary exponent `q` are derived as:
         * Normal (`1 ≤ biasedExp ≤ 2046`):
             m = 2^52 + mantissaBits     (∈ [2^52, 2^53))
             q = biasedExp - 1023 - 52   (∈ [-1074, 971])
         * Subnormal / zero (`biasedExp = 0`):
             m = mantissaBits            (∈ [0, 2^52))
             q = -1074

   NaN and Infinity (`biasedExp = 2047`) are exposed via `isNaN` / `isInf`
   predicates and are otherwise out of scope for the decomposition. -/

import Srtfp.Decimal

namespace Srtfp.Float

/-! ## Bit-field extraction -/

/-- The sign bit of a `Float` (bit 63). -/
def signBit (f : _root_.Float) : Bool :=
  (f.toBits >>> 63) ≠ 0

/-- The 11-bit biased exponent of a `Float` (bits 62..52). Range `[0, 2047]`. -/
def biasedExpBits (f : _root_.Float) : Nat :=
  ((f.toBits >>> 52) &&& 0x7FF).toNat

/-- The 52-bit mantissa field of a `Float` (bits 51..0). Range `[0, 2^52)`.
    For *normal* numbers this is the fractional part of the significand (the
    leading `1` is implicit); for *subnormals* it is the significand. -/
def mantissaBits (f : _root_.Float) : Nat :=
  (f.toBits &&& 0x000F_FFFF_FFFF_FFFF).toNat

/-! ## Decomposition into integer significand × power-of-two -/

/-- Decomposed finite `Float`: `value = (if sign then -1 else 1) * m * 2^q`.
    For zero, `m = 0` and `q = -1074` (the subnormal-zero convention). -/
structure Decoded where
  sign : Bool
  /-- Integer significand. For normals, `m ∈ [2^52, 2^53)`. For subnormals,
      `m ∈ [0, 2^52)`. -/
  m : Nat
  /-- Binary exponent. `q ∈ [-1074, 971]` over the finite-Float domain. -/
  q : Int
  deriving Repr, DecidableEq, Inhabited

/-- Decode a `Float` into `(sign, m, q)`. The result is meaningful only for
    finite Floats; for NaN / Infinity the fields are returned uninterpreted. -/
def decode (f : _root_.Float) : Decoded :=
  let s := signBit f
  let e := biasedExpBits f
  let mb := mantissaBits f
  if e = 0 then
    -- Subnormal or zero.
    ⟨s, mb, -1074⟩
  else
    -- Normal. Restore the implicit leading 1.
    ⟨s, mb + (1 <<< 52), (e : Int) - 1023 - 52⟩

/-! ## Bit-pattern predicates -/

/-- `f` is NaN if `biasedExp = 2047` and `mantissaBits ≠ 0`. -/
def isNaNBits (f : _root_.Float) : Bool :=
  biasedExpBits f = 2047 && mantissaBits f ≠ 0

/-- `f` is `+∞` or `-∞` if `biasedExp = 2047` and `mantissaBits = 0`. -/
def isInfBits (f : _root_.Float) : Bool :=
  biasedExpBits f = 2047 && mantissaBits f = 0

/-- `f` is finite if `biasedExp < 2047`. -/
def isFiniteBits (f : _root_.Float) : Bool :=
  biasedExpBits f < 2047

/-! ## Re-encoding (round-trip via bits) -/

/-- Reassemble a `Float` from raw bit fields. Inverse of the
    `(signBit, biasedExpBits, mantissaBits)` triple. -/
def fromBits (sign : Bool) (biasedExp : Nat) (mantissa : Nat) : _root_.Float :=
  let s : UInt64 := if sign then (1 : UInt64) <<< 63 else 0
  let e : UInt64 := (UInt64.ofNat biasedExp &&& 0x7FF) <<< 52
  let mPart : UInt64 := UInt64.ofNat mantissa &&& 0x000F_FFFF_FFFF_FFFF
  _root_.Float.ofBits (s ||| e ||| mPart)

end Srtfp.Float

module
/- IEEE-754 binary64 bit-level decomposition.

   This file has two layers:

   1. **Word layer** (`Srtfp.Float.Word`): pure `UInt64` functions — field
      extraction (sign / biased exponent / mantissa), the decoded
      "integer significand × power-of-two" form, the NaN/Inf/finite
      pattern predicates, and field packing — plus their algebra
      (projection round-trips, field bounds). Everything here is
      axiom-free: no `Float` value is ever consulted.

   2. **Float layer**: the same names on `Float`, each a one-line
      composition of the word layer with `Float.toBits` / `Float.ofBits`.

   For a finite binary64 word `w`:

     value = (-1)^sign × m × 2^q

   where:
     - `sign` is the top bit
     - `biasedExp` is the next 11 bits, `0 ≤ biasedExp ≤ 2047`
     - `mantissa` is the bottom 52 bits, `0 ≤ mantissa < 2^52`
     - The integer significand `m` and binary exponent `q` are derived as:
         * Normal (`1 ≤ biasedExp ≤ 2046`):
             m = 2^52 + mantissa         (∈ [2^52, 2^53))
             q = biasedExp - 1023 - 52   (∈ [-1074, 971])
         * Subnormal / zero (`biasedExp = 0`):
             m = mantissa                (∈ [0, 2^52))
             q = -1074

   NaN and Infinity (`biasedExp = 2047`) are exposed via pattern
   predicates and are otherwise out of scope for the decomposition. -/

public import Srtfp.Decimal

@[expose] public section

open Float.Model.UnpackedFloat (Sign)

namespace Srtfp.Float

/-- Decomposed finite binary64 value:
    `value = signVal sign * m * 2^q`.
    For zero, `m = 0` and `q = -1074` (the subnormal-zero convention). -/
structure Decoded where
  sign : Sign
  /-- Integer significand. For normals, `m ∈ [2^52, 2^53)`. For subnormals,
      `m ∈ [0, 2^52)`. -/
  m : Nat
  /-- Binary exponent. `q ∈ [-1074, 971]` over the finite domain. -/
  q : Int
  deriving Repr, DecidableEq, Inhabited

/-! ## Word layer: pure `UInt64` bit-field algebra -/

namespace Word

/-- The sign of a binary64 word (bit 63). -/
def signBit (w : UInt64) : Sign :=
  if w >>> 63 = 0 then .positive else .negative

/-- The 11-bit biased exponent of a binary64 word (bits 62..52).
    Range `[0, 2047]`. -/
def biasedExp (w : UInt64) : Nat :=
  ((w >>> 52) &&& 0x7FF).toNat

/-- The 52-bit mantissa field of a binary64 word (bits 51..0).
    Range `[0, 2^52)`. For *normal* numbers this is the fractional part of
    the significand (the leading `1` is implicit); for *subnormals* it is
    the significand. -/
def mantissa (w : UInt64) : Nat :=
  (w &&& 0x000F_FFFF_FFFF_FFFF).toNat

/-- Decode a binary64 word into `(sign, m, q)`. The result is meaningful
    only for finite patterns; for NaN / Infinity the fields are returned
    uninterpreted. -/
def decode (w : UInt64) : Decoded :=
  let s := signBit w
  let e := biasedExp w
  let mb := mantissa w
  if e = 0 then
    -- Subnormal or zero.
    ⟨s, mb, -1074⟩
  else
    -- Normal. Restore the implicit leading 1.
    ⟨s, mb + (1 <<< 52), (e : Int) - 1023 - 52⟩

/-- `w` is a NaN pattern: `biasedExp = 2047` and `mantissa ≠ 0`.
    Same predicate as `Float.isNaNPattern`, phrased via the field readers
    (see `isNaN_eq_isNaNPattern`). -/
def isNaN (w : UInt64) : Bool :=
  biasedExp w = 2047 && mantissa w ≠ 0

/-- `w` is a `±∞` pattern: `biasedExp = 2047` and `mantissa = 0`. -/
def isInf (w : UInt64) : Bool :=
  biasedExp w = 2047 && mantissa w = 0

/-- Assemble a binary64 word from raw bit fields. Inverse of the
    `(signBit, biasedExp, mantissa)` triple (see `pack_proj`). -/
def pack (sign : Sign) (biasedExp mantissa : Nat) : UInt64 :=
  (match sign with | .negative => (1 : UInt64) <<< 63 | .positive => 0)
    ||| (UInt64.ofNat biasedExp &&& 0x7FF) <<< 52
    ||| (UInt64.ofNat mantissa &&& 0x000F_FFFF_FFFF_FFFF)

end Word

/-! ## Float layer

Each function is *definitionally* the corresponding word-layer function
applied to `f.toBits`, with the body spelled out so that proofs unfolding
it see the raw bit expressions. -/

/-- The sign of a `Float` (bit 63). -/
def signBit (f : _root_.Float) : Sign :=
  if f.toBits >>> 63 = 0 then .positive else .negative

/-- The 11-bit biased exponent of a `Float` (bits 62..52). Range `[0, 2047]`. -/
def biasedExpBits (f : _root_.Float) : Nat :=
  ((f.toBits >>> 52) &&& 0x7FF).toNat

/-- The 52-bit mantissa field of a `Float` (bits 51..0). Range `[0, 2^52)`.
    For *normal* numbers this is the fractional part of the significand (the
    leading `1` is implicit); for *subnormals* it is the significand. -/
def mantissaBits (f : _root_.Float) : Nat :=
  (f.toBits &&& 0x000F_FFFF_FFFF_FFFF).toNat

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

/-- `f` is NaN if `biasedExp = 2047` and `mantissaBits ≠ 0`. -/
def isNaNBits (f : _root_.Float) : Bool :=
  biasedExpBits f = 2047 && mantissaBits f ≠ 0

/-- `f` is `+∞` or `-∞` if `biasedExp = 2047` and `mantissaBits = 0`. -/
def isInfBits (f : _root_.Float) : Bool :=
  biasedExpBits f = 2047 && mantissaBits f = 0

end Srtfp.Float

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

/-- A `UInt64` bit pattern is a NaN pattern iff its biased exponent field
    (bits 62..52) is all-ones (`0x7FF`) and its mantissa field (bits 51..0)
    is nonzero. The bit round-trip `Float.toBits_ofBits`
    (`Srtfp/Float/Model.lean`) is restricted to patterns outside this set:
    NaN payloads are canonicalised (`SrtfpTest/RuntimeAxiomProbe.lean`
    observes the same at runtime). -/
def Float.isNaNPattern (x : UInt64) : Bool :=
  ((x >>> 52) &&& 0x7FF == 0x7FF) && (x &&& 0xF_FFFF_FFFF_FFFF != 0)

namespace Srtfp.Float

/-- Decomposed finite binary64 value:
    `value = (if sign then -1 else 1) * m * 2^q`.
    For zero, `m = 0` and `q = -1074` (the subnormal-zero convention). -/
structure Decoded where
  sign : Bool
  /-- Integer significand. For normals, `m ∈ [2^52, 2^53)`. For subnormals,
      `m ∈ [0, 2^52)`. -/
  m : Nat
  /-- Binary exponent. `q ∈ [-1074, 971]` over the finite domain. -/
  q : Int
  deriving Repr, DecidableEq, Inhabited

/-! ## Word layer: pure `UInt64` bit-field algebra -/

namespace Word

/-- The sign bit of a binary64 word (bit 63). -/
def signBit (w : UInt64) : Bool :=
  (w >>> 63) ≠ 0

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

/-- `w` is a finite pattern: `biasedExp < 2047`. -/
def isFinite (w : UInt64) : Bool :=
  biasedExp w < 2047

/-- Assemble a binary64 word from raw bit fields. Inverse of the
    `(signBit, biasedExp, mantissa)` triple (see `pack_proj`). -/
def pack (sign : Bool) (biasedExp mantissa : Nat) : UInt64 :=
  (if sign then (1 : UInt64) <<< 63 else 0)
    ||| (UInt64.ofNat biasedExp &&& 0x7FF) <<< 52
    ||| (UInt64.ofNat mantissa &&& 0x000F_FFFF_FFFF_FFFF)

end Word

/-! ## Float layer

Each function is *definitionally* the corresponding word-layer function
applied to `f.toBits` (see the `rfl` bridge lemmas below), but the bodies
are spelled out directly so that existing proofs unfolding them see the
raw bit expressions. -/

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

/-- `f` is finite if `biasedExp < 2047`. -/
def isFiniteBits (f : _root_.Float) : Bool :=
  biasedExpBits f < 2047

/-- Reassemble a `Float` from raw bit fields. Inverse of the
    `(signBit, biasedExpBits, mantissaBits)` triple. -/
def fromBits (sign : Bool) (biasedExp : Nat) (mantissa : Nat) : _root_.Float :=
  let s : UInt64 := if sign then (1 : UInt64) <<< 63 else 0
  let e : UInt64 := (UInt64.ofNat biasedExp &&& 0x7FF) <<< 52
  let mPart : UInt64 := UInt64.ofNat mantissa &&& 0x000F_FFFF_FFFF_FFFF
  _root_.Float.ofBits (s ||| e ||| mPart)

/-! ## Bridges: the Float layer is the word layer at `f.toBits`

All are `rfl`: the two layers are definitionally equal, so bits-level
theorems about `Word.*` transport to `Float`-level statements (and back)
by rewriting with these. -/

theorem signBit_word (f : _root_.Float) : signBit f = Word.signBit f.toBits := rfl
theorem biasedExpBits_word (f : _root_.Float) :
    biasedExpBits f = Word.biasedExp f.toBits := rfl
theorem mantissaBits_word (f : _root_.Float) :
    mantissaBits f = Word.mantissa f.toBits := rfl
theorem decode_word (f : _root_.Float) : decode f = Word.decode f.toBits := rfl
theorem isNaNBits_word (f : _root_.Float) : isNaNBits f = Word.isNaN f.toBits := rfl
theorem isInfBits_word (f : _root_.Float) : isInfBits f = Word.isInf f.toBits := rfl
theorem isFiniteBits_word (f : _root_.Float) :
    isFiniteBits f = Word.isFinite f.toBits := rfl
theorem fromBits_word (sign : Bool) (biasedExp mantissa : Nat) :
    fromBits sign biasedExp mantissa
      = _root_.Float.ofBits (Word.pack sign biasedExp mantissa) := rfl

end Srtfp.Float

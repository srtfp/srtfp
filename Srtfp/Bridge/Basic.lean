/- Bridge tier, ground floor: the first consumers of the runtime axiom.

   Everything here is a word-level fact from `Srtfp/Float/Bits.lean`
   (`pack_proj`, `pack_isNaNPattern_false`) transported across the single
   restricted runtime axiom `Float.toBits_ofBits`. No new bit algebra —
   just the `(Float.ofBits w).toBits = w` cancellation. -/

import Srtfp.Float.RuntimeAxiom

namespace Srtfp.Float

/-- `fromBits`'s bits are exactly the packed word, when the fields are in
range and don't encode a NaN payload. This is the axiom's cancellation in
its rawest form; everything else in the bridge tier factors through it. -/
theorem fromBits_toBits (sign : Bool) (biasedExp mantissa : Nat)
    (h_be : biasedExp < 2048) (h_m : mantissa < 2 ^ 52)
    (h_nan : biasedExp = 2047 → mantissa = 0) :
    (fromBits sign biasedExp mantissa).toBits = Word.pack sign biasedExp mantissa := by
  unfold fromBits
  exact _root_.Float.toBits_ofBits _
    (pack_isNaNPattern_false sign biasedExp mantissa h_be h_m h_nan)

/-- Round-trip of `fromBits` through `(signBit, biasedExpBits,
mantissaBits)`. When `biasedExp < 2048`, `mantissa < 2^52`, and the pair
does not encode a NaN payload (`biasedExp = 2047 → mantissa = 0`), the
bit-field projections recover the input. The word-level content is
`pack_proj` (axiom-free); the NaN side condition discharges the restricted
`toBits_ofBits` axiom via `pack_isNaNPattern_false`. -/
theorem fromBits_proj (sign : Bool) (biasedExp : Nat) (mantissa : Nat)
    (h_be : biasedExp < 2048) (h_m : mantissa < 2 ^ 52)
    (h_nan : biasedExp = 2047 → mantissa = 0) :
    signBit (fromBits sign biasedExp mantissa) = sign ∧
    biasedExpBits (fromBits sign biasedExp mantissa) = biasedExp ∧
    mantissaBits (fromBits sign biasedExp mantissa) = mantissa := by
  unfold signBit biasedExpBits mantissaBits
  rw [fromBits_toBits sign biasedExp mantissa h_be h_m h_nan]
  exact pack_proj sign biasedExp mantissa h_be h_m

/-- Transport: decoding the `Float` made from a non-NaN word is decoding
the word. The generic bridge between the two tiers — every word-level
`decode` fact becomes a `Float`-level one through this. -/
theorem decode_ofBits (w : UInt64) (h : _root_.Float.isNaNPattern w = false) :
    decode (_root_.Float.ofBits w) = Word.decode w := by
  rw [decode_word, _root_.Float.toBits_ofBits w h]

/-- Transport for the field readers, same shape. -/
theorem signBit_ofBits (w : UInt64) (h : _root_.Float.isNaNPattern w = false) :
    signBit (_root_.Float.ofBits w) = Word.signBit w := by
  rw [signBit_word, _root_.Float.toBits_ofBits w h]

theorem biasedExpBits_ofBits (w : UInt64) (h : _root_.Float.isNaNPattern w = false) :
    biasedExpBits (_root_.Float.ofBits w) = Word.biasedExp w := by
  rw [biasedExpBits_word, _root_.Float.toBits_ofBits w h]

theorem mantissaBits_ofBits (w : UInt64) (h : _root_.Float.isNaNPattern w = false) :
    mantissaBits (_root_.Float.ofBits w) = Word.mantissa w := by
  rw [mantissaBits_word, _root_.Float.toBits_ofBits w h]

theorem isNaNBits_ofBits (w : UInt64) (h : _root_.Float.isNaNPattern w = false) :
    isNaNBits (_root_.Float.ofBits w) = Word.isNaN w := by
  rw [isNaNBits_word, _root_.Float.toBits_ofBits w h]

theorem isInfBits_ofBits (w : UInt64) (h : _root_.Float.isNaNPattern w = false) :
    isInfBits (_root_.Float.ofBits w) = Word.isInf w := by
  rw [isInfBits_word, _root_.Float.toBits_ofBits w h]

theorem isFiniteBits_ofBits (w : UInt64) (h : _root_.Float.isNaNPattern w = false) :
    isFiniteBits (_root_.Float.ofBits w) = Word.isFinite w := by
  rw [isFiniteBits_word, _root_.Float.toBits_ofBits w h]

/-- `(fromBits sign biasedExp mantissa).toBits` is never a NaN pattern,
when the fields are in range and don't encode a NaN payload. -/
theorem fromBits_toBits_isNaNPattern_false (sign : Bool) (biasedExp mantissa : Nat)
    (h_be : biasedExp < 2048) (h_m : mantissa < 2 ^ 52)
    (h_nan : biasedExp = 2047 → mantissa = 0) :
    _root_.Float.isNaNPattern (fromBits sign biasedExp mantissa).toBits = false := by
  rw [fromBits_toBits sign biasedExp mantissa h_be h_m h_nan]
  exact pack_isNaNPattern_false sign biasedExp mantissa h_be h_m h_nan

end Srtfp.Float

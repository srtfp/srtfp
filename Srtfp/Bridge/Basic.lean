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

/-- `(fromBits sign biasedExp mantissa).toBits` is never a NaN pattern,
when the fields are in range and don't encode a NaN payload. -/
theorem fromBits_toBits_isNaNPattern_false (sign : Bool) (biasedExp mantissa : Nat)
    (h_be : biasedExp < 2048) (h_m : mantissa < 2 ^ 52)
    (h_nan : biasedExp = 2047 → mantissa = 0) :
    _root_.Float.isNaNPattern (fromBits sign biasedExp mantissa).toBits = false := by
  rw [fromBits_toBits sign biasedExp mantissa h_be h_m h_nan]
  exact pack_isNaNPattern_false sign biasedExp mantissa h_be h_m h_nan

end Srtfp.Float

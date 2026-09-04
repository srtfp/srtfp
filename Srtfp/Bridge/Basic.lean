module
/- Bridge tier, ground floor: word-level facts from `Srtfp/Float/Bits.lean`
   (`pack_proj`, `pack_isNaNPattern_false`) transported across the bit
   round-trip `Float.toBits_ofBits` (`Srtfp/Float/Model.lean`). No new bit
   algebra — just the `(Float.ofBits w).toBits = w` cancellation. -/

public import Srtfp.Float.Model
public import Srtfp.Proofs.Bits

@[expose] public section

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

end Srtfp.Float

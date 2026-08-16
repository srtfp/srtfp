/- Clinger bridge, `Float` tier.

   The word-level bridge results of `Srtfp/Proofs/Clinger/{Bridge,·}.lean`
   transported across the restricted runtime axiom. All axiom consumption
   on the parser side funnels through the single application inside
   `ofDecimal_toBits`. -/

import Srtfp.Proofs.Clinger
import Srtfp.Bridge.Basic

namespace Srtfp.Clinger

open Srtfp.Float
open Srtfp.Schubfach
open Srtfp

/-! ## Float tier — derived across the runtime axiom

Everything below consumes `Float.toBits_ofBits` (exactly once, inside
`ofDecimal_toBits`); the mathematical content is the word-level material
above. -/

/-- **The parser's master bridge**: `ofDecimal`'s runtime bits are exactly
the word `ofDecimalBits` computes — unconditionally, since no leaf of the
pipeline is a NaN pattern. The only axiom application on the parser side. -/
theorem ofDecimal_toBits (d : Decimal) :
    (ofDecimal d).toBits = ofDecimalBits d := by
  rw [ofDecimal_eq_bits]
  exact _root_.Float.toBits_ofBits _ (ofDecimalBits_not_nanPattern d)

/-- `ofDecimal` never produces a NaN bit pattern (Float tier). -/
theorem ofDecimal_toBits_not_nanPattern (d : Decimal) :
    _root_.Float.isNaNPattern (ofDecimal d).toBits = false := by
  rw [ofDecimal_toBits]
  exact ofDecimalBits_not_nanPattern d

/-- **The runtime bridge** (`DecodeOfDecimalBridge`), Float tier. -/
theorem decode_of_decimal_bridge : DecodeOfDecimalBridge := by
  intro d h_finite
  rw [decode_word, ofDecimal_toBits]
  exact decode_of_decimal_bridge_bits d h_finite

/-- Overflowing inputs produce exactly `±∞` (Float tier). -/
theorem decimalToFloat_overflow_inf (sign : Bool) (sig : Nat) (exp : Int)
    (h_sig : sig ≠ 0)
    (h_not : ¬ IsFiniteAbs sign sig exp) :
    decimalToFloat sign sig exp = fromBits sign 2047 0 := by
  rw [decimalToFloat_eq_bits,
      decimalToFloatBits_overflow_inf sign sig exp h_sig h_not]
  rfl

/-- `±∞` is not finite, at the bit level (Float tier). -/
theorem isFiniteBits_fromBits_inf (sign : Bool) :
    isFiniteBits (fromBits sign 2047 0) = false := by
  rw [fromBits_word,
      isFiniteBits_ofBits _ (pack_isNaNPattern_false sign 2047 0 (by decide) (by decide)
        (fun _ => rfl))]
  exact word_isFinite_inf sign

/-- `IsFiniteAbs` from a bit-level round-trip to a finite float (Float
tier of `isFiniteAbs_of_roundtrip_bits`). -/
theorem isFiniteAbs_of_roundtrip (d : Decimal) (f : _root_.Float)
    (h_sig : d.significand ≠ 0)
    (h_fin : isFiniteBits f = true)
    (h_rt : (ofDecimal d).toBits = f.toBits) :
    IsFiniteAbs d.sign d.significand d.exponent := by
  refine isFiniteAbs_of_roundtrip_bits d f.toBits h_sig ?_ ?_
  · rw [← isFiniteBits_word]; exact h_fin
  · rw [← ofDecimal_toBits]; exact h_rt

/-- `Float`-level counterpart, across `ofDecimal_toBits` (runtime axiom). -/
theorem ofDecimal_in_Rv
    (d : Decimal)
    (h_nonzero : d.significand ≠ 0)
    (h_finite : IsFiniteAbs d.sign d.significand d.exponent) :
    let f := ofDecimal d
    let decoded := decode f
    inRoundingInterval d.significand d.exponent
        decoded.m decoded.q (isIrregular decoded.m decoded.q) = true := by
  simp only
  rw [decode_word, ofDecimal_toBits]
  exact ofDecimalBits_in_Rv d h_nonzero h_finite


end Srtfp.Clinger

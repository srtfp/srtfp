module
/- Clinger bridge, `Float` tier: the parser's runtime bits are exactly
   the word `ofDecimalBits` computes. The only application of the
   runtime axiom on the parser side is inside `ofDecimal_toBits`. -/

public import Srtfp.Proofs.Reader.Spec
public import Srtfp.Bridge.Basic

@[expose] public section

namespace Srtfp.Clinger

open Srtfp.Float

/-- `ofDecimalBits` never produces a NaN pattern: its word is finite or an
infinity. -/
theorem ofDecimalBits_not_nanPattern (d : Decimal) :
    _root_.Float.isNaNPattern (ofDecimalBits d) = false := by
  rw [ofDecimalBits_eq]
  have hspec := decimalToFloatBits_spec d.sign d.significand d.exponent
  rcases Srtfp.Compat.lt_or_ge ((d.significand : Rat) * (10 : Rat) ^ d.exponent)
      (2 ^ 1024 - 2 ^ 970) with hd | hd
  · exact isNaNPattern_false_of_isFinite _ (hspec.1 hd).1
  · rw [hspec.2 hd]
    exact pack_isNaNPattern_false _ _ _ (by decide) (by decide) (fun _ => rfl)

/-- **The parser's bridge**: `ofDecimal`'s runtime bits are the word
`ofDecimalBits` computes. -/
theorem ofDecimal_toBits (d : Decimal) : (ofDecimal d).toBits = ofDecimalBits d := by
  rw [ofDecimal_eq_bits]
  exact _root_.Float.toBits_ofBits _ (ofDecimalBits_not_nanPattern d)

/-- `ofDecimal` never produces a NaN bit pattern. -/
theorem ofDecimal_toBits_not_nanPattern (d : Decimal) :
    _root_.Float.isNaNPattern (ofDecimal d).toBits = false := by
  rw [ofDecimal_toBits]; exact ofDecimalBits_not_nanPattern d

end Srtfp.Clinger

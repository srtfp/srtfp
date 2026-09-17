module
/- Decimal-to-binary64 wrappers around Lean's own conversion.
   Import Srtfp.Perf to compile these to the verified fast reader. -/

public import Srtfp.Spec

@[expose] public section

namespace Srtfp.Reader

/-- The bits of Lean's conversion, with the decimal's sign applied. -/
def ofDecimalBits (d : Decimal) : UInt64 := d.toModel.toBits

/-- Lean's conversion as a runtime `Float`. -/
def ofDecimal (d : Decimal) : Float := Float.ofModel d.toModel

theorem ofDecimal_toBits (d : Decimal) : (ofDecimal d).toBits = ofDecimalBits d := rfl

end Srtfp.Reader

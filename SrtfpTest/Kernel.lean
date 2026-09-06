/- Runtime cross-checks of the live printer against the reference scan
   `Printer.toDecimalBits`, evaluated as written (no `@[csimp]` applies to
   it): the kernel's `Decimal` and the string emitter, on the Ryu corpora
   and the boundary values. -/

import SrtfpTest.Spec
import Srtfp.Perf
import SrtfpTest.Ryu

namespace Srtfp.Tests.Kernel

open SrtfpSpec Srtfp Srtfp.Schubfach Srtfp.Float

open Srtfp.Tests.Ryu in
/-- The full Ryu corpus, flattened. -/
private def allRyuFloats : Array Float :=
  (d2sBasic ++ d2sSwitchToSubnormal ++ d2sMinAndMax ++ d2sLotsOfTrailingZeros
    ++ d2sRegression ++ d2sLooksLikePow5 ++ d2sOutputLength ++ d2sMinMaxShift
    ++ d2sSmallIntegers ++ f2sBasic ++ f2sSwitchToSubnormal ++ f2sMinAndMax
    ++ f2sBoundaryRoundEven ++ f2sExactValueRoundEven ++ f2sLotsOfTrailingZeros
    ++ f2sRegression ++ f2sLooksLikePow5 ++ f2sOutputLength).map (fun c => c.2.1)

private def corpus : Array Float := allRyuFloats ++ #[
  2.109808898695963e16, 4.940656e-318, 1.18575755e-316,
  9007199254740992.0, 1125899906842624.25, 18014398509481982.0,
  0.0, -0.0, 1.0, -1.0, 1e22, 1e23, 5e-324, 1.7976931348623157e308,
  2.2250738585072014e-308, 2.225073858507201e-308, 4503599627370496.0,
  9007199254740991.0, 0.1, 0.3, 1e-7, 123456789012345680.0]

/-- The reference string, from the reference decimal. -/
private def refString (f : Float) : String :=
  match Printer.toDecimalBits f.toBits with
  | some d => decimalToStrRef d
  | none => if isNaNBits f then "NaN" else withSign (signBit f) "Infinity"

private structure Tally where
  badDecimal : Nat := 0
  badString : Nat := 0

private def tally : Tally := Id.run do
  let mut t : Tally := {}
  for f in corpus do
    if toDecimalBits f.toBits != Printer.toDecimalBits f.toBits then
      t := { t with badDecimal := t.badDecimal + 1 }
    if floatToString f != refString f then
      t := { t with badString := t.badString + 1 }
  return t

def runTests : TestSeq :=
  let t := tally
  test s!"Schubfach.toDecimalBits = reference scan ({corpus.size} values)" (t.badDecimal = 0)
  ++ test s!"floatToString = reference string ({corpus.size} values)" (t.badString = 0)

end Srtfp.Tests.Kernel

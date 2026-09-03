/- The reference printer agrees with the live (csimp) Schubfach printer
   on the Ryu corpus. `Printer.toDecimalBits` and `Printer.shortest`
   deliberately never get a csimp registration, so this really runs the
   exact-rational reference (only `Printer.toDecimal` is redirected). -/
import SrtfpTest.Spec
import SrtfpTest.Ryu
import Srtfp.Printer
import Srtfp.Perf.Schubfach
import Srtfp.Perf.KernelV6

namespace Srtfp.Tests.Printer

open SrtfpSpec Srtfp

open Srtfp.Tests.Ryu in
private def corpus : Array Float :=
  (d2sBasic ++ d2sSwitchToSubnormal ++ d2sMinAndMax ++ d2sLotsOfTrailingZeros
    ++ d2sRegression ++ d2sLooksLikePow5 ++ d2sOutputLength ++ d2sMinMaxShift
    ++ d2sSmallIntegers).map (fun c => c.2.1)
  ++ #[1.0, 0.1, 0.3, 1e10, 1e-10, 5e-324, 9.88e-324, 1.7976931348623157e308,
       1125899906842624.25, 4503599627370496.0, 9007199254740992.0, 2.2250738585072014e-308]

private def sameResult : Except String Decimal → Except String Decimal → Bool
  | .ok a, .ok b => a = b
  | .error a, .error b => a = b
  | _, _ => false

private def mismatches : Array (Float × Except String Decimal × Except String Decimal) := Id.run do
  let mut out := #[]
  for f in corpus do
    let r := Printer.toDecimalBits f.toBits
    let s := Schubfach.toDecimal f
    if !sameResult r s then out := out.push (f, r, s)
  return out

def runTests : TestSeq :=
  test s!"Printer.toDecimalBits = live printer (corpus of {corpus.size})" mismatches.isEmpty

end Srtfp.Tests.Printer

/- Runtime cross-checks of the live printer kernel against the reference
   scan `Printer.toDecimalBits`, evaluated as written (no `@[csimp]`
   applies to it). The fast path (`shortestUnsigned_u64_opt_v14`) and the
   fallback it defers to on an ambiguous verdict are each compared
   with the reference on every value, so the fallback is exercised even
   though live callers reach it rarely; the values on which they do are
   listed explicitly. The string emitter is checked against the reference
   string of the reference decimal. -/

import SrtfpTest.Spec
import Srtfp.Perf
import SrtfpTest.Ryu

namespace Srtfp.Tests.Kernel

open SrtfpSpec Srtfp Srtfp.Schubfach

open Float.Model.UnpackedFloat (Sign)

open Srtfp.Tests.Ryu in
/-- The full Ryu corpus, flattened. -/
private def allRyuFloats : Array Float :=
  (d2sBasic ++ d2sSwitchToSubnormal ++ d2sMinAndMax ++ d2sLotsOfTrailingZeros
    ++ d2sRegression ++ d2sLooksLikePow5 ++ d2sOutputLength ++ d2sMinMaxShift
    ++ d2sSmallIntegers ++ f2sBasic ++ f2sSwitchToSubnormal ++ f2sMinAndMax
    ++ f2sBoundaryRoundEven ++ f2sExactValueRoundEven ++ f2sLotsOfTrailingZeros
    ++ f2sRegression ++ f2sLooksLikePow5 ++ f2sOutputLength).map (fun c => c.2.1)

/-- Values on which a 128-bit verdict is ambiguous, so the live kernel
    takes the packed fallback (every such value of the bench corpora). -/
private def fallbackFloats : Array Float :=
  #[4863511224840317085, 14074519758152169412, 4845873199050653696,
    4832362400168542209, 4832362400168542211, 4850376798678024191].map Float.ofBits

private def corpus : Array Float := allRyuFloats ++ fallbackFloats ++ #[
  2.109808898695963e16, 4.940656e-318, 1.18575755e-316,
  9007199254740992.0, 1125899906842624.25, 18014398509481982.0,
  0.0, -0.0, 1.0, -1.0, 1e22, 1e23, 5e-324, 1.7976931348623157e308]

/-- The bit fields as the live kernel takes them: the significand with the
    hidden bit and the biased exponent `q + 1074`. -/
private def fields (f : Float) : UInt64 × UInt64 :=
  let bits := f.toBits
  let expBits : UInt64 := (bits >>> 52) &&& 0x7FF
  let mantBits : UInt64 := bits &&& 0x000F_FFFF_FFFF_FFFF
  ((if expBits = 0 then mantBits else mantBits + 4503599627370496),
   (if expBits = 0 then 0 else expBits - 1))

private def signOf (f : Float) : Sign := if f.toBits >>> 63 = 0 then .positive else .negative

private structure Tally where
  fast : Nat := 0
  fallback : Nat := 0
  badFast : Nat := 0
  badFallback : Nat := 0
  badString : Nat := 0

private def tally : Tally := Id.run do
  let mut t : Tally := {}
  for f in corpus do
    let some ref := Printer.toDecimalBits f.toBits | continue
    if toStringFast10 f != decimalToStrRef ref then t := { t with badString := t.badString + 1 }
    let (mU, qB) := fields f
    if mU = 0 then continue
    let s := signOf f
    match shortestUnsigned_u64_opt_v14 mU qB with
    | some (sU, kB) =>
      t := { t with fast := t.fast + 1 }
      if Decimal.mk' s sU.toNat ((kB.toNat : Int) - 324) != ref then
        t := { t with badFast := t.badFast + 1 }
    | none => t := { t with fallback := t.fallback + 1 }
    let (sig, exp) := shortestUnsignedN mU.toNat ((qB.toNat : Int) - 1074)
    if Decimal.mk' s sig exp != ref then t := { t with badFallback := t.badFallback + 1 }
  return t

def runTests : TestSeq :=
  let t := tally
  test s!"v14 fast path = reference scan ({t.fast} values)" (t.badFast = 0)
  ++ test s!"fallback = reference scan ({t.fast + t.fallback} values, {t.fallback} live fallbacks)"
      (t.badFallback = 0 && t.fallback ≥ 5)
  ++ test s!"toStringFast10 = reference string ({corpus.size} values)" (t.badString = 0)

end Srtfp.Tests.Kernel

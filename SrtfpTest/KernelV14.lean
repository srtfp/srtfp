/- Runtime cross-check of the v14 kernel (the live string and Decimal
   path: v13 with `UInt8` verdicts and a biased `UInt64` exponent) against
   `shortestUnsigned_v2` (the established UInt64 path) on the Ryu corpus +
   Schubfach-edge inputs, plus the two live entry points against their v13
   predecessors.

   v14 is what the `floatToStrRef` / `Printer.toDecimal` `@[csimp]`s select
   at runtime (`toStringFast10`, `toDecimal_v14`). Its full correctness is
   the formal proof `shortestUnsigned_u64_opt_v14_some_eq_v13` chained to
   the v13 proofs; this is a belt-and-suspenders runtime witness. -/

import SrtfpTest.Spec
import Srtfp.Perf.Schubfach
import Srtfp.Perf.Uint64Kernel
import Srtfp.Perf.KernelV14
import Srtfp.Perf.Bits
import SrtfpTest.Ryu

namespace Srtfp.Tests.KernelV14

open SrtfpSpec Srtfp Srtfp.Schubfach Srtfp.Float

open Srtfp.Tests.Ryu in
/-- The full Ryu corpus, flattened. -/
private def allRyuFloats : Array Float :=
  (d2sBasic ++ d2sSwitchToSubnormal ++ d2sMinAndMax ++ d2sLotsOfTrailingZeros
    ++ d2sRegression ++ d2sLooksLikePow5 ++ d2sOutputLength ++ d2sMinMaxShift
    ++ d2sSmallIntegers ++ f2sBasic ++ f2sSwitchToSubnormal ++ f2sMinAndMax
    ++ f2sBoundaryRoundEven ++ f2sExactValueRoundEven ++ f2sLotsOfTrailingZeros
    ++ f2sRegression ++ f2sLooksLikePow5 ++ f2sOutputLength).map (fun c => c.2.1)

private def crossCheckCorpus : Array Float := allRyuFloats ++ #[
  2.109808898695963e16, 4.940656e-318, 1.18575755e-316,
  9007199254740992.0, 1125899906842624.25, 18014398509481982.0,
  0.0, -0.0, 1.0, -1.0, 1e22, 1e23, 5e-324, 1.7976931348623157e308]

/-- Cross-check `shortestUnsigned_v14` (biased exponent, unbiased here)
    against `shortestUnsigned_v2`. -/
private def kernelMismatches : Array (Float × (Nat × Int) × (Nat × Int)) := Id.run do
  let mut mismatches : Array (Float × (Nat × Int) × (Nat × Int)) := #[]
  for f in crossCheckCorpus do
    let d := decode f
    if d.m = 0 then continue
    let mU : UInt64 := UInt64.ofNat d.m
    let qB : UInt64 := UInt64.ofNat (d.q + 1074).toNat
    let (sU, kB) := shortestUnsigned_v14 mU qB
    let v14 : Nat × Int := (sU.toNat, (kB.toNat : Int) - 324)
    let v2 := shortestUnsigned_v2 d.m d.q
    if v14 ≠ v2 then
      mismatches := mismatches.push (f, v2, v14)
  return mismatches

/-- `toStringFast10` (live) against `toStringFast9` (previous live kernel). -/
private def stringMismatches : Array (Float × String × String) := Id.run do
  let mut mismatches := #[]
  for f in crossCheckCorpus do
    let s10 := toStringFast10 f
    let s9 := toStringFast9 f
    if s10 ≠ s9 then mismatches := mismatches.push (f, s9, s10)
  return mismatches

/-- `toDecimal_v14` (live) against `toDecimal_v13`. -/
private def decimalMismatches : Array Float := Id.run do
  let mut mismatches := #[]
  for f in crossCheckCorpus do
    if toDecimal_v14 f != toDecimal_v13 f then mismatches := mismatches.push f
  return mismatches

def runTests : TestSeq :=
  test s!"shortestUnsigned_v14 = shortestUnsigned_v2 (corpus of {crossCheckCorpus.size})"
    kernelMismatches.isEmpty ++
  test s!"toStringFast10 = toStringFast9 (corpus of {crossCheckCorpus.size})"
    stringMismatches.isEmpty ++
  test s!"toDecimal_v14 = toDecimal_v13 (corpus of {crossCheckCorpus.size})"
    decimalMismatches.isEmpty

end Srtfp.Tests.KernelV14

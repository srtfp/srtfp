/- Runtime cross-check that `shortestUnsigned_v13` (the live string-path
   kernel: boundary-product `s = 5P` extraction + flipped interval tests)
   agrees with `shortestUnsigned_v2` (the established UInt64 path) on the
   Ryu corpus + Schubfach-edge inputs, including the inputs that earlier
   kernels fall back on.

   v13 is the kernel the `floatToStrRef` `@[csimp]` selects at runtime
   (`toStringFast9`), so this exercises the live shortest-decimal path.
   Its full correctness is the formal proof
   `shortestUnsigned_u64_opt_v13_some_eq_packed`; this is a belt-and-
   suspenders runtime witness over the corpus. -/

import LSpec
import Srtfp.Numeric.Schubfach
import Srtfp.Numeric.Schubfach.Perf.Uint64Kernel
import Srtfp.Numeric.Schubfach.Perf.KernelV13
import Srtfp.Numeric.Float.Bits
import SrtfpTest.Ryu

namespace PP.Numeric.Tests.KernelV13

open LSpec PP.Numeric PP.Numeric.Schubfach PP.Numeric.Float

open PP.Numeric.Tests.Ryu in
/-- The full Ryu corpus, flattened. -/
private def allRyuFloats : Array Float :=
  (d2sBasic ++ d2sSwitchToSubnormal ++ d2sMinAndMax ++ d2sLotsOfTrailingZeros
    ++ d2sRegression ++ d2sLooksLikePow5 ++ d2sOutputLength ++ d2sMinMaxShift
    ++ d2sSmallIntegers ++ f2sBasic ++ f2sSwitchToSubnormal ++ f2sMinAndMax
    ++ f2sBoundaryRoundEven ++ f2sExactValueRoundEven ++ f2sLotsOfTrailingZeros
    ++ f2sRegression ++ f2sLooksLikePow5 ++ f2sOutputLength).map (fun c => c.2.1)

private def crossCheckCorpus : Array Float := allRyuFloats ++ #[
  -- The 3 inputs the 128-bit kernel falls back on (per PERFLOG), plus
  -- powers of two whose irregular bands exercise v13's w = 127 path.
  2.109808898695963e16, 4.940656e-318, 1.18575755e-316,
  9007199254740992.0, 1125899906842624.25, 18014398509481982.0]

/-- Cross-check `shortestUnsigned_v13` (live kernel, UInt64 bit-field args)
    against `shortestUnsigned_v2` (established path, `(m, q)` args). -/
private def findMismatches : Array (Float × (Nat × Int) × (Nat × Int)) := Id.run do
  let mut mismatches : Array (Float × (Nat × Int) × (Nat × Int)) := #[]
  for f in crossCheckCorpus do
    let d := decode f
    if d.m = 0 then continue
    let mU : UInt64 := UInt64.ofNat d.m
    let qB : UInt64 := UInt64.ofNat (d.q + 1074).toNat
    let v13 := shortestUnsigned_v13 mU qB
    let v2 := shortestUnsigned_v2 d.m d.q
    if v13 ≠ v2 then
      mismatches := mismatches.push (f, v2, v13)
  return mismatches

def runTests : TestSeq :=
  test s!"shortestUnsigned_v13 = shortestUnsigned_v2 (corpus of {crossCheckCorpus.size})"
    findMismatches.isEmpty

end PP.Numeric.Tests.KernelV13

/- Runtime cross-check that `shortestUnsigned_v2` (UInt64 path) and
   `shortestUnsigned_packed` (spec-csimp path) produce identical results
   on the entire Ryu corpus + other Schubfach-edge inputs.

   This serves as a correctness witness pending the formal equivalence
   proof (see `PP/Numeric/Schubfach/Uint64Kernel.lean` TODO). -/

import LSpec
import Srtfp.Numeric.Schubfach
import Srtfp.Numeric.Schubfach.Perf.Orchestration
import Srtfp.Numeric.Schubfach.Perf.Uint64Kernel
import Srtfp.Numeric.Schubfach.Perf.Uint64Bridge
import Srtfp.Numeric.Float.Bits
import SrtfpTest.Ryu

namespace PP.Numeric.Tests.Uint64Kernel

open LSpec PP.Numeric PP.Numeric.Schubfach PP.Numeric.Float

open PP.Numeric.Tests.Ryu in
/-- The full Ryu corpus, flattened. -/
private def allRyuFloats : Array Float :=
  (d2sBasic ++ d2sSwitchToSubnormal ++ d2sMinAndMax ++ d2sLotsOfTrailingZeros
    ++ d2sRegression ++ d2sLooksLikePow5 ++ d2sOutputLength ++ d2sMinMaxShift
    ++ d2sSmallIntegers ++ f2sBasic ++ f2sSwitchToSubnormal ++ f2sMinAndMax
    ++ f2sBoundaryRoundEven ++ f2sExactValueRoundEven ++ f2sLotsOfTrailingZeros
    ++ f2sRegression ++ f2sLooksLikePow5 ++ f2sOutputLength).map (fun c => c.2.1)

/-- Spec vs v2 cross-check on a single `Float`. -/
private def specEqV2 (f : Float) : Bool :=
  let d := decode f
  if d.m = 0 then true  -- skipped by the orchestration anyway
  else shortestUnsigned_packed d.m d.q == shortestUnsigned_v2 d.m d.q

/-- An array of inputs to cross-check. -/
private def crossCheckCorpus : Array Float := allRyuFloats ++ #[
  -- Additional edge cases.
  1.0, 2.0, 0.1, 0.2, 0.3, 0.1 + 0.2,
  1e10, 1e-10, 1.7976931348623157e308, 5e-324,
  3.14159265358979, 2.718281828459045,
  1.0/3.0, 1.0/7.0, 1.0/11.0,
  42.0, 100.0, 1000.0, 999999.999999,
  1.5, 2.5, 3.5, 4.5
]

/-- Cross-check all corpus inputs.  Returns the list of disagreements. -/
private def findMismatches : Array (Float × (Nat × Int) × (Nat × Int)) := Id.run do
  let mut mismatches : Array (Float × (Nat × Int) × (Nat × Int)) := #[]
  for f in crossCheckCorpus do
    let d := decode f
    if d.m = 0 then continue
    let p := shortestUnsigned_packed d.m d.q
    let v := shortestUnsigned_v2 d.m d.q
    if p ≠ v then
      mismatches := mismatches.push (f, p, v)
  return mismatches

def runTests : TestSeq :=
  test s!"shortestUnsigned_v2 = shortestUnsigned_packed (corpus of {crossCheckCorpus.size})"
    findMismatches.isEmpty

/-- Cross-check `floorLog10Pow2_fast` against the spec across the full
    binary64 exponent range `[-1074, 971]`. -/
private def findFloorLogMismatches : Array (Int × Int × Int) := Id.run do
  let mut mismatches : Array (Int × Int × Int) := #[]
  for q in [0:2046] do
    let qInt : Int := -1074 + (q : Int)
    let regular := floorLog10Pow2 qInt
    let regular_fast := floorLog10Pow2_fast qInt
    if regular ≠ regular_fast then
      mismatches := mismatches.push (qInt, regular, regular_fast)
  return mismatches

private def findFloorLog3Q4Mismatches : Array (Int × Int × Int) := Id.run do
  let mut mismatches : Array (Int × Int × Int) := #[]
  for q in [0:2046] do
    let qInt : Int := -1074 + (q : Int)
    let spec := floorLog10ThreeQuartersPow2 qInt
    let fast := floorLog10ThreeQuartersPow2_fast qInt
    if spec ≠ fast then
      mismatches := mismatches.push (qInt, spec, fast)
  return mismatches

/-- Cross-check `kOfMQ_fast` vs `kOfMQ` on the bench-input corpus. -/
private def findKOfMQMismatches : Array (Float × Int × Int) := Id.run do
  let mut mismatches : Array (Float × Int × Int) := #[]
  for f in crossCheckCorpus do
    let d := decode f
    if d.m = 0 then continue
    let spec := kOfMQ d.m d.q
    let fast := kOfMQ_fast d.m d.q
    if spec ≠ fast then
      mismatches := mismatches.push (f, spec, fast)
  return mismatches

def runFloorLogTests : TestSeq :=
  test s!"floorLog10Pow2_fast = floorLog10Pow2 (q ∈ [-1074, 971])"
    findFloorLogMismatches.isEmpty
  ++
  test s!"floorLog10ThreeQuartersPow2_fast = ... (q ∈ [-1074, 971])"
    findFloorLog3Q4Mismatches.isEmpty
  ++
  test s!"kOfMQ_fast = kOfMQ on corpus"
    findKOfMQMismatches.isEmpty

end PP.Numeric.Tests.Uint64Kernel

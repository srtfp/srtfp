/- Runtime cross-check that `shiftedSig_v4` (192-bit kernel) and
   `shiftedSig` (spec) produce identical results on the Ryu corpus +
   Schubfach-edge inputs, including the 3 inputs that the 128-bit
   kernel falls back to the slow path for.

   Correctness witness for the 192-bit path pending the formal
   equivalence proof. -/

import SrtfpTest.Spec
import Srtfp.Schubfach
import Srtfp.Schubfach.Perf.Orchestration
import Srtfp.Schubfach.Perf.Uint64Kernel
import Srtfp.Schubfach.Perf.Uint64Kernel192
import Srtfp.Float.Bits
import SrtfpTest.Ryu

namespace Srtfp.Tests.Uint64Kernel192

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
  -- The 3 inputs that the 128-bit kernel falls back on (per PERFLOG).
  5e-324, 1e-10, 1.7976931348623157e308,
  -- Other edge cases.
  1.0, 2.0, 0.1, 0.2, 0.3, 0.1 + 0.2,
  1e10, 3.14159265358979, 2.718281828459045,
  1.0/3.0, 1.0/7.0, 1.0/11.0,
  42.0, 100.0, 1000.0, 999999.999999,
  1.5, 2.5, 3.5, 4.5
]

/-- Cross-check `shiftedSig_v4` (192-bit kernel) vs `shiftedSig` (spec)
    on a corpus of `(m, q, k)` triples derived from real `Float` inputs. -/
private def findShiftedSigMismatches : Array (Float × Nat × Nat) := Id.run do
  let mut mismatches : Array (Float × Nat × Nat) := #[]
  for f in crossCheckCorpus do
    let d := decode f
    if d.m = 0 then continue
    let k := kOfMQ d.m d.q
    let spec := shiftedSig d.m d.q k
    let fast := shiftedSig_v4 d.m d.q k
    if spec ≠ fast then
      mismatches := mismatches.push (f, spec, fast)
  return mismatches

def runTests : TestSeq :=
  test s!"shiftedSig_v4 = shiftedSig (corpus of {crossCheckCorpus.size})"
    findShiftedSigMismatches.isEmpty

/-! ## End-to-end `shortestUnsigned_v4` cross-check (Phase 8C precursor).

Mirrors `shortestUnsigned_v2 = shortestUnsigned_packed` but uses
`shortestUnsigned_v4` (the 192-bit shiftedSig variant defined in
`BenchU192End.lean` — re-defined here to avoid that exe dependency). -/

set_option linter.unusedVariables false in
/-- A v4 shortestUnsigned definition matching `BenchU192End`'s.  Kept
    in lockstep with that file.  Same body as `shortestUnsigned_u64_opt`
    with `shiftedSig_v3` swapped for `shiftedSig_v4`. -/
@[inline]
def shortestUnsigned_u64_opt_v4 (m : Nat) (q : Int) : Option (Nat × Int) :=
  if h_m : m ≥ (1 <<< 53 : Nat) then none
  else if h_q_lo : q < (-1074 : Int) then none
  else if h_q_hi : q > 971 then none
  else
    let irregular := isIrregular m q
    let k := kOfMQ_fast m q
    if h_k_lo : k < pow10Table128_kMin then none
    else if h_k_hi : k + 1 > pow10Table128_kMax then none
    else
    let s := shiftedSig_v4 m q k
    if h_s : s ≥ (1 <<< 57 : Nat) then none
    else
      let sU : UInt64 := UInt64.ofNat s
      let mU : UInt64 := UInt64.ofNat m
      if s ≥ 10 then
        let kHigh : Int := k + 1
        let cmpTupleH := pow10Lookup128 kHigh
        let cmpHGHi := cmpTupleH.1
        let cmpHGLo := cmpTupleH.2.1
        let cmpHH := cmpTupleH.2.2
        let cmpHQPlusH : Int := q + cmpHH
        if h_qh_lo : cmpHQPlusH < 64 then none
        else if h_qh_hi : cmpHQPlusH > 132 then none
        else
          let cmpHQPlusH8 : UInt64 := UInt64.ofNat cmpHQPlusH.toNat
          let sHighU : UInt64 := sU / 10
          let uV := inRoundingInterval_u64_packed_u8 cmpHGHi cmpHGLo cmpHQPlusH8
                      sHighU mU irregular
          if uV = inRoundingInterval_u8_AMBIG then none
          else if uV = inRoundingInterval_u8_TRUE then some (sHighU.toNat, kHigh)
          else
            let wV := inRoundingInterval_u64_packed_u8 cmpHGHi cmpHGLo cmpHQPlusH8
                        (sHighU + 1) mU irregular
            if wV = inRoundingInterval_u8_AMBIG then none
            else if wV = inRoundingInterval_u8_TRUE then some ((sHighU + 1).toNat, kHigh)
            else
              let cmpTuple := pow10Lookup128 k
              let cmpGHi := cmpTuple.1
              let cmpGLo := cmpTuple.2.1
              let cmpH := cmpTuple.2.2
              let cmpQPlusH : Int := q + cmpH
              if h_qh2_lo : cmpQPlusH < 64 then none
              else if h_qh2_hi : cmpQPlusH > 132 then none
              else
                let cmpQPlusH8 : UInt64 := UInt64.ofNat cmpQPlusH.toNat
                match pickNearer_u64_opt cmpGHi cmpGLo cmpQPlusH8 sU mU irregular with
                | none => none
                | some chosen => some (chosen.toNat, k)
      else if h_s1 : s = 0 then none
      else
        let cmpTuple := pow10Lookup128 k
        let cmpGHi := cmpTuple.1
        let cmpGLo := cmpTuple.2.1
        let cmpH := cmpTuple.2.2
        let cmpQPlusH : Int := q + cmpH
        if h_qh2_lo : cmpQPlusH < 64 then none
        else if h_qh2_hi : cmpQPlusH > 132 then none
        else
          let cmpQPlusH8 : UInt64 := UInt64.ofNat cmpQPlusH.toNat
          match pickNearer_u64_opt cmpGHi cmpGLo cmpQPlusH8 sU mU irregular with
          | none => none
          | some chosen => some (chosen.toNat, k)

@[inline]
def shortestUnsigned_v4 (m : Nat) (q : Int) : Nat × Int :=
  match shortestUnsigned_u64_opt_v4 m q with
  | some v => v
  | none => shortestUnsigned_packed m q

/-- End-to-end cross-check: `shortestUnsigned_v4 = shortestUnsigned_v2`. -/
private def findEndToEndMismatches : Array (Float × (Nat × Int) × (Nat × Int)) := Id.run do
  let mut mismatches : Array (Float × (Nat × Int) × (Nat × Int)) := #[]
  for f in crossCheckCorpus do
    let d := decode f
    if d.m = 0 then continue
    let v2 := shortestUnsigned_v2 d.m d.q
    let v4 := shortestUnsigned_v4 d.m d.q
    if v2 ≠ v4 then
      mismatches := mismatches.push (f, v2, v4)
  return mismatches

def runEndToEndTests : TestSeq :=
  test s!"shortestUnsigned_v4 = shortestUnsigned_v2 (corpus of {crossCheckCorpus.size})"
    findEndToEndMismatches.isEmpty

end Srtfp.Tests.Uint64Kernel192

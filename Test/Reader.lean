/- Runtime cross-checks of the reader tier.

   `Reader.ofDecimalBits` compiles to the fast kernel (`readFast`, falling
   back to `readExact`) through `@[csimp]`; its correctness is the proof
   `Srtfp.Reader.ofDecimalBits_fast_eq`. These tests are the runtime
   witness: direct calls to Lean's `ofScientific` exercise its own
   registration too. Every Ryu-suite decimal reads back to its float's bits, and a
   random sweep of `(m, e)` pairs compares the fast kernel and the exact
   fallback against the reference `read` evaluated on `Rat`. -/

import Test.Harness
import Srtfp.Perf.ReadFast
import Test.Ryu

namespace Srtfp.Tests.Reader

open Test.Harness Srtfp Srtfp.Reader

open Srtfp.Tests.Ryu in
/-- The Ryu suite: every `(float, shortest decimal)` pair. -/
private def ryuPairs : Array (Float × Decimal) :=
  (d2sBasic ++ d2sSwitchToSubnormal ++ d2sMinAndMax ++ d2sLotsOfTrailingZeros
    ++ d2sRegression ++ d2sLooksLikePow5 ++ d2sOutputLength ++ d2sMinMaxShift
    ++ d2sSmallIntegers ++ f2sBasic ++ f2sSwitchToSubnormal ++ f2sMinAndMax
    ++ f2sBoundaryRoundEven ++ f2sExactValueRoundEven ++ f2sLotsOfTrailingZeros
    ++ f2sRegression ++ f2sLooksLikePow5 ++ f2sOutputLength ++ d2sExactTies).map
    (fun c => (c.2.1, c.2.2))

/-- Call the upstream entry point directly so compilation exercises its
    registration independently of the public reader wrappers. -/
private def scientificBits (d : Decimal) : UInt64 :=
  let x := Float.Model.ofScientific d.significand d.exponent
  (match d.sign with | .positive => x | .negative => -x).toBits

/-- Shortest decimals read back to their float, on every path. -/
private def roundTripMismatches : Array (Float × Decimal) := Id.run do
  let mut out := #[]
  for (f, d) in ryuPairs do
    let bits := f.toBits
    let live := Reader.ofDecimalBits d
    let exact := (Float.Model.pack (readExact d)).toBits
    let fast := let w := readFast d; if w = declined then exact else w
    if live != bits || scientificBits d != bits || exact != bits || fast != bits then
      out := out.push (f, d)
  return out

structure Rng where state : UInt64

private def Rng.next (r : Rng) : UInt64 × Rng :=
  let s := r.state + 0x9E3779B97F4A7C15
  let z := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31), ⟨s⟩)

/-- Hand-picked edges: ties, the overflow threshold, the subnormal floor,
    exact binary fractions, long significands. -/
private def edgeDecimals : Array Decimal := #[
  ⟨.positive, 0, 0⟩, ⟨.negative, 0, 5⟩, ⟨.positive, 5, -1⟩, ⟨.positive, 125, -1⟩, ⟨.positive, 25, -2⟩,
  ⟨.positive, 1, 0⟩, ⟨.positive, 3, 0⟩, ⟨.positive, 17976931348623157, 292⟩,
  ⟨.positive, 17976931348623158, 292⟩, ⟨.positive, 17976931348623159, 292⟩,
  ⟨.positive, 5, -324⟩, ⟨.positive, 2, -324⟩, ⟨.positive, 3, -324⟩,
  ⟨.positive, 24703282292062327, -340⟩, ⟨.positive, 24703282292062328, -340⟩,
  ⟨.positive, 22250738585072014, -324⟩, ⟨.positive, 22250738585072011, -324⟩,
  ⟨.positive, 9007199254740993, 0⟩, ⟨.positive, 9007199254740992, 0⟩, ⟨.positive, 9007199254740995, 0⟩,
  ⟨.positive, 1, 23⟩, ⟨.positive, 1, 308⟩, ⟨.positive, 1, 309⟩, ⟨.positive, 2, 308⟩,
  ⟨.positive, 18446744073709551615, 0⟩, ⟨.positive, 18446744073709551615, -20⟩,
  ⟨.positive, 12345678901234567890, 5⟩, ⟨.positive, 1, 54⟩, ⟨.positive, 1, 55⟩,
  ⟨.positive, 7, 54⟩, ⟨.positive, 7, 55⟩, ⟨.negative, 15, -1⟩,
  ⟨.positive, 4503599627370496, -1074⟩, ⟨.positive, 1, -325⟩, ⟨.positive, 10000000000000000000, -325⟩,
  ⟨.positive, 123456789012345678901234567890, -20⟩, ⟨.negative, 100000000000000000000000, -30⟩,
  ⟨.positive, 0, 2049⟩, ⟨.negative, 0, -2049⟩,
  ⟨.positive, 1, 2049⟩, ⟨.negative, 1, -2049⟩,
  ⟨.positive, 5 ^ 1075 - 1, -1075⟩, ⟨.negative, 5 ^ 1075, -1075⟩,
  ⟨.positive, 5 ^ 1075 + 1, -1075⟩,
  ⟨.positive, (2 ^ 54 - 1) * 2 ^ 970 - 1, 0⟩,
  ⟨.negative, (2 ^ 54 - 1) * 2 ^ 970, 0⟩,
  ⟨.positive, (2 ^ 54 - 1) * 2 ^ 970 + 1, 0⟩]

/-- Random `(m, e)` with one to twenty digits and `e ∈ [-340, 320]`. -/
private def randomDecimals (n : Nat) : Array Decimal := Id.run do
  let mut r : Rng := ⟨0x1234_5678_9ABC_DEF0⟩
  let mut out := #[]
  for _ in [0:n] do
    let (a, r1) := r.next
    let (b, r2) := r1.next
    let (c, r3) := r2.next
    r := r3
    let digits := (a % 20).toNat + 1
    let m := b.toNat % (10 ^ digits)
    let e : Int := ((c % 661).toNat : Int) - 340
    out := out.push ⟨if a % 2 = 0 then .positive else .negative, m, e⟩
  return out

/-- `(mismatches, fast-path answers)` over a corpus. -/
private def sweep (ds : Array Decimal) : Nat × Nat := Id.run do
  let mut bad := 0
  let mut fast := 0
  for d in ds do
    let ref := Reader.referenceBits d
    let exact := (Float.Model.pack (readExact d)).toBits
    let live := Reader.ofDecimalBits d
    if exact != ref || live != ref || scientificBits d != ref then bad := bad + 1
    let w := readFast d
    if w != declined then
      fast := fast + 1
      if w != ref then bad := bad + 1
  return (bad, fast)

def runTests : TestSeq :=
  let rt := roundTripMismatches
  let (badE, _) := sweep edgeDecimals
  let ds := randomDecimals 4000
  let (badR, fastR) := sweep ds
  test s!"Ryu-suite decimals read back to their floats ({ryuPairs.size} pairs)" (rt.isEmpty)
  ++ test "reader wrappers and upstream conversion agree at rounding boundaries" (badE = 0)
  ++ test "decimal literals and negation preserve both signs of zero"
      (ofDecimalBits (-0.0 : Decimal) == 0x8000000000000000
        && ofDecimalBits (-(-0.0 : Decimal)) == 0
        && ofDecimalBits (-(-(-0.0 : Decimal))) == 0x8000000000000000)
  ++ test s!"random decimals agree with the reference reader ({ds.size} cases, {fastR} on the fast path)"
      (badR = 0 && fastR * 10 ≥ ds.size * 9)

end Srtfp.Tests.Reader

/- Runtime probe of the `Float.toBits_ofBits` theorem.

Run: `lake env lean Test/FloatRuntime.lean`

Since Lean v4.33 the non-NaN bit round trip is proved over core's
`Float.Model` in `Srtfp/Bridge/Basic.lean`. This probe checks the compiled
runtime against that model on zeros, subnormals, normals, boundary values,
and infinities. NaN payloads are canonicalised to 0x7FF8000000000000,
which is why the theorem excludes them. These samples exercise the
runtime contract; they are not the proof of the universal theorem. -/

import Srtfp.Bridge.Basic
import Srtfp.Perf.Bits

/-- The NaN bit patterns: biased exponent `0x7FF` and a nonzero mantissa. -/
def isNaNPattern (x : UInt64) : Bool :=
  ((x >>> 52) &&& 0x7FF == 0x7FF) && (x &&& 0xF_FFFF_FFFF_FFFF != 0)

def nanProbes : List UInt64 :=
  [0x7FF0000000000001, 0x7FF8000000000000, 0xFFF8000000000000,
   0x7FFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF]

def nonNanProbes : List UInt64 :=
  [0x7FF0000000000000, 0xFFF0000000000000,     -- ±inf
   0x0000000000000001, 0x8000000000000000,     -- min subnormal, -0
   0x0000000000000000, 0x7FEFFFFFFFFFFFFF,     -- +0, max finite
   0x0010000000000000, 0x3FF0000000000000]     -- min normal, 1.0

/-- info: (true, true) -/
#guard_msgs in
#eval (nonNanProbes.all (fun x => (Float.ofBits x).toBits == x),
       nanProbes.all   (fun x => (Float.ofBits x).toBits == 0x7FF8000000000000))

-- `isNaNPattern` agrees with the observed round-trip split: `false` on
-- every probe that round-trips exactly, `true` on every probe that gets
-- canonicalised.
/-- info: (true, true) -/
#guard_msgs in
#eval (nonNanProbes.all (fun x => isNaNPattern x == false),
       nanProbes.all    (fun x => isNaNPattern x == true))

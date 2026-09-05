/- # Empirical probe of the `Float.toBits_ofBits` round-trip (once an axiom)

Run: `lake env lean SrtfpTest/RuntimeAxiomProbe.lean`

Finding (2026-07-02, x86-64 Linux, Lean 4.27.0): every non-NaN bit
pattern round-trips exactly (zeros, subnormals, normals, boundary
values, ±inf), but the runtime CANONICALISES NaN payloads — every NaN
pattern returns 0x7FF8000000000000. The naive axiom statement
(`∀ x : UInt64, (Float.ofBits x).toBits = x`) is therefore stronger
than the runtime warrants on NaN payloads.

Because `ofBits`/`toBits` are opaque to the logic this cannot make
Lean inconsistent; its cost is that theorems instantiated at NaN
patterns do not transfer to the running system. The printer rejects
NaN before any bit-level reasoning, so `correct_iff_toDecimal` needs
the axiom only on non-NaN patterns, where this probe shows it exact.

DONE (2026-07-02): the statement is restricted to non-NaN words. Since
v4.33 it is a theorem over core's `Float.Model`
(`Srtfp/Bridge/Basic.lean`); this probe checks the runtime against the
model. `isNaNPattern` (biased exponent `0x7FF` and mantissa nonzero, the
Perf tier's bit-level NaN test) is checked below to agree exactly with
the empirical NaN/non-NaN split observed above. -/

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

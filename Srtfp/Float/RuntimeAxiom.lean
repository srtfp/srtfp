/- IEEE-754 binary64 runtime axiom.

   `Float.toBits` and `Float.ofBits` are `@[extern]` runtime functions
   implemented by the Lean compiler against the host platform's IEEE-754
   binary64 representation. The naive inverse identity

     ∀ x : UInt64, (Float.ofBits x).toBits = x

   does *not* hold at every `x`: `SrtfpTest/RuntimeAxiomProbe.lean` empirically
   demonstrates that the runtime canonicalises NaN payloads — every NaN bit
   pattern `x` (biased exponent all-ones, mantissa nonzero) round-trips to
   the single canonical quiet-NaN pattern `0x7FF8000000000000`, not to `x`
   itself — while every non-NaN pattern (`isNaNPattern x = false`) round-trips
   exactly. The axiom below is restricted to that non-NaN domain, where it
   holds by the implementation contract: `Float.ofBits` simply
   `reinterpret_cast`s the 64 bits into the host's binary64 register, and
   `Float.toBits` is the reverse. This restricted identity still cannot be
   derived in pure Lean 4 because the Float type itself is opaque.

   This file isolates that single non-derivable identity as an audited
   axiom — nothing else lives here. The side-condition predicate
   `Float.isNaNPattern` is pure bit algebra and is defined in the
   axiom-free layer (`Srtfp/Float/Bits.lean`); the theorems that *consume*
   the axiom (e.g. `fromBits_proj`) live in the bridge tier
   (`Srtfp/Bridge/Basic.lean`). Importing this module (directly or via the
   `Srtfp.Bridge` umbrella) is the single opt-in for trusting the runtime
   contract. -/

import Srtfp.Float.Bits

namespace Float

/-- IEEE-754 binary64 bit round-trip, restricted to non-NaN bit patterns.
    Lean's `Float.toBits` and `Float.ofBits` are `@[extern]` runtime
    functions; this identity holds by the implementation but is not
    derivable in pure Lean 4. Taken on trust from the IEEE-754
    specification and Lean's runtime contract — and, on the NaN patterns
    excluded here, is empirically *false* (the runtime canonicalises NaN
    payloads to a single quiet NaN on the `ofBits` side); see
    `SrtfpTest/RuntimeAxiomProbe.lean`. -/
axiom toBits_ofBits : ∀ x : UInt64, isNaNPattern x = false → (Float.ofBits x).toBits = x

end Float

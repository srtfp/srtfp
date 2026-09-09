module
/- Bridge tier, ground floor: the bit round-trip `(Float.ofBits x).toBits = x`
   for every word that is not a NaN, a theorem over core's `Float.Model`
   (`Srtfp/Proofs/Model.lean`).

   Since Lean v4.33 `Float` is a structure around `Float.Model` (a `UInt64`
   whose NaNs are canonical) and `Float.ofBits`, `Float.toBits` are
   definitions over it; `@[extern]` only attaches the runtime
   implementation. So the round-trip is provable: `pack ∘ unpack` is the
   identity on valid words. What remains trusted is the compiler's
   `@[extern]` contract, as for every primitive type. The round-trip fails
   on NaN payloads (the runtime, like the model, canonicalises them; see
   `Test/FloatRuntime.lean`), hence the side condition. -/
public import Srtfp.Proofs.Model

@[expose] public section


/-- **The runtime bit round-trip**, for every word that is not a NaN. -/
theorem Float.toBits_ofBits (x : UInt64) (h : Srtfp.Spec.unpack x ≠ .notANumber) :
    (Float.ofBits x).toBits = x :=
  Srtfp.Model.toBits_ofBits x h

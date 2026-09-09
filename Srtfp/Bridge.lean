module
/- The `Float` tier of srtfp: the theorems of `Srtfp/Correctness.lean`
   attached to the runtime `Float` type (`Srtfp/Bridge/Correctness.lean`).

   `import Srtfp` certifies both the bit-pattern and runtime entry points
   using a specification over all binary64 words. This tier gives the
   equivalent specification with competitors quantified over `Float`,
   using the bit round-trip
   `Float.toBits_ofBits` (`Srtfp/Bridge/Basic.lean`): `(Float.ofBits x).toBits
   = x` for every non-NaN pattern, a theorem over core's `Float.Model`. No
   axiom is involved; what is trusted is that the compiled `Float.ofBits`
   and `Float.toBits` implement their definitions, the `@[extern]` contract
   every primitive carries. -/
public import Srtfp
public import Srtfp.Bridge.Basic
public import Srtfp.Bridge.Correctness

@[expose] public section

/- The `Float` tier of srtfp — OPT-IN for the runtime axiom.

   `import Srtfp` alone is fully axiom-free: every definition and theorem
   there (including the flagship certification in `Srtfp/Correctness.lean`)
   depends only on `propext`, `Classical.choice`, and `Quot.sound`, and
   speaks about IEEE-754 binary64 *bit patterns* (`UInt64` words).

   Importing THIS module additionally admits the single restricted runtime
   axiom `Float.toBits_ofBits` (`Srtfp/Float/RuntimeAxiom.lean`):
   `(Float.ofBits x).toBits = x` for every non-NaN pattern `x` — the
   IEEE-754 implementation contract of Lean's opaque `Float` type, not
   derivable in pure Lean, empirically probed by
   `SrtfpTest/RuntimeAxiomProbe.lean` (NaN payloads are canonicalised,
   which is why the axiom is restricted). In exchange the certification
   statements attach to the runtime `Float` type itself
   (`Srtfp/Bridge/Correctness.lean`). -/

import Srtfp
import Srtfp.Float.RuntimeAxiom
import Srtfp.Bridge.Basic
import Srtfp.Bridge.Clinger
import Srtfp.Bridge.Correctness

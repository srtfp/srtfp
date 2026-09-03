/- srtfp performance tier — OPT-IN.

   Everything under `Srtfp/Perf/` is runtime acceleration: fixed-width
   `UInt64` kernels, precomputed power tables, fused string emitters, and
   the proofs that each one is pointwise equal to the reference function
   it replaces. Importing this module registers those equalities as
   `@[csimp]` rewrites, so natively compiled callers of `toDecimal`,
   `Decimal.mk'`, and friends run the fast kernels.

   Nothing here is needed for correctness. `import Srtfp` alone gives
   the reference implementation and its certification; deleting this
   directory (and this file) leaves that tier intact, only slower. -/

import Srtfp.Perf.Schubfach
import Srtfp.Perf.SchubfachEq
import Srtfp.Perf.DecimalFast
import Srtfp.Perf.MulHigh128
import Srtfp.Perf.Pow10Table
import Srtfp.Perf.Pow10Table128
import Srtfp.Perf.Pow10Table192
import Srtfp.Perf.TableInvariant
import Srtfp.Perf.TableInvariant192
import Srtfp.Perf.Kernel128Defs
import Srtfp.Perf.Kernel192
import Srtfp.Perf.KernelCorrectness
import Srtfp.Perf.Kernel128
import Srtfp.Perf.Kernel192Correctness
import Srtfp.Perf.KernelSupport
import Srtfp.Perf.KernelR20
import Srtfp.Perf.KernelV5
import Srtfp.Perf.KernelV6
import Srtfp.Perf.KernelV13
import Srtfp.Perf.Orchestration
import Srtfp.Perf.R20BandSweep
import Srtfp.Perf.R20Continuant
import Srtfp.Perf.R20Keystone
import Srtfp.Perf.R20Legendre
import Srtfp.Perf.StringFast
import Srtfp.Perf.DigitsFast
import Srtfp.Perf.Uint64Bridge
import Srtfp.Perf.Uint64Kernel
import Srtfp.Perf.Uint64Kernel192

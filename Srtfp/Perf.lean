module
/- srtfp performance tier — OPT-IN.

   Everything under `Srtfp/Perf/` is runtime acceleration: the Schubfach
   algorithm (kernel 0, `Perf/Schubfach.lean`, equal to the reference by
   `Perf/SchubfachEq.lean`), its fixed-width `UInt64` kernels, precomputed
   power tables, fused string emitters, the bit-field view of a word the
   kernels work on (`Perf/Bits.lean`, related to the model's `unpack` in
   `Perf/Unpack.lean`), and the proofs that each one is pointwise equal
   to the function it replaces. Importing this module
   registers those equalities as `@[csimp]` rewrites, so natively
   compiled callers of `Printer.toDecimal`, `Decimal.mk'`, and friends run
   the fast kernels.

   Nothing here is needed for correctness. `import Srtfp` alone gives
   the reference implementation and its certification; deleting this
   directory (and this file) leaves that tier intact, only slower. -/

public import Srtfp.Perf.Schubfach
public import Srtfp.Perf.SchubfachEq
public import Srtfp.Perf.DecimalFast
public import Srtfp.Perf.MulHigh128
public import Srtfp.Perf.Pow10Table
public import Srtfp.Perf.Pow10Table128
public import Srtfp.Perf.Pow10Table192
public import Srtfp.Perf.TableInvariant
public import Srtfp.Perf.TableInvariant192
public import Srtfp.Perf.Kernel128Defs
public import Srtfp.Perf.Kernel192
public import Srtfp.Perf.KernelCorrectness
public import Srtfp.Perf.Kernel128
public import Srtfp.Perf.Kernel192Correctness
public import Srtfp.Perf.KernelSupport
public import Srtfp.Perf.KernelR20
public import Srtfp.Perf.KernelV5
public import Srtfp.Perf.KernelV6
public import Srtfp.Perf.KernelV13
public import Srtfp.Perf.Orchestration
public import Srtfp.Perf.R20BandSweep
public import Srtfp.Perf.R20Continuant
public import Srtfp.Perf.R20Keystone
public import Srtfp.Perf.R20Legendre
public import Srtfp.Perf.StringFast
public import Srtfp.Perf.DigitsFast
public import Srtfp.Perf.Uint64Bridge
public import Srtfp.Perf.Uint64Kernel
public import Srtfp.Perf.Uint64Kernel192

@[expose] public section

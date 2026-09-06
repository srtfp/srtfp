module
/- srtfp performance tier — OPT-IN.

   Everything under `Srtfp/Perf/` is runtime acceleration: the Schubfach
   printer (`Perf/Schubfach/`, the paper's algorithm on 64-bit words with
   its proof, results R1–R25), the reader's fixed-width fast path
   (`Perf/ReadFast.lean`), the string emitter (`Perf/StringFast.lean`),
   the `Decimal` helpers (`Perf/DecimalFast.lean`, `Perf/CanonFast.lean`),
   the bit-field view of a word the kernels work on (`Perf/Bits.lean`,
   related to the model's `unpack` in `Perf/Unpack.lean`), and the proofs
   that each one is pointwise equal to the function it replaces. Importing
   this module registers those equalities as `@[csimp]` rewrites, so
   natively compiled callers of `Printer.toDecimal`, `Decimal.mk'`, and
   friends run the fast paths.

   Nothing here is needed for correctness. `import Srtfp` alone gives the
   reference implementation and its certification; deleting this directory
   (and this file) leaves that tier intact, only slower. -/

public import Srtfp.Perf.Schubfach
public import Srtfp.Perf.Schubfach.R14R15
public import Srtfp.Perf.Schubfach.Exact
public import Srtfp.Perf.Schubfach.RoundOdd
public import Srtfp.Perf.Schubfach.Table
public import Srtfp.Perf.Schubfach.Continuant
public import Srtfp.Perf.Schubfach.Legendre
public import Srtfp.Perf.Schubfach.Keystone
public import Srtfp.Perf.Schubfach.NadezhinDefs
public import Srtfp.Perf.Schubfach.NadezhinBands
public import Srtfp.Perf.Schubfach.NadezhinSweep1
public import Srtfp.Perf.Schubfach.NadezhinSweep2
public import Srtfp.Perf.Schubfach.NadezhinSweep3
public import Srtfp.Perf.Schubfach.NadezhinSweep4
public import Srtfp.Perf.Schubfach.Nadezhin
public import Srtfp.Perf.Schubfach.Product
public import Srtfp.Perf.Schubfach.Tests
public import Srtfp.Perf.Schubfach.Estimate
public import Srtfp.Perf.Schubfach.Index
public import Srtfp.Perf.Schubfach.Kernel
public import Srtfp.Perf.Schubfach.Entry
public import Srtfp.Perf.DecimalFast
public import Srtfp.Perf.CanonFast
public import Srtfp.Perf.MulHigh128
public import Srtfp.Perf.Pow10Table128
public import Srtfp.Perf.TableInvariant
public import Srtfp.Perf.StringFast
public import Srtfp.Perf.Bits
public import Srtfp.Perf.BitsLemmas
public import Srtfp.Perf.Unpack
public import Srtfp.Perf.Tactics
public import Srtfp.Perf.ReadExact
public import Srtfp.Perf.ReadFast

@[expose] public section

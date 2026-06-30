/- srtfp: a verified shortest round-trip float printer (and parser).

   Schubfach-based binary64 shortest-round-trip printing and
   Clinger-style correctly-rounded parsing, with the round-trip
   theorem proven at the `.toBits` level. Factored out of the
   QuadParsers biparser library; declarations currently live in the
   `PP.Numeric` namespace pending a rename. -/

import Srtfp.Numeric.Clinger
import Srtfp.Numeric.Correctness
import Srtfp.Numeric.Decimal.Instances
import Srtfp.Numeric.Decimal
import Srtfp.Numeric.Decimal.Perf.Fast
import Srtfp.Numeric.DecimalSyntax
import Srtfp.Numeric.Float.Bits
import Srtfp.Numeric.Float.Rep
import Srtfp.Numeric.Float.RuntimeAxiom
import Srtfp.Numeric.Schubfach.Kernel192
import Srtfp.Numeric.Schubfach.KernelCorrectness
import Srtfp.Numeric.Schubfach
import Srtfp.Numeric.Schubfach.MulHigh128
import Srtfp.Numeric.Schubfach.Perf.CsimpPin
import Srtfp.Numeric.Schubfach.Perf.dead.PackedB64
import Srtfp.Numeric.Schubfach.Perf.DigitsFast
import Srtfp.Numeric.Schubfach.Perf.Kernel128
import Srtfp.Numeric.Schubfach.Perf.Kernel192Correctness
import Srtfp.Numeric.Schubfach.Perf.KernelR20
import Srtfp.Numeric.Schubfach.Perf.KernelV10
import Srtfp.Numeric.Schubfach.Perf.KernelV11
import Srtfp.Numeric.Schubfach.Perf.KernelV12
import Srtfp.Numeric.Schubfach.Perf.KernelV13
import Srtfp.Numeric.Schubfach.Perf.KernelV5
import Srtfp.Numeric.Schubfach.Perf.KernelV6
import Srtfp.Numeric.Schubfach.Perf.KernelV9
import Srtfp.Numeric.Schubfach.Perf.Orchestration
import Srtfp.Numeric.Schubfach.Perf.Pow10Table192
import Srtfp.Numeric.Schubfach.Perf.StringFast
import Srtfp.Numeric.Schubfach.Perf.TableInvariant192
import Srtfp.Numeric.Schubfach.Perf.Uint64Bridge
import Srtfp.Numeric.Schubfach.Perf.Uint64Kernel192
import Srtfp.Numeric.Schubfach.Perf.Uint64Kernel
import Srtfp.Numeric.Schubfach.Pow10Table128
import Srtfp.Numeric.Schubfach.Pow10Table
import Srtfp.Numeric.Schubfach.R20BandSweep
import Srtfp.Numeric.Schubfach.R20Keystone
import Srtfp.Numeric.Schubfach.R20Legendre
import Srtfp.Numeric.Schubfach.R20Sweep
import Srtfp.Numeric.Schubfach.TableInvariant
import Srtfp.Proofs.Numeric.Clinger.Base
import Srtfp.Proofs.Numeric.Clinger.Bridge
import Srtfp.Proofs.Numeric.Clinger.Dispatch
import Srtfp.Proofs.Numeric.Clinger.FindBinaryExp
import Srtfp.Proofs.Numeric.Clinger.IrregularCarry
import Srtfp.Proofs.Numeric.Clinger.IrregularNoCarry
import Srtfp.Proofs.Numeric.Clinger
import Srtfp.Proofs.Numeric.Clinger.Regular
import Srtfp.Proofs.Numeric.Correctness
import Srtfp.Proofs.Numeric.CorrectnessSpec
import Srtfp.Proofs.Numeric.Decimal
import Srtfp.Proofs.Numeric.Disjointness
import Srtfp.Proofs.Numeric.ReaderCorrectness
import Srtfp.Proofs.Numeric.RoundTrip
import Srtfp.Proofs.Numeric.Schubfach.K
import Srtfp.Proofs.Numeric.Schubfach.Minimal
import Srtfp.Proofs.Numeric.Schubfach.PickNearer
import Srtfp.Proofs.Numeric.Schubfach.R14R15
import Srtfp.Proofs.Numeric.Schubfach.RoundingInterval
import Srtfp.Proofs.Numeric.Schubfach.ShiftedSig
import Srtfp.Proofs.Numeric.Schubfach.Shorter
import Srtfp.Proofs.Numeric.Schubfach.Shortest
import Srtfp.Proofs.Numeric.Schubfach.TieBreak
import Srtfp.Proofs.Numeric.Schubfach.ToDecimal

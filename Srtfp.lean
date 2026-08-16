/- srtfp: a verified shortest round-trip float printer (and parser).

   Schubfach-based binary64 shortest-round-trip printing and
   Clinger-style correctly-rounded parsing, with the round-trip
   theorem proven at the `.toBits` level. Factored out of the
   QuadParsers biparser library. -/

import Srtfp.Clinger
import Srtfp.Rat
import Srtfp.NatLog
import Srtfp.Correctness
import Srtfp.Decimal.Instances
import Srtfp.Decimal
import Srtfp.Decimal.Perf.Fast
import Srtfp.DecimalSyntax
import Srtfp.Float.Bits
import Srtfp.Float.RuntimeAxiom
import Srtfp.Proofs.Clinger.Base
import Srtfp.Proofs.Clinger.Bridge
import Srtfp.Proofs.Clinger.Dispatch
import Srtfp.Proofs.Clinger.FindBinaryExp
import Srtfp.Proofs.Clinger.IrregularCarry
import Srtfp.Proofs.Clinger.IrregularNoCarry
import Srtfp.Proofs.Clinger
import Srtfp.Proofs.Clinger.Regular
import Srtfp.Proofs.Correctness
import Srtfp.Proofs.CorrectnessSpec
import Srtfp.Proofs.Decimal
import Srtfp.Proofs.Disjointness
import Srtfp.Proofs.ReaderCorrectness
import Srtfp.Proofs.RoundTrip
import Srtfp.Proofs.Schubfach.K
import Srtfp.Proofs.Schubfach.Minimal
import Srtfp.Proofs.Schubfach.PickNearer
import Srtfp.Proofs.Schubfach.R14R15
import Srtfp.Proofs.Schubfach.RoundingInterval
import Srtfp.Proofs.Schubfach.ShiftedSig
import Srtfp.Proofs.Schubfach.Shorter
import Srtfp.Proofs.Schubfach.Shortest
import Srtfp.Proofs.Schubfach.TieBreak
import Srtfp.Proofs.Schubfach.ToDecimal
import Srtfp.Schubfach.Kernel192
import Srtfp.Schubfach.KernelCorrectness
import Srtfp.Tactics
import Srtfp.Schubfach
import Srtfp.Schubfach.MulHigh128
import Srtfp.Schubfach.Perf.CsimpPin
import Srtfp.Schubfach.Perf.DigitsFast
import Srtfp.Schubfach.Perf.Kernel128
import Srtfp.Schubfach.Perf.Kernel192Correctness
import Srtfp.Schubfach.Perf.KernelR20
import Srtfp.Schubfach.Perf.KernelSupport
import Srtfp.Schubfach.Perf.KernelV13
import Srtfp.Schubfach.Perf.KernelV5
import Srtfp.Schubfach.Perf.KernelV6
import Srtfp.Schubfach.Perf.Orchestration
import Srtfp.Schubfach.Perf.Pow10Table192
import Srtfp.Schubfach.Perf.StringFast
import Srtfp.Schubfach.Perf.TableInvariant192
import Srtfp.Schubfach.Perf.Uint64Bridge
import Srtfp.Schubfach.Perf.Uint64Kernel192
import Srtfp.Schubfach.Perf.Uint64Kernel
import Srtfp.Schubfach.Pow10Table128
import Srtfp.Schubfach.Pow10Table
import Srtfp.Schubfach.R20BandSweep
import Srtfp.Schubfach.R20Continuant
import Srtfp.Schubfach.R20Keystone
import Srtfp.Schubfach.R20Legendre
import Srtfp.Schubfach.TableInvariant

/- srtfp: a verified shortest round-trip float printer (and parser).

   Schubfach-based binary64 shortest-round-trip printing and
   Clinger-style correctly-rounded parsing, with the round-trip
   theorem proven at the `.toBits` level.

   This umbrella is the reference tier: the definitions, the proof
   stack, and the certification in `Srtfp/Correctness.lean`. It is
   axiom-free beyond `propext` / `Quot.sound` / `Classical.choice`.
   Two further tiers are opt-in:

     - `Srtfp.Perf`   — verified runtime fast paths (`@[csimp]`);
     - `Srtfp.Bridge` — the same theorems on the runtime `Float` type,
                        admitting the single axiom `Float.toBits_ofBits`. -/

import Srtfp.Decimal
import Srtfp.DecimalSyntax
import Srtfp.Float.Bits
import Srtfp.Clinger
import Srtfp.Printer
import Srtfp.Schubfach
import Srtfp.Rat
import Srtfp.NatLog
import Srtfp.Tactics
import Srtfp.Proofs.Clinger.Base
import Srtfp.Proofs.Clinger.Bridge
import Srtfp.Proofs.Clinger.Dispatch
import Srtfp.Proofs.Clinger.FindBinaryExp
import Srtfp.Proofs.Clinger.IrregularCarry
import Srtfp.Proofs.Clinger.IrregularNoCarry
import Srtfp.Proofs.Clinger.Regular
import Srtfp.Proofs.Clinger
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
import Srtfp.Proofs.Bits
import Srtfp.Proofs.Decimal
import Srtfp.Proofs.Decimal.Canonical
import Srtfp.Proofs.Disjointness
import Srtfp.Proofs.RoundTrip
import Srtfp.Proofs.ReaderCorrectness
import Srtfp.Proofs.CorrectnessSpec
import Srtfp.Proofs.Correctness
import Srtfp.Correctness
import Srtfp.Text
import Srtfp.Text.Roundtrip

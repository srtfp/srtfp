module
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

public import Srtfp.Decimal
public import Srtfp.DecimalSyntax
public import Srtfp.Float.Bits
public import Srtfp.Clinger
public import Srtfp.Printer
public import Srtfp.Rat
public import Srtfp.NatLog
public import Srtfp.Tactics
public import Srtfp.Proofs.Clinger.Base
public import Srtfp.Proofs.Clinger.Bridge
public import Srtfp.Proofs.Clinger.Dispatch
public import Srtfp.Proofs.Clinger.FindBinaryExp
public import Srtfp.Proofs.Clinger.IrregularCarry
public import Srtfp.Proofs.Clinger.IrregularNoCarry
public import Srtfp.Proofs.Clinger.Regular
public import Srtfp.Proofs.Clinger
public import Srtfp.Proofs.Bits
public import Srtfp.Proofs.Decimal
public import Srtfp.Proofs.Decimal.Canonical
public import Srtfp.Proofs.Disjointness
public import Srtfp.Proofs.ReaderCorrectness
public import Srtfp.Proofs.CorrectnessSpec
public import Srtfp.Proofs.Clinger.NatIntervalDefs
public import Srtfp.Proofs.Clinger.Interface
public import Srtfp.Proofs.Printer.Vocab
public import Srtfp.Proofs.Printer.Interval
public import Srtfp.Proofs.Printer.Grid
public import Srtfp.Proofs.Printer.Length
public import Srtfp.Proofs.Printer.Scan
public import Srtfp.Proofs.Printer.Spec
public import Srtfp.Spec
public import Srtfp.Proofs.ReaderSpec
public import Srtfp.Correctness
public import Srtfp.Text
public import Srtfp.Text.Roundtrip

@[expose] public section

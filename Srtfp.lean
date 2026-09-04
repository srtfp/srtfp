module
/- srtfp: a verified shortest round-trip float printer (and parser).

   Shortest-round-trip binary64 printing and correctly-rounded
   parsing, with the correctness theorems proven at the `.toBits`
   level.

   This umbrella is the reference tier: the definitions, the proof
   stack, and the certification in `Srtfp/Correctness.lean`. It is
   axiom-free beyond `propext` / `Quot.sound` / `Classical.choice`.
   Two further tiers are opt-in:

     - `Srtfp.Perf`   — verified runtime fast paths (`@[csimp]`);
     - `Srtfp.Bridge` — the same theorems on the runtime `Float` type,
                        across the bit round-trip proven over core's
                        `Float.Model` (`Srtfp/Float/Model.lean`). -/

public import Srtfp.Decimal
public import Srtfp.DecimalSyntax
public import Srtfp.Float.Bits
public import Srtfp.Clinger
public import Srtfp.Printer
public import Srtfp.Rat
public import Srtfp.NatLog
public import Srtfp.Proofs.Bits
public import Srtfp.Proofs.Decimal
public import Srtfp.Proofs.Decimal.Canonical
public import Srtfp.Proofs.Reader.Round
public import Srtfp.Proofs.Reader.Words
public import Srtfp.Proofs.Reader.Compute
public import Srtfp.Proofs.Reader.Nearest
public import Srtfp.Proofs.Reader.Spec
public import Srtfp.Proofs.Printer.Vocab
public import Srtfp.Proofs.Printer.Interval
public import Srtfp.Proofs.Printer.Grid
public import Srtfp.Proofs.Printer.Length
public import Srtfp.Proofs.Printer.Scan
public import Srtfp.Proofs.Printer.Spec
public import Srtfp.Spec
public import Srtfp.Correctness
public import Srtfp.Text
public import Srtfp.Proofs.Text

@[expose] public section

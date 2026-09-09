module
/- srtfp: a verified shortest round-trip float printer (and parser).

   Shortest-round-trip binary64 printing and correctly-rounded
   parsing, with the correctness theorems proven at the `.toBits`
   level.

   This umbrella is the reference tier: the definitions, the proof
   stack, and the certification in `Srtfp/Correctness.lean`. It is
   axiom-free beyond `propext` / `Quot.sound` / `Classical.choice`.
   Both the bit-pattern and runtime `Float` APIs satisfy the same
   specification. `Srtfp.Perf` adds verified runtime fast paths
   (`@[csimp]`) as an opt-in import. -/

public import Srtfp.Spec
public import Srtfp.Decimal
public import Srtfp.DecimalSyntax
public import Srtfp.Reader
public import Srtfp.Printer
public import Srtfp.Rat
public import Srtfp.Proofs.Model
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
public import Srtfp.Correctness
public import Srtfp.Text
public import Srtfp.Text.Float
public import Srtfp.Proofs.Text
public import Srtfp.Text.Correctness

@[expose] public section

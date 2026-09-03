module
/- The two correctness theorems, one per direction: a function is a
   correct reader iff it is `Clinger.ofDecimalBits` (`Srtfp/Clinger.lean`),
   and a correct printer iff it is `Printer.toDecimalBits`
   (`Srtfp/Printer.lean`). Correctness is defined in `Srtfp/Spec.lean`; the
   proofs are `Srtfp/Proofs/ReaderSpec.lean` and
   `Srtfp/Proofs/Printer/Spec.lean`.

   The same theorems on the runtime `Float` type are derived in
   `Srtfp/Bridge/Correctness.lean`; those additionally admit the single
   restricted runtime axiom `Float.toBits_ofBits`
   (see `Srtfp/Float/RuntimeAxiom.lean`). -/

public import Srtfp.Spec
public import Srtfp.Printer
public import Srtfp.Proofs.ReaderSpec
public import Srtfp.Proofs.Printer.Spec

@[expose] public section

namespace Srtfp.Spec

open Compat Float

/-- **A function is a correct reader iff it is `Clinger.ofDecimalBits`**,
bit for bit. -/
theorem correct_iff_ofDecimal (p : Decimal → UInt64) :
    CorrectReader p ↔ ∀ d : Decimal, p d = Clinger.ofDecimalBits d :=
  Clinger.correctReader_iff_ofDecimal p

/-- **A function is a correct printer iff it is `Printer.toDecimalBits`.**
The forward direction gives uniqueness (nothing else satisfies the spec);
the backward direction gives correctness (`toDecimalBits` satisfies it). -/
theorem correct_iff_toDecimal (p : UInt64 → Except String Decimal) :
    CorrectPrinter p ↔ p = Printer.toDecimalBits :=
  Printer.correctPrinter_iff_toDecimal p

/-- For each finite word, **exactly one** decimal is the shortest: the one
`Printer.toDecimalBits` returns. -/
theorem shortest_decimal_exists_unique (w : UInt64) (h_fin : Word.isFinite w) :
    ∃! d : Decimal, ShortestDecimal w d :=
  Printer.shortestDecimal_exists_unique w h_fin

end Srtfp.Spec

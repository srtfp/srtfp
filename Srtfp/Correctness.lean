module
/- The two correctness theorems, one per direction: a function is a
   correct reader iff it is `Reader.ofDecimalBits` (`Srtfp/Reader.lean`),
   and a correct printer iff it is `Printer.toDecimalBits`
   (`Srtfp/Printer.lean`). Correctness is defined in `Srtfp/Spec.lean`; the
   proofs are `Srtfp/Proofs/Reader/Spec.lean` and
   `Srtfp/Proofs/Printer/Spec.lean`.

   The same theorems on the runtime `Float` type are derived in
   `Srtfp/Bridge/Correctness.lean`; those cross to `Float` through the
   bit round-trip `Float.toBits_ofBits`, a theorem over core's
   `Float.Model` (`Srtfp/Bridge/Basic.lean`). -/

public import Srtfp.Spec
public import Srtfp.Reader
public import Srtfp.Printer
public import Srtfp.Proofs.Reader.Spec
public import Srtfp.Proofs.Printer.Spec

@[expose] public section

namespace Srtfp.Spec


/-- **A function is a correct reader iff it is `Reader.ofDecimalBits`**,
bit for bit. -/
theorem correct_iff_ofDecimal (p : Decimal → UInt64) :
    CorrectReader p ↔ ∀ d : Decimal, p d = Reader.ofDecimalBits d :=
  Reader.correctReader_iff_ofDecimal p

/-- **A function is a correct printer iff it is `Printer.toDecimalBits`.**
The forward direction gives uniqueness (nothing else satisfies the spec);
the backward direction gives correctness (`toDecimalBits` satisfies it). -/
theorem correct_iff_toDecimal (p : UInt64 → Option Decimal) :
    CorrectPrinter p ↔ p = Printer.toDecimalBits :=
  Printer.correctPrinter_iff_toDecimal p

/-- For each finite word, **exactly one** decimal is the shortest: the one
`Printer.toDecimalBits` returns. -/
theorem shortest_decimal_exists_unique (w : UInt64) (h_fin : (unpack w).isFinite) :
    ∃ d : Decimal, ShortestDecimal w d ∧ ∀ d' : Decimal, ShortestDecimal w d' → d' = d :=
  Printer.shortestDecimal_exists_unique w h_fin

end Srtfp.Spec

module
/- The printer meets the upstream-model specification, which uniquely
   determines its behavior. Runtime Float results satisfy the same
   specification through their bit patterns. -/

public import Srtfp.Spec
public import Srtfp.Printer
public import Srtfp.Proofs.Printer.Spec

@[expose] public section

namespace Srtfp.Spec

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

/-- The runtime printer rejects precisely the non-finite inputs. Every
successful result is the canonical, shortest, closest, ties-to-even decimal
from the same bit-level specification. -/
theorem toDecimal_spec (f : Float) :
    match Printer.toDecimal f with
    | none => (unpack f.toBits).isFinite = false
    | some d => (unpack f.toBits).isFinite = true ∧ ShortestDecimal f.toBits d := by
  have hp := (correct_iff_toDecimal Printer.toDecimalBits).mpr rfl
  cases hf : (unpack f.toBits).isFinite with
  | false => simp [Printer.toDecimal_eq_bits, hp.special _ hf]
  | true =>
    obtain ⟨d, hd, hs⟩ := hp.finite _ hf
    simpa [Printer.toDecimal_eq_bits, hd, hf] using hs

end Srtfp.Spec

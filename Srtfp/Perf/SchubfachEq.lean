module
/- Kernel 0 of the Perf chain: the Nat-form Schubfach printer equals the
   reference. Derived from the specification's uniqueness for now (both
   satisfy it); the direct proof, the paper's R8–R12, is the backburner
   item of the design doc. -/
public import Srtfp.Correctness
public import Srtfp.Perf.Schubfach.Correctness

@[expose] public section

open Srtfp.Compat

namespace Srtfp.Schubfach

open Srtfp Srtfp.Float

private theorem spec_wordVal_eq {w : UInt64} (hw : Word.isFinite w = true) :
    Spec.wordVal w = wordVal w := by
  rw [Srtfp.Float.wordVal_eq hw]; rfl

private theorem spec_dist_eq (d : Decimal) {w : UInt64} (hw : Word.isFinite w = true) :
    Spec.dist d w = |Decimal.toRat d - wordVal w| := by
  unfold Spec.dist; rw [spec_wordVal_eq hw, abs_sub_comm]; rfl

/-- The old conjunction-form correctness predicate implies the spec's. -/
theorem correctPrinter_of_bits {p : UInt64 → Except String Decimal}
    (h : IsCorrectPrinterBits p) : Spec.CorrectPrinter p where
  nan w hw := (h w).1 ((unpack_eq_nan_iff w).mp hw)
  inf w s hw := by
    obtain ⟨hi, hs⟩ := (unpack_eq_inf_iff w s).mp hw
    rw [(h w).2.1 hi, hs]
    cases Word.signBit w <;> rfl
  finite w hw := by
    have hw' := (isFinite_iff w).mp hw
    obtain ⟨d, hd, hc, hrt, hs⟩ := (h w).2.2 hw'
    refine ⟨d, hd, hc, (Clinger.readsTo_iff d w).mpr hrt, fun d' hne hc' hrt' => ?_⟩
    rcases hs d' hne hc' ((Clinger.readsTo_iff d' w).mp hrt') with h1 | ⟨h1, h2 | ⟨h2, h3⟩⟩
    · exact .shorter (by rwa [decDigitLength_eq_digits, decDigitLength_eq_digits] at h1)
    · exact .closer (by rwa [decDigitLength_eq_digits, decDigitLength_eq_digits] at h1)
        (by rw [spec_dist_eq _ hw', spec_dist_eq _ hw']; exact h2)
    · exact .even (by rwa [decDigitLength_eq_digits, decDigitLength_eq_digits] at h1)
        (by rw [spec_dist_eq _ hw', spec_dist_eq _ hw']; exact h2) h3

theorem toDecimalBits_eq_printer : Schubfach.toDecimalBits = Printer.toDecimalBits :=
  (Srtfp.Spec.correct_iff_toDecimal Schubfach.toDecimalBits).mp
    (correctPrinter_of_bits correctness_proof)

theorem toDecimal_eq_printer : Schubfach.toDecimal = Printer.toDecimal :=
  funext fun f => congrArg (· f.toBits) toDecimalBits_eq_printer

end Srtfp.Schubfach

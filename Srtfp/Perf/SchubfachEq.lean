/- Kernel 0 of the Perf chain: the Nat-form Schubfach printer equals the
   reference. Derived from the specification's uniqueness for now (both
   satisfy it); the direct proof, the paper's R8–R12, is the backburner
   item of the design doc. -/
import Srtfp.Correctness
import Srtfp.Perf.Schubfach.Correctness

namespace Srtfp.Schubfach

theorem toDecimalBits_eq_printer : Schubfach.toDecimalBits = Printer.toDecimalBits :=
  (Srtfp.Spec.correct_iff_toDecimal Schubfach.toDecimalBits).mp
    ((Schubfach.correct_iff_toDecimal_proof Schubfach.toDecimalBits).mpr rfl)

theorem toDecimal_eq_printer : Schubfach.toDecimal = Printer.toDecimal :=
  funext fun f => congrArg (· f.toBits) toDecimalBits_eq_printer

end Srtfp.Schubfach

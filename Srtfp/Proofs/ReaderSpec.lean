module
/- The reader meets `Srtfp/Spec.lean`: a structured restatement of
   `correct_iff_ofDecimal_proof` from `ReaderCorrectness.lean`, whose
   vocabulary is the older conjunction form. -/
public import Srtfp.Spec
public import Srtfp.Proofs.ReaderCorrectness

@[expose] public section

open Srtfp.Compat

namespace Srtfp.Clinger

open Srtfp Srtfp.Float

theorem spec_wordVal_eq (w : UInt64) : Spec.wordVal w = Schubfach.wordVal w := by
  unfold Spec.wordVal Schubfach.wordVal Schubfach.magVal Spec.val
  rfl

theorem spec_toRat_eq (d : Decimal) : Spec.toRat d = Decimal.toRat d := rfl

theorem spec_dist_eq (d : Decimal) (w : UInt64) :
    Spec.dist d w = |Schubfach.wordVal w - Decimal.toRat d| := by
  unfold Spec.dist; rw [spec_wordVal_eq, spec_toRat_eq]

theorem nearestWord_iff (d : Decimal) (w : UInt64) :
    Spec.NearestWord d w ↔ IsNearestWord d w := by
  constructor
  · intro h
    refine ⟨h.finite, h.sign, fun v hv => ?_, fun v hv hne heq => ?_⟩
    · have := (h.nearest v hv).1
      rwa [spec_dist_eq, spec_dist_eq] at this
    · exact (h.nearest v hv).2 (by rwa [spec_wordVal_eq, spec_wordVal_eq])
        (by rw [spec_dist_eq, spec_dist_eq]; exact heq)
  · rintro ⟨hf, hs, h1, h2⟩
    refine ⟨hf, hs, fun v hv => ⟨?_, fun hne heq => ?_⟩⟩
    · rw [spec_dist_eq, spec_dist_eq]; exact h1 v hv
    · exact h2 v hv (by rwa [← spec_wordVal_eq, ← spec_wordVal_eq])
        (by rw [spec_dist_eq, spec_dist_eq] at heq; exact heq)

theorem correctReader_iff (p : Decimal → UInt64) :
    Spec.CorrectReader p ↔ IsCorrectReaderBits p := by
  constructor
  · intro h d
    exact ⟨fun hd => (nearestWord_iff _ _).mp (h.inRange d (by rwa [spec_toRat_eq])),
           fun hd => h.overflow d (by rwa [spec_toRat_eq])⟩
  · intro h
    exact ⟨fun d hd => (nearestWord_iff _ _).mpr ((h d).1 (by rwa [spec_toRat_eq] at hd)),
           fun d hd => (h d).2 (by rwa [spec_toRat_eq] at hd)⟩

/-- **The reader theorem**, in the vocabulary of `Srtfp/Spec.lean`. -/
theorem correctReader_iff_ofDecimal (p : Decimal → UInt64) :
    Spec.CorrectReader p ↔ ∀ d : Decimal, p d = Clinger.ofDecimalBits d :=
  (correctReader_iff p).trans (correct_iff_ofDecimal_proof p)

end Srtfp.Clinger

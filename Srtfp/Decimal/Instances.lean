/- Canonicalisation lemmas for Decimal. -/

import Srtfp.Decimal

namespace Srtfp.Decimal

/-! ## Unfolding lemmas for `canonicaliseAux` -/

theorem canonicaliseAux_not_div (s : Nat) (e : Int) (hs : s ≠ 0) (h10 : s % 10 ≠ 0) :
    canonicaliseAux s e = (s, e) := by
  rw [canonicaliseAux.eq_def, dif_neg hs, if_neg h10]

theorem canonicaliseAux_div (s : Nat) (e : Int) (hs : s ≠ 0) (h10 : s % 10 = 0) :
    canonicaliseAux s e = canonicaliseAux (s / 10) (e + 1) := by
  rw [canonicaliseAux.eq_def, dif_neg hs, if_pos h10]

/-! ## Key invariant: nonzero input ⇒ nonzero output, mod-10-nonzero output -/

private theorem div_ten_nonzero {s : Nat} (hs : s ≠ 0) (h10 : s % 10 = 0) : s / 10 ≠ 0 := by
  omega

/-- `canonicaliseAux` preserves nonzero-ness of the significand. -/
theorem canonicaliseAux_fst_ne_zero :
    ∀ (s : Nat), s ≠ 0 → ∀ (e : Int), (canonicaliseAux s e).1 ≠ 0 := by
  intro s
  induction s using Nat.strongRecOn with
  | _ s ih =>
    intro hs e
    by_cases h10 : s % 10 = 0
    · rw [canonicaliseAux_div s e hs h10]
      exact ih (s / 10)
        (Nat.div_lt_self (Nat.pos_of_ne_zero hs) (by decide))
        (div_ten_nonzero hs h10) (e + 1)
    · rw [canonicaliseAux_not_div s e hs h10]; exact hs

/-! ## Main results about `canonical` -/

@[simp] theorem canonical_zero : canonical zero = zero := by
  unfold canonical; simp [zero]

end Srtfp.Decimal

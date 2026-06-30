/- Canonicalisation lemmas for Decimal. -/

import Srtfp.Numeric.Decimal

namespace PP.Numeric.Decimal

/-! ## Unfolding lemmas for `canonicaliseAux` -/

theorem canonicaliseAux_zero (e : Int) :
    canonicaliseAux 0 e = (0, 0) := by
  rw [canonicaliseAux.eq_def]; rfl

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

/-- `canonicaliseAux` produces a significand not divisible by 10 (when input is nonzero). -/
theorem canonicaliseAux_fst_mod_ne_zero :
    ∀ (s : Nat), s ≠ 0 → ∀ (e : Int), (canonicaliseAux s e).1 % 10 ≠ 0 := by
  intro s
  induction s using Nat.strongRecOn with
  | _ s ih =>
    intro hs e
    by_cases h10 : s % 10 = 0
    · rw [canonicaliseAux_div s e hs h10]
      exact ih (s / 10)
        (Nat.div_lt_self (Nat.pos_of_ne_zero hs) (by decide))
        (div_ten_nonzero hs h10) (e + 1)
    · rw [canonicaliseAux_not_div s e hs h10]; exact h10

/-! ## Main results about `canonical` -/

@[simp] theorem canonical_zero : canonical zero = zero := by
  unfold canonical; simp [zero]

/-- `canonical d` always satisfies `IsCanonical`. -/
theorem canonical_isCanonical (d : Decimal) : IsCanonical (canonical d) := by
  unfold canonical IsCanonical
  by_cases hd : d.significand = 0
  · simp [hd]
  · simp [hd]
    right
    refine ⟨?_, ?_⟩
    · exact canonicaliseAux_fst_ne_zero d.significand hd d.exponent
    · exact canonicaliseAux_fst_mod_ne_zero d.significand hd d.exponent

/-- A canonical Decimal is a fixed point of `canonical`. -/
theorem canonical_fixed_of_isCanonical (d : Decimal) (h : IsCanonical d) :
    canonical d = d := by
  unfold canonical
  rcases h with ⟨h0, hexp⟩ | ⟨hne, h10⟩
  · rcases d with ⟨sd, sigd, ed⟩
    simp at h0 hexp
    subst h0; subst hexp
    simp
  · rcases d with ⟨sd, sigd, ed⟩
    simp at hne h10 ⊢
    rw [if_neg hne, canonicaliseAux_not_div _ _ hne h10]

/-- `canonical` is idempotent. -/
theorem canonical_idem (d : Decimal) : canonical (canonical d) = canonical d :=
  canonical_fixed_of_isCanonical _ (canonical_isCanonical d)

end PP.Numeric.Decimal

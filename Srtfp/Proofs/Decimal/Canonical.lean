module
/- `Decimal.canonical` is idempotent and lands in `IsCanonical`; unfolding
   lemmas for `canonicaliseAux`. Consumed by the text round-trip proof. -/

public import Srtfp.Proofs.Decimal

@[expose] public section

open Float.Model.UnpackedFloat (Sign)

namespace Srtfp.Decimal

/-! ## Unfolding lemmas for `canonicaliseAux` -/

theorem canonicaliseAux_not_div (s : Nat) (e : Int) (hs : s ≠ 0) (h10 : s % 10 ≠ 0) :
    canonicaliseAux s e = (s, e) := by
  rw [canonicaliseAux.eq_def, dif_neg hs, if_neg h10]

theorem canonicaliseAux_div (s : Nat) (e : Int) (hs : s ≠ 0) (h10 : s % 10 = 0) :
    canonicaliseAux s e = canonicaliseAux (s / 10) (e + 1) := by
  rw [canonicaliseAux.eq_def, dif_neg hs, if_pos h10]

/-! ## Key invariant: nonzero input ⇒ nonzero output, mod-10-nonzero output -/

theorem div_ten_nonzero {s : Nat} (hs : s ≠ 0) (h10 : s % 10 = 0) : s / 10 ≠ 0 := by
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

/-- `mk'` is the identity on canonical field triples. -/
theorem mk'_eq_self_of_isCanonical {sign : Sign} {sig : Nat} {exp : Int}
    (h : IsCanonical ⟨sign, sig, exp⟩) :
    Decimal.mk' sign sig exp = ⟨sign, sig, exp⟩ :=
  canonical_fixed_of_isCanonical _ h

/-! ## Main results about `canonical` -/

@[simp] theorem canonical_zero : canonical zero = zero := by
  unfold canonical; simp [zero]

/-! ## Canonicalisation absorbs trailing zeros -/

theorem mk'_mul_ten (s : Sign) (v : Nat) (e : Int) :
    Decimal.mk' s (v * 10) e = Decimal.mk' s v (e + 1) := by
  by_cases hv : v = 0
  · subst hv; rfl
  · have h10 : v * 10 ≠ 0 := Nat.mul_ne_zero hv (by decide)
    simp only [Decimal.mk', Decimal.canonical, if_neg hv, if_neg h10,
      Decimal.canonicaliseAux_div _ _ h10 (Nat.mul_mod_left v 10),
      Nat.mul_div_cancel v (by decide : 0 < 10)]

/-- Trailing zeros in the significand shift into the exponent. -/
theorem mk'_shift (s : Sign) (v : Nat) (e : Int) (k : Nat) :
    Decimal.mk' s (v * 10 ^ k) (e - k) = Decimal.mk' s v e := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.pow_succ, ← Nat.mul_assoc, mk'_mul_ten, show e - ↑(k + 1) + 1 = e - ↑k by omega, ih]

/-! ## The normalization specification -/

theorem normalizes_mk (sign : Sign) (sig : Nat) (exp : Int) :
    Normalizes sign sig exp (Decimal.mk' sign sig exp) := by
  refine ⟨Decimal.canonical_isCanonical _, ?_⟩
  by_cases h : sig = 0
  · subst sig
    exact ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
  · obtain ⟨hs, _, _, he, hv⟩ := mk_pos_props sign sig exp h
    refine ⟨hs, Or.inr ⟨((Decimal.mk' sign sig exp).exponent - exp).toNat, hv.symm, ?_⟩⟩
    omega

theorem normalizes_iff (sign : Sign) (sig : Nat) (exp : Int) (d : Decimal) :
    Normalizes sign sig exp d ↔ Decimal.mk' sign sig exp = d := by
  constructor
  · rintro ⟨hc, hs, hzero | ⟨k, hsig, he⟩⟩
    · obtain ⟨rfl, hz⟩ := hzero
      have he : d.exponent = 0 := by
        rcases hc with h | h
        · exact h.2
        · exact False.elim (h.1 hz)
      cases d
      simp_all [Decimal.mk', Decimal.canonical]
    · rw [hsig, ← hs, show exp = d.exponent - k by omega, mk'_shift]
      exact Decimal.canonical_fixed_of_isCanonical d hc
  · rintro rfl
    exact normalizes_mk sign sig exp

end Srtfp.Decimal

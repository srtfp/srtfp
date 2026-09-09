module
/- Pure `Decimal.mk'` / `canonicaliseAux` canonicalisation lemmas.

   Factored from QuadParsers' `PP/Proofs/Numeric/Decimal.lean`: this is
   the framework-independent slice used by the Schubfach/Clinger proof
   stack (`Schubfach.Minimal`, `RoundTrip`, `TieBreak`, `Correctness`). -/

public import Srtfp.Decimal

@[expose] public section

open Float.Model.UnpackedFloat (Sign)

namespace Srtfp

/-- `canonicaliseAux` for `s ≠ 0`: preserves the product, produces a
    non-multiple-of-10 sig, and shifts the exponent up by exactly the number
    of stripped trailing zeros (so `e ≤ e'` even when `e` is negative). -/
private theorem canonicaliseAux_value_gen (s : Nat) (hs0 : s ≠ 0) :
    ∀ (e : Int) s' e', Decimal.canonicaliseAux s e = (s', e') →
    s' * 10 ^ (e' - e).toNat = s ∧ e ≤ e' ∧ s' ≠ 0 ∧ s' % 10 ≠ 0 := by
  induction s using Nat.strongRecOn with
  | _ s ih =>
    intro e s' e' heq
    unfold Decimal.canonicaliseAux at heq
    simp only [hs0, ↓reduceDIte] at heq
    by_cases hmod : s % 10 = 0
    · rw [if_pos hmod] at heq
      obtain ⟨hval, hexp, hsne, hcanon⟩ :=
        ih (s / 10) (Nat.div_lt_self (Nat.pos_of_ne_zero hs0) (by decide)) (by omega) (e + 1) s' e' heq
      refine ⟨?_, by omega, hsne, hcanon⟩
      rw [show (e' - e).toNat = (e' - (e + 1)).toNat + 1 by omega, Nat.pow_succ, ← Nat.mul_assoc, hval]
      omega
    · rw [if_neg hmod] at heq
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      exact ⟨by simp, Int.le_refl _, hs0, hmod⟩

/-- `Decimal.mk' sign sig exp` with `sig ≠ 0`: produces a canonical Decimal
    with the same sign, a (possibly smaller) significand without trailing
    decimal zeros, and an exponent such that
    `result.significand * 10^(result.exponent - exp).toNat = sig`. -/
theorem mk_pos_props (sign : Sign) (sig : Nat) (exp : Int) (hsig : sig ≠ 0) :
    (Decimal.mk' sign sig exp).sign = sign ∧
    (Decimal.mk' sign sig exp).significand ≠ 0 ∧
    (Decimal.mk' sign sig exp).significand % 10 ≠ 0 ∧
    exp ≤ (Decimal.mk' sign sig exp).exponent ∧
    (Decimal.mk' sign sig exp).significand *
      10 ^ ((Decimal.mk' sign sig exp).exponent - exp).toNat = sig := by
  unfold Decimal.mk' Decimal.canonical
  dsimp only
  simp only [hsig, ↓reduceIte]
  cases hp : Decimal.canonicaliseAux sig exp with
  | mk s' e' =>
    dsimp only
    obtain ⟨hval, hexp_le, hsne, hcanon⟩ := canonicaliseAux_value_gen sig hsig exp s' e' hp
    exact ⟨trivial, hsne, hcanon, hexp_le, hval⟩

namespace Decimal

@[simp] theorem neg_neg (d : Decimal) : -(-d) = d := by
  rcases d with ⟨sign, sig, exp⟩
  cases sign <;> rfl

@[simp] theorem neg_isCanonical (d : Decimal) : (-d).IsCanonical ↔ d.IsCanonical := Iff.rfl

end Decimal

end Srtfp

/- Pure `Decimal.mk'` / `canonicaliseAux` canonicalisation lemmas.

   Factored from QuadParsers' `PP/Proofs/Numeric/Decimal.lean`: this is
   the framework-independent slice used by the Schubfach/Clinger proof
   stack (`Schubfach.Minimal`, `RoundTrip`, `TieBreak`, `Correctness`). -/

import Srtfp.Decimal

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
      have hslt : s / 10 < s := Nat.div_lt_self (Nat.pos_of_ne_zero hs0) (by decide)
      have hsd : s / 10 ≠ 0 := by
        have hpos : s > 0 := Nat.pos_of_ne_zero hs0; omega
      obtain ⟨hval, hexp, hsne, hcanon⟩ := ih (s / 10) hslt hsd (e + 1) s' e' heq
      refine ⟨?_, by omega, hsne, hcanon⟩
      have hdiff : (e' - e).toNat = (e' - (e + 1)).toNat + 1 := by
        have h1 : 0 ≤ e' - (e + 1) := by omega
        have h2 : 0 ≤ e' - e := by omega
        omega
      rw [hdiff, Nat.pow_succ]
      have hediv : (s / 10) * 10 = s := by omega
      have hrearr : s' * (10 ^ (e' - (e + 1)).toNat * 10)
          = (s' * 10 ^ (e' - (e + 1)).toNat) * 10 := by
        rw [← Nat.mul_assoc]
      rw [hrearr, hval, hediv]
    · rw [if_neg hmod] at heq
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      have hee : (e - e).toNat = 0 := by simp
      refine ⟨?_, Int.le_refl _, hs0, hmod⟩
      rw [hee]; simp

/-- `Decimal.mk' sign sig exp` with `sig ≠ 0`: produces a canonical Decimal
    with the same sign, a (possibly smaller) significand without trailing
    decimal zeros, and an exponent such that
    `result.significand * 10^(result.exponent - exp).toNat = sig`. -/
theorem mk_pos_props (sign : Bool) (sig : Nat) (exp : Int) (hsig : sig ≠ 0) :
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

end Srtfp

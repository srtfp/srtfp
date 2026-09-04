module
/- Vocabulary shared by the printer proofs (`v`, the magnitude of a word,
   and the spec's `digits`), and the digit-count facts. -/
public import Srtfp.Spec
public import Srtfp.Printer

@[expose] public section

open Srtfp.Compat

namespace Srtfp.Printer

open Srtfp.Float

/-- `v = m · 2^q`, the magnitude of a finite word. -/
def v (m : Nat) (q : Int) : ℚ := (m : ℚ) * (2 : ℚ) ^ q

-- `digits n`, the number of decimal digits (`digits 0 = 1`), is the spec's.
export Spec (digits)

/-! ## Digit counting

Everything follows from the two bounds `10^(digits n - 1) ≤ n < 10^(digits n)`. -/

theorem digits_pos (n : Nat) : 1 ≤ digits n := by unfold digits; omega

theorem lt_pow_digits (n : Nat) : n < 10 ^ digits n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    unfold digits
    by_cases h : 10 ≤ n
    · rw [Nat.log_eq_log_div_add_one h (by decide)]
      have ih' := ih (n / 10) (Nat.div_lt_self (by omega) (by decide))
      unfold digits at ih'
      rw [Nat.pow_succ]
      omega
    · rw [Nat.log_eq_zero_of_not (by omega)]
      omega

theorem pow_digits_le {n : Nat} (h : 1 ≤ n) : 10 ^ (digits n - 1) ≤ n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    unfold digits
    by_cases h10 : 10 ≤ n
    · rw [Nat.log_eq_log_div_add_one h10 (by decide)]
      have ih' := ih (n / 10) (Nat.div_lt_self (by omega) (by decide)) (by omega)
      unfold digits at ih'
      simp only [Nat.add_sub_cancel] at ih' ⊢
      rw [Nat.pow_succ]
      omega
    · rw [Nat.log_eq_zero_of_not (by omega)]
      simpa using h

theorem digits_zero : digits 0 = 1 := by
  unfold digits; rw [Nat.log_eq_zero_of_not (by omega)]

theorem digits_le_of_le {a b : Nat} (h : a ≤ b) : digits a ≤ digits b := by
  rcases Nat.lt_or_ge (digits b) (digits a) with hlt | hle
  · exfalso
    rcases Nat.eq_zero_or_pos a with ha | ha
    · subst ha; rw [digits_zero] at hlt; have := digits_pos b; omega
    have h1 := lt_pow_digits b
    have h2 : 10 ^ (digits b) ≤ 10 ^ (digits a - 1) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have h3 : 10 ^ (digits a - 1) ≤ a := pow_digits_le ha
    omega
  · exact hle

theorem digits_lt_of_pow_le {a b k : Nat} (hb : 10 ^ k ≤ b) (ha : digits a ≤ k) :
    digits a < digits b := by
  rcases Nat.lt_or_ge (digits a) (digits b) with hlt | hge
  · exact hlt
  · exfalso
    have h1 := lt_pow_digits b
    have h2 : 10 ^ (digits b) ≤ 10 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
    omega

/-- Digit counts change only at multiples of ten (the powers of ten ≥ 10). -/
theorem digits_eq_of_no_ten_dvd_between {a b : Nat} (ha : 1 ≤ a) (hab : a ≤ b)
    (h : ∀ c, a ≤ c → c ≤ b → c % 10 ≠ 0) : digits a = digits b := by
  have hle := digits_le_of_le hab
  rcases Nat.lt_or_ge (digits a) (digits b) with hlt | hge
  · exfalso
    -- the power of ten `10 ^ digits a` lies in `(a, b]` and is a multiple of ten
    have hc_gt : a < 10 ^ digits a := lt_pow_digits a
    have hc_le : 10 ^ digits a ≤ b :=
      Nat.le_trans
        (Nat.pow_le_pow_right (by decide) (show digits a ≤ digits b - 1 by omega))
        (pow_digits_le (show 1 ≤ b by omega))
    have hmod : 10 ^ digits a % 10 = 0 := by
      have := digits_pos a
      obtain ⟨j, hj⟩ : ∃ j, digits a = j + 1 := ⟨digits a - 1, by omega⟩
      rw [hj, Nat.pow_succ]
      simp
    exact h _ (by omega) hc_le hmod
  · omega

theorem digits_mul_pow {n : Nat} (h : 1 ≤ n) (k : Nat) :
    digits (n * 10 ^ k) = digits n + k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hpk : 1 ≤ 10 ^ k := Nat.one_le_pow _ _ (by decide)
    have h10 : 10 ≤ 10 ^ (k + 1) := by rw [Nat.pow_succ]; omega
    have hk : 10 ≤ n * 10 ^ (k + 1) :=
      calc 10 ≤ 10 ^ (k + 1) := h10
        _ = 1 * 10 ^ (k + 1) := (Nat.one_mul _).symm
        _ ≤ n * 10 ^ (k + 1) := Nat.mul_le_mul_right _ h
    unfold digits
    rw [Nat.log_eq_log_div_add_one hk (by decide)]
    have hdiv : n * 10 ^ (k + 1) / 10 = n * 10 ^ k := by
      rw [Nat.pow_succ, ← Nat.mul_assoc]
      exact Nat.mul_div_cancel _ (by decide)
    rw [hdiv]
    unfold digits at ih
    omega

end Srtfp.Printer

module
/- Vocabulary shared by the printer proofs (`v`, the magnitude of a word,
   and the spec's `digits`), and the digit-count facts, all derived from
   the two bounds `10^(digits n - 1) ≤ n < 10^(digits n)`. -/
public import Srtfp.Rat
public import Srtfp.Spec
public import Srtfp.Printer

@[expose] public section

open Srtfp.Compat

namespace Srtfp.Printer

open Srtfp.Float

/-- `v = m · 2^q`, the magnitude of a finite word. -/
def v (m : Nat) (q : Int) : Rat := (m : Rat) * (2 : Rat) ^ q

-- `digits n`, the number of decimal digits (`digits 0 = 1`), is the spec's.
export Spec (digits)

/-! ## Digit counting

Everything follows from the two bounds `10^(digits n - 1) ≤ n < 10^(digits n)`. -/

theorem digits_pos (n : Nat) : 1 ≤ digits n := Nat.length_toDigits_pos

theorem lt_pow_digits (n : Nat) : n < 10 ^ digits n :=
  (Nat.length_toDigits_le_iff (by decide) (digits_pos n)).mp (Nat.le_refl _)

theorem pow_digits_le {n : Nat} (h : 1 ≤ n) : 10 ^ (digits n - 1) ≤ n := by
  rcases Nat.eq_or_lt_of_le (digits_pos n) with h1 | h1
  · rw [← h1]; simpa using h
  · apply Nat.le_of_not_lt
    intro hlt
    have h2 := (Nat.length_toDigits_le_iff (b := 10) (n := n) (k := digits n - 1) (by decide)
      (by omega)).mpr hlt
    have h3 : digits n = (Nat.toDigits 10 n).length := rfl
    omega

theorem digits_zero : digits 0 = 1 := by
  have h1 := digits_pos 0
  have h2 := (Nat.length_toDigits_le_iff (b := 10) (n := 0) (k := 1) (by decide) (by decide)).mpr
    (by decide)
  have h3 : digits 0 = (Nat.toDigits 10 0).length := rfl
  omega

/-- The two bounds pin the digit count. -/
theorem digits_eq_of_bounds {n k : Nat} (hk : 1 ≤ k) (h1 : 10 ^ (k - 1) ≤ n) (h2 : n < 10 ^ k) :
    digits n = k := by
  have hlt := lt_pow_digits n
  have hpos := digits_pos n
  rcases Nat.lt_trichotomy (digits n) k with h | h | h
  · have : 10 ^ digits n ≤ 10 ^ (k - 1) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  · exact h
  · have hle := pow_digits_le (n := n) (by have := Nat.one_le_pow (k - 1) 10 (by decide); omega)
    have : 10 ^ k ≤ 10 ^ (digits n - 1) := Nat.pow_le_pow_right (by decide) (by omega)
    omega

theorem digits_eq_one_of_le_nine {n : Nat} (hn : n ≤ 9) : digits n = 1 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; exact digits_zero
  · exact digits_eq_of_bounds (by decide) (by show 10 ^ 0 ≤ n; omega) (by omega)

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

end Srtfp.Printer

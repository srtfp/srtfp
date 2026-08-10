/- Core-only `Nat.log`, definitionally matching Mathlib's, plus the three
   lemmas about it this library uses. Introduced when the Mathlib
   dependency was dropped: the digit-count spec is phrased in terms of
   `Nat.log 10`. -/

namespace Nat

/-- Base-`b` logarithm of a natural number: largest `k` with `b ^ k ≤ n`,
    and `0` where that reading is meaningless (`n = 0` or `b ≤ 1`).
    Matches Mathlib's `Nat.log`. -/
def log (b : Nat) : Nat → Nat
  | n =>
    if h : b ≤ n ∧ 1 < b then
      have : n / b < n := Nat.div_lt_self (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_lt h.2)) h.1) h.2
      log b (n / b) + 1
    else 0

theorem log_eq_log_div_add_one {b n : Nat} (h : b ≤ n) (hb : 1 < b) :
    log b n = log b (n / b) + 1 := by
  rw [log]; rw [dif_pos ⟨h, hb⟩]

theorem log_eq_zero_of_not {b n : Nat} (h : ¬(b ≤ n ∧ 1 < b)) : log b n = 0 := by
  rw [log]; rw [dif_neg h]

theorem log_eq_zero_iff {b n : Nat} : log b n = 0 ↔ n < b ∨ b ≤ 1 := by
  constructor
  · intro h0
    by_cases hc : b ≤ n ∧ 1 < b
    · rw [log_eq_log_div_add_one hc.1 hc.2] at h0; omega
    · omega
  · intro h
    exact log_eq_zero_of_not (by omega)

theorem log_pos {b n : Nat} (hb : 1 < b) (hn : b ≤ n) : 0 < log b n := by
  rw [log_eq_log_div_add_one hn hb]; omega

theorem log_div_base (b n : Nat) : log b (n / b) = log b n - 1 := by
  by_cases hc : b ≤ n ∧ 1 < b
  · rw [log_eq_log_div_add_one hc.1 hc.2]; omega
  · have h1 : log b n = 0 := log_eq_zero_of_not hc
    have h2 : log b (n / b) = 0 := by
      apply log_eq_zero_of_not
      intro ⟨hle, hlt⟩
      exact hc ⟨Nat.le_trans hle (Nat.div_le_self n b), hlt⟩
    omega

end Nat

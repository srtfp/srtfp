module
/- The rest of the ℚ compatibility layer: lemmas the reference tier no
   longer uses, kept for the performance tier's older proofs. Same
   `Srtfp.Compat` namespace as `Srtfp/Rat.lean`. -/

public import Srtfp.Rat

@[expose] public section

namespace Srtfp.Compat

theorem abs_sub_comm (a b : ℚ) : |a - b| = |b - a| := by
  rw [show b - a = -(a - b) from (Rat.neg_sub a b).symm, abs_neg]

theorem mul_right_cancel₀ {a b c : ℤ} (hc : c ≠ 0) (h : a * c = b * c) : a = b := by
  rcases Int.lt_trichotomy a b with hlt | heq | hgt
  · exfalso
    rcases Int.lt_trichotomy c 0 with hc0 | hc0 | hc0
    · have := Int.mul_lt_mul_of_neg_right hlt hc0; omega
    · exact hc hc0
    · have := Int.mul_lt_mul_of_pos_right hlt hc0; omega
  · exact heq
  · exfalso
    rcases Int.lt_trichotomy c 0 with hc0 | hc0 | hc0
    · have := Int.mul_lt_mul_of_neg_right hgt hc0; omega
    · exact hc hc0
    · have := Int.mul_lt_mul_of_pos_right hgt hc0; omega

theorem one_le_pow_of_le {a : ℤ} (ha : 1 ≤ a) : ∀ n : Nat, 1 ≤ a ^ n
  | 0 => by simp
  | (n+1) => by
    have ih := one_le_pow_of_le ha n
    rw [Int.pow_succ]
    have := Int.mul_le_mul ih ha (by omega) (by omega)
    omega

theorem pow_le_pow_right₀ {a : ℤ} (ha : 1 ≤ a) {m n : Nat} (h : m ≤ n) : a ^ m ≤ a ^ n := by
  have hd : n = m + (n - m) := by omega
  rw [hd, Int.pow_add]
  have h1 := one_le_pow_of_le ha (n - m)
  have hm := one_le_pow_of_le ha m
  have := Int.mul_le_mul_of_nonneg_left h1 (by omega : (0:ℤ) ≤ a ^ m)
  omega

theorem pow_lt_pow_right₀ {a : ℤ} (ha : 1 < a) {m n : Nat} (h : m < n) : a ^ m < a ^ n := by
  have hd : n = m + (n - m - 1) + 1 := by omega
  rw [hd, Int.pow_succ, Int.pow_add]
  have hk := one_le_pow_of_le (by omega : (1:ℤ) ≤ a) (n - m - 1)
  have hm := one_le_pow_of_le (by omega : (1:ℤ) ≤ a) m
  have h1 : a ^ m * 1 < a ^ m * (a ^ (n - m - 1) * a) := by
    apply Int.mul_lt_mul_of_pos_left ?_ (by omega)
    have := Int.mul_le_mul hk (Int.le_refl a) (by omega) (by omega)
    omega
  calc a ^ m = a ^ m * 1 := by grind
    _ < a ^ m * (a ^ (n - m - 1) * a) := h1
    _ = a ^ m * a ^ (n - m - 1) * a := by grind

theorem Int.cast_lt {a b : ℤ} : (a : ℚ) < (b : ℚ) ↔ a < b := Rat.intCast_lt_intCast

theorem Int.cast_inj {a b : ℤ} : (a : ℚ) = (b : ℚ) ↔ a = b := Rat.intCast_inj

theorem mul_lt_mul_iff_of_pos_right {a b c : ℚ} (hc : 0 < c) :
    a * c < b * c ↔ a < b := Rat.mul_lt_mul_right hc

private theorem mul_self_lt_mul_self_iff {x y : ℚ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x * x < y * y ↔ x < y := by
  constructor
  · intro h
    rcases Rat.le_total (a := y) (b := x) with hc | hc
    · exfalso
      have h1 : y * y ≤ x * y := Rat.mul_le_mul_of_nonneg_right hc hy
      have h2 : x * y ≤ x * x := Rat.mul_le_mul_of_nonneg_left hc hx
      grind
    · exact Rat.lt_of_le_of_ne hc (fun he => absurd h (by grind))
  · intro h
    have hy_pos : 0 < y := by grind
    have h1 : x * x ≤ y * x := Rat.mul_le_mul_of_nonneg_right (Rat.le_of_lt h) hx
    have h2 : y * x < y * y := Rat.mul_lt_mul_of_pos_left h hy_pos
    grind

theorem abs_mul_self (a : ℚ) : |a| * |a| = a * a := by
  by_cases h : a < 0
  · rw [abs_of_neg h]; grind
  · rw [abs_of_nonneg (Rat.not_lt.mp h)]

theorem abs_lt_iff_mul_self_lt {a b : ℚ} : |a| < |b| ↔ a * a < b * b := by
  rw [← abs_mul_self a, ← abs_mul_self b]
  exact (mul_self_lt_mul_self_iff (abs_nonneg a) (abs_nonneg b)).symm

theorem abs_eq_iff_mul_self_eq {a b : ℚ} : |a| = |b| ↔ a * a = b * b := by
  constructor
  · intro h
    rw [← abs_mul_self a, ← abs_mul_self b, h]
  · intro h
    have h1 : ¬(|a| < |b|) := by
      rw [abs_lt_iff_mul_self_lt]; grind
    have h2 : ¬(|b| < |a|) := by
      rw [abs_lt_iff_mul_self_lt]; grind
    have := Rat.le_antisymm (Rat.not_lt.mp h2) (Rat.not_lt.mp h1)
    exact this

theorem lt_of_not_ge {a b : ℚ} (h : ¬a ≥ b) : a < b := Rat.not_le.mp h

theorem le_of_eq {a b : ℚ} (h : a = b) : a ≤ b := by grind

theorem le_or_gt (a b : ℤ) : a ≤ b ∨ a > b := by omega

theorem abs_le {a b : ℚ} : |a| ≤ b ↔ -b ≤ a ∧ a ≤ b := by
  rw [abs_def]
  split <;> rename_i h <;> constructor <;> intro hh <;> first | grind | (constructor <;> grind)

theorem abs_mul (a b : ℚ) : |a * b| = |a| * |b| := by
  by_cases ha : a < 0 <;> by_cases hb : b < 0
  · have hpos : 0 < a * b := by
      have h1 : (0:ℚ) < -a := by grind
      have h2 : (0:ℚ) < -b := by grind
      have := Rat.mul_pos h1 h2
      grind
    rw [abs_of_nonneg (Rat.le_of_lt hpos), abs_of_neg ha, abs_of_neg hb]
    grind
  · have hb' : (0:ℚ) ≤ b := Rat.not_lt.mp hb
    have hab : a * b ≤ 0 := by
      have := Rat.mul_le_mul_of_nonneg_right (Rat.le_of_lt ha) hb'
      grind
    rw [abs_of_nonpos hab, abs_of_neg ha, abs_of_nonneg hb']
    grind
  · have ha' : (0:ℚ) ≤ a := Rat.not_lt.mp ha
    have hab : a * b ≤ 0 := by
      have := Rat.mul_le_mul_of_nonneg_left (Rat.le_of_lt hb) ha'
      grind
    rw [abs_of_nonpos hab, abs_of_nonneg ha', abs_of_neg hb]
    grind
  · have ha' : (0:ℚ) ≤ a := Rat.not_lt.mp ha
    have hb' : (0:ℚ) ≤ b := Rat.not_lt.mp hb
    rw [abs_of_nonneg (Rat.mul_nonneg ha' hb'), abs_of_nonneg ha', abs_of_nonneg hb']

theorem sub_lt_sub_left {a b : ℚ} (h : a < b) (c : ℚ) : c - b < c - a := by grind

theorem abs_cases (a : ℚ) : |a| = a ∧ 0 ≤ a ∨ |a| = -a ∧ a < 0 := by
  by_cases h : a < 0
  · right; exact ⟨abs_of_neg h, h⟩
  · left; exact ⟨abs_of_nonneg (Rat.not_lt.mp h), Rat.not_lt.mp h⟩

theorem sub_pos {a b : ℚ} : 0 < a - b ↔ b < a := by grind

theorem rat_pow_lt_pow_right {a : ℚ} (ha : 1 < a) {m n : ℕ} (h : m < n) : a ^ m < a ^ n := by
  obtain ⟨k, hk_eq⟩ : ∃ k, n = m + k + 1 := ⟨n - m - 1, by omega⟩
  subst hk_eq
  rw [Rat.pow_succ, Rat.pow_add]
  have hk := one_le_pow_rat (Rat.le_of_lt ha) k
  have hm := one_le_pow_rat (Rat.le_of_lt ha) m
  have hcomb : (1 : ℚ) < a ^ k * a := by
    have h1 := Rat.mul_le_mul_of_nonneg_right hk (by grind : (0:ℚ) ≤ a)
    grind
  calc a ^ m = a ^ m * 1 := by grind
    _ < a ^ m * (a ^ k * a) := Rat.mul_lt_mul_of_pos_left hcomb (by grind)
    _ = a ^ m * a ^ k * a := by grind

/-- `dvd_pow` for `Nat` (vendored). -/
theorem Nat.dvd_pow' {a b : Nat} (h : a ∣ b) {n : Nat} (hn : n ≠ 0) : a ∣ b ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.pow_succ]
  exact Nat.dvd_trans h (Nat.dvd_mul_left b (b ^ m))

theorem lt_trans {a b c : ℚ} (h1 : a < b) (h2 : b < c) : a < c := by grind

/-- `dvd_pow_self` for `Nat` (vendored). -/
theorem dvd_pow_self (a : Nat) {n : Nat} (hn : n ≠ 0) : a ∣ a ^ n :=
  Nat.dvd_pow' (Nat.dvd_refl a) hn

end Srtfp.Compat

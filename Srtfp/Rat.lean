module
/- What core's `Init.Data.Rat` lacks and the proofs use: the `|·|` bars
   for `Rat.abs`, monotonicity of `zpow`, cancellation, the `Trans`
   instances behind `calc`, and a few order facts. Everything lives in
   the `Srtfp.Compat` namespace with scoped notation; proof files start
   with `open Srtfp.Compat`. -/

@[expose] public section

namespace Srtfp.Compat

/-- `|a|` is core's `Rat.abs`. -/
scoped macro:max atomic("|" noWs) a:term noWs "|" : term => `(Rat.abs $a)

theorem abs_def (q : Rat) : |q| = if 0 ≤ q then q else -q := rfl

theorem eq_or_lt_of_le {a b : Int} (h : a ≤ b) : a = b ∨ a < b := by omega

theorem mul_left_inj' {a b c : Rat} (hc : c ≠ 0) : a * c = b * c ↔ a = b := by
  constructor
  · intro h
    have hsub : (a - b) * c = 0 := by grind
    rcases Rat.mul_eq_zero.mp hsub with h0 | h0
    · grind
    · exact absurd h0 hc
  · intro h; rw [h]

theorem lt_of_le_of_lt {a b c : Rat} (h1 : a ≤ b) (h2 : b < c) : a < c := by grind

theorem one_le_pow_rat {a : Rat} (ha : 1 ≤ a) : ∀ m : Nat, 1 ≤ a ^ m
  | 0 => by rw [Rat.pow_zero]; exact Rat.le_refl
  | (m+1) => by
    rw [Rat.pow_succ]
    have ih := one_le_pow_rat ha m
    have h0 : (0 : Rat) ≤ a ^ m := by grind
    have := Rat.mul_le_mul_of_nonneg_left ha h0
    grind

theorem one_le_zpow_of_nonneg {a : Rat} (ha : 1 ≤ a) {n : Int} (hn : 0 ≤ n) : 1 ≤ a ^ n := by
  have h := Rat.zpow_natCast a n.toNat
  rw [Int.toNat_of_nonneg hn] at h
  rw [h]
  exact one_le_pow_rat ha n.toNat

theorem zpow_le_zpow_right₀ {a : Rat} (ha : 1 ≤ a) {m n : Int} (h : m ≤ n) : a ^ m ≤ a ^ n := by
  have hne : a ≠ 0 := by grind
  have hsplit : a ^ n = a ^ m * a ^ (n - m) := by
    rw [← Rat.zpow_add hne]
    congr 1
    omega
  have h1 : 1 ≤ a ^ (n - m) := one_le_zpow_of_nonneg ha (by omega)
  have h0 : 0 < a ^ m := Rat.zpow_pos (by grind)
  calc a ^ m = a ^ m * 1 := by grind
    _ ≤ a ^ m * a ^ (n - m) := Rat.mul_le_mul_of_nonneg_left h1 (Rat.le_of_lt h0)
    _ = a ^ n := hsplit.symm

/-! ### grind hints: Rat order/monotonicity facts the proof stack leans on -/

attribute [grind .] Rat.mul_le_mul_of_nonneg_left Rat.mul_le_mul_of_nonneg_right
  Rat.mul_lt_mul_of_pos_left Rat.mul_lt_mul_of_pos_right
  Rat.mul_pos Rat.mul_nonneg Rat.natCast_nonneg

theorem sub_zero (a : Rat) : a - 0 = a := by grind

theorem lt_of_lt_of_le {a b c : Rat} (h1 : a < b) (h2 : b ≤ c) : a < c := by grind

protected theorem Rat.pow_add (a : Rat) (m n : Nat) : a ^ (m + n) = a ^ m * a ^ n := by
  induction n with
  | zero => rw [Nat.add_zero, Rat.pow_zero]; grind
  | succ n ih =>
    rw [show m + (n+1) = (m+n) + 1 from by omega, Rat.pow_succ, ih, Rat.pow_succ]
    grind

instance : Trans (α := Rat) (· < ·) (· ≤ ·) (· < ·) := ⟨fun h1 h2 => lt_of_lt_of_le h1 h2⟩
instance : Trans (α := Rat) (· ≤ ·) (· < ·) (· < ·) := ⟨fun h1 h2 => lt_of_le_of_lt h1 h2⟩
instance : Trans (α := Rat) (· ≤ ·) (· ≤ ·) (· ≤ ·) := ⟨fun h1 h2 => Rat.le_trans h1 h2⟩
instance : Trans (α := Rat) (· < ·) (· < ·) (· < ·) :=
  ⟨fun h1 h2 => lt_of_lt_of_le h1 (Rat.le_of_lt h2)⟩

protected theorem Rat.lt_trichotomy (a b : Rat) : a < b ∨ a = b ∨ b < a := by
  rcases Rat.le_total (a := a) (b := b) with h | h
  · by_cases he : a = b
    · exact Or.inr (Or.inl he)
    · exact Or.inl (Rat.lt_of_le_of_ne h he)
  · by_cases he : b = a
    · exact Or.inr (Or.inl he.symm)
    · exact Or.inr (Or.inr (Rat.lt_of_le_of_ne h he))

theorem lt_or_ge (a b : Rat) : a < b ∨ a ≥ b := by
  by_cases h : a < b
  · exact Or.inl h
  · exact Or.inr (Rat.not_lt.mp h)

protected theorem Rat.eq_or_lt_of_le {a b : Rat} (h : a ≤ b) : a = b ∨ a < b := by
  by_cases he : a = b
  · exact Or.inl he
  · exact Or.inr (Rat.lt_of_le_of_ne h he)

theorem mul_left_cancel₀ {a b c : Rat} (ha : a ≠ 0) (h : a * b = a * c) : b = c := by
  have h' : b * a = c * a := by grind
  exact (mul_left_inj' ha).mp h'

end Srtfp.Compat

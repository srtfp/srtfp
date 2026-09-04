module
/- Core-only Rat compatibility layer.

   The proof stack was written against Mathlib's rational-number surface;
   core Lean (`Init.Data.Rat`) provides the type, field arithmetic, order,
   `zpow` and `Rat.abs`, but not the `|·|` bars or Mathlib's lemma
   names. This file supplies exactly that missing surface.

   Everything lives in the `Srtfp.Compat` namespace with scoped
   notation, so importing srtfp never collides with Mathlib's root
   names; proof files start with `open Srtfp.Compat`. -/

@[expose] public section

namespace Srtfp.Compat

universe u

/-- `|a|` is core's `Rat.abs`. -/
scoped macro:max atomic("|" noWs) a:term noWs "|" : term => `(Rat.abs $a)

namespace Rat

/- `neg_neg` / `neg_zero` exist in newer cores but not in v4.27; private
non-colliding copies keep this file toolchain-portable (they are only
used within this file). -/
private theorem rat_neg_neg (q : Rat) : -(-q) = q := by
  calc -(-q) = -(-q) + 0 := (Rat.add_zero _).symm
    _ = -(-q) + (-q + q) := by rw [Rat.neg_add_cancel]
    _ = -(-q) + -q + q := by rw [Rat.add_assoc]
    _ = 0 + q := by rw [Rat.neg_add_cancel]
    _ = q := Rat.zero_add q

private theorem rat_neg_zero : -(0 : Rat) = 0 := rfl

protected theorem neg_nonneg {q : Rat} : 0 ≤ -q ↔ q ≤ 0 := by
  constructor
  · intro h
    have := (Rat.le_iff_sub_nonneg 0 (-q)).mp h
    simp only [Rat.sub_eq_add_neg, rat_neg_zero, Rat.add_zero] at this
    exact (Rat.le_iff_sub_nonneg q 0).mpr (by
      simp only [Rat.sub_eq_add_neg, Rat.zero_add]
      exact this)
  · intro h
    have := (Rat.le_iff_sub_nonneg q 0).mp h
    simp only [Rat.sub_eq_add_neg, Rat.zero_add] at this
    exact this

protected theorem neg_lt_zero {q : Rat} : -q < 0 ↔ 0 < q := by
  constructor
  · intro h
    have := (Rat.lt_iff_sub_pos (-q) 0).mp h
    simp only [Rat.sub_eq_add_neg, Rat.zero_add, rat_neg_neg] at this
    exact this
  · intro h
    have := (Rat.lt_iff_sub_pos 0 q).mp h
    apply (Rat.lt_iff_sub_pos (-q) 0).mpr
    simp only [Rat.sub_eq_add_neg, rat_neg_zero, Rat.add_zero, Rat.zero_add, rat_neg_neg] at this ⊢
    exact this

end Rat

section RatAbs

theorem abs_def (q : Rat) : |q| = if 0 ≤ q then q else -q := rfl

theorem abs_of_nonneg {q : Rat} (h : 0 ≤ q) : |q| = q := Rat.abs_of_nonneg h

theorem abs_of_neg {q : Rat} (h : q < 0) : |q| = -q := by
  rw [abs_def, if_neg (Rat.not_le.mpr h)]

theorem abs_nonneg (q : Rat) : 0 ≤ |q| := Rat.abs_nonneg

theorem abs_neg (q : Rat) : |(-q)| = |q| := Rat.abs_neg

end RatAbs

/-! ### Generic order-lemma names used by the proof stack (Int-valued sites) -/

theorem lt_or_eq_of_le {a b : Int} (h : a ≤ b) : a < b ∨ a = b := by omega

theorem le_antisymm {a b : Int} (h1 : a ≤ b) (h2 : b ≤ a) : a = b := by omega

theorem eq_or_lt_of_le {a b : Int} (h : a ≤ b) : a = b ∨ a < b := by omega

theorem lt_trichotomy (a b : Int) : a < b ∨ a = b ∨ b < a := by omega

/-! ### Rat compatibility aliases for TieBreak -/

theorem mul_left_inj' {a b c : Rat} (hc : c ≠ 0) : a * c = b * c ↔ a = b := by
  constructor
  · intro h
    have hsub : (a - b) * c = 0 := by grind
    rcases Rat.mul_eq_zero.mp hsub with h0 | h0
    · grind
    · exact absurd h0 hc
  · intro h; rw [h]

theorem not_lt {a b : Rat} : ¬a < b ↔ b ≤ a := Rat.not_lt

theorem abs_of_nonpos {a : Rat} (h : a ≤ 0) : |a| = -a := Rat.abs_of_nonpos h

theorem le_of_lt {a b : Rat} : a < b → a ≤ b := Rat.le_of_lt

theorem lt_of_le_of_lt {a b c : Rat} (h1 : a ≤ b) (h2 : b < c) : a < c := by grind

theorem le_refl (a : Rat) : a ≤ a := Rat.le_refl

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

theorem abs_zero : |(0 : Rat)| = 0 := Rat.abs_zero

theorem sub_zero (a : Rat) : a - 0 = a := by grind

theorem mul_zero (a : Rat) : a * 0 = 0 := Rat.mul_zero a

theorem zero_mul (a : Rat) : 0 * a = 0 := Rat.zero_mul a

theorem le_trans {a b c : Rat} : a ≤ b → b ≤ c → a ≤ c := Rat.le_trans

theorem lt_irrefl (a : Rat) : ¬a < a := by grind

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

theorem one_mul (a : Rat) : 1 * a = a := Rat.one_mul a

theorem mul_one (a : Rat) : a * 1 = a := Rat.mul_one a

theorem le_of_mul_le_mul_right {a b c : Rat} (h : a * c ≤ b * c) (hc : 0 < c) : a ≤ b :=
  Rat.le_of_mul_le_mul_right h hc

theorem abs_eq_zero {a : Rat} : |a| = 0 ↔ a = 0 := Rat.abs_eq_zero_iff

theorem lt_or_ge (a b : Rat) : a < b ∨ a ≥ b := by
  by_cases h : a < b
  · exact Or.inl h
  · exact Or.inr (Rat.not_lt.mp h)

protected theorem Rat.le_or_gt (a b : Rat) : a ≤ b ∨ a > b := by
  by_cases h : a ≤ b
  · exact Or.inl h
  · exact Or.inr (Rat.not_le.mp h)

theorem lt_of_le_of_ne {a b : Rat} (h : a ≤ b) (hne : a ≠ b) : a < b :=
  Rat.lt_of_le_of_ne h hne

protected theorem Rat.eq_or_lt_of_le {a b : Rat} (h : a ≤ b) : a = b ∨ a < b := by
  by_cases he : a = b
  · exact Or.inl he
  · exact Or.inr (Rat.lt_of_le_of_ne h he)

theorem mul_left_cancel₀ {a b c : Rat} (ha : a ≠ 0) (h : a * b = a * c) : b = c := by
  have h' : b * a = c * a := by grind
  exact (mul_left_inj' ha).mp h'

theorem abs_pos {a : Rat} : 0 < |a| ↔ a ≠ 0 := Rat.abs_pos_iff

end Srtfp.Compat

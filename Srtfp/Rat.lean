/- Core-only ℚ compatibility layer.

   The proof stack was written against Mathlib's rational-number surface;
   core Lean (`Init.Data.Rat`) provides the type, field arithmetic, order,
   and `zpow`, but not the `ℚ` notation, `abs`, or the `|·|` bars. This
   file supplies exactly that missing surface.

   Everything lives in the `Srtfp.Compat` namespace with scoped
   notation, so importing srtfp never collides with Mathlib's root
   names; proof files start with `open Srtfp.Compat`. -/

namespace Srtfp.Compat

@[inherit_doc] scoped notation "ℚ" => Rat
@[inherit_doc] scoped notation "ℤ" => Int
@[inherit_doc] scoped notation "ℕ" => Nat

universe u

/-- Absolute value on `ℚ`. Deliberately NOT named `Rat.abs`: newer cores
declare their own `Rat.abs` with a different (extensionally equal) body,
and keeping our copy under a separate name preserves `abs_def` as `rfl`
on every toolchain. -/
def ratAbs (q : ℚ) : ℚ := if q < 0 then -q else q

/-- Minimal stand-in for Mathlib's `Abs` class: just enough to give `|·|`
    a home. -/
class Abs (α : Type u) where
  /-- The absolute value, written `|a|`. -/
  abs : α → α

instance : Abs ℚ := ⟨ratAbs⟩

scoped macro:max atomic("|" noWs) a:term noWs "|" : term => `(Abs.abs $a)

namespace Rat

/- `neg_neg` / `neg_zero` exist in newer cores but not in v4.27; private
non-colliding copies keep this file toolchain-portable (they are only
used within this file). -/
private theorem rat_neg_neg (q : ℚ) : -(-q) = q := by
  calc -(-q) = -(-q) + 0 := (Rat.add_zero _).symm
    _ = -(-q) + (-q + q) := by rw [Rat.neg_add_cancel]
    _ = -(-q) + -q + q := by rw [Rat.add_assoc]
    _ = 0 + q := by rw [Rat.neg_add_cancel]
    _ = q := Rat.zero_add q

private theorem rat_neg_zero : -(0 : ℚ) = 0 := rfl

protected theorem neg_nonneg {q : ℚ} : 0 ≤ -q ↔ q ≤ 0 := by
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

protected theorem neg_lt_zero {q : ℚ} : -q < 0 ↔ 0 < q := by
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

theorem abs_def (q : ℚ) : |q| = if q < 0 then -q else q := rfl

theorem abs_of_nonneg {q : ℚ} (h : 0 ≤ q) : |q| = q := by
  rw [abs_def, if_neg (Rat.not_lt.mpr h)]

theorem abs_of_neg {q : ℚ} (h : q < 0) : |q| = -q := by
  rw [abs_def, if_pos h]

theorem abs_nonneg (q : ℚ) : 0 ≤ |q| := by
  rw [abs_def]; split
  · rename_i h; exact Rat.neg_nonneg.mpr (Rat.le_of_lt h)
  · rename_i h; exact Rat.not_lt.mp h

theorem abs_neg (q : ℚ) : |(-q)| = |q| := by
  by_cases h : q < 0
  · rw [abs_of_neg h, abs_of_nonneg (Rat.neg_nonneg.mpr (Rat.le_of_lt h))]
  · have h' : 0 ≤ q := Rat.not_lt.mp h
    by_cases h0 : q = 0
    · subst h0; rfl
    · have hpos : 0 < q := Rat.lt_of_le_of_ne h' (fun e => h0 e.symm)
      rw [abs_of_nonneg h', abs_of_neg (Rat.neg_lt_zero.mpr hpos), Rat.rat_neg_neg]

theorem abs_sub_comm (a b : ℚ) : |a - b| = |b - a| := by
  rw [show b - a = -(a - b) from (Rat.neg_sub a b).symm, abs_neg]

end RatAbs

/-! ### Generic order-lemma names used by the proof stack (Int-valued sites) -/

theorem lt_or_eq_of_le {a b : ℤ} (h : a ≤ b) : a < b ∨ a = b := by omega

theorem le_antisymm {a b : ℤ} (h1 : a ≤ b) (h2 : b ≤ a) : a = b := by omega

theorem eq_or_lt_of_le {a b : ℤ} (h : a ≤ b) : a = b ∨ a < b := by omega

theorem lt_trichotomy (a b : ℤ) : a < b ∨ a = b ∨ b < a := by omega

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

/-! ### ℚ compatibility aliases for TieBreak -/

theorem Int.cast_lt {a b : ℤ} : (a : ℚ) < (b : ℚ) ↔ a < b := Rat.intCast_lt_intCast

theorem Int.cast_inj {a b : ℤ} : (a : ℚ) = (b : ℚ) ↔ a = b := Rat.intCast_inj

theorem mul_lt_mul_iff_of_pos_right {a b c : ℚ} (hc : 0 < c) :
    a * c < b * c ↔ a < b := Rat.mul_lt_mul_right hc

theorem mul_left_inj' {a b c : ℚ} (hc : c ≠ 0) : a * c = b * c ↔ a = b := by
  constructor
  · intro h
    have hsub : (a - b) * c = 0 := by grind
    rcases Rat.mul_eq_zero.mp hsub with h0 | h0
    · grind
    · exact absurd h0 hc
  · intro h; rw [h]

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

theorem not_lt {a b : ℚ} : ¬a < b ↔ b ≤ a := Rat.not_lt

theorem lt_of_not_ge {a b : ℚ} (h : ¬a ≥ b) : a < b := Rat.not_le.mp h

theorem abs_of_nonpos {a : ℚ} (h : a ≤ 0) : |a| = -a := by
  by_cases h0 : a < 0
  · exact abs_of_neg h0
  · have ha : a = 0 := by grind
    rw [ha]
    rfl

theorem le_of_lt {a b : ℚ} : a < b → a ≤ b := Rat.le_of_lt

theorem le_of_eq {a b : ℚ} (h : a = b) : a ≤ b := by grind

theorem lt_of_le_of_lt {a b c : ℚ} (h1 : a ≤ b) (h2 : b < c) : a < c := by grind

theorem le_refl (a : ℚ) : a ≤ a := Rat.le_refl

theorem le_or_gt (a b : ℤ) : a ≤ b ∨ a > b := by omega

theorem one_le_pow_rat {a : ℚ} (ha : 1 ≤ a) : ∀ m : Nat, 1 ≤ a ^ m
  | 0 => by rw [Rat.pow_zero]; exact Rat.le_refl
  | (m+1) => by
    rw [Rat.pow_succ]
    have ih := one_le_pow_rat ha m
    have h0 : (0 : ℚ) ≤ a ^ m := by grind
    have := Rat.mul_le_mul_of_nonneg_left ha h0
    grind

theorem one_le_zpow_of_nonneg {a : ℚ} (ha : 1 ≤ a) {n : ℤ} (hn : 0 ≤ n) : 1 ≤ a ^ n := by
  have h := Rat.zpow_natCast a n.toNat
  rw [Int.toNat_of_nonneg hn] at h
  rw [h]
  exact one_le_pow_rat ha n.toNat

theorem zpow_le_zpow_right₀ {a : ℚ} (ha : 1 ≤ a) {m n : ℤ} (h : m ≤ n) : a ^ m ≤ a ^ n := by
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

/-! ### grind hints: ℚ order/monotonicity facts the proof stack leans on -/

attribute [grind .] Rat.mul_le_mul_of_nonneg_left Rat.mul_le_mul_of_nonneg_right
  Rat.mul_lt_mul_of_pos_left Rat.mul_lt_mul_of_pos_right
  Rat.mul_pos Rat.mul_nonneg Rat.natCast_nonneg

theorem abs_zero : |(0 : ℚ)| = 0 := rfl

theorem sub_zero (a : ℚ) : a - 0 = a := by grind

theorem mul_zero (a : ℚ) : a * 0 = 0 := Rat.mul_zero a

theorem zero_mul (a : ℚ) : 0 * a = 0 := Rat.zero_mul a

theorem abs_le {a b : ℚ} : |a| ≤ b ↔ -b ≤ a ∧ a ≤ b := by
  rw [abs_def]
  split <;> rename_i h <;> constructor <;> intro hh <;> first | grind | (constructor <;> grind)

theorem le_trans {a b c : ℚ} : a ≤ b → b ≤ c → a ≤ c := Rat.le_trans

theorem lt_of_lt_of_le {a b c : ℚ} (h1 : a < b) (h2 : b ≤ c) : a < c := by grind

theorem lt_irrefl (a : ℚ) : ¬a < a := by grind

protected theorem Rat.pow_add (a : ℚ) (m n : ℕ) : a ^ (m + n) = a ^ m * a ^ n := by
  induction n with
  | zero => rw [Nat.add_zero, Rat.pow_zero]; grind
  | succ n ih =>
    rw [show m + (n+1) = (m+n) + 1 from by omega, Rat.pow_succ, ih, Rat.pow_succ]
    grind

instance : Trans (α := ℚ) (· < ·) (· ≤ ·) (· < ·) := ⟨fun h1 h2 => lt_of_lt_of_le h1 h2⟩
instance : Trans (α := ℚ) (· ≤ ·) (· < ·) (· < ·) := ⟨fun h1 h2 => lt_of_le_of_lt h1 h2⟩
instance : Trans (α := ℚ) (· ≤ ·) (· ≤ ·) (· ≤ ·) := ⟨fun h1 h2 => Rat.le_trans h1 h2⟩
instance : Trans (α := ℚ) (· < ·) (· < ·) (· < ·) :=
  ⟨fun h1 h2 => lt_of_lt_of_le h1 (Rat.le_of_lt h2)⟩

protected theorem Rat.lt_trichotomy (a b : ℚ) : a < b ∨ a = b ∨ b < a := by
  rcases Rat.le_total (a := a) (b := b) with h | h
  · by_cases he : a = b
    · exact Or.inr (Or.inl he)
    · exact Or.inl (Rat.lt_of_le_of_ne h he)
  · by_cases he : b = a
    · exact Or.inr (Or.inl he.symm)
    · exact Or.inr (Or.inr (Rat.lt_of_le_of_ne h he))

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

theorem one_mul (a : ℚ) : 1 * a = a := Rat.one_mul a

theorem mul_one (a : ℚ) : a * 1 = a := Rat.mul_one a

theorem le_of_mul_le_mul_right {a b c : ℚ} (h : a * c ≤ b * c) (hc : 0 < c) : a ≤ b :=
  Rat.le_of_mul_le_mul_right h hc

theorem sub_lt_sub_left {a b : ℚ} (h : a < b) (c : ℚ) : c - b < c - a := by grind

theorem abs_eq_zero {a : ℚ} : |a| = 0 ↔ a = 0 := by
  rw [abs_def]; split <;> grind

theorem abs_cases (a : ℚ) : |a| = a ∧ 0 ≤ a ∨ |a| = -a ∧ a < 0 := by
  by_cases h : a < 0
  · right; exact ⟨abs_of_neg h, h⟩
  · left; exact ⟨abs_of_nonneg (Rat.not_lt.mp h), Rat.not_lt.mp h⟩

theorem sub_pos {a b : ℚ} : 0 < a - b ↔ b < a := by grind

theorem lt_or_ge (a b : ℚ) : a < b ∨ a ≥ b := by
  by_cases h : a < b
  · exact Or.inl h
  · exact Or.inr (Rat.not_lt.mp h)

protected theorem Rat.le_or_gt (a b : ℚ) : a ≤ b ∨ a > b := by
  by_cases h : a ≤ b
  · exact Or.inl h
  · exact Or.inr (Rat.not_le.mp h)

theorem lt_of_le_of_ne {a b : ℚ} (h : a ≤ b) (hne : a ≠ b) : a < b :=
  Rat.lt_of_le_of_ne h hne

protected theorem Rat.eq_or_lt_of_le {a b : ℚ} (h : a ≤ b) : a = b ∨ a < b := by
  by_cases he : a = b
  · exact Or.inl he
  · exact Or.inr (Rat.lt_of_le_of_ne h he)

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

theorem mul_left_cancel₀ {a b c : ℚ} (ha : a ≠ 0) (h : a * b = a * c) : b = c := by
  have h' : b * a = c * a := by grind
  exact (mul_left_inj' ha).mp h'

/-- Mathlib-style unique existence (vendored: core has no `∃!`). -/
def ExistsUnique {α : Sort u} (p : α → Prop) : Prop := ∃ x, p x ∧ ∀ y, p y → y = x

open Lean in
@[inherit_doc ExistsUnique]
scoped macro "∃!" xs:explicitBinders ", " b:term : term => do
  return ⟨← expandExplicitBinders ``ExistsUnique xs b⟩

/-- `dvd_pow` for `Nat` (vendored). -/
theorem Nat.dvd_pow' {a b : Nat} (h : a ∣ b) {n : Nat} (hn : n ≠ 0) : a ∣ b ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.pow_succ]
  exact Nat.dvd_trans h (Nat.dvd_mul_left b (b ^ m))

theorem abs_pos {a : ℚ} : 0 < |a| ↔ a ≠ 0 := by
  constructor
  · intro h he
    rw [he] at h
    exact lt_irrefl _ h
  · intro h
    rcases (abs_nonneg a) |> Rat.eq_or_lt_of_le with he | hlt
    · exact absurd (abs_eq_zero.mp he.symm) h
    · exact hlt

theorem lt_trans {a b c : ℚ} (h1 : a < b) (h2 : b < c) : a < c := by grind

/-- `dvd_pow_self` for `Nat` (vendored). -/
theorem dvd_pow_self (a : Nat) {n : Nat} (hn : n ≠ 0) : a ∣ a ^ n :=
  Nat.dvd_pow' (Nat.dvd_refl a) hn

end Srtfp.Compat

module
/- What core's `Init.Data.Rat` lacks and the proofs use: the `|·|` bars for
   `Rat.abs`, order facts and the `Trans` instances behind `calc`, division
   and cancellation, integer powers and their monotonicity, floors of
   quotients. Everything lives in the `Srtfp.Compat` namespace with scoped
   notation; proof files start with `open Srtfp.Compat`. -/

@[expose] public section

namespace Srtfp.Compat

/-! ## Notation and order -/

/-- `|a|` is core's `Rat.abs`. -/
scoped macro:max atomic("|" noWs) a:term noWs "|" : term => `(Rat.abs $a)

theorem abs_def (q : Rat) : |q| = if 0 ≤ q then q else -q := rfl

theorem eq_or_lt_of_le {a b : Int} (h : a ≤ b) : a = b ∨ a < b := by omega

theorem lt_of_le_of_lt {a b c : Rat} (h1 : a ≤ b) (h2 : b < c) : a < c := by grind
theorem lt_of_lt_of_le {a b c : Rat} (h1 : a < b) (h2 : b ≤ c) : a < c := by grind

instance : Trans (α := Rat) (· < ·) (· ≤ ·) (· < ·) := ⟨lt_of_lt_of_le⟩
instance : Trans (α := Rat) (· ≤ ·) (· < ·) (· < ·) := ⟨lt_of_le_of_lt⟩
instance : Trans (α := Rat) (· ≤ ·) (· ≤ ·) (· ≤ ·) := ⟨Rat.le_trans⟩
instance : Trans (α := Rat) (· < ·) (· < ·) (· < ·) := ⟨fun h1 h2 => lt_of_lt_of_le h1 (Rat.le_of_lt h2)⟩

theorem lt_or_ge (a b : Rat) : a < b ∨ a ≥ b := by grind
protected theorem Rat.lt_trichotomy (a b : Rat) : a < b ∨ a = b ∨ b < a := by grind
protected theorem Rat.eq_or_lt_of_le {a b : Rat} (h : a ≤ b) : a = b ∨ a < b := by grind
theorem sub_zero (a : Rat) : a - 0 = a := by grind

/-! ### grind hints: the monotonicity facts the proofs lean on -/

attribute [grind .] Rat.mul_le_mul_of_nonneg_left Rat.mul_le_mul_of_nonneg_right
  Rat.mul_lt_mul_of_pos_left Rat.mul_lt_mul_of_pos_right
  Rat.mul_pos Rat.mul_nonneg Rat.natCast_nonneg

/-! ## Multiplication and division -/

theorem mul_left_inj' {a b c : Rat} (hc : c ≠ 0) : a * c = b * c ↔ a = b :=
  ⟨fun h => by rw [← Rat.mul_div_cancel hc (a := a), h, Rat.mul_div_cancel hc], fun h => by rw [h]⟩

theorem mul_left_cancel₀ {a b c : Rat} (ha : a ≠ 0) (h : a * b = a * c) : b = c :=
  (mul_left_inj' ha).mp (by rw [Rat.mul_comm b, Rat.mul_comm c, h])

theorem div_le_iff {a b c : Rat} (hc : 0 < c) : a / c ≤ b ↔ a ≤ b * c := by
  rw [← Rat.not_lt, ← Rat.not_lt, Rat.lt_div_iff hc]

theorem le_div_iff {a b c : Rat} (hc : 0 < c) : a ≤ b / c ↔ a * c ≤ b := by
  rw [← Rat.not_lt, ← Rat.not_lt, Rat.div_lt_iff hc]

theorem div_eq_iff {a b c : Rat} (hc : 0 < c) : a / c = b ↔ a = b * c :=
  ⟨fun h => by rw [← h, Rat.div_mul_cancel (Rat.ne_of_gt hc)],
   fun h => by rw [h, Rat.mul_div_cancel (Rat.ne_of_gt hc)]⟩

theorem eq_div_iff {a b c : Rat} (hc : 0 < c) : a = b / c ↔ a * c = b := by
  rw [eq_comm, div_eq_iff hc, eq_comm]

theorem div_div (a b c : Rat) : a / (b * c) = a / b / c := by
  rw [Rat.div_def, Rat.div_def, Rat.div_def, Rat.inv_mul_rev, Rat.mul_comm c⁻¹, Rat.mul_assoc]

theorem div_mul_mul {a b d : Rat} (hb : b ≠ 0) : a / b * (b * d) = a * d := by
  rw [← Rat.mul_assoc, Rat.div_mul_cancel hb]

theorem div_mul_div_comm (a b c d : Rat) : a / b * (c / d) = a * c / (b * d) := by
  rw [Rat.div_def, Rat.div_def, Rat.div_def, Rat.inv_mul_rev]; grind

theorem div_le_div_iff {a b c d : Rat} (hb : 0 < b) (hd : 0 < d) :
    a / b ≤ c / d ↔ a * d ≤ c * b := by
  rw [← div_mul_mul (Rat.ne_of_gt hb) (d := d), ← div_mul_mul (Rat.ne_of_gt hd) (d := b), Rat.mul_comm d b]
  exact ⟨fun h => Rat.mul_le_mul_of_nonneg_right h (Rat.le_of_lt (Rat.mul_pos hb hd)),
    fun h => Rat.le_of_mul_le_mul_right h (Rat.mul_pos hb hd)⟩

theorem div_lt_div_iff {a b c d : Rat} (hb : 0 < b) (hd : 0 < d) :
    a / b < c / d ↔ a * d < c * b := by
  rw [← div_mul_mul (Rat.ne_of_gt hb) (d := d), ← div_mul_mul (Rat.ne_of_gt hd) (d := b), Rat.mul_comm d b,
    Rat.mul_lt_mul_right (Rat.mul_pos hb hd)]

theorem div_nonneg {a b : Rat} (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ a / b :=
  (le_div_iff hb).mpr (by grind)

theorem div_pos {a b : Rat} (ha : 0 < a) (hb : 0 < b) : 0 < a / b :=
  (Rat.lt_div_iff hb).mpr (by grind)

/-- `p / A < r / B` from `p · B < r · A`, for positive `A`, `B`. -/
theorem mul_inv_lt_mul_inv {A B p r : Rat} (hA : 0 < A) (hB : 0 < B) (h : p * B < r * A) :
    p * A⁻¹ < r * B⁻¹ := by
  have hA' := Rat.mul_inv_cancel A (Rat.ne_of_gt hA)
  have hB' := Rat.mul_inv_cancel B (Rat.ne_of_gt hB)
  rw [← Rat.mul_lt_mul_right (Rat.mul_pos hA hB),
    show p * A⁻¹ * (A * B) = p * B by grind, show r * B⁻¹ * (A * B) = r * A by grind]
  exact h

theorem mul_inv_le_mul_inv {A B p r : Rat} (hA : 0 < A) (hB : 0 < B) (h : p * B ≤ r * A) :
    p * A⁻¹ ≤ r * B⁻¹ := by
  have hA' := Rat.mul_inv_cancel A (Rat.ne_of_gt hA)
  have hB' := Rat.mul_inv_cancel B (Rat.ne_of_gt hB)
  refine Rat.le_of_mul_le_mul_right ?_ (Rat.mul_pos hA hB)
  rw [show p * A⁻¹ * (A * B) = p * B by grind, show r * B⁻¹ * (A * B) = r * A by grind]
  exact h

theorem inv_lt_inv {a b : Rat} (ha : 0 < a) (h : a < b) : b⁻¹ < a⁻¹ := by
  have := mul_inv_lt_mul_inv (p := 1) (r := 1) (by grind : 0 < b) ha (by grind); grind

theorem inv_le_inv {a b : Rat} (ha : 0 < a) (h : a ≤ b) : b⁻¹ ≤ a⁻¹ := by
  have := mul_inv_le_mul_inv (p := 1) (r := 1) (by grind : 0 < b) ha (by grind); grind

/-! ## Powers -/

protected theorem Rat.pow_add (a : Rat) (m n : Nat) : a ^ (m + n) = a ^ m * a ^ n := by
  induction n with
  | zero => rw [Nat.add_zero, Rat.pow_zero, Rat.mul_one]
  | succ n ih => rw [← Nat.add_assoc, Rat.pow_succ, ih, Rat.pow_succ, Rat.mul_assoc]

theorem one_le_pow {a : Rat} (ha : 1 ≤ a) (n : Nat) : 1 ≤ a ^ n := by
  induction n with
  | zero => rw [Rat.pow_zero]; exact Rat.le_refl
  | succ n ih => rw [Rat.pow_succ]; have := Rat.mul_le_mul_of_nonneg_left ha (by grind : (0 : Rat) ≤ a ^ n); grind

theorem ten_pow_split (n : Nat) : (10 : Rat) ^ n = 2 ^ n * 5 ^ n := by
  have : ((10 ^ n : Nat) : Rat) = ((2 ^ n * 5 ^ n : Nat) : Rat) := by rw [← Nat.mul_pow]
  exact_mod_cast this

/-! ## Integer powers -/

theorem two_zpow_pos (q : Int) : (0 : Rat) < 2 ^ q := Rat.zpow_pos (by decide)
theorem ten_zpow_pos (q : Int) : (0 : Rat) < 10 ^ q := Rat.zpow_pos (by decide)

theorem zpow_mul_neg {b : Rat} (hb : b ≠ 0) (e : Int) : b ^ e * b ^ (-e) = 1 := by
  rw [← Rat.zpow_add hb, show e + -e = 0 by omega, Rat.zpow_zero]

/-- A nonnegative integer exponent is a natural one. -/
theorem zpow_toNat {b : Rat} {e : Int} (he : 0 ≤ e) : b ^ e = b ^ e.toNat := by
  rw [← Rat.zpow_natCast, Int.toNat_of_nonneg he]

theorem zpow_neg_toNat {b : Rat} {e : Int} (he : 0 ≤ e) : b ^ (-e) = (b ^ e.toNat)⁻¹ := by
  rw [Rat.zpow_neg, zpow_toNat he]

theorem zpow_neg_natCast (b : Rat) (n : Nat) : b ^ (-(n : Int)) = (b ^ n)⁻¹ := by
  rw [Rat.zpow_neg, Rat.zpow_natCast]

theorem two_zpow_natCast (n : Nat) : (2 : Rat) ^ (n : Int) = ((2 ^ n : Nat) : Rat) := by
  rw [Rat.zpow_natCast]; push_cast; rfl
theorem ten_zpow_natCast (n : Nat) : (10 : Rat) ^ (n : Int) = ((10 ^ n : Nat) : Rat) := by
  rw [Rat.zpow_natCast]; push_cast; rfl
theorem two_zpow_toNat {e : Int} (he : 0 ≤ e) : (2 : Rat) ^ e = ((2 ^ e.toNat : Nat) : Rat) := by
  rw [← two_zpow_natCast, Int.toNat_of_nonneg he]
theorem ten_zpow_toNat {e : Int} (he : 0 ≤ e) : (10 : Rat) ^ e = ((10 ^ e.toNat : Nat) : Rat) := by
  rw [← ten_zpow_natCast, Int.toNat_of_nonneg he]
theorem two_zpow_neg_toNat {e : Int} (he : 0 ≤ e) : (2 : Rat) ^ (-e) = (((2 ^ e.toNat : Nat) : Rat))⁻¹ := by
  rw [Rat.zpow_neg, two_zpow_toNat he]
theorem ten_zpow_neg_toNat {e : Int} (he : 0 ≤ e) : (10 : Rat) ^ (-e) = (((10 ^ e.toNat : Nat) : Rat))⁻¹ := by
  rw [Rat.zpow_neg, ten_zpow_toNat he]

/-- `b^i = b^j · b^(i-j)` for `j ≤ i`, the difference a natural. -/
theorem zpow_split {b : Rat} (hb : b ≠ 0) {i j : Int} (hj : j ≤ i) :
    b ^ i = b ^ j * b ^ (i - j).toNat := by
  rw [← zpow_toNat (by omega), ← Rat.zpow_add hb, show j + (i - j) = i by omega]

/-- `b^i / b^j = b^(i-j)`. -/
theorem zpow_sub {b : Rat} (hb : b ≠ 0) (i j : Int) : b ^ (i - j) = b ^ i / b ^ j := by
  rw [Int.sub_eq_add_neg, Rat.zpow_add hb, Rat.zpow_neg, Rat.div_def]

/-- `b^e` as a quotient of natural powers. -/
theorem zpow_eq_div (b : Rat) (e : Int) : b ^ e = b ^ e.toNat / b ^ (-e).toNat := by
  rcases Int.le_total 0 e with he | he
  · rw [zpow_toNat he, show (-e).toNat = 0 by omega, Rat.pow_zero, Rat.div_def,
      Rat.inv_eq_of_mul_eq_one (Rat.mul_one 1), Rat.mul_one]
  · rw [show e = -(-e) by omega, zpow_neg_toNat (by omega), Int.neg_neg, show e.toNat = 0 by omega,
      Rat.pow_zero, Rat.div_def, Rat.one_mul]

/-- `b^q · b^{max(-q,0)} = b^{max(q,0)}`. -/
theorem zpow_split_gen (b : Rat) (hb : b ≠ 0) (q : Int) :
    b ^ q * b ^ (if q < 0 then (-q).toNat else 0) = b ^ (if q ≥ 0 then q.toNat else 0) := by
  split
  · rw [if_neg (by omega), ← zpow_toNat (b := b) (by omega), zpow_mul_neg hb, Rat.pow_zero]
  · rw [if_pos (by omega), Rat.pow_zero, Rat.mul_one, zpow_toNat (by omega)]

theorem one_le_zpow_of_nonneg {a : Rat} (ha : 1 ≤ a) {n : Int} (hn : 0 ≤ n) : 1 ≤ a ^ n := by
  rw [zpow_toNat hn]; exact one_le_pow ha _

theorem zpow_le_zpow_right₀ {a : Rat} (ha : 1 ≤ a) {m n : Int} (h : m ≤ n) : a ^ m ≤ a ^ n := by
  rw [zpow_split (by grind) h]
  have := Rat.mul_le_mul_of_nonneg_left (one_le_pow ha (n - m).toNat)
    (Rat.le_of_lt (Rat.zpow_pos (n := m) (by grind : (0 : Rat) < a)))
  grind

theorem zpow_lt_zpow {a : Rat} (ha : 1 < a) {x y : Int} (h : x < y) : a ^ x < a ^ y := by
  rw [zpow_split (by grind) (Int.le_of_lt h), show (y - x).toNat = (y - x - 1).toNat + 1 by omega,
    Rat.pow_succ]
  have h1 := Rat.mul_le_mul_of_nonneg_right (one_le_pow (Rat.le_of_lt ha) (y - x - 1).toNat)
    (by grind : (0 : Rat) ≤ a)
  have h2 := Rat.zpow_pos (n := x) (by grind : (0 : Rat) < a)
  have := Rat.mul_lt_mul_of_pos_left (show 1 < a ^ (y - x - 1).toNat * a by grind) h2
  grind

theorem lt_of_zpow_lt {a : Rat} (ha : 1 ≤ a) {x y : Int} (h : a ^ x < a ^ y) : x < y := by
  rcases Int.lt_or_le x y with h' | h'
  · exact h'
  · exact absurd h (Rat.not_lt.mpr (zpow_le_zpow_right₀ ha h'))

theorem le_of_zpow_le {a : Rat} (ha : 1 < a) {x y : Int} (h : a ^ x ≤ a ^ y) : x ≤ y := by
  rcases Int.lt_or_le y x with h' | h'
  · exact absurd (zpow_lt_zpow ha h') (Rat.not_lt.mpr h)
  · exact h'

/-! ## Ratios of powers of two and ten, cross-multiplied

`b^e` is `N_b / D_b` with `N_b = b^|e|`, `D_b = 1` for `e ≥ 0` and `N_b = 1`,
`D_b = b^|e|` otherwise; comparing `a · 10^x` with `c · 2^y` is comparing the
naturals `a · N₁₀ · D₂` and `c · N₂ · D₁₀`. -/

theorem zpow_ratio (b : Nat) (hb : 0 < b) (e : Int) :
    (b : Rat) ^ e * ((if e ≥ 0 then 1 else b ^ e.natAbs : Nat) : Rat)
      = ((if e ≥ 0 then b ^ e.natAbs else 1 : Nat) : Rat) := by
  have hbq : (b : Rat) ≠ 0 := Rat.ne_of_gt (by exact_mod_cast hb)
  by_cases he : e ≥ 0
  · rw [if_pos he, if_pos he]; push_cast
    rw [Rat.mul_one, ← Rat.zpow_natCast, Int.natAbs_of_nonneg he]
  · rw [if_neg he, if_neg he]; push_cast
    rw [← Rat.zpow_natCast, Int.ofNat_natAbs_of_nonpos (by omega), ← Rat.zpow_add hbq,
      show e + -e = 0 by omega, Rat.zpow_zero]

theorem denom_pos (b : Nat) (hb : 0 < b) (e : Int) :
    (0 : Rat) < ((if e ≥ 0 then 1 else b ^ e.natAbs : Nat) : Rat) := by
  have : 0 < (if e ≥ 0 then 1 else b ^ e.natAbs : Nat) := by split <;> first | decide | exact Nat.pow_pos hb
  exact_mod_cast this

/-- The cross-multiplied `Nat` forms of `a·10^x` and `c·2^y` are the rationals
    scaled by one positive `D`. -/
theorem cross_eq (a c : Nat) (x y : Int) :
    ∃ D : Rat, 0 < D
      ∧ ((a * (if x ≥ 0 then 10 ^ x.natAbs else 1) * (if y ≥ 0 then 1 else 2 ^ y.natAbs) : Nat) : Rat)
          = (a : Rat) * (10 : Rat) ^ x * D
      ∧ ((c * (if y ≥ 0 then 2 ^ y.natAbs else 1) * (if x ≥ 0 then 1 else 10 ^ x.natAbs) : Nat) : Rat)
          = (c : Rat) * (2 : Rat) ^ y * D := by
  refine ⟨_, Rat.mul_pos (denom_pos 2 (by decide) y) (denom_pos 10 (by decide) x), ?_, ?_⟩
  · push_cast; rw [← zpow_ratio 10 (by decide) x]; push_cast; grind
  · push_cast; rw [← zpow_ratio 2 (by decide) y]; push_cast; grind

theorem le_of_ratio {a c : Nat} {x y : Int}
    (h : a * (if x ≥ 0 then 10 ^ x.natAbs else 1) * (if y ≥ 0 then 1 else 2 ^ y.natAbs)
        ≤ c * (if y ≥ 0 then 2 ^ y.natAbs else 1) * (if x ≥ 0 then 1 else 10 ^ x.natAbs)) :
    (a : Rat) * (10 : Rat) ^ x ≤ (c : Rat) * (2 : Rat) ^ y := by
  obtain ⟨D, hD, e1, e2⟩ := cross_eq a c x y
  exact Rat.le_of_mul_le_mul_right (by rw [← e1, ← e2]; exact_mod_cast h) hD

theorem lt_of_ratio' {a c : Nat} {x y : Int}
    (h : a * (if x ≥ 0 then 10 ^ x.natAbs else 1) * (if y ≥ 0 then 1 else 2 ^ y.natAbs)
        < c * (if y ≥ 0 then 2 ^ y.natAbs else 1) * (if x ≥ 0 then 1 else 10 ^ x.natAbs)) :
    (a : Rat) * (10 : Rat) ^ x < (c : Rat) * (2 : Rat) ^ y := by
  obtain ⟨D, hD, e1, e2⟩ := cross_eq a c x y
  exact Rat.lt_of_mul_lt_mul_right (by rw [← e1, ← e2]; exact_mod_cast h) (Rat.le_of_lt hD)

theorem le_of_ratio' {a c : Nat} {x y : Int}
    (h : c * (if y ≥ 0 then 2 ^ y.natAbs else 1) * (if x ≥ 0 then 1 else 10 ^ x.natAbs)
        ≤ a * (if x ≥ 0 then 10 ^ x.natAbs else 1) * (if y ≥ 0 then 1 else 2 ^ y.natAbs)) :
    (c : Rat) * (2 : Rat) ^ y ≤ (a : Rat) * (10 : Rat) ^ x := by
  obtain ⟨D, hD, e1, e2⟩ := cross_eq a c x y
  exact Rat.le_of_mul_le_mul_right (by rw [← e1, ← e2]; exact_mod_cast h) hD

theorem lt_of_ratio {a c : Nat} {x y : Int}
    (h : c * (if y ≥ 0 then 2 ^ y.natAbs else 1) * (if x ≥ 0 then 1 else 10 ^ x.natAbs)
        < a * (if x ≥ 0 then 10 ^ x.natAbs else 1) * (if y ≥ 0 then 1 else 2 ^ y.natAbs)) :
    (c : Rat) * (2 : Rat) ^ y < (a : Rat) * (10 : Rat) ^ x := by
  obtain ⟨D, hD, e1, e2⟩ := cross_eq a c x y
  exact Rat.lt_of_mul_lt_mul_right (by rw [← e1, ← e2]; exact_mod_cast h) (Rat.le_of_lt hD)

/-- The comparisons between plain powers (`a = c = 1`). -/
theorem two_zpow_le_ten_zpow {x y : Int}
    (h : (if y ≥ 0 then 2 ^ y.natAbs else 1) * (if x ≥ 0 then 1 else 10 ^ x.natAbs)
        ≤ (if x ≥ 0 then 10 ^ x.natAbs else 1) * (if y ≥ 0 then 1 else 2 ^ y.natAbs)) :
    (2 : Rat) ^ y ≤ (10 : Rat) ^ x :=
  Rat.le_of_mul_le_mul_left
    (le_of_ratio' (a := 1) (c := 1) (by rw [Nat.one_mul, Nat.one_mul]; exact h)) (by decide)

theorem two_zpow_lt_ten_zpow {x y : Int}
    (h : (if y ≥ 0 then 2 ^ y.natAbs else 1) * (if x ≥ 0 then 1 else 10 ^ x.natAbs)
        < (if x ≥ 0 then 10 ^ x.natAbs else 1) * (if y ≥ 0 then 1 else 2 ^ y.natAbs)) :
    (2 : Rat) ^ y < (10 : Rat) ^ x :=
  Rat.lt_of_mul_lt_mul_left
    (lt_of_ratio (a := 1) (c := 1) (by rw [Nat.one_mul, Nat.one_mul]; exact h)) (by decide)

theorem ten_zpow_lt_two_zpow {x y : Int}
    (h : (if x ≥ 0 then 10 ^ x.natAbs else 1) * (if y ≥ 0 then 1 else 2 ^ y.natAbs)
        < (if y ≥ 0 then 2 ^ y.natAbs else 1) * (if x ≥ 0 then 1 else 10 ^ x.natAbs)) :
    (10 : Rat) ^ x < (2 : Rat) ^ y :=
  Rat.lt_of_mul_lt_mul_left
    (lt_of_ratio' (a := 1) (c := 1) (by rw [Nat.one_mul, Nat.one_mul]; exact h)) (by decide)

/-! ## Floors -/

theorem floor_nonneg {x : Rat} (hx : 0 ≤ x) : 0 ≤ x.floor := Rat.le_floor_iff.mpr (by exact_mod_cast hx)

/-- The floor is the integer `h` with `h ≤ y < h + 1`. -/
theorem floor_eq_of {y : Rat} {h : Int} (h1 : (h : Rat) ≤ y) (h2 : y < h + 1) : y.floor = h := by
  have := Rat.le_floor_iff.mpr h1
  have := Rat.floor_lt_iff.mpr (show y < ((h + 1 : Int) : Rat) by push_cast; exact h2)
  omega

/-- Integer division brackets the rational quotient. -/
theorem natDiv_bounds (N D : Nat) (hD : 0 < D) :
    ((N / D : Nat) : Rat) ≤ N / D ∧ (N : Rat) / D < (N / D : Nat) + 1 := by
  have hDq : (0 : Rat) < D := by exact_mod_cast hD
  have hlt : N < (N / D + 1) * D := by rw [Nat.mul_comm]; exact Nat.lt_mul_div_succ N hD
  exact ⟨(le_div_iff hDq).mpr (by exact_mod_cast Nat.div_mul_le_self N D),
    (Rat.div_lt_iff hDq).mpr (by exact_mod_cast hlt)⟩

/-- `⌊x / n⌋ = ⌊x⌋ / n` for a positive natural `n`. -/
theorem floor_div_natCast (x : Rat) {n : Nat} (hn : 0 < n) : (x / n).floor = x.floor / n := by
  have hnq : (0 : Rat) < n := by exact_mod_cast hn
  have hnz : (n : Int) ≠ 0 := by omega
  refine floor_eq_of ((le_div_iff hnq).mpr ?_) ((Rat.div_lt_iff hnq).mpr ?_)
  · exact Rat.le_trans (by exact_mod_cast Int.ediv_mul_le x.floor hnz) (Rat.floor_le x)
  · exact lt_of_lt_of_le (Rat.lt_floor_add_one x)
      (by exact_mod_cast Int.lt_ediv_add_one_mul_self x.floor (by omega : (0 : Int) < n))

theorem floor_natDiv (N D : Nat) (hD : 0 < D) : ((N : Rat) / D).floor = ((N / D : Nat) : Int) :=
  floor_eq_of (by exact_mod_cast (natDiv_bounds N D hD).1) (by exact_mod_cast (natDiv_bounds N D hD).2)

theorem frac_natDiv (N D : Nat) (hD : 0 < D) :
    (N : Rat) / D - ((N / D : Nat) : Rat) = ((N % D : Nat) : Rat) / D := by
  have hDq : (0 : Rat) < D := by exact_mod_cast hD
  rw [eq_comm, div_eq_iff hDq]
  have := Rat.div_mul_cancel (a := (N : Rat)) (Rat.ne_of_gt hDq)
  have : (N : Rat) = ((D * (N / D) + N % D : Nat) : Rat) := by rw [Nat.div_add_mod]
  push_cast at this
  grind

end Srtfp.Compat

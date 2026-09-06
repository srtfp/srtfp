module
/- Result 20: from the per-exponent checks to the paper's quantities.

   With `k = kOfMQ c q` from R10, each of `2V`, `2V_l`, `2V_r` is
   `m'·2^{q'}·10^{-k}` with `m' < 2^54` and `q' ∈ {q, q−1}`, and R10 places
   `(q', k)` in one of three bands: `0 ≤ k ≤ q'` (a fraction over `5^k`),
   `q' ≤ k < 0` (a fraction over `2^{-q'+k}`), or `q' ≥ 0 > k` (an
   integer). The first two are what `checkAt` sweeps. -/

public import Srtfp.Perf.Schubfach.NadezhinDefs

@[expose] public section

open Srtfp.Compat

namespace Srtfp.Schubfach.R20

open Srtfp Srtfp.Printer Srtfp.Schubfach.Exact

variable {m : Nat} {q : Int}

/-! ## Powers -/

theorem lt_of_zpow_lt {a : Rat} (ha : 1 ≤ a) {x y : Int} (h : a ^ x < a ^ y) : x < y := by
  rcases Int.lt_or_le x y with hxy | hxy
  · exact hxy
  · exact absurd h (Rat.not_lt.mpr (zpow_le_zpow_right₀ ha hxy))

theorem zpow_lt_succ {a : Rat} (ha : 1 < a) (x : Int) : a ^ x < a ^ (x + 1) := by
  rw [Rat.zpow_add_one (by grind)]
  have hp := Rat.zpow_pos (n := x) (by grind : (0 : Rat) < a)
  calc a ^ x = a ^ x * 1 := (Rat.mul_one _).symm
    _ < a ^ x * a := Rat.mul_lt_mul_of_pos_left ha hp

theorem le_of_zpow_le {a : Rat} (ha : 1 < a) {x y : Int} (h : a ^ x ≤ a ^ y) : x ≤ y := by
  rcases Int.lt_or_le y x with hxy | hxy
  · have h1 : a ^ (y + 1) ≤ a ^ x := zpow_le_zpow_right₀ (Rat.le_of_lt ha) (by omega)
    have h2 := zpow_lt_succ ha y
    exact (Rat.lt_irrefl (lt_of_lt_of_le h2 (Rat.le_trans h1 h))).elim
  · exact hxy

theorem zpow_lt_of_lt {a : Rat} (ha : 1 < a) {x y : Int} (h : x < y) : a ^ x < a ^ y :=
  lt_of_lt_of_le (zpow_lt_succ ha x) (zpow_le_zpow_right₀ (Rat.le_of_lt ha) (by omega))

theorem ten_pow_split (n : Nat) : (10 : Rat) ^ n = (2 : Rat) ^ n * (5 : Rat) ^ n := by
  have : ((10 ^ n : Nat) : Rat) = ((2 ^ n * 5 ^ n : Nat) : Rat) := by rw [← Nat.mul_pow]
  push_cast at this
  exact this

/-- `2^j ≤ 10^j` for `j ≥ 0`. -/
theorem two_zpow_le_ten_zpow {j : Int} (hj : 0 ≤ j) : (2 : Rat) ^ j ≤ (10 : Rat) ^ j := by
  obtain ⟨n, rfl⟩ : ∃ n : Nat, j = n := ⟨j.toNat, by omega⟩
  rw [Rat.zpow_natCast, Rat.zpow_natCast]
  exact_mod_cast Nat.pow_le_pow_left (by decide : 2 ≤ 10) n

/-! ## The bands: `k` against `q` and `q − 1` (from R10) -/

theorem width_lt_two_zpow (hirr : isIrregular m q = true) :
    vr m q - vl m q = 3 / 4 * (2 : Rat) ^ q := by
  rw [width_eq, if_pos (isIrregular_iff.mp hirr)]

theorem width_eq_two_zpow (hirr : isIrregular m q = false) :
    vr m q - vl m q = (2 : Rat) ^ q := by
  rw [width_eq, if_neg (fun hc => by rw [isIrregular_iff.mpr hc] at hirr; cases hirr), Rat.one_mul]

/-- Regular spacing, `q < 0`: `k < 0`. -/
theorem band_reg_neg (h : InRange m q) (hirr : isIrregular m q = false) (hq : q < 0) :
    kOfMQ m q < 0 := by
  obtain ⟨h1, _⟩ := k_spec h
  rw [width_eq_two_zpow hirr] at h1
  generalize kOfMQ m q = k at *
  have hq1 : (2 : Rat) ^ q < 2 ^ (0 : Int) := zpow_lt_of_lt (by decide) hq
  rw [Rat.zpow_zero] at hq1
  have : (10 : Rat) ^ k < 10 ^ (0 : Int) := by rw [Rat.zpow_zero]; exact lt_of_le_of_lt h1 hq1
  exact lt_of_zpow_lt (by decide) this

/-- Regular spacing, `q ≥ 0`: `0 ≤ k ≤ q`. -/
theorem band_reg_nonneg (h : InRange m q) (hirr : isIrregular m q = false) (hq : 0 ≤ q) :
    0 ≤ kOfMQ m q ∧ kOfMQ m q ≤ q := by
  obtain ⟨h1, h2⟩ := k_spec h
  rw [width_eq_two_zpow hirr] at h1 h2
  generalize kOfMQ m q = k at *
  have hq1 : (2 : Rat) ^ (0 : Int) ≤ 2 ^ q := zpow_le_zpow_right₀ (by decide) hq
  rw [Rat.zpow_zero] at hq1
  have hk : 0 ≤ k := by
    have : (10 : Rat) ^ (0 : Int) < 10 ^ (k + 1) := by rw [Rat.zpow_zero]; exact lt_of_le_of_lt hq1 h2
    have := lt_of_zpow_lt (by decide) this
    omega
  refine ⟨hk, ?_⟩
  have : (2 : Rat) ^ k ≤ (2 : Rat) ^ q := Rat.le_trans (two_zpow_le_ten_zpow hk) h1
  exact le_of_zpow_le (by decide) this

/-- Irregular spacing, `q ≤ 0`: `k < 0`. -/
theorem band_irr_nonpos (h : InRange m q) (hirr : isIrregular m q = true) (hq : q ≤ 0) :
    kOfMQ m q < 0 := by
  obtain ⟨h1, _⟩ := k_spec h
  rw [width_lt_two_zpow hirr] at h1
  generalize kOfMQ m q = k at *
  have hq1 : (2 : Rat) ^ q ≤ 2 ^ (0 : Int) := zpow_le_zpow_right₀ (by decide) hq
  rw [Rat.zpow_zero] at hq1
  have : (10 : Rat) ^ k < 10 ^ (0 : Int) := by rw [Rat.zpow_zero]; grind
  exact lt_of_zpow_lt (by decide) this

/-- Irregular spacing, `q ≥ 1`: `0 ≤ k ≤ q − 1`. -/
theorem band_irr_pos (h : InRange m q) (hirr : isIrregular m q = true) (hq : 1 ≤ q) :
    0 ≤ kOfMQ m q ∧ kOfMQ m q ≤ q - 1 := by
  obtain ⟨h1, h2⟩ := k_spec h
  rw [width_lt_two_zpow hirr] at h1 h2
  generalize kOfMQ m q = k at *
  have hq1 : (2 : Rat) ^ (1 : Int) ≤ 2 ^ q := zpow_le_zpow_right₀ (by decide) hq
  have h21 : (2 : Rat) ^ (1 : Int) = 2 := by
    rw [show (1 : Int) = ((1 : Nat) : Int) from rfl, Rat.zpow_natCast]; simp
  rw [h21] at hq1
  have hk : 0 ≤ k := by
    have : (10 : Rat) ^ (0 : Int) < 10 ^ (k + 1) := by rw [Rat.zpow_zero]; grind
    have := lt_of_zpow_lt (by decide) this
    omega
  refine ⟨hk, ?_⟩
  have h2q : (0 : Rat) < 2 ^ q := Rat.zpow_pos (by decide)
  have : (2 : Rat) ^ k < (2 : Rat) ^ q := by
    have := two_zpow_le_ten_zpow hk
    grind
  have := lt_of_zpow_lt (by decide) this
  omega

/-! ## The quantities as fractions -/

/-- Band 2: `m'·2^{q'}·10^{-k} = m'·2^{q'-k} / 5^k`. -/
theorem band2_val (m' : Nat) {q' k : Int} (hk : 0 ≤ k) (hkq : k ≤ q') :
    (m' : Rat) * (2 : Rat) ^ q' * (10 : Rat) ^ (-k)
      = ((m' * 2 ^ (q' - k).toNat : Nat) : Rat) / ((5 ^ k.toNat : Nat) : Rat) := by
  have h5 : (0 : Rat) < ((5 ^ k.toNat : Nat) : Rat) := by exact_mod_cast Nat.pow_pos (by decide)
  rw [eq_comm, Reader.div_eq_iff h5]
  have e1 : (10 : Rat) ^ (-k) * (10 : Rat) ^ k = 1 := by
    rw [← Rat.zpow_add (by decide), show -k + k = 0 by omega, Rat.zpow_zero]
  have e2 : (10 : Rat) ^ k = ((2 ^ k.toNat : Nat) : Rat) * ((5 ^ k.toNat : Nat) : Rat) := by
    rw [← Int.toNat_of_nonneg hk, Rat.zpow_natCast, ten_pow_split, Int.toNat_natCast]; push_cast; rfl
  have e3 : (2 : Rat) ^ q' = ((2 ^ (q' - k).toNat : Nat) : Rat) * ((2 ^ k.toNat : Nat) : Rat) := by
    rw [show q' = (q' - k) + k by omega, Rat.zpow_add (by decide),
      show q' - k + k - k = q' - k by omega]
    rw [← Int.toNat_of_nonneg (by omega : 0 ≤ q' - k), ← Int.toNat_of_nonneg hk,
      Rat.zpow_natCast, Rat.zpow_natCast, Int.toNat_natCast, Int.toNat_natCast]
    push_cast; rfl
  rw [e2] at e1
  rw [e3]
  push_cast
  grind

/-- Band 1: `m'·2^{q'}·10^{-k} = m'·5^{-k} / 2^{-q'+k}`. -/
theorem band1_val (m' : Nat) {q' k : Int} (hk : k < 0) (hqk : q' ≤ k) :
    (m' : Rat) * (2 : Rat) ^ q' * (10 : Rat) ^ (-k)
      = ((m' * 5 ^ (-k).toNat : Nat) : Rat) / ((2 ^ (-q' + k).toNat : Nat) : Rat) := by
  have h2 : (0 : Rat) < ((2 ^ (-q' + k).toNat : Nat) : Rat) := by exact_mod_cast Nat.pow_pos (by decide)
  rw [eq_comm, Reader.div_eq_iff h2]
  have e1 : (2 : Rat) ^ q' * (2 : Rat) ^ (-q') = 1 := by
    rw [← Rat.zpow_add (by decide), show q' + -q' = 0 by omega, Rat.zpow_zero]
  have e2 : (10 : Rat) ^ (-k) = ((2 ^ (-k).toNat : Nat) : Rat) * ((5 ^ (-k).toNat : Nat) : Rat) := by
    rw [← Int.toNat_of_nonneg (by omega : 0 ≤ -k), Rat.zpow_natCast, ten_pow_split, Int.toNat_natCast]
    push_cast; rfl
  have e3 : (2 : Rat) ^ (-q') = ((2 ^ (-q' + k).toNat : Nat) : Rat) * ((2 ^ (-k).toNat : Nat) : Rat) := by
    push_cast
    rw [← Rat.zpow_natCast, ← Rat.zpow_natCast, Int.toNat_of_nonneg (by omega),
      Int.toNat_of_nonneg (by omega), ← Rat.zpow_add (by decide)]
    congr 1; omega
  rw [e3] at e1
  rw [e2]
  push_cast
  grind

/-- `q' ≥ 0 > k`: an integer. -/
theorem int_val (m' : Nat) {q' k : Int} (hq' : 0 ≤ q') (hk : k < 0) :
    (m' : Rat) * (2 : Rat) ^ q' * (10 : Rat) ^ (-k)
      = ((m' * 2 ^ q'.toNat * 10 ^ (-k).toNat : Nat) : Rat) := by
  rw [← Int.toNat_of_nonneg hq', ← Int.toNat_of_nonneg (by omega : 0 ≤ -k), Rat.zpow_natCast,
    Rat.zpow_natCast, Int.toNat_natCast, Int.toNat_natCast]
  push_cast; rfl

/-- `k < q' < 0`: also an integer. -/
theorem int_val' (m' : Nat) {q' k : Int} (hk : k < 0) (hkq : k < q') :
    (m' : Rat) * (2 : Rat) ^ q' * (10 : Rat) ^ (-k)
      = ((m' * 2 ^ (q' - k).toNat * 5 ^ (-k).toNat : Nat) : Rat) := by
  have e2 : (10 : Rat) ^ (-k) = ((2 ^ (-k).toNat : Nat) : Rat) * ((5 ^ (-k).toNat : Nat) : Rat) := by
    rw [← Int.toNat_of_nonneg (by omega : 0 ≤ -k), Rat.zpow_natCast, ten_pow_split, Int.toNat_natCast]
    push_cast; rfl
  have e3 : (2 : Rat) ^ q' * ((2 ^ (-k).toNat : Nat) : Rat) = ((2 ^ (q' - k).toNat : Nat) : Rat) := by
    push_cast
    rw [← Rat.zpow_natCast, Int.toNat_of_nonneg (by omega), ← Rat.zpow_add (by decide),
      ← Rat.zpow_natCast, Int.toNat_of_nonneg (by omega)]
    congr 1
  rw [e2]
  push_cast
  grind

/-- An integer is separated. -/
theorem separated_natCast (ε : Rat) (n : Nat) : Separated ε (n : Rat) := by
  left
  rw [show ((n : Rat)).floor = (n : Int) from
    floor_eq_of (by rw [Rat.intCast_natCast]; exact Rat.le_refl) (by rw [Rat.intCast_natCast]; grind)]
  rfl

/-- The check at `(q', k)` separates `m'·2^{q'}·10^{-k}` for `m' < 2^54`, given
    the band facts from R10. -/
theorem separated_of_checkAt (m' : Nat) (q' k : Int) (hm : 0 < m') (hm54 : m' < 2 ^ 54)
    (hcheck : checkAt q' k = true)
    (hb2 : 0 ≤ q' → 0 ≤ k → k ≤ q') (hb1 : q' < 0 → k < 0) :
    Separated eps ((m' : Rat) * (2 : Rat) ^ q' * (10 : Rat) ^ (-k)) := by
  unfold checkAt at hcheck
  by_cases hq' : 0 ≤ q'
  · by_cases hk : 0 ≤ k
    · rw [if_pos ⟨hq', hk⟩] at hcheck
      rw [band2_val m' hk (hb2 hq' hk)]
      refine separated_of_gaps _ _ 64 (Nat.pow_pos (by decide)) ?_
      have := check2_sound q'.toNat k.toNat (by omega) hcheck m' hm hm54
      rwa [show q'.toNat - k.toNat = (q' - k).toNat by omega] at this
    · rw [int_val m' hq' (by omega)]
      exact separated_natCast _ _
  · have hq'' : q' < 0 := by omega
    have hk := hb1 hq''
    rcases Int.lt_or_le k q' with hkq | hqk
    · rw [int_val' m' hk hkq]
      exact separated_natCast _ _
    · rw [if_neg (by omega), if_pos ⟨hq'', hk⟩] at hcheck
      rw [band1_val m' hk hqk]
      refine separated_of_gaps _ _ 64 (Nat.pow_pos (by decide)) ?_
      have := check1_sound (-q').toNat (-k).toNat (by omega) hcheck m' hm hm54
      rwa [show (-q').toNat - (-k).toNat = (-q' + k).toNat by omega] at this

/-! ## The three quantities -/

theorem twoV_eq (m : Nat) (q k : Int) :
    2 * V m q k = ((2 * m : Nat) : Rat) * (2 : Rat) ^ q * (10 : Rat) ^ (-k) := by
  unfold V v
  rw [Rat.div_def, ← Rat.zpow_neg]
  push_cast; grind

theorem twoVr_eq (m : Nat) (q k : Int) :
    2 * Vr m q k = ((2 * m + 1 : Nat) : Rat) * (2 : Rat) ^ q * (10 : Rat) ^ (-k) := by
  unfold Vr vr
  rw [Rat.div_def, ← Rat.zpow_neg]
  push_cast; grind

theorem twoVl_eq_reg (h : InRange m q) (hirr : isIrregular m q = false) (k : Int) :
    2 * Vl m q k = ((2 * m - 1 : Nat) : Rat) * (2 : Rat) ^ q * (10 : Rat) ^ (-k) := by
  have hm := h.1
  unfold Vl vl
  rw [if_neg (fun hc => by rw [isIrregular_iff.mpr hc] at hirr; cases hirr), Rat.div_def, ← Rat.zpow_neg]
  have : ((2 * m - 1 : Nat) : Rat) = 2 * (m : Rat) - 1 := by
    have h1 : 2 * m - 1 + 1 = 2 * m := by omega
    have h2 : ((2 * m - 1 + 1 : Nat) : Rat) = ((2 * m : Nat) : Rat) := by rw [h1]
    push_cast at h2; grind
  rw [this]
  grind

theorem twoVl_eq_irr (h : InRange m q) (hirr : isIrregular m q = true) (k : Int) :
    2 * Vl m q k = ((4 * m - 1 : Nat) : Rat) * (2 : Rat) ^ (q - 1) * (10 : Rat) ^ (-k) := by
  have hm := h.1
  unfold Vl vl
  rw [if_pos (isIrregular_iff.mp hirr), Rat.div_def, ← Rat.zpow_neg]
  have : ((4 * m - 1 : Nat) : Rat) = 4 * (m : Rat) - 1 := by
    have h1 : 4 * m - 1 + 1 = 4 * m := by omega
    have h2 : ((4 * m - 1 + 1 : Nat) : Rat) = ((4 * m : Nat) : Rat) := by rw [h1]
    push_cast at h2; grind
  rw [this, Rat.zpow_sub_one (by decide)]
  grind

/-- **Result 20** for the exponent `q`, given its check. -/
theorem R20_of_checkQ (h : InRange m q) (hcheck : checkQ q = true) :
    Separated eps (2 * V m q (kOfMQ m q))
    ∧ Separated eps (2 * Vl m q (kOfMQ m q))
    ∧ Separated eps (2 * Vr m q (kOfMQ m q)) := by
  have hm := h.1
  have hm53 : m < 2 ^ 53 := h.2.1
  unfold checkQ at hcheck
  simp only [Bool.and_eq_true] at hcheck
  obtain ⟨⟨⟨c15, _⟩, c14⟩, c14'⟩ := hcheck
  by_cases hirr : isIrregular m q = true
  · have hm52 : m = 2 ^ 52 := (isIrregular_iff.mp hirr).1
    have hk : kOfMQ m q = floorLog10ThreeQuartersPow2 q := by unfold kOfMQ; rw [if_pos hirr]
    rw [← hk] at c14 c14'
    have hb2 : 0 ≤ q → 0 ≤ kOfMQ m q → kOfMQ m q ≤ q := fun _ hk0 => by
      rcases Int.lt_or_le q 1 with h1 | h1
      · have := band_irr_nonpos h hirr (by omega); omega
      · have := (band_irr_pos h hirr h1).2; omega
    have hb2' : 0 ≤ q - 1 → 0 ≤ kOfMQ m q → kOfMQ m q ≤ q - 1 := fun hq _ =>
      (band_irr_pos h hirr (by omega)).2
    have hb1 : q < 0 → kOfMQ m q < 0 := fun hq => band_irr_nonpos h hirr (by omega)
    have hb1' : q - 1 < 0 → kOfMQ m q < 0 := fun hq => band_irr_nonpos h hirr (by omega)
    refine ⟨?_, ?_, ?_⟩
    · rw [twoV_eq]; exact separated_of_checkAt _ _ _ (by omega) (by omega) c14 hb2 hb1
    · rw [twoVl_eq_irr h hirr]; exact separated_of_checkAt _ _ _ (by omega) (by omega) c14' hb2' hb1'
    · rw [twoVr_eq]; exact separated_of_checkAt _ _ _ (by omega) (by omega) c14 hb2 hb1
  · have hirr' : isIrregular m q = false := by cases hb : isIrregular m q <;> simp_all
    have hk : kOfMQ m q = floorLog10Pow2 q := by unfold kOfMQ; rw [if_neg hirr]
    rw [← hk] at c15
    have hb2 : 0 ≤ q → 0 ≤ kOfMQ m q → kOfMQ m q ≤ q := fun hq _ => (band_reg_nonneg h hirr' hq).2
    have hb1 : q < 0 → kOfMQ m q < 0 := fun hq => band_reg_neg h hirr' hq
    refine ⟨?_, ?_, ?_⟩
    · rw [twoV_eq]; exact separated_of_checkAt _ _ _ (by omega) (by omega) c15 hb2 hb1
    · rw [twoVl_eq_reg h hirr']; exact separated_of_checkAt _ _ _ (by omega) (by omega) c15 hb2 hb1
    · rw [twoVr_eq]; exact separated_of_checkAt _ _ _ (by omega) (by omega) c15 hb2 hb1

end Srtfp.Schubfach.R20

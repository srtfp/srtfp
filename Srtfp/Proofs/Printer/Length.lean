/- §6.2–6.3: lengths of decimals across grids. Result R2 (coarser grids
   sit inside finer ones), the core of R7 (consecutive grid points that
   avoid the coarser grid share a digit count) and of R6 (a canonical
   decimal on a finer grid, strictly between two consecutive coarse
   points, is longer than the lower one). -/
import Srtfp.Proofs.Printer.Grid

open Srtfp.Compat

namespace Srtfp.Printer

variable {i j : Int} {x : ℚ} {n f d a b c : Nat}

/-- `10^i = 10^b · 10^(i - b)` for `b ≤ i`, the exponent difference as a `Nat`. -/
theorem ten_zpow_split (hj : j ≤ i) :
    (10 : ℚ) ^ i = (10 : ℚ) ^ j * (10 : ℚ) ^ ((i - j).toNat) := by
  have h1 : (10 : ℚ) ^ i = (10 : ℚ) ^ (j + (i - j)) := by congr 1; omega
  rw [h1, Rat.zpow_add (by decide), ← Rat.zpow_natCast, Int.toNat_of_nonneg (by omega)]

/-- R2: a coarser grid is contained in the next finer one. -/
theorem onGrid_of_onGrid_succ (h : OnGrid (i + 1) x) : OnGrid i x := by
  obtain ⟨n, rfl⟩ := h
  refine ⟨n * 10, ?_⟩
  rw [Rat.zpow_add_one (by decide)]
  push_cast
  grind

theorem onGrid_of_le (hj : i ≤ j) (h : OnGrid j x) : OnGrid i x := by
  obtain ⟨n, rfl⟩ := h
  refine ⟨n * 10 ^ (j - i).toNat, ?_⟩
  rw [ten_zpow_split hj]
  push_cast
  grind

theorem onGrid_succ_of_ten_dvd (h : n % 10 = 0) :
    OnGrid (i + 1) ((n : ℚ) * (10 : ℚ) ^ i) := by
  refine ⟨n / 10, ?_⟩
  have hn : n = n / 10 * 10 := (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h)).symm
  rw [Rat.zpow_add_one (by decide)]
  rw [show (n : ℚ) = ((n / 10 * 10 : Nat) : ℚ) by exact_mod_cast hn]
  push_cast
  grind

theorem ten_dvd_of_onGrid_succ (h : OnGrid (i + 1) ((n : ℚ) * (10 : ℚ) ^ i)) : n % 10 = 0 := by
  obtain ⟨k, hk⟩ := h
  rw [Rat.zpow_add_one (by decide)] at hk
  have h10 := ten_zpow_pos i
  have hk' : (n : ℚ) = (k * 10 : Nat) := by
    push_cast
    have := (mul_left_inj' (Rat.ne_of_gt h10)).mp
      (show (n : ℚ) * 10 ^ i = (k * 10) * 10 ^ i by grind)
    grind
  have : n = k * 10 := by exact_mod_cast hk'
  omega

theorem not_onGrid_of_finer (hj : j < i) (hf : f % 10 ≠ 0) :
    ¬ OnGrid i ((f : ℚ) * (10 : ℚ) ^ j) := by
  rintro ⟨k, hk⟩
  rw [ten_zpow_split (Int.le_of_lt hj)] at hk
  have h10 := ten_zpow_pos j
  have hk' : (f : ℚ) = ((k * 10 ^ (i - j).toNat : Nat) : ℚ) := by
    push_cast
    exact (mul_left_inj' (Rat.ne_of_gt h10)).mp
      (show (f : ℚ) * 10 ^ j = (k * 10 ^ (i - j).toNat) * 10 ^ j by grind)
  have hfk : f = k * 10 ^ (i - j).toNat := by exact_mod_cast hk'
  have hδ : 1 ≤ (i - j).toNat := by omega
  obtain ⟨δ, hδ'⟩ : ∃ δ, (i - j).toNat = δ + 1 := ⟨(i - j).toNat - 1, by omega⟩
  rw [hδ', Nat.pow_succ, ← Nat.mul_assoc] at hfk
  exact hf (by rw [hfk]; simp)

/-- R7 core: consecutive grid points, none of which lies on the coarser
    grid, all have the same number of digits. -/
theorem same_digits_on_grid (ha : 1 ≤ a) (hab : a ≤ b)
    (h : ∀ c, a ≤ c → c ≤ b → ¬ OnGrid (i + 1) ((c : ℚ) * (10 : ℚ) ^ i)) :
    digits a = digits b :=
  digits_eq_of_no_ten_dvd_between ha hab fun c hac hcb hmod =>
    h c hac hcb (onGrid_succ_of_ten_dvd hmod)

/-- R6 core: a decimal `f · 10^j` on a finer grid, strictly above the point
    `d · 10^i` of a coarser grid, is longer than `d`. -/
theorem finer_is_longer (hj : j < i) (hd : 1 ≤ d)
    (hlo : (d : ℚ) * (10 : ℚ) ^ i < (f : ℚ) * (10 : ℚ) ^ j) :
    digits d < digits f := by
  have h10 := ten_zpow_pos j
  rw [ten_zpow_split (Int.le_of_lt hj)] at hlo
  have hδ1 : 1 ≤ (i - j).toNat := by omega
  generalize hδ : (i - j).toNat = δ at hlo hδ1
  -- cancel `10^j`
  have hlo' : (d : ℚ) * 10 ^ δ < f :=
    Rat.lt_of_mul_lt_mul_right (a := (d : ℚ) * 10 ^ δ) (b := f) (c := 10 ^ j)
      (by grind) (le_of_lt h10)
  have hloN : d * 10 ^ δ < f := by exact_mod_cast hlo'
  -- `10^(digits d - 1 + δ) ≤ d · 10^δ < f`
  have hpow : 10 ^ (digits d - 1 + δ) ≤ f := by
    rw [Nat.pow_add]
    have := Nat.mul_le_mul_right (10 ^ δ) (pow_digits_le hd)
    omega
  have := digits_pos d
  exact digits_lt_of_pow_le hpow (by omega)

end Srtfp.Printer

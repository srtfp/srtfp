module
/- §6.2–6.3: lengths of decimals across grids. Result R2 (coarser grids
   sit inside finer ones), the core of R7 (consecutive grid points that
   avoid the coarser grid share a digit count) and of R6 (a canonical
   decimal on a finer grid, strictly between two consecutive coarse
   points, is longer than the lower one). -/
public import Srtfp.Proofs.Printer.Grid

@[expose] public section

open Srtfp.Compat

namespace Srtfp.Printer

variable {i j : Int} {x : Rat} {n f d a b c : Nat}

theorem onGrid_of_le (hj : i ≤ j) (h : OnGrid j x) : OnGrid i x := by
  obtain ⟨n, rfl⟩ := h
  refine ⟨n * 10 ^ (j - i).toNat, ?_⟩
  rw [zpow_split (b := 10) (by decide) hj]
  push_cast
  grind

theorem onGrid_succ_of_ten_dvd (h : n % 10 = 0) :
    OnGrid (i + 1) ((n : Rat) * (10 : Rat) ^ i) :=
  ⟨n / 10, by
    rw [Rat.zpow_add_one (by decide), show (n : Rat) = ((n / 10 * 10 : Nat) : Rat) by
      exact_mod_cast (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h)).symm]
    push_cast; grind⟩

theorem not_onGrid_of_finer (hj : j < i) (hf : f % 10 ≠ 0) :
    ¬ OnGrid i ((f : Rat) * (10 : Rat) ^ j) := by
  rintro ⟨k, hk⟩
  rw [zpow_split (b := 10) (by decide) (Int.le_of_lt hj)] at hk
  have hfk : f = k * 10 ^ (i - j).toNat := by
    exact_mod_cast (mul_left_inj' (Rat.ne_of_gt (ten_zpow_pos j))).mp
      (show (f : Rat) * 10 ^ j = ((k * 10 ^ (i - j).toNat : Nat) : Rat) * 10 ^ j by push_cast; grind)
  obtain ⟨δ, hδ⟩ : ∃ δ, (i - j).toNat = δ + 1 := ⟨(i - j).toNat - 1, by omega⟩
  rw [hδ, Nat.pow_succ, ← Nat.mul_assoc] at hfk
  exact hf (by rw [hfk]; simp)

/-- R7 core: consecutive grid points, none of which lies on the coarser
    grid, all have the same number of digits. -/
theorem same_digits_on_grid (ha : 1 ≤ a) (hab : a ≤ b)
    (h : ∀ c, a ≤ c → c ≤ b → ¬ OnGrid (i + 1) ((c : Rat) * (10 : Rat) ^ i)) :
    digits a = digits b :=
  digits_eq_of_no_ten_dvd_between ha hab fun c hac hcb hmod =>
    h c hac hcb (onGrid_succ_of_ten_dvd hmod)

/-- R6 core: a decimal `f · 10^j` on a finer grid, strictly above the point
    `d · 10^i` of a coarser grid, is longer than `d`. -/
theorem finer_is_longer (hj : j < i) (hd : 1 ≤ d)
    (hlo : (d : Rat) * (10 : Rat) ^ i < (f : Rat) * (10 : Rat) ^ j) :
    digits d < digits f := by
  rw [zpow_split (b := 10) (by decide) (Int.le_of_lt hj), Rat.mul_comm ((10 : Rat) ^ j),
    ← Rat.mul_assoc, Rat.mul_lt_mul_right (ten_zpow_pos j)] at hlo
  have hloN : d * 10 ^ (i - j).toNat < f := by exact_mod_cast hlo
  have := Nat.mul_le_mul_right (10 ^ (i - j).toNat) (pow_digits_le hd)
  have := digits_pos d
  exact digits_lt_of_pow_le (k := digits d - 1 + (i - j).toNat) (by rw [Nat.pow_add]; omega) (by omega)

end Srtfp.Printer

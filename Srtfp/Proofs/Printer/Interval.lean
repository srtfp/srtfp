module
/- §5: the rounding interval `R_v = [vl, vr]` of `v = m · 2^q`, with the
   endpoints included iff `m` is even (round-ties-to-even). Result R1 and
   the interval's width. -/
public import Srtfp.Proofs.Printer.Vocab

@[expose] public section

open Srtfp.Compat

namespace Srtfp.Printer

variable {m : Nat} {q : Int} {x y z : ℚ}

theorem two_zpow_pos (q : Int) : (0 : ℚ) < (2 : ℚ) ^ q := Rat.zpow_pos (by decide)

theorem ten_zpow_pos (i : Int) : (0 : ℚ) < (10 : ℚ) ^ i := Rat.zpow_pos (by decide)

theorem vl_lt_v (hm : 1 ≤ m) : vl m q < v m q := by
  unfold vl v
  have h2 := two_zpow_pos q
  have hm' : (1 : ℚ) ≤ m := by exact_mod_cast hm
  split <;> grind

theorem v_lt_vr : v m q < vr m q := by
  unfold vr v
  have h2 := two_zpow_pos q
  grind

theorem vl_pos (hm : 1 ≤ m) : 0 < vl m q := by
  unfold vl
  have h2 := two_zpow_pos q
  have hm' : (1 : ℚ) ≤ m := by exact_mod_cast hm
  split <;> grind

theorem InRv_v (hm : 1 ≤ m) : InRv m q (v m q) = true := by
  have hl := vl_lt_v (q := q) hm
  have hr := v_lt_vr (m := m) (q := q)
  unfold InRv
  split <;> simp <;> grind

/-- R1, one half: strictly inside means inside, whatever the parity. -/
theorem InRv_of_strict (hl : vl m q < x) (hr : x < vr m q) : InRv m q x = true := by
  unfold InRv
  split <;> simp <;> grind

/-- R1, other half. -/
theorem le_of_InRv (h : InRv m q x = true) : vl m q ≤ x ∧ x ≤ vr m q := by
  unfold InRv at h
  split at h <;> simp at h <;> grind

/-- `R_v` is an interval. -/
theorem InRv_convex (hx : InRv m q x = true) (hz : InRv m q z = true)
    (hxy : x ≤ y) (hyz : y ≤ z) : InRv m q y = true := by
  unfold InRv at *
  split at hx <;> simp at hx hz ⊢ <;> grind

theorem width_eq :
    vr m q - vl m q = (if m = 2 ^ 52 ∧ q > -1074 then 3/4 else 1) * (2 : ℚ) ^ q := by
  unfold vr vl
  split <;> grind

theorem width_le_two_zpow : vr m q - vl m q ≤ (2 : ℚ) ^ q := by
  rw [width_eq]
  have h2 := two_zpow_pos q
  split <;> grind

theorem width_ge : 3/4 * (2 : ℚ) ^ q ≤ vr m q - vl m q := by
  rw [width_eq]
  have h2 := two_zpow_pos q
  split <;> grind

end Srtfp.Printer

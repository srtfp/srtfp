module
/- §5: the rounding interval `R_v = [vl, vr]` of `v = m · 2^q`, with the
   endpoints included iff `m` is even (round-ties-to-even). Result R1 and
   the interval's width. -/
public import Srtfp.Proofs.Printer.Vocab

@[expose] public section

open Srtfp.Compat

namespace Srtfp.Printer

variable {m : Nat} {q : Int} {x y z : Rat}

theorem two_zpow_pos (q : Int) : (0 : Rat) < (2 : Rat) ^ q := Rat.zpow_pos (by decide)

theorem ten_zpow_pos (i : Int) : (0 : Rat) < (10 : Rat) ^ i := Rat.zpow_pos (by decide)

theorem two_zpow_natCast (n : Nat) : (2 : Rat) ^ (n : Int) = ((2 ^ n : Nat) : Rat) := by
  rw [Rat.zpow_natCast]; push_cast; rfl

theorem two_zpow_mul_neg (e : Int) : (2 : Rat) ^ e * (2 : Rat) ^ (-e) = 1 := by
  rw [← Rat.zpow_add (by decide), show e + -e = 0 by omega, Rat.zpow_zero]

/-- A nonnegative integer exponent is a natural one. -/
theorem two_zpow_toNat {e : Int} (he : 0 ≤ e) : (2 : Rat) ^ e = (2 : Rat) ^ e.toNat := by
  conv => lhs; rw [← Int.toNat_of_nonneg he]
  exact Rat.zpow_natCast _ _

/-- `b^q · b^{max(-q,0)} = b^{max(q,0)}`, for nonzero `b`. -/
theorem zpow_split_gen (b : Rat) (hb : b ≠ 0) (q : Int) :
    b ^ q * b ^ (if q < 0 then (-q).toNat else 0)
      = b ^ (if q ≥ 0 then q.toNat else 0) := by
  by_cases hq : q < 0
  · rw [if_pos hq, if_neg (by omega : ¬ q ≥ 0)]
    rw [← Rat.zpow_natCast b (-q).toNat, Int.toNat_of_nonneg (by omega : (0:Int) ≤ -q),
        ← Rat.zpow_add hb]
    rw [show q + -q = 0 from by omega, Rat.zpow_zero]
    exact (Rat.pow_zero b).symm
  · rw [if_neg hq, if_pos (by omega : q ≥ 0)]
    rw [← Rat.zpow_natCast b q.toNat, Int.toNat_of_nonneg (by omega : (0:Int) ≤ q)]
    simp

theorem zpow_two_split (q : Int) :
    (2 : Rat) ^ q * (2 : Rat) ^ (if q < 0 then (-q).toNat else 0)
      = (2 : Rat) ^ (if q ≥ 0 then q.toNat else 0) :=
  zpow_split_gen 2 (by grind) q

theorem zpow_ten_split (k : Int) :
    (10 : Rat) ^ k * (10 : Rat) ^ (if k < 0 then (-k).toNat else 0)
      = (10 : Rat) ^ (if k ≥ 0 then k.toNat else 0) :=
  zpow_split_gen 10 (by grind) k

theorem vl_lt_v (hm : 1 ≤ m) : vl m q < v m q := by
  unfold vl v
  have h2 := two_zpow_pos q
  have hm' : (1 : Rat) ≤ m := by exact_mod_cast hm
  split <;> grind

theorem v_lt_vr : v m q < vr m q := by
  unfold vr v
  have h2 := two_zpow_pos q
  grind

theorem vl_pos (hm : 1 ≤ m) : 0 < vl m q := by
  unfold vl
  have h2 := two_zpow_pos q
  have hm' : (1 : Rat) ≤ m := by exact_mod_cast hm
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
    vr m q - vl m q = (if m = 2 ^ 52 ∧ q > -1074 then 3/4 else 1) * (2 : Rat) ^ q := by
  unfold vr vl
  split <;> grind

theorem width_le_two_zpow : vr m q - vl m q ≤ (2 : Rat) ^ q := by
  rw [width_eq]
  have h2 := two_zpow_pos q
  split <;> grind

theorem width_ge : 3/4 * (2 : Rat) ^ q ≤ vr m q - vl m q := by
  rw [width_eq]
  have h2 := two_zpow_pos q
  split <;> grind

end Srtfp.Printer

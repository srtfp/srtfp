module
/- The scan: `shortest` returns a hit on the coarsest grid that has one.
   Three facts are specific to binary64 — no grid above `10^308` meets
   `R_v` (T1), the grid `10^{-324}` always does (T2), and `v` is nearer to
   a power of ten in `R_v` than to the one-digit decimal below it (T3).
   Everything else is the loop invariant. -/
public import Srtfp.Proofs.Printer.Length
public import Srtfp.Proofs.Model

@[expose] public section

open Srtfp.Compat

namespace Srtfp.Printer

open Srtfp.Model

/-- The `(m, q)` of a finite nonzero binary64 word. -/
def InRange (m : Nat) (q : Int) : Prop := 1 ≤ m ∧ Legal m q

variable {m : Nat} {q i j : Int} {n : Nat}

/-! ## T1: no grid above `10^308` meets `R_v` -/

theorem vr_lt_two_pow_1024 (h : InRange m q) : vr m q < (2 : Rat) ^ (1024 : Nat) := by
  obtain ⟨_, hm53, _, hq2, _⟩ := h
  have hm' : (m : Rat) + 1/2 < (2 : Rat) ^ (53 : Nat) := by
    have : ((m + 1 : Nat) : Rat) ≤ ((2 ^ 53 : Nat) : Rat) := by exact_mod_cast hm53
    push_cast at this; grind
  have hq' : (2 : Rat) ^ q ≤ 2 ^ (971 : Nat) := zpow_le_zpow_right₀ (n := 971) (by decide) hq2
  have h2 := two_zpow_pos q
  have h53 : (0 : Rat) < 2 ^ (53 : Nat) := Rat.pow_pos (by decide)
  unfold vr
  rw [show (2 : Rat) ^ (1024 : Nat) = 2 ^ (53 : Nat) * 2 ^ (971 : Nat) from by rw [← Rat.pow_add]]
  have := Rat.mul_lt_mul_of_pos_right hm' h2
  have := Rat.mul_le_mul_of_nonneg_left hq' (Rat.le_of_lt h53)
  grind

theorem candidate_none_above (h : InRange m q) (hi : 308 < i) : candidate m q i = none := by
  rw [candidate_none_iff h.1]
  rintro ⟨x, ⟨k, rfl⟩, hxR⟩
  obtain ⟨hl, hr⟩ := le_of_InRv hxR
  have h10 := ten_zpow_pos i
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; have := vl_pos (q := q) h.1; simp at hl; grind
  · have h1 := vr_lt_two_pow_1024 h
    have h2 : (2 : Rat) ^ (1024 : Nat) < (10 : Rat) ^ (309 : Int) := by
      show (2 : Rat) ^ (1024 : Nat) < (10 : Rat) ^ (309 : Nat)
      exact_mod_cast (by decide +kernel : (2 : Nat) ^ 1024 < 10 ^ 309)
    have h3 : (10 : Rat) ^ (309 : Int) ≤ (10 : Rat) ^ i := zpow_le_zpow_right₀ (by decide) (by omega)
    have h4 : (1 : Rat) ≤ k := by exact_mod_cast hk
    have := Rat.mul_le_mul_of_nonneg_right h4 (Rat.le_of_lt h10)
    grind

/-! ## T2: the grid `10^{-324}` always meets `R_v` -/

theorem two_zpow_neg_1074_le (h : InRange m q) : (2 : Rat) ^ (-1074 : Int) ≤ (2 : Rat) ^ q :=
  zpow_le_zpow_right₀ (by decide) h.2.2.1

set_option exponentiation.threshold 1100 in
/-- `10^{-324} < 3/4 · 2^{-1074}`, i.e. `4 · 2^1074 < 3 · 10^324`. -/
theorem ten_zpow_neg_324_lt_width : (10 : Rat) ^ (-324 : Int) < 3/4 * (2 : Rat) ^ (-1074 : Int) := by
  rw [show (-324 : Int) = -((324 : Nat) : Int) from rfl, show (-1074 : Int) = -((1074 : Nat) : Int) from rfl,
    zpow_neg_natCast, zpow_neg_natCast, ← Rat.one_mul ((10 : Rat) ^ 324)⁻¹]
  refine mul_inv_lt_mul_inv (Rat.pow_pos (by decide)) (Rat.pow_pos (by decide)) ?_
  have := (by decide +kernel : 4 * (2 : Nat) ^ 1074 < 3 * 10 ^ 324)
  have : 4 * (2 : Rat) ^ 1074 < 3 * 10 ^ 324 := by exact_mod_cast this
  grind

theorem hit_at_bottom (h : InRange m q) : candidate m q (-324) ≠ none := by
  intro hnone
  apply (candidate_none_iff h.1).mp hnone
  have h10 := ten_zpow_pos (-324 : Int)
  have hvl := vl_pos (q := q) h.1
  -- `10^{-324}` is narrower than the interval, so `(⌊vl / 10^{-324}⌋ + 1) · 10^{-324}` is inside
  have hwidth : (10 : Rat) ^ (-324 : Int) < vr m q - vl m q := by
    have := Rat.mul_le_mul_of_nonneg_left (two_zpow_neg_1074_le h) (by grind : (0 : Rat) ≤ 3/4)
    have := width_ge (m := m) (q := q); have := ten_zpow_neg_324_lt_width; grind
  have hVmul := Rat.div_mul_cancel (a := vl m q) (Rat.ne_of_gt h10)
  have hfl := floor_nonneg (Rat.le_of_lt (div_pos hvl h10))
  have hVlt := Rat.lt_floor_add_one (vl m q / 10 ^ (-324 : Int))
  have hVle := Rat.floor_le (vl m q / 10 ^ (-324 : Int))
  generalize vl m q / 10 ^ (-324 : Int) = V at *
  push_cast at hVlt
  refine ⟨((V.floor + 1).toNat : Rat) * 10 ^ (-324 : Int), ⟨_, rfl⟩, ?_⟩
  rw [show (((V.floor + 1).toNat : Nat) : Rat) = (V.floor : Rat) + 1 by
    rw [← Rat.intCast_natCast, Int.toNat_of_nonneg (by omega)]; push_cast; rfl]
  have := Rat.mul_lt_mul_of_pos_right hVlt h10
  have := Rat.mul_le_mul_of_nonneg_right hVle (Rat.le_of_lt h10)
  exact InRv_of_strict (by grind) (by grind)

/-! ## T3: a power of ten in `R_v` is nearer than the one-digit decimal below it -/

/-- If `10^i` and `9 · 10^(i-1)` both lie in `R_v`, then `v` is nearer to
    `10^i`. Only a subnormal `v` with `m ≤ 9` has an interval that wide,
    and then `i = -323` and `m ≥ 2`. -/
theorem ten_pow_closer (h : InRange m q) (hw : InRv m q ((10 : Rat) ^ i) = true)
    (h9 : InRv m q (9 * (10 : Rat) ^ (i - 1)) = true) :
    (10 : Rat) ^ i - v m q < v m q - 9 * (10 : Rat) ^ (i - 1) := by
  obtain ⟨hm1, hm53, hq0, hq1, hnorm⟩ := h
  have hP := two_zpow_pos q
  have hTi : (10 : Rat) ^ i = 10 ^ (i - 1) * 10 := by
    rw [← Rat.zpow_add_one (by decide), Int.sub_add_cancel]
  obtain ⟨hl', hr⟩ := le_of_InRv hw
  have hl := (le_of_InRv h9).1
  have hvl : ((m : Rat) - 1/2) * 2 ^ q ≤ vl m q := by unfold vl; split <;> grind
  unfold vr at hr; unfold v
  rw [hTi] at hr ⊢
  have hm1' : (1 : Rat) ≤ m := by exact_mod_cast hm1
  -- `(m - 1/2) 2^q ≤ 9 T` and `10 T ≤ (m + 1/2) 2^q` give `m ≤ 9`, so `q = Q_min`
  have hm9 : m ≤ 9 := by
    have := Rat.le_of_mul_le_mul_right
      (show (10 * (m : Rat) - 5) * 2 ^ q ≤ (9 * m + 9/2) * 2 ^ q by grind) hP
    have : m < 10 := by exact_mod_cast (show (m : Rat) < 10 by grind)
    omega
  obtain rfl : q = -1074 := by omega
  have hmP := Rat.mul_le_mul_of_nonneg_right (show (m : Rat) ≤ 9 by exact_mod_cast hm9) (Rat.le_of_lt hP)
  have hmP1 := Rat.mul_le_mul_of_nonneg_right hm1' (Rat.le_of_lt hP)
  -- `i = -323`: `2^(-1075) ≤ v_l ≤ 10^i ≤ v_r < 10 · 2^(-1074)`
  obtain rfl : i = -323 := by
    have h1 := ten_zpow_lt_two_zpow (x := -324) (y := -1075) (by decide +kernel)
    have h2 := lt_of_ratio (a := 1) (c := 10) (x := -322) (y := -1074) (by decide +kernel)
    have h3 : (2 : Rat) ^ (-1074 : Int) = 2 ^ (-1075 : Int) * 2 := by
      rw [← Rat.zpow_add_one (by decide)]; rfl
    simp only [Rat.natCast_ofNat, Rat.one_mul] at h2
    have := lt_of_zpow_lt (a := 10) (by decide) (show (10 : Rat) ^ (-324 : Int) < 10 ^ i by grind)
    have := lt_of_zpow_lt (a := 10) (by decide) (show (10 : Rat) ^ i < 10 ^ (-322 : Int) by grind)
    omega
  rw [show (-323 : Int) - 1 = -324 by decide] at hr hl ⊢
  -- `m ≥ 2` (`m = 1` puts `v_r` below `10^(-323)`), and then the inequality
  have h4 := lt_of_ratio (a := 20) (c := 3) (x := -324) (y := -1074) (by decide +kernel)
  have h5 := lt_of_ratio' (a := 19) (c := 4) (x := -324) (y := -1074) (by decide +kernel)
  simp only [Rat.natCast_ofNat] at h4 h5
  have hm2 : (2 : Rat) ≤ m := by
    rcases Nat.lt_or_ge m 2 with hlt | hge
    · exfalso; obtain rfl : m = 1 := by omega
      simp only [Rat.natCast_ofNat] at hr; grind
    · exact_mod_cast hge
  have := Rat.mul_le_mul_of_nonneg_right hm2 (Rat.le_of_lt hP)
  grind

/-! ## The loop invariant -/

theorem go_spec (m : Nat) (q : Int) :
    ∀ (fuel : Nat) (i : Int),
      (∃ j, i - fuel ≤ j ∧ j ≤ i ∧ candidate m q j ≠ none) →
      ∃ n j, shortest.go m q i (fuel + 1) = (n, j) ∧ i - fuel ≤ j ∧ j ≤ i
        ∧ candidate m q j = some n ∧ ∀ k, j < k → k ≤ i → candidate m q k = none := by
  intro fuel
  induction fuel with
  | zero =>
    intro i ⟨j, hj1, hj2, hj⟩
    have hji : j = i := by omega
    subst hji
    obtain ⟨n, hc⟩ := Option.ne_none_iff_exists'.mp hj
    exact ⟨n, j, by simp [shortest.go, hc], by omega, by omega, hc, fun k h1 h2 => by omega⟩
  | succ fuel ih =>
    intro i ⟨j, hj1, hj2, hj⟩
    cases hc : candidate m q i with
    | some n =>
      exact ⟨n, i, by simp [shortest.go, hc], by omega, by omega, hc, fun k h1 h2 => by omega⟩
    | none =>
      have hji : j ≠ i := fun e => hj (e ▸ hc)
      obtain ⟨n, j', hgo, h1, h2, hc', hnone⟩ :=
        ih (i - 1) ⟨j, by omega, by omega, hj⟩
      refine ⟨n, j', ?_, by omega, by omega, hc', ?_⟩
      · simp [shortest.go, hc]; exact hgo
      · intro k hk1 hk2
        rcases Int.lt_or_eq_of_le hk2 with hk | hk
        · exact hnone k hk1 (by omega)
        · subst hk; exact hc

/-- The scan returns a hit on the coarsest grid that has one. -/
theorem scan_spec (h : InRange m q) (hs : shortest m q = (n, i)) :
    1 ≤ n ∧ -324 ≤ i ∧ i ≤ 308 ∧ candidate m q i = some n
    ∧ ∀ j, i < j → candidate m q j = none := by
  obtain ⟨n', j, hgo, h1, h2, hc, hnone⟩ :=
    go_spec m q 632 308 ⟨-324, by omega, by omega, hit_at_bottom h⟩
  have hsg : shortest m q = shortest.go m q 308 633 := rfl
  rw [hsg, hgo] at hs
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hs
  refine ⟨(candidate_some h.1 hc).1, by omega, h2, hc, fun j hj => ?_⟩
  rcases Int.lt_or_le 308 j with hj' | hj'
  · exact candidate_none_above h hj'
  · exact hnone j hj hj'

theorem no_hit_above (h : InRange m q) (hs : shortest m q = (n, i)) (hj : i < j) :
    ¬ ∃ x, OnGrid j x ∧ InRv m q x = true :=
  (candidate_none_iff h.1).mp ((scan_spec h hs).2.2.2.2 j hj)

end Srtfp.Printer

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

/-! ## Binary64 numerics -/

set_option exponentiation.threshold 1100 in
theorem two_pow_1024_lt : (2 : Nat) ^ 1024 < 10 ^ 309 := by decide

set_option exponentiation.threshold 1100 in
theorem two_pow_1074_le : (2 : Nat) ^ 1074 ≤ 10 ^ 324 := by decide

set_option exponentiation.threshold 1100 in
theorem four_two_pow_1074_lt : 4 * (2 : Nat) ^ 1074 < 3 * 10 ^ 324 := by decide

theorem zpow_natCast_lit (b : Rat) (n : Nat) : b ^ (n : Int) = b ^ n := rfl

/-! ## T1: no grid above `10^308` meets `R_v` -/

theorem vr_lt_two_pow_1024 (h : InRange m q) : vr m q < (2 : Rat) ^ (1024 : Nat) := by
  obtain ⟨_, hm53, _, hq2, _⟩ := h
  have hm' : (m : Rat) + 1/2 < (2 : Rat) ^ (53 : Nat) := by
    have : ((m + 1 : Nat) : Rat) ≤ ((2 ^ 53 : Nat) : Rat) := by exact_mod_cast hm53
    push_cast at this; grind
  have hq' : (2 : Rat) ^ q ≤ (2 : Rat) ^ (971 : Int) := zpow_le_zpow_right₀ (by decide) hq2
  have h2 := two_zpow_pos q
  unfold vr
  calc ((m : Rat) + 1/2) * 2 ^ q < 2 ^ (53 : Nat) * 2 ^ q := Rat.mul_lt_mul_of_pos_right hm' h2
    _ ≤ 2 ^ (53 : Nat) * 2 ^ (971 : Int) :=
        Rat.mul_le_mul_of_nonneg_left hq' (le_of_lt (Rat.pow_pos (by decide)))
    _ = 2 ^ (1024 : Nat) := by
        show (2 : Rat) ^ (53 : Nat) * (2 : Rat) ^ (971 : Nat) = (2 : Rat) ^ (1024 : Nat)
        rw [← Rat.pow_add]

theorem candidate_none_above (h : InRange m q) (hi : 308 < i) : candidate m q i = none := by
  rw [candidate_none_iff h.1]
  rintro ⟨x, ⟨k, rfl⟩, hxR⟩
  obtain ⟨hl, hr⟩ := le_of_InRv hxR
  have h10 := ten_zpow_pos i
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have := vl_pos (q := q) h.1
    simp at hl
    grind
  · have h1 := vr_lt_two_pow_1024 h
    have h2 : (2 : Rat) ^ (1024 : Nat) < (10 : Rat) ^ (309 : Int) := by
      show (2 : Rat) ^ (1024 : Nat) < (10 : Rat) ^ (309 : Nat)
      exact_mod_cast two_pow_1024_lt
    have h3 : (10 : Rat) ^ (309 : Int) ≤ (10 : Rat) ^ i := zpow_le_zpow_right₀ (by decide) (by omega)
    have h4 : (1 : Rat) ≤ k := by exact_mod_cast hk
    have h5 : (1 : Rat) * 10 ^ i ≤ (k : Rat) * 10 ^ i := Rat.mul_le_mul_of_nonneg_right h4 (le_of_lt h10)
    grind

/-! ## T2: the grid `10^{-324}` always meets `R_v` -/

theorem two_zpow_neg_1074_le (h : InRange m q) : (2 : Rat) ^ (-1074 : Int) ≤ (2 : Rat) ^ q :=
  zpow_le_zpow_right₀ (by decide) h.2.2.1

set_option exponentiation.threshold 1100 in
/-- `10^{-324} ≤ 2^{-1074}`, i.e. `2^1074 ≤ 10^324`. -/
theorem ten_zpow_neg_324_le : (10 : Rat) ^ (-324 : Int) ≤ (2 : Rat) ^ (-1074 : Int) := by
  have hA : (0 : Rat) < (10 : Rat) ^ (324 : Nat) := Rat.pow_pos (by decide)
  have hB : (0 : Rat) < (2 : Rat) ^ (1074 : Nat) := Rat.pow_pos (by decide)
  have hAB : (2 : Rat) ^ (1074 : Nat) ≤ (10 : Rat) ^ (324 : Nat) := by exact_mod_cast two_pow_1074_le
  rw [show (10 : Rat) ^ (-324 : Int) = ((10 : Rat) ^ (324 : Nat))⁻¹ by rw [Rat.zpow_neg]; rfl,
      show (2 : Rat) ^ (-1074 : Int) = ((2 : Rat) ^ (1074 : Nat))⁻¹ by rw [Rat.zpow_neg]; rfl]
  generalize (10 : Rat) ^ (324 : Nat) = A at hA hAB ⊢
  generalize (2 : Rat) ^ (1074 : Nat) = B at hB hAB ⊢
  have hA' := Rat.mul_inv_cancel A (Rat.ne_of_gt hA)
  have hB' := Rat.mul_inv_cancel B (Rat.ne_of_gt hB)
  apply Rat.le_of_mul_le_mul_right (c := A * B) _ (Rat.mul_pos hA hB)
  calc A⁻¹ * (A * B) = B := by grind
    _ ≤ A := hAB
    _ = B⁻¹ * (A * B) := by grind

set_option exponentiation.threshold 1100 in
/-- `10^{-324} < 3/4 · 2^{-1074}`, i.e. `4 · 2^1074 < 3 · 10^324`. -/
theorem ten_zpow_neg_324_lt_width : (10 : Rat) ^ (-324 : Int) < 3/4 * (2 : Rat) ^ (-1074 : Int) := by
  have hA : (0 : Rat) < (10 : Rat) ^ (324 : Nat) := Rat.pow_pos (by decide)
  have hB : (0 : Rat) < (2 : Rat) ^ (1074 : Nat) := Rat.pow_pos (by decide)
  have hAB : 4 * (2 : Rat) ^ (1074 : Nat) < 3 * (10 : Rat) ^ (324 : Nat) := by
    exact_mod_cast four_two_pow_1074_lt
  rw [show (10 : Rat) ^ (-324 : Int) = ((10 : Rat) ^ (324 : Nat))⁻¹ by rw [Rat.zpow_neg]; rfl,
      show (2 : Rat) ^ (-1074 : Int) = ((2 : Rat) ^ (1074 : Nat))⁻¹ by rw [Rat.zpow_neg]; rfl]
  generalize (10 : Rat) ^ (324 : Nat) = A at hA hAB ⊢
  generalize (2 : Rat) ^ (1074 : Nat) = B at hB hAB ⊢
  have hA' := Rat.mul_inv_cancel A (Rat.ne_of_gt hA)
  have hB' := Rat.mul_inv_cancel B (Rat.ne_of_gt hB)
  apply Rat.lt_of_mul_lt_mul_right (c := A * B) _ (le_of_lt (Rat.mul_pos hA hB))
  calc A⁻¹ * (A * B) = B := by grind
    _ < 3/4 * A := by grind
    _ = 3/4 * B⁻¹ * (A * B) := by grind

theorem hit_at_bottom (h : InRange m q) : candidate m q (-324) ≠ none := by
  have hm : 1 ≤ m := h.1
  intro hnone
  apply (candidate_none_iff hm).mp hnone
  -- a grid point strictly inside `(vl, vr)`: `10^{-324}` is narrower than the interval
  have h10 := ten_zpow_pos (-324 : Int)
  have hvl := vl_pos (q := q) hm
  have hwidth : (10 : Rat) ^ (-324 : Int) < vr m q - vl m q := by
    have h1 := ten_zpow_neg_324_lt_width
    have h2 := two_zpow_neg_1074_le h
    have h3 := width_ge (m := m) (q := q)
    have : 3/4 * (2 : Rat) ^ (-1074 : Int) ≤ 3/4 * (2 : Rat) ^ q :=
      Rat.mul_le_mul_of_nonneg_left h2 (by grind)
    grind
  -- `n := ⌊vl / 10^{-324}⌋ + 1`
  have hVpos : 0 < vl m q / (10 : Rat) ^ (-324 : Int) :=
    (Rat.lt_div_iff h10).mpr (by rw [Rat.zero_mul]; exact hvl)
  have hVlt := Rat.lt_floor_add_one (vl m q / (10 : Rat) ^ (-324 : Int))
  have hVle := Rat.floor_le (vl m q / (10 : Rat) ^ (-324 : Int))
  generalize hV : vl m q / (10 : Rat) ^ (-324 : Int) = V at hVpos hVlt hVle
  have hfl0 : 0 ≤ V.floor := by
    rcases Int.lt_or_le V.floor 0 with hneg | hnn
    · exfalso; have := Rat.floor_lt_iff.mp hneg; simp at this; grind
    · exact hnn
  have hfl1 : (((V.floor + 1 : Int)) : Rat) = (V.floor : Rat) + 1 := by simp
  rw [hfl1] at hVlt
  refine ⟨((V.floor + 1).toNat : Rat) * (10 : Rat) ^ (-324 : Int), ⟨_, rfl⟩, ?_⟩
  have hcast : (((V.floor + 1).toNat : Nat) : Rat) = ((V.floor : Rat) + 1) := by
    rw [← Rat.intCast_natCast, Int.toNat_of_nonneg (by omega)]; exact hfl1
  rw [hcast]
  have hVmul : V * (10 : Rat) ^ (-324 : Int) = vl m q := by
    rw [← hV]; exact Rat.div_mul_cancel (Rat.ne_of_gt h10)
  apply InRv_of_strict
  · have := Rat.mul_lt_mul_of_pos_right hVlt h10
    rw [hVmul] at this
    exact this
  · have := Rat.mul_le_mul_of_nonneg_right hVle (le_of_lt h10)
    rw [hVmul] at this
    grind

/-! ## T3: a power of ten in `R_v` is nearer than the one-digit decimal below it -/

set_option exponentiation.threshold 1100 in
theorem nineteen_ten_pow_323_lt : 19 * (10 : Rat) ^ 323 < 20 * (2 : Rat) ^ 1074 := by
  exact_mod_cast (by decide : 19 * (10 : Nat) ^ 323 < 20 * 2 ^ 1074)

set_option exponentiation.threshold 1100 in
theorem eighteen_two_pow_1074_lt : 18 * (2 : Rat) ^ 1074 < 1 * (10 : Rat) ^ 325 := by
  exact_mod_cast (by decide : 18 * (2 : Nat) ^ 1074 < 1 * 10 ^ 325)

set_option exponentiation.threshold 1100 in
theorem three_ten_pow_324_lt : 3 * (10 : Rat) ^ 324 < 20 * (2 : Rat) ^ 1074 := by
  exact_mod_cast (by decide : 3 * (10 : Nat) ^ 324 < 20 * 2 ^ 1074)

set_option exponentiation.threshold 1100 in
theorem nineteen_two_pow_1074_lt : 19 * (2 : Rat) ^ 1074 < 4 * (10 : Rat) ^ 324 := by
  exact_mod_cast (by decide : 19 * (2 : Nat) ^ 1074 < 4 * 10 ^ 324)

/-- `p / A < r / B` from `p · B < r · A`, for positive `A`, `B`. -/
theorem mul_inv_lt_mul_inv {A B p r : Rat} (hA : 0 < A) (hB : 0 < B) (h : p * B < r * A) :
    p * A⁻¹ < r * B⁻¹ := by
  have hA' := Rat.mul_inv_cancel A (Rat.ne_of_gt hA)
  have hB' := Rat.mul_inv_cancel B (Rat.ne_of_gt hB)
  apply Rat.lt_of_mul_lt_mul_right (c := A * B) _ (le_of_lt (Rat.mul_pos hA hB))
  calc p * A⁻¹ * (A * B) = p * B := by grind
    _ < r * A := h
    _ = r * B⁻¹ * (A * B) := by grind

theorem two_zpow_neg_eq (a : Nat) : (2 : Rat) ^ (-(a : Int)) = ((2 : Rat) ^ a)⁻¹ := by
  rw [Rat.zpow_neg]; rfl

theorem ten_zpow_neg_eq (a : Nat) : (10 : Rat) ^ (-(a : Int)) = ((10 : Rat) ^ a)⁻¹ := by
  rw [Rat.zpow_neg]; rfl

/-- If `10^i` and `9 · 10^(i-1)` both lie in `R_v`, then `v` is nearer to
    `10^i`. Only a subnormal `v` with `m ≤ 9` has an interval that wide,
    and then `i = -323` and `m ≥ 2`. -/
theorem ten_pow_closer (h : InRange m q) (hw : InRv m q ((10 : Rat) ^ i) = true)
    (h9 : InRv m q (9 * (10 : Rat) ^ (i - 1)) = true) :
    (10 : Rat) ^ i - v m q < v m q - 9 * (10 : Rat) ^ (i - 1) := by
  obtain ⟨hm1, hm53, hq0, hq1, hnorm⟩ := h
  have hP := two_zpow_pos q
  have hT := ten_zpow_pos (i - 1)
  have hTi : (10 : Rat) ^ i = 10 ^ (i - 1) * 10 := by
    rw [← Rat.zpow_add_one (by decide), Int.sub_add_cancel]
  have hr := (le_of_InRv hw).2
  have hl := (le_of_InRv h9).1
  have hvl : ((m : Rat) - 1/2) * 2 ^ q ≤ vl m q := by unfold vl; split <;> grind
  unfold vr at hr; unfold v
  rw [hTi] at hr ⊢
  generalize hPq : (2 : Rat) ^ q = P at *
  generalize hTi' : (10 : Rat) ^ (i - 1) = T at *
  -- (a) `(m - 1/2) P ≤ 9 T` and (b) `10 T ≤ (m + 1/2) P` give `m ≤ 9`
  have hm9 : m ≤ 9 := by
    have h1 : (10 * (m : Rat) - 5) * P ≤ (9 * (m : Rat) + 9/2) * P := by grind
    have h2 := Rat.le_of_mul_le_mul_right h1 hP
    have h3 : (m : Rat) < 10 := by grind
    have h4 : m < 10 := by exact_mod_cast h3
    omega
  have hq : q = -1074 := by
    rcases Int.lt_or_eq_of_le hq0 with hlt | heq
    · exact absurd (hnorm (by omega)) (by omega)
    · exact heq.symm
  subst hq
  have hm' : (m : Rat) ≤ 9 := by exact_mod_cast hm9
  have hm1' : (1 : Rat) ≤ m := by exact_mod_cast hm1
  have hmP := Rat.mul_le_mul_of_nonneg_right hm' (le_of_lt hP)
  have hmP1 := Rat.mul_le_mul_of_nonneg_right hm1' (le_of_lt hP)
  have hP2 : (0 : Rat) < 2 ^ 1074 := Rat.pow_pos (by decide)
  rw [show (-1074 : Int) = -((1074 : Nat) : Int) by rfl, two_zpow_neg_eq] at hPq
  -- `i = -323`
  have hi1 : i ≤ -323 := by
    rcases Int.lt_or_le (-323) i with hi | hi
    · exfalso
      have hT1 : (10 : Rat) ^ (-((323 : Nat) : Int)) ≤ T := by
        rw [← hTi']; exact zpow_le_zpow_right₀ (by decide) (by omega)
      rw [ten_zpow_neg_eq] at hT1
      have hF := mul_inv_lt_mul_inv hP2 (Rat.pow_pos (by decide)) nineteen_ten_pow_323_lt
      rw [hPq] at hF
      grind
    · exact hi
  have hi2 : -323 ≤ i := by
    rcases Int.lt_or_le i (-323) with hi | hi
    · exfalso
      have hT1 : T ≤ (10 : Rat) ^ (-((325 : Nat) : Int)) := by
        rw [← hTi']; exact zpow_le_zpow_right₀ (by decide) (by omega)
      rw [ten_zpow_neg_eq] at hT1
      have hF := mul_inv_lt_mul_inv (Rat.pow_pos (by decide)) hP2 eighteen_two_pow_1074_lt
      rw [hPq] at hF
      grind
    · exact hi
  have hi : i = -323 := by omega
  subst hi
  have hT' : T = ((10 : Rat) ^ (324 : Nat))⁻¹ := by
    rw [← hTi', ← ten_zpow_neg_eq]; rfl
  subst hT'
  have hT2 : (0 : Rat) < 10 ^ 324 := Rat.pow_pos (by decide)
  -- `m ≥ 2`
  have hm2 : (2 : Rat) ≤ m := by
    rcases Nat.lt_or_ge m 2 with hlt | hge
    · exfalso
      have hF := mul_inv_lt_mul_inv hP2 hT2 three_ten_pow_324_lt
      rw [hPq] at hF
      have : m = 1 := by omega
      subst this
      push_cast at hr
      grind
    · exact_mod_cast hge
  have hF := mul_inv_lt_mul_inv hT2 hP2 nineteen_two_pow_1074_lt
  rw [hPq] at hF
  have := Rat.mul_le_mul_of_nonneg_right hm2 (le_of_lt hP)
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

module
/- The scan: `shortest` returns a hit on the coarsest grid that has one.
   Three facts are specific to binary64 — the grid `10^308` is above every
   value (T1), the grid `10^{-324}` always meets `R_v` (T2), and a tie
   between `9 · 10^i` and `10 · 10^i` cannot occur (T3). Everything else is
   the loop invariant. -/
public import Srtfp.Proofs.Printer.Length
public import Srtfp.Proofs.Clinger.NatIntervalRat

@[expose] public section

open Srtfp.Compat

namespace Srtfp.Printer

/-- The `(m, q)` a finite nonzero binary64 word decodes to. -/
def InRange (m : Nat) (q : Int) : Prop := 1 ≤ m ∧ m < 2 ^ 53 ∧ -1074 ≤ q ∧ q ≤ 971

variable {m : Nat} {q i j : Int} {n : Nat}

/-! ## Binary64 numerics -/

set_option exponentiation.threshold 1100 in
theorem two_pow_1024_lt : (2 : ℕ) ^ 1024 < 10 ^ 309 := by decide

set_option exponentiation.threshold 1100 in
theorem two_pow_1074_le : (2 : ℕ) ^ 1074 ≤ 10 ^ 324 := by decide

set_option exponentiation.threshold 1100 in
theorem four_two_pow_1074_lt : 4 * (2 : ℕ) ^ 1074 < 3 * 10 ^ 324 := by decide

theorem zpow_natCast_lit (b : ℚ) (n : ℕ) : b ^ (n : Int) = b ^ n := rfl

/-! ## T1: nothing above `10^308` -/

theorem v_lt_two_pow_1024 (h : InRange m q) : v m q < (2 : ℚ) ^ (1024 : ℕ) := by
  obtain ⟨_, hm53, _, hq2⟩ := h
  have hm' : (m : ℚ) < (2 : ℚ) ^ (53 : ℕ) := by exact_mod_cast hm53
  have hq' : (2 : ℚ) ^ q ≤ (2 : ℚ) ^ (971 : Int) := zpow_le_zpow_right₀ (by decide) hq2
  have h2 := two_zpow_pos q
  unfold v
  calc (m : ℚ) * 2 ^ q < 2 ^ (53 : ℕ) * 2 ^ q := Rat.mul_lt_mul_of_pos_right hm' h2
    _ ≤ 2 ^ (53 : ℕ) * 2 ^ (971 : Int) :=
        Rat.mul_le_mul_of_nonneg_left hq' (le_of_lt (Rat.pow_pos (by decide)))
    _ = 2 ^ (1024 : ℕ) := by
        show (2 : ℚ) ^ (53 : ℕ) * (2 : ℚ) ^ (971 : ℕ) = (2 : ℚ) ^ (1024 : ℕ)
        rw [← Rat.pow_add]

set_option exponentiation.threshold 1100 in
theorem s_eq_zero_above (h : InRange m q) (hi : 308 < i) : s m q i = 0 := by
  have h10 := ten_zpow_pos i
  have hv : v m q < (10 : ℚ) ^ i := by
    have h1 := v_lt_two_pow_1024 h
    have h2 : (2 : ℚ) ^ (1024 : ℕ) < (10 : ℚ) ^ (309 : Int) := by
      show (2 : ℚ) ^ (1024 : ℕ) < (10 : ℚ) ^ (309 : ℕ)
      exact_mod_cast two_pow_1024_lt
    have h3 : (10 : ℚ) ^ (309 : Int) ≤ (10 : ℚ) ^ i := zpow_le_zpow_right₀ (by decide) (by omega)
    grind
  unfold s
  have hfl : (v m q / (10 : ℚ) ^ i).floor < 1 :=
    Rat.floor_lt_iff.mpr (by rw [Rat.div_lt_iff h10]; simpa using hv)
  exact Int.toNat_eq_zero.mpr (by omega)

/-! ## T2: the grid `10^{-324}` always meets `R_v` -/

theorem two_zpow_neg_1074_le (h : InRange m q) : (2 : ℚ) ^ (-1074 : Int) ≤ (2 : ℚ) ^ q :=
  zpow_le_zpow_right₀ (by decide) h.2.2.1

set_option exponentiation.threshold 1100 in
/-- `10^{-324} ≤ 2^{-1074}`, i.e. `2^1074 ≤ 10^324`. -/
theorem ten_zpow_neg_324_le : (10 : ℚ) ^ (-324 : Int) ≤ (2 : ℚ) ^ (-1074 : Int) := by
  have hA : (0 : ℚ) < (10 : ℚ) ^ (324 : ℕ) := Rat.pow_pos (by decide)
  have hB : (0 : ℚ) < (2 : ℚ) ^ (1074 : ℕ) := Rat.pow_pos (by decide)
  have hAB : (2 : ℚ) ^ (1074 : ℕ) ≤ (10 : ℚ) ^ (324 : ℕ) := by exact_mod_cast two_pow_1074_le
  rw [show (10 : ℚ) ^ (-324 : Int) = ((10 : ℚ) ^ (324 : ℕ))⁻¹ by rw [Rat.zpow_neg]; rfl,
      show (2 : ℚ) ^ (-1074 : Int) = ((2 : ℚ) ^ (1074 : ℕ))⁻¹ by rw [Rat.zpow_neg]; rfl]
  generalize (10 : ℚ) ^ (324 : ℕ) = A at hA hAB ⊢
  generalize (2 : ℚ) ^ (1074 : ℕ) = B at hB hAB ⊢
  have hA' := Rat.mul_inv_cancel A (Rat.ne_of_gt hA)
  have hB' := Rat.mul_inv_cancel B (Rat.ne_of_gt hB)
  -- `A⁻¹ ≤ B⁻¹ ⇔ A⁻¹ (A B) ≤ B⁻¹ (A B) ⇔ B ≤ A`
  apply Rat.le_of_mul_le_mul_right (c := A * B) _ (Rat.mul_pos hA hB)
  calc A⁻¹ * (A * B) = B := by grind
    _ ≤ A := hAB
    _ = B⁻¹ * (A * B) := by grind

set_option exponentiation.threshold 1100 in
/-- `10^{-324} < 3/4 · 2^{-1074}`, i.e. `4 · 2^1074 < 3 · 10^324`. -/
theorem ten_zpow_neg_324_lt_width : (10 : ℚ) ^ (-324 : Int) < 3/4 * (2 : ℚ) ^ (-1074 : Int) := by
  have hA : (0 : ℚ) < (10 : ℚ) ^ (324 : ℕ) := Rat.pow_pos (by decide)
  have hB : (0 : ℚ) < (2 : ℚ) ^ (1074 : ℕ) := Rat.pow_pos (by decide)
  have hAB : 4 * (2 : ℚ) ^ (1074 : ℕ) < 3 * (10 : ℚ) ^ (324 : ℕ) := by
    exact_mod_cast four_two_pow_1074_lt
  rw [show (10 : ℚ) ^ (-324 : Int) = ((10 : ℚ) ^ (324 : ℕ))⁻¹ by rw [Rat.zpow_neg]; rfl,
      show (2 : ℚ) ^ (-1074 : Int) = ((2 : ℚ) ^ (1074 : ℕ))⁻¹ by rw [Rat.zpow_neg]; rfl]
  generalize (10 : ℚ) ^ (324 : ℕ) = A at hA hAB ⊢
  generalize (2 : ℚ) ^ (1074 : ℕ) = B at hB hAB ⊢
  have hA' := Rat.mul_inv_cancel A (Rat.ne_of_gt hA)
  have hB' := Rat.mul_inv_cancel B (Rat.ne_of_gt hB)
  apply Rat.lt_of_mul_lt_mul_right (c := A * B) _ (le_of_lt (Rat.mul_pos hA hB))
  calc A⁻¹ * (A * B) = B := by grind
    _ < 3/4 * A := by grind
    _ = 3/4 * B⁻¹ * (A * B) := by grind

theorem hit_at_bottom (h : InRange m q) : candidate m q (-324) ≠ none := by
  have hm : 1 ≤ m := h.1
  intro hnone
  rcases (candidate_none_iff hm).mp hnone with hs | hno
  · -- `s ≥ 1` because `10^{-324} ≤ 2^{-1074} ≤ v`
    have : 1 ≤ s m q (-324) := by
      rw [s_pos_iff hm]
      have h1 := ten_zpow_neg_324_le
      have h2 := two_zpow_neg_1074_le h
      have hm' : (1 : ℚ) ≤ m := by exact_mod_cast hm
      have h2q := two_zpow_pos q
      unfold v
      have : (2 : ℚ) ^ q ≤ (m : ℚ) * 2 ^ q := by
        have := Rat.mul_le_mul_of_nonneg_right hm' (le_of_lt h2q); grind
      grind
    omega
  · -- a grid point strictly inside `(vl, vr)`: `10^{-324}` is narrower than the interval
    apply hno
    have h10 := ten_zpow_pos (-324 : Int)
    have hvl := vl_pos (q := q) hm
    have hwidth : (10 : ℚ) ^ (-324 : Int) < vr m q - vl m q := by
      have h1 := ten_zpow_neg_324_lt_width
      have h2 := two_zpow_neg_1074_le h
      have h3 := width_ge (m := m) (q := q)
      have : 3/4 * (2 : ℚ) ^ (-1074 : Int) ≤ 3/4 * (2 : ℚ) ^ q :=
        Rat.mul_le_mul_of_nonneg_left h2 (by grind)
      grind
    -- `n := ⌊vl / 10^{-324}⌋ + 1`
    have hVpos : 0 < vl m q / (10 : ℚ) ^ (-324 : Int) :=
      (Rat.lt_div_iff h10).mpr (by rw [Rat.zero_mul]; exact hvl)
    have hVlt := Rat.lt_floor_add_one (vl m q / (10 : ℚ) ^ (-324 : Int))
    have hVle := Rat.floor_le (vl m q / (10 : ℚ) ^ (-324 : Int))
    generalize hV : vl m q / (10 : ℚ) ^ (-324 : Int) = V at hVpos hVlt hVle
    have hfl0 : 0 ≤ V.floor := by
      rcases Int.lt_or_le V.floor 0 with hneg | hnn
      · exfalso; have := Rat.floor_lt_iff.mp hneg; simp at this; grind
      · exact hnn
    have hfl1 : (((V.floor + 1 : Int)) : ℚ) = (V.floor : ℚ) + 1 := by simp
    rw [hfl1] at hVlt
    refine ⟨((V.floor + 1).toNat : ℚ) * (10 : ℚ) ^ (-324 : Int), ⟨_, rfl⟩, ?_⟩
    have hcast : (((V.floor + 1).toNat : Nat) : ℚ) = ((V.floor : ℚ) + 1) := by
      rw [← Rat.intCast_natCast, Int.toNat_of_nonneg (by omega)]; exact hfl1
    rw [hcast]
    have hVmul : V * (10 : ℚ) ^ (-324 : Int) = vl m q := by
      rw [← hV]; exact Rat.div_mul_cancel (Rat.ne_of_gt h10)
    apply InRv_of_strict
    · -- `vl < (⌊V⌋ + 1) · 10^{-324}` since `V < ⌊V⌋ + 1`
      have := Rat.mul_lt_mul_of_pos_right hVlt h10
      rw [hVmul] at this
      exact this
    · -- `(⌊V⌋ + 1) · 10^{-324} ≤ vl + 10^{-324} < vr`
      have := Rat.mul_le_mul_of_nonneg_right hVle (le_of_lt h10)
      rw [hVmul] at this
      grind

/-! ## T3: no tie between `9 · 10^i` and `10 · 10^i` -/

private theorem mod19_table :
    ∀ r, r < 19 → r ≠ 0 → ∀ c, c < 19 → c ≠ 0 → (r * c) % 19 ≠ 0 := by decide

private theorem mul_mod19_ne_zero {x y : ℕ} (hx : x % 19 ≠ 0) (hy : y % 19 ≠ 0) :
    (x * y) % 19 ≠ 0 := by
  rw [Nat.mul_mod]
  exact mod19_table _ (Nat.mod_lt _ (by decide)) hx _ (Nat.mod_lt _ (by decide)) hy

private theorem pow_mod19_ne_zero {b : ℕ} (hb : b % 19 ≠ 0) (a : ℕ) : (b ^ a) % 19 ≠ 0 := by
  induction a with
  | zero => simp
  | succ a ih => rw [Nat.pow_succ]; exact mul_mod19_ne_zero ih hb

theorem nine_ten_tie_impossible (h : InRange m q) :
    ¬ (InRv m q (9 * (10 : ℚ) ^ i) = true ∧ InRv m q (10 * (10 : ℚ) ^ i) = true
       ∧ v m q - 9 * (10 : ℚ) ^ i = 10 * (10 : ℚ) ^ i - v m q) := by
  rintro ⟨h9, h10r, htie⟩
  obtain ⟨hm1, _, _, _⟩ := h
  have hl := (le_of_InRv h9).1
  have hr := (le_of_InRv h10r).2
  have hw := width_le_two_zpow (m := m) (q := q)
  have h2 := two_zpow_pos q
  have h10 := ten_zpow_pos i
  -- the two memberships force `10^i ≤ 2^q`; the tie says `2 v = 19 · 10^i`
  have hgrid : (10 : ℚ) ^ i ≤ (2 : ℚ) ^ q := by grind
  have hmv : (2 * m : ℚ) * (2 : ℚ) ^ q = 19 * (10 : ℚ) ^ i := by unfold v at htie; grind
  have hm9 : m ≤ 9 := by
    have h1 : (2 * m : ℚ) * 2 ^ q ≤ 19 * 2 ^ q := by
      rw [hmv]; exact Rat.mul_le_mul_of_nonneg_left hgrid (by grind)
    have h2' : (2 * m : ℚ) ≤ 19 := Rat.le_of_mul_le_mul_right h1 h2
    have : 2 * m ≤ 19 := by exact_mod_cast h2'
    omega
  -- clear the denominators: `2m · 2^a · 10^c' = 19 · 10^b · 2^a'` in `ℕ`
  have hsplit2 := Srtfp.Schubfach.zpow_two_split q
  have hsplit10 := Srtfp.Schubfach.zpow_ten_split i
  have hnat : (2 * m * 2 ^ (if q ≥ 0 then q.toNat else 0) * 10 ^ (if i < 0 then (-i).toNat else 0) : ℕ)
      = 19 * 10 ^ (if i ≥ 0 then i.toNat else 0) * 2 ^ (if q < 0 then (-q).toNat else 0) := by
    have hq : (2 * m : ℚ) * (2 : ℚ) ^ q * (2 : ℚ) ^ (if q < 0 then (-q).toNat else 0)
        * (10 : ℚ) ^ (if i < 0 then (-i).toNat else 0)
        = 19 * (10 : ℚ) ^ i * (10 : ℚ) ^ (if i < 0 then (-i).toNat else 0)
          * (2 : ℚ) ^ (if q < 0 then (-q).toNat else 0) := by rw [hmv]; grind
    rw [show (2 * m : ℚ) * (2 : ℚ) ^ q * (2 : ℚ) ^ (if q < 0 then (-q).toNat else 0)
        = (2 * m : ℚ) * ((2 : ℚ) ^ q * (2 : ℚ) ^ (if q < 0 then (-q).toNat else 0)) by grind,
      hsplit2,
      show 19 * (10 : ℚ) ^ i * (10 : ℚ) ^ (if i < 0 then (-i).toNat else 0)
        = 19 * ((10 : ℚ) ^ i * (10 : ℚ) ^ (if i < 0 then (-i).toNat else 0)) by grind,
      hsplit10] at hq
    exact_mod_cast hq
  -- the left side is prime to 19, the right side is a multiple of it
  have hL : (2 * m * 2 ^ (if q ≥ 0 then q.toNat else 0)
      * 10 ^ (if i < 0 then (-i).toNat else 0)) % 19 ≠ 0 :=
    mul_mod19_ne_zero (mul_mod19_ne_zero (by omega) (pow_mod19_ne_zero (by decide) _))
      (pow_mod19_ne_zero (by decide) _)
  have hR : (19 * 10 ^ (if i ≥ 0 then i.toNat else 0) * 2 ^ (if q < 0 then (-q).toNat else 0)) % 19
      = 0 := by
    rw [Nat.mul_assoc, Nat.mul_mod_right]
  rw [hnat] at hL
  exact hL hR

/-! ## The loop invariant -/

theorem candidate_snd (h : candidate m q i = some (n, j)) : j = i := by
  rw [candidate_def] at h
  split at h
  · exact absurd h (by simp)
  · split at h <;> simp at h <;> omega

theorem go_spec (m : Nat) (q : Int) :
    ∀ (fuel : Nat) (i : Int),
      (∃ j, i - fuel ≤ j ∧ j ≤ i ∧ candidate m q j ≠ none) →
      ∃ n j, shortest.go m q i (fuel + 1) = (n, j) ∧ i - fuel ≤ j ∧ j ≤ i
        ∧ candidate m q j = some (n, j) ∧ ∀ k, j < k → k ≤ i → candidate m q k = none := by
  intro fuel
  induction fuel with
  | zero =>
    intro i ⟨j, hj1, hj2, hj⟩
    have hji : j = i := by omega
    rw [hji] at hj
    obtain ⟨⟨n, j'⟩, hc⟩ := Option.ne_none_iff_exists'.mp hj
    have hj'i := candidate_snd hc
    refine ⟨n, j', ?_, by omega, by omega, by subst hj'i; exact hc, fun k h1 h2 => by omega⟩
    simp [shortest.go, hc]
  | succ fuel ih =>
    intro i ⟨j, hj1, hj2, hj⟩
    cases hc : candidate m q i with
    | some r =>
      obtain ⟨n, j'⟩ := r
      have hj'i := candidate_snd hc
      refine ⟨n, j', ?_, by omega, by omega, by subst hj'i; exact hc, fun k h1 h2 => by omega⟩
      simp [shortest.go, hc]
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
    1 ≤ n ∧ -324 ≤ i ∧ i ≤ 308 ∧ candidate m q i = some (n, i)
    ∧ ∀ j, i < j → candidate m q j = none := by
  have hm : 1 ≤ m := h.1
  obtain ⟨n', j, hgo, h1, h2, hc, hnone⟩ :=
    go_spec m q 632 308 ⟨-324, by omega, by omega, hit_at_bottom h⟩
  have hsg : shortest m q = shortest.go m q 308 633 := rfl
  rw [hsg, hgo] at hs
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hs
  obtain ⟨_, hs1, hn, _⟩ := candidate_some hm hc
  refine ⟨by omega, by omega, h2, hc, fun j hj => ?_⟩
  rcases Int.lt_or_le 308 j with hj' | hj'
  · rw [candidate_def, if_pos (s_eq_zero_above h hj')]
  · exact hnone j hj hj'

theorem no_hit_above (h : InRange m q) (hs : shortest m q = (n, i)) (hj : i < j) :
    s m q j = 0 ∨ ¬ ∃ x, OnGrid j x ∧ InRv m q x = true :=
  (candidate_none_iff h.1).mp ((scan_spec h hs).2.2.2.2 j hj)

end Srtfp.Printer

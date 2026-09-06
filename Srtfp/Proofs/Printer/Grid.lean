module
/- §6.1: one decimal grid `D_i = {n · 10^i}` and the two neighbours
   `u ≤ v < w` of `v` on it (Definition 2, Result R3), and what
   `candidate` returns. -/
public import Srtfp.Proofs.Printer.Interval

@[expose] public section

open Srtfp.Compat

namespace Srtfp.Printer

variable {m : Nat} {q i : Int} {x : Rat} {n : Nat}

/-- The floor `s_i(v) = ⌊v · 10^{-i}⌋` of Definition 2, as `candidate` computes it. -/
def s (m : Nat) (q i : Int) : Nat := ((v m q) / (10 : Rat) ^ i).floor.toNat

/-- `u_i = s_i · 10^i`, the closest grid point at or below `v`. -/
def u (m : Nat) (q i : Int) : Rat := (s m q i : Rat) * (10 : Rat) ^ i

/-- `w_i = (s_i + 1) · 10^i`, the closest grid point above `v`. -/
def w (m : Nat) (q i : Int) : Rat := ((s m q i : Rat) + 1) * (10 : Rat) ^ i

/-- `x` is a non-negative multiple of `10^i` (the set `D_i`). -/
def OnGrid (i : Int) (x : Rat) : Prop := ∃ n : Nat, x = (n : Rat) * (10 : Rat) ^ i

theorem v_pos (hm : 1 ≤ m) : 0 < v m q := by
  unfold v; have : (1 : Rat) ≤ m := by exact_mod_cast hm
  have := two_zpow_pos q; grind

/-- `V = v / 10^i` is positive, so `s = ⌊V⌋` read in `Rat` is the floor itself. -/
theorem s_cast (hm : 1 ≤ m) :
    ((s m q i : Nat) : Rat) = (((v m q) / (10 : Rat) ^ i).floor : Rat) := by
  unfold s
  rw [← Rat.intCast_natCast, Int.toNat_of_nonneg (floor_nonneg (Rat.le_of_lt (div_pos (v_pos hm) (ten_zpow_pos i))))]

theorem u_le_v (hm : 1 ≤ m) : u m q i ≤ v m q := by
  unfold u; rw [s_cast hm, ← le_div_iff (ten_zpow_pos i)]; exact Rat.floor_le _

theorem v_lt_w (hm : 1 ≤ m) : v m q < w m q i := by
  unfold w; rw [s_cast hm, ← Rat.div_lt_iff (ten_zpow_pos i)]
  exact_mod_cast Rat.lt_floor_add_one _

theorem s_pos_iff : 1 ≤ s m q i ↔ (10 : Rat) ^ i ≤ v m q := by
  unfold s
  rw [show 1 ≤ (v m q / (10 : Rat) ^ i).floor.toNat ↔ 1 ≤ (v m q / (10 : Rat) ^ i).floor by omega,
    Rat.le_floor_iff, le_div_iff (ten_zpow_pos i)]
  simp

theorem onGrid_u : OnGrid i (u m q i) := ⟨s m q i, rfl⟩

theorem onGrid_w : OnGrid i (w m q i) := ⟨s m q i + 1, by unfold w; push_cast; rfl⟩

/-- R3: on `D_i`, every point is at or below `u` or at or above `w`. -/
theorem onGrid_le_u_or_w_le (hx : OnGrid i x) : x ≤ u m q i ∨ w m q i ≤ x := by
  obtain ⟨k, rfl⟩ := hx
  have h10 := ten_zpow_pos i
  rcases Nat.lt_or_ge k (s m q i + 1) with hk | hk
  · left
    unfold u
    exact Rat.mul_le_mul_of_nonneg_right (by exact_mod_cast (show k ≤ s m q i by omega)) (Rat.le_of_lt h10)
  · right
    unfold w
    have : ((s m q i : Rat) + 1) ≤ k := by exact_mod_cast hk
    exact Rat.mul_le_mul_of_nonneg_right this (Rat.le_of_lt h10)

/-- The grid meets `R_v` iff a neighbour does (R3 and convexity). -/
theorem hit_iff_neighbour (hm : 1 ≤ m) :
    (∃ x, OnGrid i x ∧ InRv m q x = true) ↔
      (InRv m q (u m q i) = true ∨ InRv m q (w m q i) = true) := by
  constructor
  · rintro ⟨x, hx, hxR⟩
    rcases onGrid_le_u_or_w_le (m := m) (q := q) hx with hxu | hwx
    · left
      exact InRv_convex hxR (InRv_v hm) hxu (u_le_v hm)
    · right
      exact InRv_convex (InRv_v hm) hxR (Rat.le_of_lt (v_lt_w hm)) hwx
  · rintro (h | h)
    · exact ⟨_, onGrid_u, h⟩
    · exact ⟨_, onGrid_w, h⟩

/-! ## What `candidate` returns -/

/-- `candidate` unfolded in terms of `s`, `u`, `w`. -/
theorem candidate_def :
    candidate m q i =
      match InRv m q (u m q i), InRv m q (w m q i) with
      | true,  true  => some (if v m q - u m q i < w m q i - v m q
                              ∨ (v m q - u m q i = w m q i - v m q ∧ s m q i % 2 = 0)
                              then s m q i else s m q i + 1)
      | true,  false => some (s m q i)
      | false, true  => some (s m q i + 1)
      | false, false => none := rfl

theorem candidate_none_iff (hm : 1 ≤ m) :
    candidate m q i = none ↔ ¬ ∃ x, OnGrid i x ∧ InRv m q x = true := by
  rw [hit_iff_neighbour hm, candidate_def]
  cases hu : InRv m q (u m q i) <;> cases hw : InRv m q (w m q i) <;> simp [*]

/-- `u` is in `R_v` only above the leading digit: `u = 0` is not. -/
theorem s_pos_of_InRv_u (hm : 1 ≤ m) (hu : InRv m q (u m q i) = true) : 1 ≤ s m q i :=
  Nat.pos_of_ne_zero fun h0 => by
    have h1 := (le_of_InRv hu).1; have h2 := vl_pos (q := q) hm
    unfold u at h1; rw [h0] at h1; simp at h1; grind

/-- A grid point in `R_v` at or below `u` is no closer than `u`; one at or
    above `w` is in `R_v` only if `w` is. -/
theorem grid_point_side (hm : 1 ≤ m) (hx : OnGrid i x) (hxR : InRv m q x = true) :
    (x ≤ u m q i) ∨ (w m q i ≤ x ∧ InRv m q (w m q i) = true) := by
  rcases onGrid_le_u_or_w_le (m := m) (q := q) hx with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h, InRv_convex (InRv_v hm) hxR (Rat.le_of_lt (v_lt_w hm)) h⟩

theorem grid_point_side' (hm : 1 ≤ m) (hx : OnGrid i x) (hxR : InRv m q x = true) :
    (w m q i ≤ x) ∨ (x ≤ u m q i ∧ InRv m q (u m q i) = true) := by
  rcases onGrid_le_u_or_w_le (m := m) (q := q) hx with h | h
  · exact Or.inr ⟨h, InRv_convex hxR (InRv_v hm) h (u_le_v hm)⟩
  · exact Or.inl h

private theorem close_u (hm : 1 ≤ m)
    (hle : InRv m q (w m q i) = true → v m q - u m q i ≤ w m q i - v m q)
    (hx : OnGrid i x) (hxR : InRv m q x = true) :
    |v m q - u m q i| ≤ |v m q - x| := by
  have huv := u_le_v (q := q) (i := i) hm
  have hvw := v_lt_w (q := q) (i := i) hm
  rw [Rat.abs_of_nonneg (by grind)]
  rcases grid_point_side hm hx hxR with h | ⟨h, hw⟩
  · rw [Rat.abs_of_nonneg (by grind)]; grind
  · rw [Rat.abs_of_nonpos (by grind)]; have := hle hw; grind

private theorem close_w (hm : 1 ≤ m)
    (hle : InRv m q (u m q i) = true → w m q i - v m q ≤ v m q - u m q i)
    (hx : OnGrid i x) (hxR : InRv m q x = true) :
    |v m q - w m q i| ≤ |v m q - x| := by
  have huv := u_le_v (q := q) (i := i) hm
  have hvw := v_lt_w (q := q) (i := i) hm
  rw [Rat.abs_of_nonpos (by grind)]
  rcases grid_point_side' hm hx hxR with h | ⟨h, hu⟩
  · rw [Rat.abs_of_nonpos (by grind)]; grind
  · rw [Rat.abs_of_nonneg (by grind)]; have := hle hu; grind

private theorem tie_u (hm : 1 ≤ m)
    (hc : InRv m q (w m q i) = true →
      v m q - u m q i < w m q i - v m q ∨ (v m q - u m q i = w m q i - v m q ∧ s m q i % 2 = 0))
    (hx : OnGrid i x) (hxR : InRv m q x = true) (hne : x ≠ u m q i)
    (heq : |v m q - u m q i| = |v m q - x|) : s m q i % 2 = 0 := by
  have huv := u_le_v (q := q) (i := i) hm
  have hvw := v_lt_w (q := q) (i := i) hm
  rw [Rat.abs_of_nonneg (by grind)] at heq
  rcases grid_point_side hm hx hxR with h | ⟨h, hw⟩
  · rw [Rat.abs_of_nonneg (by grind)] at heq; exact absurd (by grind) hne
  · rw [Rat.abs_of_nonpos (by grind)] at heq
    rcases hc hw with hlt | ⟨_, he⟩
    · exfalso; grind
    · exact he

private theorem tie_w (hm : 1 ≤ m)
    (hc : InRv m q (u m q i) = true →
      ¬ (v m q - u m q i < w m q i - v m q ∨ (v m q - u m q i = w m q i - v m q ∧ s m q i % 2 = 0)))
    (hx : OnGrid i x) (hxR : InRv m q x = true) (hne : x ≠ w m q i)
    (heq : |v m q - w m q i| = |v m q - x|) : (s m q i + 1) % 2 = 0 := by
  have huv := u_le_v (q := q) (i := i) hm
  have hvw := v_lt_w (q := q) (i := i) hm
  rw [Rat.abs_of_nonpos (by grind)] at heq
  rcases grid_point_side' hm hx hxR with h | ⟨h, hu⟩
  · rw [Rat.abs_of_nonpos (by grind)] at heq; exact absurd (by grind) hne
  · rw [Rat.abs_of_nonneg (by grind)] at heq
    have hc' := hc hu
    have hge : w m q i - v m q ≤ v m q - u m q i := by grind
    have heqd : v m q - u m q i = w m q i - v m q := by grind
    have hodd : s m q i % 2 ≠ 0 := fun he => hc' (Or.inr ⟨heqd, he⟩)
    omega

/-- What a hit returns: a positive neighbour in `R_v`, no farther from `v`
    than any grid point in `R_v`, and even on an exact tie. -/
theorem candidate_some (hm : 1 ≤ m) (h : candidate m q i = some n) :
    1 ≤ n ∧ (n = s m q i ∨ n = s m q i + 1)
    ∧ InRv m q ((n : Rat) * (10 : Rat) ^ i) = true
    ∧ (∀ x, OnGrid i x → InRv m q x = true → |v m q - n * (10 : Rat) ^ i| ≤ |v m q - x|)
    ∧ (∀ x, OnGrid i x → InRv m q x = true → x ≠ n * (10 : Rat) ^ i →
         |v m q - n * (10 : Rat) ^ i| = |v m q - x| → n % 2 = 0) := by
  rw [candidate_def] at h
  have hu_def : u m q i = (s m q i : Rat) * (10 : Rat) ^ i := rfl
  have hw_def : w m q i = ((s m q i : Rat) + 1) * (10 : Rat) ^ i := rfl
  have hw_cast : ((s m q i + 1 : Nat) : Rat) * (10 : Rat) ^ i = w m q i := by
    rw [hw_def]; push_cast; rfl
  cases hu : InRv m q (u m q i) <;> cases hw : InRv m q (w m q i) <;> rw [hu, hw] at h <;> simp at h
  · -- only `w`
    subst h
    refine ⟨by omega, Or.inr rfl, by rw [hw_cast]; exact hw, ?_, ?_⟩
    · intro x hx hxR; rw [hw_cast]
      exact close_w hm (fun h' => by rw [hu] at h'; cases h') hx hxR
    · intro x hx hxR hne heq; rw [hw_cast] at hne heq
      exact tie_w hm (fun h' => by rw [hu] at h'; cases h') hx hxR hne heq
  · -- only `u`
    subst h
    refine ⟨s_pos_of_InRv_u hm hu, Or.inl rfl, hu, ?_, ?_⟩
    · intro x hx hxR
      exact close_u hm (fun h' => by rw [hw] at h'; cases h') hx hxR
    · intro x hx hxR hne heq
      exact tie_u hm (fun h' => by rw [hw] at h'; cases h') hx hxR hne heq
  · -- both: the nearer, ties to even
    split at h
    · rename_i hc
      subst h
      refine ⟨s_pos_of_InRv_u hm hu, Or.inl rfl, hu, ?_, ?_⟩
      · intro x hx hxR
        exact close_u hm (fun _ => by rcases hc with h1 | ⟨h1, _⟩ <;> grind) hx hxR
      · intro x hx hxR hne heq
        exact tie_u hm (fun _ => hc) hx hxR hne heq
    · rename_i hc
      subst h
      refine ⟨by omega, Or.inr rfl, by rw [hw_cast]; exact hw, ?_, ?_⟩
      · intro x hx hxR; rw [hw_cast]
        exact close_w hm (fun _ => by grind) hx hxR
      · intro x hx hxR hne heq; rw [hw_cast] at hne heq
        exact tie_w hm (fun _ => hc) hx hxR hne heq

end Srtfp.Printer

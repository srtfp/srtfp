module
/- The reader lands in the rounding interval. Below the overflow
   threshold, `read d` is a finite word (or a zero) of the decimal's sign
   whose interval `R_w` contains the magnitude; at or past the threshold
   it is the infinity of that sign. Read off the definition in
   `Srtfp/Reader.lean`, with `roundEven` and `gridExp` as specified in
   `Srtfp/Proofs/Reader/Round.lean`. -/
public import Srtfp.Proofs.Reader.Round
public import Srtfp.Proofs.Reader.Words

@[expose] public section

open Srtfp.Compat

namespace Srtfp.Reader

open Srtfp.Printer Srtfp.Model
open Float.Model (UnpackedFloat)

/-- The overflow threshold is the right endpoint of the largest interval. -/
theorem threshold_eq : (2 : Rat) ^ 1024 - 2 ^ 970 = (2 ^ 53 - 1/2) * (2 : Rat) ^ (971 : Int) := by
  rw [show (2 : Rat) ^ (971 : Int) = (2 : Rat) ^ (971 : Nat) from rfl]
  have h1 : (2 : Rat) ^ 1024 = 2 ^ 53 * 2 ^ 971 := by rw [← Rat.pow_add]
  have h2 : (2 : Rat) ^ 971 = 2 * 2 ^ 970 := by rw [Rat.pow_succ]; grind
  grind

/-- `y · 2^k ∈ R_(n, k)` when `y` rounds to `n` (ties only for even `n`),
    with `y` at least `n - 1/4` at the bottom of a binade. -/
theorem InRv_of_round {y : Rat} {k : Int} {n : Nat}
    (hlo : (n : Rat) - 1/2 ≤ y) (hhi : y ≤ n + 1/2)
    (hlo' : y = n - 1/2 → n % 2 = 0) (hhi' : y = n + 1/2 → n % 2 = 0)
    (hirr : n = 2 ^ 52 ∧ k > -1074 → (n : Rat) - 1/4 ≤ y) :
    InRv n k (y * 2 ^ k) = true := by
  have hP := Rat.le_of_lt (two_zpow_pos k)
  unfold InRv vl vr
  split
  · -- even: closed endpoints
    simp only [decide_eq_true_eq]
    split
    · exact ⟨Rat.mul_le_mul_of_nonneg_right (hirr (by assumption)) hP,
        Rat.mul_le_mul_of_nonneg_right hhi hP⟩
    · exact ⟨Rat.mul_le_mul_of_nonneg_right hlo hP, Rat.mul_le_mul_of_nonneg_right hhi hP⟩
  · -- odd: no tie, so both bounds are strict
    rename_i hodd
    simp only [decide_eq_true_eq]
    have hP' := two_zpow_pos k
    have h1 : (n : Rat) - 1/2 < y := Rat.lt_of_le_of_ne hlo (fun h => hodd (hlo' h.symm))
    have h2 : y < n + 1/2 := Rat.lt_of_le_of_ne hhi (fun h => hodd (hhi' h))
    rw [if_neg (fun h => hodd (by rw [h.1]))]
    exact ⟨Rat.mul_lt_mul_of_pos_right h1 hP', Rat.mul_lt_mul_of_pos_right h2 hP'⟩

/-- What `read` returns, below and above the threshold. -/
theorem read_spec (d : Decimal) :
    ((d.significand : Rat) * (10 : Rat) ^ d.exponent < 2 ^ 1024 - 2 ^ 970 →
      (read d).isFinite = true ∧ usign (read d) = d.sign
      ∧ Legal (mq (read d)).1 (mq (read d)).2
      ∧ InRv (mq (read d)).1 (mq (read d)).2 ((d.significand : Rat) * (10 : Rat) ^ d.exponent) = true)
    ∧ (2 ^ 1024 - 2 ^ 970 ≤ (d.significand : Rat) * (10 : Rat) ^ d.exponent →
      read d = .infinity d.sign) := by
  unfold read
  dsimp only
  rw [abs_toRat]
  have hx0 := mag_nonneg d
  have hc52 : ((2 ^ 52 : Nat) : Rat) = (2 : Rat) ^ 52 := by rw [← two_zpow_natCast, Rat.zpow_natCast]
  have hc53 : ((2 ^ 53 : Nat) : Rat) = (2 : Rat) ^ 53 := by rw [← two_zpow_natCast, Rat.zpow_natCast]
  have h53 : (2 : Rat) ^ 53 = 2 ^ 52 * 2 := Rat.pow_succ 2 52
  generalize (d.significand : Rat) * (10 : Rat) ^ d.exponent = x at *
  split
  · rename_i hT
    exact ⟨fun h => absurd hT (Rat.not_le.mpr h), fun _ => rfl⟩
  rename_i hT
  refine ⟨fun _ => ?_, fun h => absurd h hT⟩
  have hT' : x < (2 ^ 53 - 1/2) * (2 : Rat) ^ (971 : Int) := by
    rw [← threshold_eq]; exact Rat.not_le.mp hT
  -- the grid `2^k`, and `y = x / 2^k` rounded to `r`
  obtain ⟨hk0, hk1, hk2⟩ := gridExp_spec hx0
  generalize gridExp x = k at *
  have hP := two_zpow_pos k
  have e53 : (2 : Rat) ^ (k + 53) = 2 ^ 53 * 2 ^ k := by
    rw [Rat.zpow_add (by decide), Rat.mul_comm]; rfl
  have e52 : (2 : Rat) ^ (k + 52) = 2 ^ 52 * 2 ^ k := by
    rw [Rat.zpow_add (by decide), Rat.mul_comm]; rfl
  rw [e53] at hk1
  rw [e52] at hk2
  have hxy : x = x / 2 ^ k * 2 ^ k := (Rat.div_mul_cancel (Rat.ne_of_gt hP)).symm
  have hy0 : 0 ≤ x / 2 ^ k := div_nonneg hx0 hP
  have hy53 : x / 2 ^ k < ((2 ^ 53 : Nat) : Rat) := by rw [hc53]; exact (Rat.div_lt_iff hP).mpr hk1
  have hr53 := roundEven_le hy53
  obtain ⟨hlo, hhi, hlo', hhi'⟩ := roundEven_spec (x / 2 ^ k)
  have hr0 := roundEven_nonneg hy0
  generalize roundEven (x / 2 ^ k) = r at *
  generalize x / 2 ^ k = y at *
  subst hxy
  have hy52 : k = -1074 ∨ (2 : Rat) ^ 52 ≤ y := by
    rcases hk2 with h | h
    · exact Or.inl h
    · exact Or.inr (Rat.le_of_mul_le_mul_right h hP)
  have hrN : ((r.toNat : Nat) : Rat) = (r : Rat) := by
    rw [← Rat.intCast_natCast, Int.toNat_of_nonneg hr0]
  -- the threshold bounds `k`: `k ≤ 971`, and `k ≤ 970` once `y` reaches `2^53 - 1/2`
  have hk971 : (2 : Rat) ^ 52 ≤ y → k ≤ 971 := fun h => by
    have h1024 : (2 : Rat) ^ (1024 : Int) = 2 ^ 53 * 2 ^ (971 : Int) := by
      rw [show (1024 : Int) = 53 + 971 by rfl, Rat.zpow_add (by decide)]; rfl
    have := lt_of_zpow_lt (a := 2) (by decide) (x := k + 52) (y := 1024) (by
      rw [e52, h1024]
      exact lt_of_le_of_lt (Rat.mul_le_mul_of_nonneg_right h (Rat.le_of_lt hP))
        (lt_of_lt_of_le hT' (Rat.mul_le_mul_of_nonneg_right (by grind)
          (Rat.le_of_lt (two_zpow_pos _)))))
    omega
  have hk970 : (2 : Rat) ^ 53 - 1/2 ≤ y → k ≤ 970 := fun h => by
    have h1 := lt_of_le_of_lt (Rat.mul_le_mul_of_nonneg_right h (Rat.le_of_lt hP)) hT'
    rw [Rat.mul_comm, Rat.mul_comm _ ((2 : Rat) ^ (971 : Int))] at h1
    have := lt_of_zpow_lt (a := 2) (by decide) (Rat.lt_of_mul_lt_mul_right h1 (by grind))
    omega
  split
  · -- `r = 0`: `y ≤ 1/2`, on the bottom grid
    rename_i h0
    obtain rfl : r = 0 := by omega
    push_cast at hhi
    rcases hy52 with rfl | h
    · refine ⟨rfl, rfl, legal_zero, InRv_of_round (n := 0) (by push_cast; grind) (by push_cast; grind)
        (fun _ => rfl) (fun _ => rfl) (fun h => absurd h.1 (by decide))⟩
    · exfalso; have := one_le_pow (a := (2 : Rat)) (by decide) 52; grind
  · rename_i h0
    split
    · -- `r = 2^53`: the carry, `2^52` on the next grid
      rename_i h53'
      have hr' : (r : Rat) = 2 ^ 53 := by rw [← hrN, h53', hc53]
      rw [hr'] at hlo hhi
      have hk := hk970 hlo
      simp only [mq]
      refine ⟨rfl, rfl, ⟨by omega, by omega, by omega, fun _ => Nat.le_refl _⟩, ?_⟩
      rw [show y * 2 ^ k = y / 2 * 2 ^ (k + 1) by rw [Rat.zpow_add_one (by decide)]; grind]
      exact InRv_of_round (n := 2 ^ 52) (by rw [hc52]; grind) (by rw [hc52]; grind)
        (fun _ => by decide) (fun _ => by decide) (fun _ => by rw [hc52]; grind)
    · -- the grid point `r · 2^k`
      rename_i h53'
      have hn52 : k ≠ -1074 → 2 ^ 52 ≤ r.toNat := fun hk => by
        have h := hy52.resolve_left hk
        have h1 : ((2 ^ 52 : Nat) : Rat) < ((r.toNat + 1 : Nat) : Rat) := by
          rw [hc52]; push_cast; rw [hrN]; grind
        have h2 : 2 ^ 52 < r.toNat + 1 := by exact_mod_cast h1
        omega
      simp only [mq]
      refine ⟨rfl, rfl, ⟨by omega, hk0, ?_, hn52⟩, ?_⟩
      · rcases Int.lt_or_le 971 k with h | h
        · exact absurd (hk971 (hy52.resolve_left (by omega))) (by omega)
        · exact h
      · rw [← hrN] at hlo hhi hlo' hhi'
        exact InRv_of_round hlo hhi (fun h => by have := hlo' h; omega)
          (fun h => by have := hhi' h; omega)
          (fun hi => by
            rcases hy52 with h | h
            · omega
            · rw [hi.1, hc52]; grind)

end Srtfp.Reader

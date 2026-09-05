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

theorem natCast_two_pow (n : Nat) : ((2 ^ n : Nat) : Rat) = (2 : Rat) ^ n := by
  rw [← two_zpow_natCast]; rfl

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
  have hc52 := natCast_two_pow 52
  have hc53 := natCast_two_pow 53
  have h53pos : (0 : Rat) < 2 ^ 53 := Rat.pow_pos (by decide)
  generalize (d.significand : Rat) * (10 : Rat) ^ d.exponent = x at *
  split
  · rename_i hT
    exact ⟨fun h => absurd hT (Rat.not_le.mpr h), fun _ => rfl⟩
  · rename_i hT
    refine ⟨fun _ => ?_, fun h => absurd h hT⟩
    have hT' : x < 2 ^ 1024 - 2 ^ 970 := Rat.not_le.mp hT
    rw [threshold_eq] at hT'
    -- the grid `2^k` and the rounding of `y = x / 2^k`
    obtain ⟨hk0, hk1, hk2⟩ := gridExp_spec hx0
    generalize gridExp x = k at *
    have hP := two_zpow_pos k
    have e53 : (2 : Rat) ^ (k + 53) = 2 ^ 53 * 2 ^ k := by
      rw [Rat.zpow_add (by decide), Rat.mul_comm]; rfl
    have e52 : (2 : Rat) ^ (k + 52) = 2 ^ 52 * 2 ^ k := by
      rw [Rat.zpow_add (by decide), Rat.mul_comm]; rfl
    rw [e53] at hk1
    have hxy : x = x / 2 ^ k * 2 ^ k := (Rat.div_mul_cancel (Rat.ne_of_gt hP)).symm
    have hy0 : 0 ≤ x / 2 ^ k := (le_div_iff hP).mpr (by rw [Rat.zero_mul]; exact hx0)
    have hy53 : x / 2 ^ k < ((2 ^ 53 : Nat) : Rat) := by
      rw [hc53]; exact (Rat.div_lt_iff hP).mpr hk1
    have hr53 := roundEven_le hy53
    obtain ⟨hlo, hhi, hlo', hhi'⟩ := roundEven_spec (x / 2 ^ k)
    have hr0 := roundEven_nonneg hy0
    generalize roundEven (x / 2 ^ k) = r at *
    generalize x / 2 ^ k = y at *
    subst hxy
    rw [hc53] at hy53
    have hy52 : k = -1074 ∨ (2 : Rat) ^ 52 ≤ y := by
      rcases hk2 with h | h
      · exact Or.inl h
      · rw [e52] at h
        exact Or.inr (Rat.le_of_mul_le_mul_right h hP)
    have hrN : ((r.toNat : Nat) : Rat) = (r : Rat) := by
      rw [← Rat.intCast_natCast, Int.toNat_of_nonneg hr0]
    -- membership in `R_v` for the returned `(n, k)`
    have mem (n : Nat) (hn : (n : Rat) = r) (hn52 : k ≠ -1074 → 2 ^ 52 ≤ n) :
        InRv n k (y * 2 ^ k) = true := by
      have hnr : (n : Int) = r := by exact_mod_cast hn
      rw [← hn] at hlo hhi hlo' hhi'
      unfold InRv vl vr
      have hvl : ((n : Rat) - 1/2) * 2 ^ k ≤ y * 2 ^ k :=
        Rat.mul_le_mul_of_nonneg_right hlo (Rat.le_of_lt hP)
      have hvr : y * 2 ^ k ≤ ((n : Rat) + 1/2) * 2 ^ k :=
        Rat.mul_le_mul_of_nonneg_right hhi (Rat.le_of_lt hP)
      have hirr : n = 2 ^ 52 ∧ k > -1074 → ((n : Rat) - 1/4) * 2 ^ k ≤ y * 2 ^ k := by
        rintro ⟨hn2, hk⟩
        rcases hy52 with h | h
        · omega
        · have : ((n : Rat) - 1/4) ≤ y := by rw [hn2, hc52]; grind
          exact Rat.mul_le_mul_of_nonneg_right this (Rat.le_of_lt hP)
      split
      · rename_i heven
        simp only [decide_eq_true_eq]
        split
        · exact ⟨hirr (by assumption), hvr⟩
        · exact ⟨hvl, hvr⟩
      · rename_i hodd
        simp only [decide_eq_true_eq]
        have hlt1 : ((n : Rat) - 1/2) < y := by
          rcases Rat.eq_or_lt_of_le hlo with h | h
          · exfalso; have := hlo' h.symm; omega
          · exact h
        have hlt2 : y < (n : Rat) + 1/2 := by
          rcases Rat.eq_or_lt_of_le hhi with h | h
          · exfalso; have := hhi' h; omega
          · exact h
        have hvl' := Rat.mul_lt_mul_of_pos_right hlt1 hP
        have hvr' := Rat.mul_lt_mul_of_pos_right hlt2 hP
        split
        · rename_i hi
          refine ⟨?_, hvr'⟩
          rcases hy52 with h | h
          · omega
          · have : ((n : Rat) - 1/4) < y := by rw [hi.1, hc52]; grind
            exact Rat.mul_lt_mul_of_pos_right this hP
        · exact ⟨hvl', hvr'⟩
    split
    · -- zero: `y ≤ 1/2`, on the bottom grid
      rename_i h0
      have hr0' : r = 0 := by omega
      have hk : k = -1074 := by
        rcases hy52 with h | h
        · exact h
        · exfalso; rw [hr0'] at hhi; push_cast at hhi
          have : (1 : Rat) ≤ 2 ^ 52 := one_le_pow_rat (by decide) 52
          grind
      subst hk
      refine ⟨rfl, rfl, legal_zero, ?_⟩
      exact mem 0 (by rw [hr0']; rfl) (fun h => absurd rfl h)
    · rename_i h0
      split
      · -- carry: `y` rounds to `2^53`; the value is `2^52 · 2^(k+1)`
        rename_i h53
        have hr' : (r : Rat) = 2 ^ 53 := by rw [← hrN, h53, hc53]
        have hk : k ≤ 970 := by
          rcases Int.lt_or_le k 971 with h | h
          · omega
          · exfalso
            rw [hr'] at hlo
            have h1 : (2 : Rat) ^ (971 : Int) ≤ 2 ^ k := zpow_le_zpow_right₀ (by decide) h
            have h2 : ((2 : Rat) ^ 53 - 1/2) * 2 ^ (971 : Int) ≤ (2 ^ 53 - 1/2) * 2 ^ k :=
              Rat.mul_le_mul_of_nonneg_left h1 (by grind)
            have h3 : ((2 : Rat) ^ 53 - 1/2) * 2 ^ k ≤ y * 2 ^ k :=
              Rat.mul_le_mul_of_nonneg_right hlo (Rat.le_of_lt hP)
            exact absurd hT' (Rat.not_lt.mpr (Rat.le_trans h2 h3))
        refine ⟨rfl, rfl, ?_, ?_⟩
        · show Legal (2 ^ 52) (k + 1)
          exact ⟨by omega, by omega, by omega, fun _ => Nat.le_refl _⟩
        show InRv (2 ^ 52) (k + 1) (y * 2 ^ k) = true
        have h2 : (2 : Rat) ^ (k + 1) = 2 ^ k * 2 := Rat.zpow_add_one (by decide) k
        unfold InRv vl vr
        rw [if_pos (by decide), if_pos ⟨rfl, by omega⟩, h2, hc52]
        simp only [decide_eq_true_eq]
        rw [hr'] at hlo hhi
        have h53 : (2 : Rat) ^ 53 = 2 ^ 52 * 2 := by rw [Rat.pow_succ]
        constructor
        · have : ((2 : Rat) ^ 52 - 1/4) * (2 ^ k * 2) = (2 ^ 53 - 1/2) * 2 ^ k := by
            rw [h53]; grind
          rw [this]; exact Rat.mul_le_mul_of_nonneg_right hlo (Rat.le_of_lt hP)
        · have : ((2 : Rat) ^ 52 + 1/2) * (2 ^ k * 2) = (2 ^ 53 + 1) * 2 ^ k := by
            rw [h53]; grind
          rw [this]
          exact Rat.mul_le_mul_of_nonneg_right (by grind) (Rat.le_of_lt hP)
      · -- the grid point `r · 2^k`
        rename_i h53
        have hr' : (r.toNat : Rat) = r := hrN
        have hn52 : k ≠ -1074 → 2 ^ 52 ≤ r.toNat := by
          intro hk
          rcases hy52 with h | h
          · exact absurd h hk
          · have h1 : (2 : Rat) ^ 52 - 1 < r.toNat := by rw [hr']; grind
            have h2 : ((2 ^ 52 : Nat) : Rat) < ((r.toNat + 1 : Nat) : Rat) := by
              rw [hc52]; push_cast; grind
            have h3 : 2 ^ 52 < r.toNat + 1 := by exact_mod_cast h2
            omega
        have hk : k ≤ 971 := by
          rcases Int.lt_or_le 971 k with h | h
          · exfalso
            have h52 := hn52 (by omega)
            have h1 : (2 : Rat) ^ 52 ≤ y := by
              rcases hy52 with h' | h'
              · omega
              · exact h'
            have h2 : (2 : Rat) ^ (972 : Int) ≤ (2 : Rat) ^ k := zpow_le_zpow_right₀ (by decide) h
            have h3 : (2 : Rat) ^ (972 : Int) = 2 * 2 ^ (971 : Int) := by
              rw [show (972 : Int) = 971 + 1 by rfl, Rat.zpow_add_one (by decide)]; grind
            have h4 := two_zpow_pos (971 : Int)
            have h5 : (2 : Rat) ^ 52 * 2 ^ k ≤ y * 2 ^ k :=
              Rat.mul_le_mul_of_nonneg_right h1 (Rat.le_of_lt hP)
            have h6 : (2 : Rat) ^ 52 * 2 ^ (972 : Int) ≤ (2 : Rat) ^ 52 * 2 ^ k :=
              Rat.mul_le_mul_of_nonneg_left h2 (Rat.le_of_lt (Rat.pow_pos (by decide)))
            have h7 : (2 : Rat) ^ 53 = 2 ^ 52 * 2 := by rw [Rat.pow_succ]
            grind
          · exact h
        refine ⟨rfl, rfl, ?_, ?_⟩
        · show Legal r.toNat k
          exact ⟨by omega, hk0, hk, hn52⟩
        · show InRv r.toNat k (y * 2 ^ k) = true
          exact mem r.toNat hr' hn52

end Srtfp.Reader

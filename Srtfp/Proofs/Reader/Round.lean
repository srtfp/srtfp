module
/- The two arithmetic helpers of `Srtfp/Proofs/Reader/Reference.lean`, read over `Rat`:
   `roundEven` is the nearest integer with ties to even, and `gridExp`
   the exponent of the binary64 grid around a magnitude. -/

public import Srtfp.Proofs.Reader.Reference
public import Srtfp.Proofs.Printer.Interval

@[expose] public section

open Srtfp.Compat

namespace Srtfp.Reader


/-! ## `roundEven` -/

/-- `n = roundEven x` is the integer nearest to `x`: `n - 1/2 ≤ x ≤ n + 1/2`,
    and an endpoint is attained only for even `n`. -/
theorem roundEven_spec (x : Rat) :
    (roundEven x : Rat) - 1/2 ≤ x ∧ x ≤ roundEven x + 1/2
    ∧ (x = roundEven x - 1/2 → roundEven x % 2 = 0)
    ∧ (x = roundEven x + 1/2 → roundEven x % 2 = 0) := by
  unfold roundEven
  dsimp only
  have hle := Rat.floor_le (x + 1/2)
  have hlt := Rat.lt_floor_add_one (x + 1/2)
  generalize (x + 1/2).floor = n at *
  split
  · rename_i h
    obtain ⟨heq, hodd⟩ := h
    push_cast
    refine ⟨by grind, by grind, fun h' => ?_, fun _ => by omega⟩
    exfalso; grind
  · rename_i h
    refine ⟨by grind, by grind, fun h' => ?_, fun h' => ?_⟩
    · have hodd : ¬ n % 2 = 1 := fun ho => h ⟨by grind, ho⟩
      omega
    · exfalso; grind

theorem roundEven_nonneg {x : Rat} (hx : 0 ≤ x) : 0 ≤ roundEven x := by
  have h := (roundEven_spec x).2.1
  have : ((-1 : Int) : Rat) < roundEven x := by push_cast; grind
  have : (-1 : Int) < roundEven x := by exact_mod_cast this
  omega

/-- Below a natural bound `b`, the rounding stays at or below `b`. -/
theorem roundEven_le {x : Rat} {b : Nat} (hx : x < b) : roundEven x ≤ b := by
  have h := (roundEven_spec x).1
  have : (roundEven x : Rat) < ((b : Int) + 1 : Int) := by push_cast; grind
  have : roundEven x < (b : Int) + 1 := by exact_mod_cast this
  omega

/-! ## `gridExp` -/

/-- `k = gridExp x` for `x ≥ 0`: `-1074 ≤ k`, `x < 2^(k+53)`, and
    `2^(k+52) ≤ x` unless `k = -1074`. -/
theorem gridExp_spec {x : Rat} (hx : 0 ≤ x) :
    -1074 ≤ gridExp x ∧ x < (2 : Rat) ^ (gridExp x + 53)
    ∧ (gridExp x = -1074 ∨ (2 : Rat) ^ (gridExp x + 52) ≤ x) := by
  unfold gridExp
  have hP : (0 : Rat) < 2 ^ 1074 := Rat.pow_pos (by decide)
  have hle := Rat.floor_le (x * 2 ^ 1074)
  have hlt := Rat.lt_floor_add_one (x * 2 ^ 1074)
  have hy0 : 0 ≤ (x * 2 ^ 1074).floor :=
    Rat.le_floor_iff.mpr (by simpa using Rat.mul_nonneg hx (Rat.le_of_lt hP))
  generalize (x * 2 ^ 1074).floor = y at *
  have hYy : ((y.toNat : Nat) : Rat) = (y : Rat) := by
    rw [← Rat.intCast_natCast, Int.toNat_of_nonneg hy0]
  have hYlt : y.toNat < 2 ^ (y.toNat.log2 + 1) := Nat.lt_log2_self
  have hYge : y.toNat ≠ 0 → 2 ^ y.toNat.log2 ≤ y.toNat := Nat.log2_self_le
  have hL0 : y.toNat = 0 → y.toNat.log2 = 0 := fun h => by rw [h]; exact Nat.log2_zero
  generalize y.toNat = Y at *
  generalize Y.log2 = L at *
  have hsplit : ∀ j : Int, (2 : Rat) ^ (j + 1074) = 2 ^ j * 2 ^ 1074 := fun j => by
    rw [Rat.zpow_add (by decide)]; rfl
  refine ⟨by omega, ?_, ?_⟩
  · -- `x · 2^1074 < Y + 1 ≤ 2^(L+1) ≤ 2^(k+53) · 2^1074`
    have h1 : ((Y : Nat) : Rat) + 1 ≤ ((2 ^ (L + 1) : Nat) : Rat) := by exact_mod_cast hYlt
    have h2 : ((2 ^ (L + 1) : Nat) : Rat) ≤ (2 : Rat) ^ (max ((L : Int) - 1074 - 52) (-1074) + 53 + 1074) := by
      rw [← two_zpow_natCast]
      exact zpow_le_zpow_right₀ (by decide) (by push_cast; omega)
    rw [hsplit] at h2
    exact Rat.lt_of_mul_lt_mul_right (by grind) (Rat.le_of_lt hP)
  · by_cases hk : max ((L : Int) - 1074 - 52) (-1074) = -1074
    · exact Or.inl hk
    · right
      have hY : Y ≠ 0 := fun h0 => hk (by have := hL0 h0; omega)
      have h1 : ((2 ^ L : Nat) : Rat) ≤ ((Y : Nat) : Rat) := by exact_mod_cast hYge hY
      have h2 : (2 : Rat) ^ (max ((L : Int) - 1074 - 52) (-1074) + 52 + 1074) = ((2 ^ L : Nat) : Rat) := by
        rw [← two_zpow_natCast, show max ((L : Int) - 1074 - 52) (-1074) + 52 + 1074 = (L : Int) by omega]
      rw [hsplit] at h2
      exact Rat.le_of_mul_le_mul_right (by grind) hP

end Srtfp.Reader

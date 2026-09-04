module
/- Finite binary64 words as `(m, q)` pairs: which pairs occur (`Legal`),
   injectivity of the value `m · 2^q`, and the gap around a value: no
   legal value lies strictly between `m · 2^q` and its two neighbours. -/
public import Srtfp.Proofs.Bits
public import Srtfp.Proofs.Printer.Interval

@[expose] public section

open Srtfp.Compat

namespace Srtfp.Float

open Srtfp.Printer

/-- The `(m, q)` pairs finite words decode to: `m < 2^53`, `-1074 ≤ q ≤ 971`,
and only the subnormal exponent admits `m < 2^52`. -/
def Legal (m : Nat) (q : Int) : Prop :=
  m < 2 ^ 53 ∧ -1074 ≤ q ∧ q ≤ 971 ∧ (q ≠ -1074 → 2 ^ 52 ≤ m)

theorem decode_legal {w : UInt64} (hw : Word.isFinite w = true) :
    Legal (Word.decode w).m (Word.decode w).q := by
  have hb := word_biasedExp_lt w
  have hm := word_mantissa_lt w
  unfold Word.isFinite at hw; simp only [decide_eq_true_eq] at hw
  unfold Legal Word.decode
  by_cases he : Word.biasedExp w = 0 <;> simp only [he, if_true, if_false, Nat.shiftLeft_eq] <;> omega

theorem legal_zero : Legal 0 (-1074) := by unfold Legal; omega

/-! ## Values -/

variable {m m' : Nat} {q q' : Int}

theorem v_nonneg : 0 ≤ v m q :=
  Rat.mul_nonneg (by exact_mod_cast Nat.zero_le m) (le_of_lt (two_zpow_pos q))

theorem v_zero_iff : v m q = 0 ↔ m = 0 := by
  unfold v
  have := two_zpow_pos q
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos m with hm | hm
    · exact hm
    · exfalso
      have : (0 : ℚ) < m := by exact_mod_cast hm
      have := Rat.mul_pos this (two_zpow_pos q)
      grind
  · intro h; subst h; simp

/-- `m · 2^q` on the grid `2^q₀`, for `q₀ ≤ q`. -/
theorem v_eq_mul (h : q' ≤ q) :
    v m q = ((m * 2 ^ (q - q').toNat : Nat) : ℚ) * (2 : ℚ) ^ q' := by
  unfold v
  push_cast
  rw [← two_zpow_toNat (by omega), Rat.mul_assoc, ← Rat.zpow_add (by decide),
    Int.sub_add_cancel]

/-- Legal pairs are determined by their value. -/
theorem v_inj (h : Legal m q) (h' : Legal m' q') (hv : v m q = v m' q') : m = m' ∧ q = q' := by
  -- with `q < q'`, `m = m' · 2^(q'-q) ≥ 2 · 2^52`
  have key : ∀ {a a' : Nat} {b b' : Int}, Legal a b → Legal a' b' → v a b = v a' b' → ¬ b < b' := by
    intro a a' b b' ha ha' hv hlt
    have hb0 := ha.2.1
    have hm' : 2 ^ 52 ≤ a' := ha'.2.2.2 (by omega)
    rw [v_eq_mul (Int.le_of_lt hlt)] at hv
    unfold v at hv
    have hp := two_zpow_pos b
    have h1 : (a : ℚ) = ((a' * 2 ^ (b' - b).toNat : Nat) : ℚ) := (mul_left_inj' (by grind)).mp hv
    have h2 : a = a' * 2 ^ (b' - b).toNat := by exact_mod_cast h1
    have h3 : 2 ≤ 2 ^ (b' - b).toNat := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ (b' - b).toNat := Nat.pow_le_pow_right (by decide) (by omega)
    have := ha.1
    have : a' * 2 ≤ a' * 2 ^ (b' - b).toNat := Nat.mul_le_mul_left _ h3
    omega
  have hq : q = q' := by
    rcases Int.lt_trichotomy q q' with hlt | heq | hgt
    · exact absurd hlt (key h h' hv)
    · exact heq
    · exact absurd hgt (key h' h hv.symm)
  subst hq
  refine ⟨?_, rfl⟩
  unfold v at hv
  have hp := two_zpow_pos q
  exact_mod_cast (mul_left_inj' (by grind)).mp hv

/-! ## The gap around a value -/

/-- The distance from `m · 2^q` down to the previous legal value: `2^q`,
or `2^(q-1)` at the bottom of a binade. -/
def gapL (m : Nat) (q : Int) : ℚ :=
  if m = 2 ^ 52 ∧ q > -1074 then (2 : ℚ) ^ (q - 1) else (2 : ℚ) ^ q

theorem gapL_pos : 0 < gapL m q := by
  unfold gapL; split <;> exact two_zpow_pos _

theorem gapL_le : gapL m q ≤ (2 : ℚ) ^ q := by
  unfold gapL; split
  · exact zpow_le_zpow_right₀ (by decide) (by omega)
  · exact le_refl _

theorem vl_eq : vl m q = v m q - gapL m q / 2 := by
  unfold vl v gapL
  have h2 : (2 : ℚ) ^ q = 2 ^ (q - 1) * 2 := by
    rw [← Rat.zpow_add_one (by decide), Int.sub_add_cancel]
  split <;> grind

theorem vr_eq : vr m q = v m q + (2 : ℚ) ^ q / 2 := by
  unfold vr v; grind

/-- No legal value lies strictly between `m · 2^q` and its neighbours. -/
theorem gap (h : Legal m q) (h' : Legal m' q') (hne : v m' q' ≠ v m q) :
    v m' q' ≤ v m q - gapL m q ∨ v m q + (2 : ℚ) ^ q ≤ v m' q' := by
  have hp := two_zpow_pos q
  have hgl := gapL_le (m := m) (q := q)
  rcases Int.lt_or_le q' q with hlt | hle
  · -- `q' < q`: every such value is below the binade of `m · 2^q`
    left
    have hq0 := h'.2.1
    have hm : 2 ^ 52 ≤ m := h.2.2.2 (by omega)
    have hm53 := h'.1
    have hp1 := two_zpow_pos (q - 1)
    have h2 : (2 : ℚ) ^ q = 2 ^ (q - 1) * 2 := by
      rw [← Rat.zpow_add_one (by decide), Int.sub_add_cancel]
    have hq' : (2 : ℚ) ^ q' ≤ (2 : ℚ) ^ (q - 1) := zpow_le_zpow_right₀ (by decide) (by omega)
    have hm' : (m' : ℚ) + 1 ≤ 2 ^ 53 := by exact_mod_cast hm53
    have hv' : (m' : ℚ) * (2 : ℚ) ^ q' ≤ (2 ^ 53 - 1) * (2 : ℚ) ^ (q - 1) :=
      calc (m' : ℚ) * (2 : ℚ) ^ q' ≤ m' * (2 : ℚ) ^ (q - 1) :=
            Rat.mul_le_mul_of_nonneg_left hq' (by exact_mod_cast Nat.zero_le m')
        _ ≤ (2 ^ 53 - 1) * (2 : ℚ) ^ (q - 1) :=
            Rat.mul_le_mul_of_nonneg_right (by grind) (le_of_lt hp1)
    unfold gapL v
    by_cases hirr : m = 2 ^ 52 ∧ q > -1074
    · rw [if_pos hirr, hirr.1]; push_cast
      generalize (2 : ℚ) ^ (q - 1) = P1 at *
      generalize (2 : ℚ) ^ q = P at *
      grind
    · rw [if_neg hirr]
      have hm1 : 2 ^ 52 + 1 ≤ m := by
        rcases Nat.eq_or_lt_of_le hm with heq | hlt'
        · exact absurd ⟨heq.symm, by omega⟩ hirr
        · omega
      have hmq : (2 ^ 52 + 1 : ℚ) ≤ m := by exact_mod_cast hm1
      have := Rat.mul_le_mul_of_nonneg_right hmq (le_of_lt hp)
      generalize (2 : ℚ) ^ (q - 1) = P1 at *
      generalize (2 : ℚ) ^ q = P at *
      grind
  · -- `q ≤ q'`: the value is on the grid `2^q`, at some `n ≠ m`
    rw [v_eq_mul hle] at hne ⊢
    generalize m' * 2 ^ (q' - q).toNat = n at hne ⊢
    unfold v at hne ⊢
    have hnm : n ≠ m := fun h => hne (by rw [h])
    rcases Nat.lt_or_gt_of_ne hnm with hlt | hgt
    · left
      have : (n : ℚ) + 1 ≤ m := by exact_mod_cast hlt
      have := Rat.mul_le_mul_of_nonneg_right this (le_of_lt hp)
      grind
    · right
      have : (m : ℚ) + 1 ≤ n := by exact_mod_cast hgt
      have := Rat.mul_le_mul_of_nonneg_right this (le_of_lt hp)
      grind

end Srtfp.Float

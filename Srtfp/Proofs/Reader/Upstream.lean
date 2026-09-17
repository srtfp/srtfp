module
/- Lean's decimal conversion agrees with the arithmetic reference reader,
   including its exponent shortcuts and both signs of zero. -/

public import Srtfp.Proofs.Reader.UpstreamMagnitude

@[expose] public section

open Srtfp.Compat
open Float.Model (UnpackedFloat)
open Float.Model.UnpackedFloat

namespace Srtfp.Reader.Upstream

theorem quotient_exponent_le_grid {m d : Nat} (hm : 0 < m) (hd : 0 < d) :
    min 0 (Float.Model.Format.binary64.targetExponent
      (Float.Model.totalExponent m 0 - Float.Model.totalExponent d 0)) ≤
        gridExp ((m : Rat) / d) := by
  have hdR : (0 : Rat) < d := by exact_mod_cast hd
  apply exponent_le_grid (div_nonneg Rat.natCast_nonneg hdR)
  let e := min 0 (Float.Model.Format.binary64.targetExponent
    (Float.Model.totalExponent m 0 - Float.Model.totalExponent d 0))
  by_cases he : e ≤ -1074
  · exact Or.inl he
  · right
    have heq : e = min 0 (max ((m.log2 : Int) - (d.log2 : Int) - 53) (-1074)) := by
      change min 0 (max (((m.log2 : Int) + 1 + 0 - ((d.log2 : Int) + 1 + 0)) - 53) (-1074)) = _
      congr 2 <;> omega
    have hprec : e + 52 ≤ (m.log2 : Int) - (d.log2 : Int) - 1 := by
      rw [heq] at he ⊢
      omega
    have hmlo : (2 : Rat) ^ (m.log2 : Int) ≤ (m : Rat) := by
      rw [two_zpow_natCast]
      exact_mod_cast Nat.log2_self_le (Nat.ne_of_gt hm)
    have hdhi : (d : Rat) < (2 : Rat) ^ ((d.log2 : Int) + 1) := by
      rw [show (d.log2 : Int) + 1 = ((d.log2 + 1 : Nat) : Int) by omega, two_zpow_natCast]
      exact_mod_cast Nat.lt_log2_self (n := d)
    have hmul : (2 : Rat) ^ ((m.log2 : Int) - (d.log2 : Int) - 1) * 2 ^ ((d.log2 : Int) + 1)
        = (2 : Rat) ^ (m.log2 : Int) := by
      rw [← Rat.zpow_add (by decide)]
      congr 1
      omega
    have hlo : (2 : Rat) ^ ((m.log2 : Int) - (d.log2 : Int) - 1) < (m : Rat) / d := by
      rw [Rat.lt_div_iff hdR]
      have h := Rat.mul_lt_mul_of_pos_left hdhi (two_zpow_pos ((m.log2 : Int) - (d.log2 : Int) - 1))
      rw [hmul] at h
      exact lt_of_lt_of_le h hmlo
    exact Rat.le_trans (zpow_le_zpow_right₀ (by decide) hprec) (Rat.le_of_lt hlo)

theorem div_correct {m d : Nat} (hm : 0 < m) (hd : 0 < d) :
    Float.Model.pack (UnpackedFloat.div .binary64 (.finite .positive m 0 hm) (.finite .positive d 0 hd)) =
      Float.Model.pack (readMag .positive ((m : Rat) / d)) := by
  let e := min 0 (Float.Model.Format.binary64.targetExponent
    (Float.Model.totalExponent m 0 - Float.Model.totalExponent d 0))
  let M := m <<< (-e).toNat
  have he : e ≤ 0 := by dsimp [e]; omega
  have hprod : (M : Rat) * (2 : Rat) ^ e = m := by
    dsimp [M]
    rw [Nat.shiftLeft_eq, Rat.natCast_mul, ← two_zpow_toNat (by omega : 0 ≤ -e),
      Rat.mul_assoc, ← Rat.zpow_add (by decide), show -e + e = 0 by omega, Rat.zpow_zero, Rat.mul_one]
  have hvalue : (M : Rat) / d * (2 : Rat) ^ e = (m : Rat) / d := by
    rw [Rat.div_def, Rat.div_def]
    calc
      (M : Rat) * (d : Rat)⁻¹ * 2 ^ e = ((M : Rat) * 2 ^ e) * (d : Rat)⁻¹ := by grind
      _ = _ := by rw [hprod]
  have hprec : e ≤ gridExp ((M : Rat) / d * 2 ^ e) := by
    rw [hvalue]
    exact quotient_exponent_le_grid hm hd
  simp only [UnpackedFloat.div, divCore, Int.sub_self, Int.zero_sub]
  change Float.Model.pack (roundWithAccuracy .binary64 .positive (M / d) e
    (accuracyOfFraction (M % d) d)) = _
  rw [roundWithAccuracy_correct .positive (quotient_represents M d hd) hprec, hvalue]

theorem mul_scientific_correct {m : Nat} {e : Int} (hm : 0 < m) (he : 0 ≤ e) :
    Float.Model.pack (UnpackedFloat.mul .binary64
      (.finite .positive (m <<< 53) (-53) (by simpa [Nat.shiftLeft_eq] using Nat.mul_pos hm (Nat.two_pow_pos 53)))
      (.finite .positive (10 ^ e.toNat) 0 (Nat.pow_pos (by decide)))) =
        Float.Model.pack (readMag .positive ((m : Rat) * (10 : Rat) ^ e)) := by
  let M := (m <<< 53) * 10 ^ e.toNat
  have hM : (M : Rat) = ((m : Rat) * (10 : Rat) ^ e) * (2 : Rat) ^ (53 : Int) := by
    dsimp [M]
    rw [Nat.shiftLeft_eq, Rat.natCast_mul, Rat.natCast_mul, ← ten_zpow_toNat he, ← two_zpow_natCast]
    grind
  have hvalue : (M : Rat) * (2 : Rat) ^ (-53 : Int) = (m : Rat) * (10 : Rat) ^ e := by
    rw [hM, Rat.mul_assoc, ← Rat.zpow_add (by decide)]
    simp only [show (53 : Int) + -53 = 0 from rfl, Rat.zpow_zero, Rat.mul_one]
  have hge : (1 : Rat) ≤ (m : Rat) * (10 : Rat) ^ e := by
    have hmR : (1 : Rat) ≤ m := by exact_mod_cast hm
    have hpow : (1 : Rat) ≤ (10 : Rat) ^ e := by
      have := zpow_le_zpow_right₀ (a := (10 : Rat)) (by decide) he
      simpa only [Rat.zpow_zero] using this
    have := Rat.mul_le_mul_of_nonneg_right hmR (Rat.le_of_lt (ten_zpow_pos e))
    grind
  have hprec : (-53 : Int) ≤ gridExp ((M : Rat) * 2 ^ (-53 : Int)) := by
    rw [hvalue]
    apply exponent_le_grid (Rat.le_trans (by decide) hge)
    exact Or.inr (Rat.le_trans (by decide +kernel) hge)
  change Float.Model.pack (roundWithAccuracy .binary64 .positive M (-53) .exact) = _
  rw [roundWithAccuracy_correct .positive (show Represents M .exact (M : Rat) from rfl) hprec, hvalue]

theorem ofScientific_eq_readMag (m : Nat) (e : Int) :
    Float.Model.ofScientific m e = Float.Model.pack (readMag .positive ((m : Rat) * (10 : Rat) ^ e)) := by
  unfold Float.Model.ofScientific UnpackedFloat.ofScientific
  split
  · rename_i hm
    subst m
    simp only [Rat.natCast_ofNat, Rat.zero_mul, readMag_zero]
  · rename_i hm
    split
    · rename_i he
      rw [readMag_infinity _ (overflow_of_big hm (by change 2048 < e at he; omega))]
    · split
      · rename_i he
        rw [readMag_small _ (Rat.mul_nonneg Rat.natCast_nonneg (Rat.le_of_lt (ten_zpow_pos e)))
          (tiny_decimal he)]
      · split
        · rename_i he
          exact mul_scientific_correct (Nat.pos_of_ne_zero hm) he
        · rename_i he
          rw [div_correct (Nat.pos_of_ne_zero hm) (Nat.pow_pos (by decide))]
          rw [← ten_zpow_toNat (by omega : 0 ≤ -e), Rat.div_def, ← Rat.zpow_neg, Int.neg_neg]

theorem readMag_neg (s : Sign) (x : Rat) : readMag (-s) x = (readMag s x).neg := by
  unfold readMag
  split
  · rfl
  · unfold ofSig
    split
    · rfl
    · split <;> rfl

theorem toModel_eq_read (d : Decimal) :
    d.toModel = Float.Model.pack (read d) := by
  cases d with
  | mk s m e =>
    cases s with
    | positive =>
      rw [read_eq_readMag, abs_toRat]
      exact ofScientific_eq_readMag m e
    | negative =>
      have hu : (Float.Model.pack (readMag .positive ((m : Rat) * (10 : Rat) ^ e))).unpack =
          readMag .positive ((m : Rat) * (10 : Rat) ^ e) := by
        have h := unpack_referenceBits ⟨.positive, m, e⟩
        change (Float.Model.pack (read ⟨.positive, m, e⟩)).unpack = read ⟨.positive, m, e⟩ at h
        simpa only [read_eq_readMag, abs_toRat] using h
      change -(Float.Model.ofScientific m e) = _
      rw [ofScientific_eq_readMag]
      change Float.Model.pack ((Float.Model.pack (readMag .positive ((m : Rat) * (10 : Rat) ^ e))).unpack.neg) = _
      rw [hu, read_eq_readMag, abs_toRat]
      exact congrArg Float.Model.pack (readMag_neg .positive _).symm

end Srtfp.Reader.Upstream

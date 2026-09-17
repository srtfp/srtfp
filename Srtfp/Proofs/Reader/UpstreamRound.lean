module
/- The residual bits in Lean's float model represent an exact rational
   interval. Shifting preserves that interval, and rounding chooses the
   same nearest integer as the reference reader. -/

public import Srtfp.Proofs.Reader.Characterize

@[expose] public section

open Srtfp.Compat
open Float.Model (UnpackedFloat)
open Float.Model.UnpackedFloat

namespace Srtfp.Reader.Upstream

/-- The exact magnitude represented by a truncated mantissa and accuracy. -/
def Represents (m : Nat) (a : Accuracy) (x : Rat) : Prop :=
  match a with
  | .exact => x = m
  | .inexact .lt => m < x ∧ x < m + 1/2
  | .inexact .eq => x = m + 1/2
  | .inexact .gt => m + 1/2 < x ∧ x < m + 1

theorem represents_bounds {m : Nat} {a : Accuracy} {x : Rat} (h : Represents m a x) :
    (m : Rat) ≤ x ∧ x < m + 1 := by
  cases a with
  | exact => simp only [Represents] at h; grind
  | inexact o => cases o <;> simp only [Represents] at h <;> grind

theorem ofMantissaAndAccuracy_represents {m : Nat} {a : Accuracy} {x : Rat}
    (h : Represents m a x) :
    Represents (ExtendedMantissa.ofMantissaAndAccuracy m a).mantissa
      (ExtendedMantissa.ofMantissaAndAccuracy m a).accuracy x := by
  cases a with
  | exact => exact h
  | inexact o => cases o <;> exact h

theorem shiftRightOne_represents {em : ExtendedMantissa} {x : Rat}
    (h : Represents em.mantissa em.accuracy x) :
    Represents em.shiftRightOne.mantissa em.shiftRightOne.accuracy (x / 2) := by
  obtain ⟨m, r, s⟩ := em
  have hdiv : (m : Rat) = (m / 2 : Nat) * 2 + (m % 2 : Nat) := by
    exact_mod_cast (Nat.div_add_mod m 2).symm.trans (by omega)
  rcases Nat.mod_two_eq_zero_or_one m with hm | hm <;>
    cases r <;> cases s <;>
    simp [ExtendedMantissa.shiftRightOne, ExtendedMantissa.accuracy, Represents, hm] at h ⊢ <;>
    rw [hm] at hdiv <;> push_cast at hdiv <;> grind

theorem roundedMantissa_eq {em : ExtendedMantissa} {x : Rat}
    (h : Represents em.mantissa em.accuracy x) :
    roundEven x = (em.roundedMantissa : Int) := by
  obtain ⟨m, r, s⟩ := em
  cases r <;> cases s <;>
    simp only [ExtendedMantissa.roundedMantissa, ExtendedMantissa.accuracy,
      Accuracy.roundToNearestEven, Represents] at h ⊢
  · exact roundEven_eq_natCast_of (by grind) (by grind) (fun h' => by grind) (fun h' => by grind)
  · exact roundEven_eq_of_strict (by grind) h.2
  · rw [h]; exact roundEven_tie m
  · apply roundEven_eq_of_strict <;> push_cast <;> grind

theorem shiftRight_represents {em : ExtendedMantissa} {x : Rat}
    (h : Represents em.mantissa em.accuracy x) (n : Nat) :
    Represents (em >>> n).mantissa (em >>> n).accuracy (x / (2 : Rat) ^ n) := by
  induction n with
  | zero =>
    change Represents em.mantissa em.accuracy (x / 1)
    simpa only [Rat.div_def, Rat.inv_eq_of_mul_eq_one (Rat.mul_one 1), Rat.mul_one] using h
  | succ n ih =>
    change Represents (em >>> n).shiftRightOne.mantissa (em >>> n).shiftRightOne.accuracy _
    have hs := shiftRightOne_represents ih
    simpa only [Rat.pow_succ, div_div] using hs

theorem shiftToTarget_small {n : Nat} {k : Int} (hn : n < 2 ^ 53) (hk : -1074 ≤ k) :
    shiftToTargetExponent .binary64 n k .exact =
      (ExtendedMantissa.ofMantissaAndAccuracy n .exact, k) := by
  have hl : n.log2 ≤ 52 := by
    by_cases hz : n = 0
    · simp [hz]
    · have := (Nat.log2_lt hz).mpr hn; omega
  have ht : Float.Model.Format.binary64.targetExponent (Float.Model.totalExponent n k) ≤ k := by
    change max ((n.log2 : Int) + 1 + k - 53) (-1074) ≤ k
    omega
  have hz : (Float.Model.Format.binary64.targetExponent (Float.Model.totalExponent n k) - k).toNat = 0 := by
    omega
  change (ExtendedMantissa.ofMantissaAndAccuracy n .exact >>> _, k + _) = _
  rw [hz]
  simp only [Int.natCast_zero, Int.add_zero]
  rfl

theorem shiftToTarget_carry {k : Int} (hk : -1074 ≤ k) :
    shiftToTargetExponent .binary64 (2 ^ 53) k .exact =
      (ExtendedMantissa.ofMantissaAndAccuracy (2 ^ 52) .exact, k + 1) := by
  have ht : Float.Model.Format.binary64.targetExponent (Float.Model.totalExponent (2 ^ 53) k) = k + 1 := by
    change max (53 + 1 + k - 53) (-1074) = k + 1
    omega
  change (ExtendedMantissa.ofMantissaAndAccuracy (2 ^ 53) .exact >>> _, k + _) = _
  rw [ht, show (k + 1 - k).toNat = 1 by omega]
  rfl

theorem finish_eq_ofSig (s : Sign) {n : Nat} {k : Int} (hn : n ≤ 2 ^ 53) (hk : -1074 ≤ k) :
    (let (em, e) := shiftToTargetExponent .binary64 n k .exact
     if h : em.mantissa = 0 then UnpackedFloat.zero s
     else .finite s em.mantissa e (Nat.pos_of_ne_zero h)) = ofSig s n k := by
  by_cases hc : n = 2 ^ 53
  · subst n
    rw [shiftToTarget_carry hk]
    rfl
  · rw [shiftToTarget_small (by omega) hk]
    dsimp only [ExtendedMantissa.ofMantissaAndAccuracy]
    unfold ofSig
    split
    · rfl
    · rfl

theorem scaled_grid_lt {x : Rat} (hx : 0 ≤ x) :
    x / 2 ^ gridExp x < ((2 ^ 53 : Nat) : Rat) := by
  have hp : (2 : Rat) ^ (gridExp x + 53) = ((2 ^ 53 : Nat) : Rat) * 2 ^ gridExp x := by
    rw [Rat.zpow_add (by decide), Rat.mul_comm, ← two_zpow_natCast]
    rfl
  rw [Rat.div_lt_iff (two_zpow_pos _), ← hp]
  exact (gridExp_spec hx).2.1

theorem targetExponent_eq_grid {m : Nat} {a : Accuracy} {x : Rat} {e : Int}
    (h : Represents m a x) (he : e ≤ gridExp (x * 2 ^ e)) :
    Float.Model.Format.binary64.targetExponent (Float.Model.totalExponent m e) =
      gridExp (x * 2 ^ e) := by
  obtain ⟨hlo, hhi⟩ := represents_bounds h
  have hx : 0 ≤ x := Rat.le_trans Rat.natCast_nonneg hlo
  have hp := two_zpow_pos e
  have hmag := Rat.mul_nonneg hx (Rat.le_of_lt hp)
  change max ((m.log2 : Int) + 1 + e - 53) (-1074) = _
  by_cases hm : m = 0
  · subst m
    have hu : x * 2 ^ e < (2 : Rat) ^ e := by
      have := Rat.mul_lt_mul_of_pos_right hhi hp
      push_cast at this
      grind
    rcases (gridExp_spec hmag).2.2 with hg | hg
    · rw [hg] at he ⊢
      change max (0 + 1 + e - 53) (-1074) = -1074
      omega
    · have hl := zpow_le_zpow_right₀ (a := (2 : Rat)) (by decide)
        (show e ≤ gridExp (x * 2 ^ e) + 52 by omega)
      grind
  · have hloglo : (2 : Rat) ^ (m.log2 : Int) ≤ x := by
      rw [two_zpow_natCast]
      exact Rat.le_trans (by exact_mod_cast Nat.log2_self_le hm) hlo
    have hloghi : x < (2 : Rat) ^ ((m.log2 : Int) + 1) := by
      rw [show (m.log2 : Int) + 1 = ((m.log2 + 1 : Nat) : Int) by omega, two_zpow_natCast]
      exact lt_of_lt_of_le hhi (by exact_mod_cast Nat.lt_log2_self (n := m))
    symm
    apply gridExp_eq_of hmag (by omega)
    · have hu := Rat.mul_lt_mul_of_pos_right hloghi hp
      rw [← Rat.zpow_add (by decide)] at hu
      exact lt_of_lt_of_le hu (zpow_le_zpow_right₀ (by decide) (by omega))
    · by_cases hk : max ((m.log2 : Int) + 1 + e - 53) (-1074) = -1074
      · exact Or.inl hk
      · right
        rw [show max ((m.log2 : Int) + 1 + e - 53) (-1074) + 52 = (m.log2 : Int) + e by omega,
          Rat.zpow_add (by decide)]
        exact Rat.mul_le_mul_of_nonneg_right hloglo (Rat.le_of_lt hp)

theorem roundWithAccuracy_eq (s : Sign) {m : Nat} {a : Accuracy} {x : Rat} {e : Int}
    (h : Represents m a x) (he : e ≤ gridExp (x * 2 ^ e)) :
    roundWithAccuracy .binary64 s m e a =
      ofSig s (roundEven (x * 2 ^ e / 2 ^ gridExp (x * 2 ^ e))).toNat (gridExp (x * 2 ^ e)) := by
  let k := gridExp (x * 2 ^ e)
  let em := ExtendedMantissa.ofMantissaAndAccuracy m a >>> (k - e).toNat
  have ht := targetExponent_eq_grid h he
  have hshift : shiftToTargetExponent .binary64 m e a = (em, k) := by
    unfold shiftToTargetExponent
    rw [ht]
    change (em, e + (k - e).toNat) = (em, k)
    congr 1
    omega
  have hscale : x * 2 ^ e / (2 : Rat) ^ k = x / (2 : Rat) ^ (k - e).toNat := by
    have hk : k = e + ((k - e).toNat : Int) := by omega
    conv => lhs; rw [hk, Rat.zpow_add (by decide), Rat.zpow_natCast]
    rw [div_div, Rat.mul_div_cancel (Rat.ne_of_gt (two_zpow_pos e))]
  have hem : Represents em.mantissa em.accuracy (x * 2 ^ e / 2 ^ k) := by
    rw [hscale]
    exact shiftRight_represents (ofMantissaAndAccuracy_represents h) _
  have hr : em.roundedMantissa = (roundEven (x * 2 ^ e / 2 ^ k)).toNat := by
    rw [roundedMantissa_eq hem, Int.toNat_natCast]
  have hx : 0 ≤ x := Rat.le_trans Rat.natCast_nonneg (represents_bounds h).1
  have hmag := Rat.mul_nonneg hx (Rat.le_of_lt (two_zpow_pos e))
  have hu' := scaled_grid_lt hmag
  have hn : (roundEven (x * 2 ^ e / 2 ^ k)).toNat ≤ 2 ^ 53 := by
    have hle : roundEven (x * 2 ^ e / 2 ^ k) ≤ ((2 ^ 53 : Nat) : Int) := roundEven_le hu'
    omega
  unfold roundWithAccuracy
  rw [hshift]
  dsimp only
  rw [hr]
  exact finish_eq_ofSig s hn (gridExp_spec hmag).1

theorem quotient_represents (m d : Nat) (hd : 0 < d) :
    Represents (m / d) (accuracyOfFraction (m % d) d) ((m : Rat) / d) := by
  have hdR : (0 : Rat) < d := by exact_mod_cast hd
  have hrem : (m % d : Rat) < d := by exact_mod_cast Nat.mod_lt m hd
  have hdiv : (m % d : Rat) / d * d = (m % d : Rat) :=
    Rat.div_mul_cancel (Rat.ne_of_gt hdR)
  have heq : (m : Rat) / d = (m / d : Nat) + (m % d : Nat) / (d : Rat) := by
    have := frac_natDiv m d hd
    grind
  unfold accuracyOfFraction
  split
  · rename_i hz
    simp only [Represents]
    rw [heq, hz]
    push_cast
    grind
  · rename_i hz
    have hpos : (0 : Rat) < (m % d : Nat) := by exact_mod_cast Nat.pos_of_ne_zero hz
    cases hc : compare (2 * (m % d)) d with
    | lt =>
      have hcR : (2 : Rat) * (m % d : Nat) < d := by exact_mod_cast Nat.compare_eq_lt.mp hc
      have hl := div_pos hpos hdR
      have hu : (m % d : Nat) / (d : Rat) < 1/2 := (Rat.div_lt_iff hdR).mpr (by grind)
      simp only [Represents]
      grind
    | eq =>
      have hcR : (2 : Rat) * (m % d : Nat) = d := by exact_mod_cast Nat.compare_eq_eq.mp hc
      simp only [Represents]
      grind
    | gt =>
      have hcR : (d : Rat) < 2 * (m % d : Nat) := by exact_mod_cast Nat.compare_eq_gt.mp hc
      have hl : (1/2 : Rat) < (m % d : Nat) / (d : Rat) := (Rat.lt_div_iff hdR).mpr (by grind)
      have hu : (m % d : Nat) / (d : Rat) < 1 := (Rat.div_lt_iff hdR).mpr (by grind)
      simp only [Represents]
      grind

end Srtfp.Reader.Upstream

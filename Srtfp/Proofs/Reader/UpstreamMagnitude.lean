module
/- Packing the upstream rounded significand handles the same overflow and
   underflow as the reference reader. These numerical bounds are proof
   details, not part of the public specification. -/

public import Srtfp.Proofs.Reader.UpstreamRound

@[expose] public section

open Srtfp.Compat
open Float.Model (UnpackedFloat)
open Float.Model.UnpackedFloat

namespace Srtfp.Reader.Upstream

theorem pack_overflow (s : Sign) {m : Nat} {e : Int} (hm : 0 < m) (he : 972 ≤ e) :
    Float.Model.pack (.finite s m e hm) = Float.Model.pack (.infinity s) := by
  apply Srtfp.Model.model_ext
  have ht : 2 ^ Float.Model.Format.binary64.exponentBits ≤
      (e + Float.Model.Format.binary64.exponentBias +
        Float.Model.Format.binary64.mantissaBitsWithoutImplicit).toNat + 1 := by
    change 2048 ≤ (e + 1023 + 52).toNat + 1
    omega
  simp only [Float.Model.pack, UnpackedFloat.pack]
  rw [if_pos ht]

theorem pack_ofSig_eq_readMag (s : Sign) {x : Rat} (hx : 0 ≤ x) :
    Float.Model.pack (ofSig s (roundEven (x / 2 ^ gridExp x)).toNat (gridExp x)) =
      Float.Model.pack (readMag s x) := by
  have hg := gridExp_spec hx
  have hy := scaled_grid_lt hx
  unfold readMag
  split
  · rename_i ht
    have hcut : (2 : Rat) ^ (1023 : Int) < (2 : Rat) ^ 1024 - 2 ^ 970 := by decide +kernel
    have hk : 971 ≤ gridExp x := by
      have := lt_of_zpow_lt (a := (2 : Rat)) (by decide)
        (lt_of_lt_of_le (lt_of_lt_of_le hcut ht) (Rat.le_of_lt hg.2.1))
      omega
    rcases eq_or_lt_of_le hk with hk | hk
    · have hk' : gridExp x = 971 := hk.symm
      rw [hk'] at hy ⊢
      have hr : roundEven (x / (2 : Rat) ^ (971 : Int)) = ((2 ^ 53 : Nat) : Int) := by
        apply roundEven_eq_natCast_of
        · rw [le_div_iff (two_zpow_pos _)]
          rw [Rat.natCast_pow, Rat.natCast_ofNat, ← threshold_eq]
          exact ht
        · grind
        · intro _; decide
        · intro _; decide
      rw [hr, Int.toNat_natCast]
      change Float.Model.pack (.finite s (2 ^ 52) 972 _) = _
      exact pack_overflow s _ (by decide)
    · have hlo : ((2 ^ 52 : Nat) : Rat) ≤ x / 2 ^ gridExp x := by
        have hp : (2 : Rat) ^ (gridExp x + 52) = ((2 ^ 52 : Nat) : Rat) * 2 ^ gridExp x := by
          rw [Rat.zpow_add (by decide), Rat.mul_comm, ← two_zpow_natCast]
          rfl
        rw [le_div_iff (two_zpow_pos _), ← hp]
        exact hg.2.2.resolve_left (by omega)
      have hn : 0 < (roundEven (x / 2 ^ gridExp x)).toNat := by
        have := roundEven_ge hlo
        omega
      unfold ofSig
      rw [dif_neg (Nat.ne_of_gt hn)]
      split <;> exact pack_overflow s _ (by omega)
  · rfl

theorem readMag_small (s : Sign) {x : Rat} (hx : 0 ≤ x)
    (hsmall : x < (2 : Rat) ^ (-1075 : Int)) : readMag s x = .zero s := by
  have hgrid : gridExp x = -1074 := gridExp_eq_of hx (by decide)
    (lt_of_lt_of_le hsmall (zpow_le_zpow_right₀ (by decide) (by decide))) (Or.inl rfl)
  have ht : ¬ ((2 : Rat) ^ 1024 - 2 ^ 970 ≤ x) := Rat.not_le.mpr
    (lt_of_lt_of_le hsmall (by decide +kernel))
  have hy : x / (2 : Rat) ^ (-1074 : Int) < 1/2 := by
    rw [Rat.div_lt_iff (two_zpow_pos _)]
    have hp : (1/2 : Rat) * 2 ^ (-1074 : Int) = 2 ^ (-1075 : Int) := by decide +kernel
    rwa [hp]
  have hy0 := div_nonneg hx (two_zpow_pos (-1074))
  have hr : roundEven (x / (2 : Rat) ^ (-1074 : Int)) = (0 : Nat) :=
    roundEven_eq_of_strict (by simp only [Rat.natCast_ofNat]; grind)
      (by simpa only [Rat.natCast_ofNat, Rat.zero_add] using hy)
  unfold readMag
  rw [if_neg ht, hgrid, hr]
  rfl

theorem exponent_le_grid {x : Rat} {e : Int} (hx : 0 ≤ x)
    (he : e ≤ -1074 ∨ (2 : Rat) ^ (e + 52) ≤ x) : e ≤ gridExp x := by
  have hg := gridExp_spec hx
  rcases he with he | he
  · omega
  · have := lt_of_zpow_lt (a := (2 : Rat)) (by decide) (lt_of_le_of_lt he hg.2.1)
    omega

theorem roundWithAccuracy_correct (s : Sign) {m : Nat} {a : Accuracy} {x : Rat} {e : Int}
    (h : Represents m a x) (he : e ≤ gridExp (x * 2 ^ e)) :
    Float.Model.pack (roundWithAccuracy .binary64 s m e a) =
      Float.Model.pack (readMag s (x * 2 ^ e)) := by
  rw [roundWithAccuracy_eq s h he]
  apply pack_ofSig_eq_readMag
  exact Rat.mul_nonneg (Rat.le_trans Rat.natCast_nonneg (represents_bounds h).1)
    (Rat.le_of_lt (two_zpow_pos e))

theorem ten_zpow_le_two_nonpos {e : Int} (he : e ≤ 0) : (10 : Rat) ^ e ≤ (2 : Rat) ^ e := by
  have h10 := zpow_neg_toNat (b := (10 : Rat)) (e := -e) (by omega)
  have h2 := zpow_neg_toNat (b := (2 : Rat)) (e := -e) (by omega)
  simp only [Int.neg_neg] at h10 h2
  rw [h10, h2]
  apply inv_le_inv (Rat.pow_pos (by decide))
  exact_mod_cast Nat.pow_le_pow_left (by decide : 2 ≤ 10) (-e).toNat

theorem tiny_decimal {m : Nat} {e : Int} (he : e < -(2048 + (m.log2 : Int))) :
    (m : Rat) * (10 : Rat) ^ e < (2 : Rat) ^ (-1075 : Int) := by
  have hm : (m : Rat) < (2 : Rat) ^ ((m.log2 : Int) + 1) := by
    rw [show (m.log2 : Int) + 1 = ((m.log2 + 1 : Nat) : Int) by omega, two_zpow_natCast]
    exact_mod_cast Nat.lt_log2_self (n := m)
  have hle := Rat.mul_le_mul_of_nonneg_left (ten_zpow_le_two_nonpos (by omega : e ≤ 0))
    (Rat.natCast_nonneg (a := m))
  have hlt := Rat.mul_lt_mul_of_pos_right hm (two_zpow_pos e)
  rw [← Rat.zpow_add (by decide)] at hlt
  exact lt_of_le_of_lt hle (lt_of_lt_of_le hlt (zpow_le_zpow_right₀ (by decide) (by omega)))

end Srtfp.Reader.Upstream

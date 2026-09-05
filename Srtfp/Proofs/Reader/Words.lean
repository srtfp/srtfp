module
/- Finite binary64 values as `(m, q)` pairs (`Srtfp.Model.Legal`):
   injectivity of the value `m · 2^q`, and the gap around a value: no
   legal value lies strictly between `m · 2^q` and its two neighbours.
   Also the spec's vocabulary (`wordVal`, `wordSign`, `wordSig`, `dist`)
   read off an unpacked word, and the algebra of signed distances. -/
public import Srtfp.Proofs.Model
public import Srtfp.Proofs.Printer.Interval

@[expose] public section

open Srtfp.Compat

namespace Srtfp.Reader

open Srtfp.Printer Srtfp.Model
open Float.Model (UnpackedFloat)
open Float.Model.UnpackedFloat (Sign)

/-! ## The spec's vocabulary on an unpacked word -/

/-- The `(m, q)` of a finite word; `(0, -1074)` for a zero. -/
def mq : UnpackedFloat → Nat × Int
  | .finite _ m e _ => (m, e)
  | _ => (0, -1074)

/-- The sign of a word; a NaN counts as positive. -/
def usign : UnpackedFloat → Sign
  | .finite s _ _ _ | .zero s | .infinity s => s
  | .notANumber => .positive

theorem legal_mq {w : UInt64} (hw : (Spec.unpack w).isFinite = true) :
    Legal (mq (Spec.unpack w)).1 (mq (Spec.unpack w)).2 := by
  rcases hu : Spec.unpack w with s | _ | s | ⟨s, n, k, hn⟩ <;> rw [hu] at hw
  · simp [UnpackedFloat.isFinite] at hw
  · simp [UnpackedFloat.isFinite] at hw
  · exact legal_zero
  · exact legal_of_unpack hu

theorem wordVal_eq {w : UInt64} (hw : (Spec.unpack w).isFinite = true) :
    Spec.wordVal w = Spec.signVal (usign (Spec.unpack w))
      * v (mq (Spec.unpack w)).1 (mq (Spec.unpack w)).2 := by
  unfold Spec.wordVal
  generalize Spec.unpack w = u at *
  cases u with
  | infinity s => simp [UnpackedFloat.isFinite] at hw
  | notANumber => simp [UnpackedFloat.isFinite] at hw
  | zero s =>
    show (0 : Rat) = _ * (((0 : Nat) : Rat) * _)
    rw [show ((0 : Nat) : Rat) = 0 by simp, Rat.zero_mul, Rat.mul_zero]
  | finite s n k hn => rfl

theorem wordSign_eq (w : UInt64) : Spec.wordSign w = usign (Spec.unpack w) := by
  unfold Spec.wordSign
  rcases Spec.unpack w with s | _ | s | ⟨s, n, k, hn⟩ <;> rfl

theorem wordSig_eq (w : UInt64) : Spec.wordSig w = (mq (Spec.unpack w)).1 := by
  unfold Spec.wordSig
  rcases Spec.unpack w with s | _ | s | ⟨s, n, k, hn⟩ <;> rfl

/-- Finite words with the same fields are the same. -/
theorem eq_of_mq_eq {u u' : UnpackedFloat} (hu : u.isFinite = true) (hu' : u'.isFinite = true)
    (hm : mq u = mq u') (hs : usign u = usign u') : u = u' := by
  cases u with
  | notANumber => simp [UnpackedFloat.isFinite] at hu
  | infinity s => simp [UnpackedFloat.isFinite] at hu
  | zero s =>
    cases u' with
    | notANumber => simp [UnpackedFloat.isFinite] at hu'
    | infinity s' => simp [UnpackedFloat.isFinite] at hu'
    | zero s' => cases (hs : s = s'); rfl
    | finite s' n' k' hn' => exfalso; simp [mq] at hm; omega
  | finite s n k hn =>
    cases u' with
    | notANumber => simp [UnpackedFloat.isFinite] at hu'
    | infinity s' => simp [UnpackedFloat.isFinite] at hu'
    | zero s' => exfalso; simp [mq] at hm; omega
    | finite s' n' k' hn' =>
      simp only [mq, Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      cases (hs : s = s'); rfl

/-! ## Signs -/

theorem sign_mul_abs (s : Sign) (a : Rat) : |Spec.signVal s * a| = |a| := by
  cases s
  · simp only [Spec.signVal]; rw [show (-1 : Rat) * a = -a by grind, Rat.abs_neg]
  · simp only [Spec.signVal, Rat.one_mul]

/-- Same sign: the signed distance is the distance of the magnitudes. -/
theorem dist_of_sign (s : Sign) (a b : Rat) :
    |Spec.signVal s * a - Spec.signVal s * b| = |a - b| := by
  rw [show Spec.signVal s * a - Spec.signVal s * b = Spec.signVal s * (a - b) by grind, sign_mul_abs]

/-- Any signs: the signed distance is at least the distance of the magnitudes. -/
theorem dist_ge (s s' : Sign) {a b : Rat} (_ha : 0 ≤ a) (_hb : 0 ≤ b) :
    |a - b| ≤ |Spec.signVal s' * a - Spec.signVal s * b| := by
  cases s <;> cases s' <;> simp only [Spec.signVal, abs_def] <;> grind

/-- Equal signed and magnitude distances from a differently signed value: the
other magnitude is zero. -/
theorem tie_sign {s s' : Sign} {a b : Rat} (_ha : 0 ≤ a) (_hb : 0 ≤ b)
    (hne : Spec.signVal s' * a ≠ Spec.signVal s * a)
    (heq : |Spec.signVal s' * a - Spec.signVal s * b| = |a - b|) : b = 0 := by
  cases s <;> cases s' <;> simp only [Spec.signVal, abs_def] at hne heq ⊢ <;> grind

theorem mag_nonneg (d : Decimal) : (0 : Rat) ≤ (d.significand : Rat) * (10 : Rat) ^ d.exponent :=
  Rat.mul_nonneg (by exact_mod_cast Nat.zero_le _) (Rat.le_of_lt (ten_zpow_pos _))

theorem abs_toRat (d : Decimal) :
    |Spec.toRat d| = (d.significand : Rat) * (10 : Rat) ^ d.exponent := by
  show |Spec.signVal d.sign * _| = _
  rw [sign_mul_abs, Rat.abs_of_nonneg (mag_nonneg d)]

theorem dist_eq (d : Decimal) {w : UInt64} (hw : (Spec.unpack w).isFinite = true) :
    Spec.dist d w = |Spec.signVal (usign (Spec.unpack w))
      * v (mq (Spec.unpack w)).1 (mq (Spec.unpack w)).2
      - Spec.signVal d.sign * ((d.significand : Rat) * (10 : Rat) ^ d.exponent)| := by
  unfold Spec.dist; rw [wordVal_eq hw]; rfl

/-! ## Values -/

variable {m m' : Nat} {q q' : Int}

theorem v_nonneg : 0 ≤ v m q :=
  Rat.mul_nonneg (by exact_mod_cast Nat.zero_le m) (Rat.le_of_lt (two_zpow_pos q))

theorem v_zero_iff : v m q = 0 ↔ m = 0 := by
  unfold v
  have := two_zpow_pos q
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos m with hm | hm
    · exact hm
    · exfalso
      have : (0 : Rat) < m := by exact_mod_cast hm
      have := Rat.mul_pos this (two_zpow_pos q)
      grind
  · intro h; subst h; simp

/-- `m · 2^q` on the grid `2^q₀`, for `q₀ ≤ q`. -/
theorem v_eq_mul (h : q' ≤ q) :
    v m q = ((m * 2 ^ (q - q').toNat : Nat) : Rat) * (2 : Rat) ^ q' := by
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
    have h1 : (a : Rat) = ((a' * 2 ^ (b' - b).toNat : Nat) : Rat) := (mul_left_inj' (by grind)).mp hv
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
def gapL (m : Nat) (q : Int) : Rat :=
  if m = 2 ^ 52 ∧ q > -1074 then (2 : Rat) ^ (q - 1) else (2 : Rat) ^ q

theorem gapL_pos : 0 < gapL m q := by
  unfold gapL; split <;> exact two_zpow_pos _

theorem gapL_le : gapL m q ≤ (2 : Rat) ^ q := by
  unfold gapL; split
  · exact zpow_le_zpow_right₀ (by decide) (by omega)
  · exact Rat.le_refl

theorem vl_eq : vl m q = v m q - gapL m q / 2 := by
  unfold vl v gapL
  have h2 : (2 : Rat) ^ q = 2 ^ (q - 1) * 2 := by
    rw [← Rat.zpow_add_one (by decide), Int.sub_add_cancel]
  split <;> grind

theorem vr_eq : vr m q = v m q + (2 : Rat) ^ q / 2 := by
  unfold vr v; grind

/-- No legal value lies strictly between `m · 2^q` and its neighbours. -/
theorem gap (h : Legal m q) (h' : Legal m' q') (hne : v m' q' ≠ v m q) :
    v m' q' ≤ v m q - gapL m q ∨ v m q + (2 : Rat) ^ q ≤ v m' q' := by
  have hp := two_zpow_pos q
  have hgl := gapL_le (m := m) (q := q)
  rcases Int.lt_or_le q' q with hlt | hle
  · -- `q' < q`: every such value is below the binade of `m · 2^q`
    left
    have hq0 := h'.2.1
    have hm : 2 ^ 52 ≤ m := h.2.2.2 (by omega)
    have hm53 := h'.1
    have hp1 := two_zpow_pos (q - 1)
    have h2 : (2 : Rat) ^ q = 2 ^ (q - 1) * 2 := by
      rw [← Rat.zpow_add_one (by decide), Int.sub_add_cancel]
    have hq' : (2 : Rat) ^ q' ≤ (2 : Rat) ^ (q - 1) := zpow_le_zpow_right₀ (by decide) (by omega)
    have hm' : (m' : Rat) + 1 ≤ 2 ^ 53 := by exact_mod_cast hm53
    have hv' : (m' : Rat) * (2 : Rat) ^ q' ≤ (2 ^ 53 - 1) * (2 : Rat) ^ (q - 1) :=
      calc (m' : Rat) * (2 : Rat) ^ q' ≤ m' * (2 : Rat) ^ (q - 1) :=
            Rat.mul_le_mul_of_nonneg_left hq' (by exact_mod_cast Nat.zero_le m')
        _ ≤ (2 ^ 53 - 1) * (2 : Rat) ^ (q - 1) :=
            Rat.mul_le_mul_of_nonneg_right (by grind) (Rat.le_of_lt hp1)
    unfold gapL v
    by_cases hirr : m = 2 ^ 52 ∧ q > -1074
    · rw [if_pos hirr, hirr.1]; push_cast
      generalize (2 : Rat) ^ (q - 1) = P1 at *
      generalize (2 : Rat) ^ q = P at *
      grind
    · rw [if_neg hirr]
      have hm1 : 2 ^ 52 + 1 ≤ m := by
        rcases Nat.eq_or_lt_of_le hm with heq | hlt'
        · exact absurd ⟨heq.symm, by omega⟩ hirr
        · omega
      have hmq : (2 ^ 52 + 1 : Rat) ≤ m := by exact_mod_cast hm1
      have := Rat.mul_le_mul_of_nonneg_right hmq (Rat.le_of_lt hp)
      generalize (2 : Rat) ^ (q - 1) = P1 at *
      generalize (2 : Rat) ^ q = P at *
      grind
  · -- `q ≤ q'`: the value is on the grid `2^q`, at some `n ≠ m`
    rw [v_eq_mul hle] at hne ⊢
    generalize m' * 2 ^ (q' - q).toNat = n at hne ⊢
    unfold v at hne ⊢
    have hnm : n ≠ m := fun h => hne (by rw [h])
    rcases Nat.lt_or_gt_of_ne hnm with hlt | hgt
    · left
      have : (n : Rat) + 1 ≤ m := by exact_mod_cast hlt
      have := Rat.mul_le_mul_of_nonneg_right this (Rat.le_of_lt hp)
      grind
    · right
      have : (m : Rat) + 1 ≤ n := by exact_mod_cast hgt
      have := Rat.mul_le_mul_of_nonneg_right this (Rat.le_of_lt hp)
      grind

end Srtfp.Reader

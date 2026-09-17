module
/- Connect Lean's decimal conversion to rounding intervals: a decimal
   reads back to a finite word iff it carries the word's sign and its
   magnitude lies in the word's rounding interval. -/
public import Srtfp.Proofs.Reader.Upstream
public import Srtfp.Proofs.Reader.Nearest

@[expose] public section

open Srtfp.Compat

namespace Srtfp.Reader

open Srtfp.Printer Srtfp.Model
open Float.Model (UnpackedFloat)
open Float.Model.UnpackedFloat (Sign)

/-- Every value in `R_w` is below the overflow threshold: the largest
interval's right endpoint is the threshold, excluded because `2^53 - 1` is odd. -/
theorem lt_threshold_of_InRv {m : Nat} {q : Int} {x : Rat} (h : Legal m q) (hx : InRv m q x = true) :
    x < 2 ^ 1024 - 2 ^ 970 := by
  have hr := (le_of_InRv hx).2
  have hev := even_of_eq_vr hx
  unfold vr at hr hev
  have hm : (m : Rat) + 1 ≤ 2 ^ 53 := by exact_mod_cast (show m + 1 ≤ 2 ^ 53 by have := h.1; omega)
  rw [threshold_eq]
  rcases Int.lt_or_le q 971 with hq | hq
  · have hp := two_zpow_pos q
    have h1 : (2 : Rat) ^ q ≤ 2 ^ (970 : Int) := zpow_le_zpow_right₀ (by decide) (by omega)
    have h2 : (2 : Rat) ^ (971 : Int) = 2 ^ (970 : Int) * 2 := by
      rw [← Rat.zpow_add_one (by decide)]; rfl
    have h3 : ((m : Rat) + 1/2) * 2 ^ q < 2 ^ 53 * 2 ^ q := Rat.mul_lt_mul_of_pos_right (by grind) hp
    have h4 : (2 : Rat) ^ 53 * 2 ^ q ≤ 2 ^ 53 * 2 ^ (970 : Int) :=
      Rat.mul_le_mul_of_nonneg_left h1 (by grind)
    generalize (2 : Rat) ^ (970 : Int) = P at *
    generalize (2 : Rat) ^ q = Q at *
    grind
  · have hq' : q = 971 := by have := h.2.2.1; omega
    subst hq'
    have hle : ((m : Rat) + 1/2) * 2 ^ (971 : Int) ≤ (2 ^ 53 - 1/2) * 2 ^ (971 : Int) :=
      Rat.mul_le_mul_of_nonneg_right (by grind) (Rat.le_of_lt (two_zpow_pos _))
    by_cases heq : x = ((m : Rat) + 1/2) * 2 ^ (971 : Int)
    · have he := hev heq
      have hm2 : (m : Rat) + 2 ≤ 2 ^ 53 := by
        exact_mod_cast (show m + 2 ≤ 2 ^ 53 by have := h.1; omega)
      rw [heq]; exact Rat.mul_lt_mul_of_pos_right (by grind) (two_zpow_pos _)
    · exact lt_of_lt_of_le (Rat.lt_of_le_of_ne hr heq) hle

/-- The public wrapper agrees with the internal arithmetic reader. -/
theorem ofDecimalBits_eq_reference (d : Decimal) : ofDecimalBits d = referenceBits d :=
  congrArg Float.Model.toBits (Upstream.toModel_eq_read d)

/-- Translate upstream round-tripping to the internal reader used in the proofs. -/
theorem readsTo_iff (d : Decimal) (w : UInt64) : Spec.ReadsTo d w ↔ referenceBits d = w := by
  change ofDecimalBits d = w ↔ referenceBits d = w
  rw [ofDecimalBits_eq_reference]

/-! ## The interface to the printer proof -/

/-- Reading a decimal back yields the finite word `w` iff the decimal
carries `w`'s sign and its magnitude lies in `R_w`. -/
theorem reads_to_iff {w : UInt64} (hw : (Spec.unpack w).isFinite = true) (d : Decimal) :
    referenceBits d = w ↔
      (d.sign = usign (Spec.unpack w)
        ∧ InRv (mq (Spec.unpack w)).1 (mq (Spec.unpack w)).2
            ((d.significand : Rat) * (10 : Rat) ^ d.exponent) = true) := by
  have hleg := legal_mq hw
  constructor
  · intro h
    rcases lt_or_ge ((d.significand : Rat) * (10 : Rat) ^ d.exponent) (2 ^ 1024 - 2 ^ 970) with hd | hd
    · obtain ⟨-, hs, -, hmem⟩ := (read_spec d).1 hd
      rw [← unpack_referenceBits, h] at hs hmem
      exact ⟨hs.symm, hmem⟩
    · exfalso
      have := (read_spec d).2 hd
      rw [← unpack_referenceBits, h] at this
      rw [this] at hw
      simp [UnpackedFloat.isFinite] at hw
  · rintro ⟨hs, hmem⟩
    have hd := lt_threshold_of_InRv hleg hmem
    obtain ⟨hfin', hs', -, hmem'⟩ := (read_spec d).1 hd
    rw [← unpack_referenceBits] at hfin' hs' hmem'
    exact (eq_of_nearestWord (nearestWord_of_InRv hw hs.symm hmem) hfin' hs' hmem').symm

/-- The same, for a finite nonzero word given by its fields. -/
theorem reads_to_finite_iff {w : UInt64} {s : Sign} {m : Nat} {q : Int} {hm : 0 < m}
    (hw : Spec.unpack w = .finite s m q hm) (d : Decimal) :
    referenceBits d = w ↔
      (d.sign = s ∧ InRv m q ((d.significand : Rat) * (10 : Rat) ^ d.exponent) = true) := by
  have hfin : (Spec.unpack w).isFinite = true := by rw [hw]; rfl
  rw [reads_to_iff hfin, hw]; rfl

end Srtfp.Reader

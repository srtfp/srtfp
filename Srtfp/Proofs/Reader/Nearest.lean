module
/- Everything in the rounding interval `R_v` reads to `v`: it is nearer to
   `v` than to any other legal value, and equidistant only from a
   neighbour, at an endpoint the even rule admits. Hence a finite word
   whose interval contains a decimal's magnitude, carrying its sign, is
   the decimal's nearest word — and the only one. -/
public import Srtfp.Spec
public import Srtfp.Proofs.Reader.Words
public import Srtfp.Proofs.Unpack

@[expose] public section

open Srtfp.Compat

namespace Srtfp.Clinger

open Srtfp.Float Srtfp.Printer

variable {m m' : Nat} {q q' : Int} {x : Rat}

/-! ## Endpoints of `R_v` -/

theorem even_of_eq_vl (hx : InRv m q x = true) (h : x = vl m q) : m % 2 = 0 := by
  unfold InRv at hx
  split at hx
  · assumption
  · simp only [decide_eq_true_eq] at hx; grind

theorem even_of_eq_vr (hx : InRv m q x = true) (h : x = vr m q) : m % 2 = 0 := by
  unfold InRv at hx
  split at hx
  · assumption
  · simp only [decide_eq_true_eq] at hx; grind

/-- `R_v` is nearer to `v` than to any other legal value; a tie needs an
even `m` and the other value to be a neighbour of `v`. -/
theorem nearest_of_InRv (h : Legal m q) (h' : Legal m' q') (hx : InRv m q x = true) :
    |v m q - x| ≤ |v m' q' - x|
    ∧ (v m' q' ≠ v m q → |v m' q' - x| = |v m q - x| →
        m % 2 = 0 ∧ (v m' q' = v m q - gapL m q ∨ v m' q' = v m q + (2 : Rat) ^ q)) := by
  by_cases hne : v m' q' = v m q
  · rw [hne]; exact ⟨le_refl _, fun h => absurd rfl h⟩
  obtain ⟨hl, hr⟩ := le_of_InRv hx
  have heven_l := even_of_eq_vl hx
  have heven_r := even_of_eq_vr hx
  rw [vl_eq] at hl heven_l
  rw [vr_eq] at hr heven_r
  have hg := gapL_pos (m := m) (q := q)
  have hgl := gapL_le (m := m) (q := q)
  have hp := two_zpow_pos q
  have habs1 := abs_def (v m q - x)
  have habs2 := abs_def (v m' q' - x)
  have hgap := gap h h' hne
  generalize v m q = V at *
  generalize v m' q' = V' at *
  generalize gapL m q = g at *
  generalize (2 : Rat) ^ q = p at *
  grind

/-! ## Signs -/

theorem sign_mul_abs (s : Bool) (a : Rat) : |(if s then -1 else 1 : Rat) * a| = |a| := by
  cases s
  · simp only [Bool.false_eq_true, if_false, one_mul]
  · simp only [if_true]; rw [show (-1 : Rat) * a = -a by grind, abs_neg]

/-- Same sign: the signed distance is the distance of the magnitudes. -/
theorem dist_of_sign (s : Bool) (a b : Rat) :
    |(if s then -1 else 1 : Rat) * a - (if s then -1 else 1 : Rat) * b| = |a - b| := by
  rw [show (if s then -1 else 1 : Rat) * a - (if s then -1 else 1 : Rat) * b
      = (if s then -1 else 1 : Rat) * (a - b) by grind, sign_mul_abs]

/-- Any signs: the signed distance is at least the distance of the magnitudes. -/
theorem dist_ge (s s' : Bool) {a b : Rat} (_ha : 0 ≤ a) (_hb : 0 ≤ b) :
    |a - b| ≤ |(if s' then -1 else 1 : Rat) * a - (if s then -1 else 1 : Rat) * b| := by
  cases s <;> cases s' <;> simp only [Bool.false_eq_true, if_true, if_false, abs_def] <;> grind

/-- Equal signed and magnitude distances from a differently signed value: the
other magnitude is zero. -/
theorem tie_sign {s s' : Bool} {a b : Rat} (_ha : 0 ≤ a) (_hb : 0 ≤ b)
    (hne : (if s' then -1 else 1 : Rat) * a ≠ (if s then -1 else 1 : Rat) * a)
    (heq : |(if s' then -1 else 1 : Rat) * a - (if s then -1 else 1 : Rat) * b| = |a - b|) : b = 0 := by
  cases s <;> cases s' <;> simp only [Bool.false_eq_true, if_true, if_false, abs_def] at hne heq ⊢
    <;> grind

/-! ## The nearest word -/

/-- The spec's vocabulary on a finite word, in terms of `v`
(`Srtfp/Proofs/Unpack.lean` relates Lean's `unpack` to `Word.decode`). -/
theorem wordVal_eq {z : UInt64} (hz : Word.isFinite z = true) :
    Spec.wordVal z = (if (Word.decode z).sign then -1 else 1 : Rat)
      * v (Word.decode z).m (Word.decode z).q :=
  Srtfp.Float.wordVal_eq hz

theorem dist_eq (d : Decimal) {z : UInt64} (hz : Word.isFinite z = true) :
    Spec.dist d z = |(if (Word.decode z).sign then -1 else 1 : Rat) * v (Word.decode z).m (Word.decode z).q
      - (if d.sign then -1 else 1 : Rat) * ((d.significand : Rat) * (10 : Rat) ^ d.exponent)| := by
  unfold Spec.dist; rw [Srtfp.Float.wordVal_eq hz]; rfl

theorem mag_nonneg (d : Decimal) : (0 : Rat) ≤ (d.significand : Rat) * (10 : Rat) ^ d.exponent :=
  Rat.mul_nonneg (by exact_mod_cast Nat.zero_le _) (le_of_lt (ten_zpow_pos _))

/-- A finite word of the decimal's sign whose interval contains the
decimal's magnitude is the decimal's nearest word. -/
theorem nearestWord_of_InRv {d : Decimal} {w : UInt64} (hw : Word.isFinite w = true)
    (hs : (Word.decode w).sign = d.sign)
    (hx : InRv (Word.decode w).m (Word.decode w).q ((d.significand : Rat) * (10 : Rat) ^ d.exponent) = true) :
    Spec.NearestWord d w := by
  have hX := mag_nonneg d
  have hleg := decode_legal hw
  refine ⟨(isFinite_iff w).mpr hw, by rw [wordSign_eq hw, signBit_eq_decode_sign, hs], fun u hu => ?_⟩
  have hu' := (isFinite_iff u).mp hu
  have hlegu := decode_legal hu'
  rw [wordSig_mod_two hw, dist_eq d hw, dist_eq d hu', wordVal_eq hu', wordVal_eq hw]
  generalize (d.significand : Rat) * (10 : Rat) ^ d.exponent = X at *
  generalize d.sign = s at *
  generalize Word.decode w = dw at *
  generalize Word.decode u = du at *
  obtain ⟨sw, mw, qw⟩ := dw
  obtain ⟨su, mu, qu⟩ := du
  simp only at *
  subst hs
  obtain ⟨hle, htie⟩ := nearest_of_InRv hleg hlegu hx
  rw [dist_of_sign]
  refine ⟨le_trans hle (dist_ge _ _ v_nonneg hX), fun hne heq => ?_⟩
  by_cases hv : v mu qu = v mw qw
  · exfalso
    rw [hv] at hne heq
    have h0 := tie_sign v_nonneg hX hne heq
    subst h0
    have h1 := (nearest_of_InRv hleg legal_zero hx).1
    rw [sub_zero, sub_zero, v_zero_iff.mpr rfl, abs_zero] at h1
    have hz : v mw qw = 0 := abs_eq_zero.mp (Rat.le_antisymm h1 (abs_nonneg _))
    rw [hz, mul_zero, mul_zero] at hne
    exact hne rfl
  · have heq' : |v mu qu - X| = |v mw qw - X| :=
      Rat.le_antisymm (by rw [← heq]; exact dist_ge _ _ v_nonneg hX) hle
    exact (htie hv heq').1

/-! ## Uniqueness -/

/-- Any nearest word is the finite word of the right sign whose interval
contains the magnitude. -/
theorem eq_of_nearestWord {d : Decimal} {w w' : UInt64} (h : Spec.NearestWord d w)
    (hw' : Word.isFinite w' = true) (hs' : (Word.decode w').sign = d.sign)
    (hx : InRv (Word.decode w').m (Word.decode w').q ((d.significand : Rat) * (10 : Rat) ^ d.exponent) = true) :
    w = w' := by
  have h' := nearestWord_of_InRv hw' hs' hx
  have hw := (isFinite_iff w).mp h.finite
  have hleg := decode_legal hw
  have hleg' := decode_legal hw'
  have hX := mag_nonneg d
  obtain ⟨hle, htie⟩ := h.nearest w' ((isFinite_iff w').mpr hw')
  obtain ⟨hle', htie'⟩ := h'.nearest w ((isFinite_iff w).mpr hw)
  have heq : Spec.dist d w' = Spec.dist d w := Rat.le_antisymm hle' hle
  have hs : (Word.decode w).sign = d.sign := by
    rw [← signBit_eq_decode_sign, ← wordSign_eq hw]; exact h.sign
  apply eq_of_decode_eq
  have heqd := heq
  rw [dist_eq d hw', dist_eq d hw, hs, hs'] at heq
  rw [wordVal_eq hw', wordVal_eq hw, hs, hs'] at htie htie'
  rw [wordSig_mod_two hw] at htie
  rw [wordSig_mod_two hw'] at htie'
  generalize (d.significand : Rat) * (10 : Rat) ^ d.exponent = X at *
  generalize d.sign = s at *
  generalize Word.decode w = dw at *
  generalize Word.decode w' = dw' at *
  obtain ⟨sw, mw, qw⟩ := dw
  obtain ⟨sw', mw', qw'⟩ := dw'
  simp only at *
  subst hs
  subst hs'
  rw [dist_of_sign, dist_of_sign] at heq
  by_cases hv : v mw qw = v mw' qw'
  · obtain ⟨rfl, rfl⟩ := v_inj hleg hleg' hv
    rfl
  · -- both mantissas are even, yet `v mw qw` is a neighbour of `v mw' qw'`
    have hne : (if sw' then -1 else 1 : Rat) * v mw' qw' ≠ (if sw' then -1 else 1 : Rat) * v mw qw :=
      fun h => hv ((mul_left_cancel₀ (by cases sw' <;> decide) h).symm)
    have he := htie hne heqd
    have he' := htie' (Ne.symm hne) heqd.symm
    obtain ⟨-, hnb⟩ := (nearest_of_InRv hleg' hleg hx).2 hv heq.symm
    exfalso
    have hp := two_zpow_pos qw'
    have hm53 := hleg'.1
    have hq0 := hleg'.2.1
    have hq1 := hleg'.2.2.1
    have hmin := hleg'.2.2.2
    rcases hnb with hL | hR
    · unfold gapL at hL
      by_cases hirr : mw' = 2 ^ 52 ∧ qw' > -1074
      · -- the value below the bottom of a binade is `(2^53 - 1) · 2^(q-1)`
        rw [if_pos hirr, hirr.1] at hL
        have hval : v mw qw = v (2 ^ 53 - 1) (qw' - 1) := by
          rw [hL]; unfold v
          have h2 : (2 : Rat) ^ qw' = 2 ^ (qw' - 1) * 2 := by
            rw [← Rat.zpow_add_one (by decide), Int.sub_add_cancel]
          rw [h2]; push_cast; grind
        have hlegN : Legal (2 ^ 53 - 1) (qw' - 1) := by unfold Legal; omega
        obtain ⟨rfl, -⟩ := v_inj hleg hlegN hval
        omega
      · rw [if_neg hirr] at hL
        obtain ⟨k, rfl⟩ : ∃ k, mw' = k + 1 := by
          refine ⟨mw' - 1, ?_⟩
          rcases Nat.eq_zero_or_pos mw' with h0 | h0
          · exfalso; subst h0
            have := v_nonneg (m := mw) (q := qw)
            rw [hL, v_zero_iff.mpr rfl] at this; grind
          · omega
        have hval : v mw qw = v k qw' := by rw [hL]; unfold v; push_cast; grind
        have hlegN : Legal k qw' := by
          unfold Legal
          refine ⟨by omega, hq0, hq1, fun hq => ?_⟩
          have := hmin hq
          have : k + 1 ≠ 2 ^ 52 := fun h => hirr ⟨h, by omega⟩
          omega
        obtain ⟨rfl, -⟩ := v_inj hleg hlegN hval
        omega
    · have hval : v mw qw = v (mw' + 1) qw' := by rw [hR]; unfold v; push_cast; grind
      have hlegN : Legal (mw' + 1) qw' := by
        unfold Legal
        refine ⟨by omega, hq0, hq1, fun hq => by have := hmin hq; omega⟩
      obtain ⟨rfl, -⟩ := v_inj hleg hlegN hval
      omega

end Srtfp.Clinger

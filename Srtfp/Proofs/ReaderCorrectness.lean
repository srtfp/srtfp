/- Reader correctness: `Clinger.ofDecimal` is THE round-to-nearest,
   ties-to-even `Decimal → Float` reader.

   Public statement: `Srtfp.Spec.correct_iff_ofDecimal`
   (`Srtfp/Correctness.lean`); internal vocabulary
   (`IsNearestWord`, `IsCorrectReaderBits`) in `CorrectnessSpec.lean`.

   ## Layering

   * Float-grid geometry: legal IEEE magnitudes are `2^q`-discrete
     upward and `2^q`/`2^(q-1)`-discrete downward (irregular binade
     bottom), values are injective, grid successors alternate mantissa
     parity.
   * `R_v` semantics: `inRoundingInterval` membership converts to ℚ
     brackets `v_l ≤/< u ≤/< v_r` around `v = magVal m q` via the
     `cmpScaledMixed_*_iff_rat` bridges from `Schubfach/TieBreak.lean`.
   * Nearest: the brackets plus grid discreteness give global distance
     minimality over every finite float, with exact ties forcing the
     even mantissa (endpoint parity of `R_v`).
   * Assembly: existence via `ofDecimal_in_Rv`, uniqueness via the tie
     analysis and `toBits_eq_of_decode_eq`; overflow via
     `decimalToFloat_overflow_inf`; zeros via `pack_proj`. -/

import Srtfp.Proofs.CorrectnessSpec
import Srtfp.Proofs.RoundTrip
import Srtfp.Proofs.Schubfach.TieBreak
import Srtfp.Tactics

namespace Srtfp.Clinger

open Srtfp.Float
open Srtfp.Schubfach
open Srtfp

/-! ## Finite decode shapes

`decode` of a finite float is either the zero pair `(0, -1074)` or a
`LegalIEEE` pair. -/

/-- The `(m, q)` shapes `decode` produces on finite floats. -/
def FinShape (m : Nat) (q : Int) : Prop :=
  (m = 0 ∧ q = -1074) ∨ LegalIEEE m q

theorem finShape_zero : FinShape 0 (-1074) := Or.inl ⟨rfl, rfl⟩

theorem FinShape.m_lt {m : Nat} {q : Int} (h : FinShape m q) : m < 2 ^ 53 := by
  rcases h with ⟨rfl, rfl⟩ | h | h <;> omega

theorem FinShape.q_ge {m : Nat} {q : Int} (h : FinShape m q) : -1074 ≤ q := by
  rcases h with ⟨rfl, rfl⟩ | h | h <;> omega

theorem FinShape.q_le {m : Nat} {q : Int} (h : FinShape m q) : q ≤ 971 := by
  rcases h with ⟨rfl, rfl⟩ | h | h <;> omega

/-- A nonzero shape is legal. -/
theorem FinShape.legal_of_ne {m : Nat} {q : Int} (h : FinShape m q) (hm : m ≠ 0) : LegalIEEE m q := by
  rcases h with ⟨rfl, rfl⟩ | h
  · exact absurd rfl hm
  · exact h

/-- Small `m` in a shape forces the subnormal exponent. -/
theorem FinShape.q_eq_of_small {m : Nat} {q : Int} (h : FinShape m q) (hm : m < 2 ^ 52) : q = -1074 := by
  rcases h with ⟨rfl, rfl⟩ | h | h
  · rfl
  · omega
  · omega

/-- `decode` of a finite float has a `FinShape`. -/
theorem decode_finShape (v : UInt64) (h_fin : Word.isFinite v = true) :
    FinShape (Word.decode v).m (Word.decode v).q := by
  by_cases hm : (Word.decode v).m = 0
  · left
    refine ⟨hm, ?_⟩
    -- m = 0 forces the subnormal branch of decode.
    unfold Word.decode at hm ⊢
    by_cases he : Word.biasedExp v = 0
    · rw [if_pos he]
    · rw [if_neg he] at hm
      simp only at hm
      omega
  · exact Or.inr (decode_legalIEEE_bits v h_fin hm)

/-! ## Grid geometry in ℚ -/

private theorem two_zpow_pos (q : Int) : (0 : ℚ) < (2 : ℚ) ^ q :=
  Rat.zpow_pos (by decide)

theorem magVal_nonneg (m : Nat) (q : Int) : (0 : ℚ) ≤ magVal m q :=
  Rat.mul_nonneg (Rat.natCast_nonneg) (le_of_lt (two_zpow_pos q))

theorem magVal_zero_eq (q : Int) : magVal 0 q = 0 := by
  unfold magVal; simp

/-- Rescale a magnitude to a lower exponent:
`magVal m' q' = (m' · 2^(q'-q)) · 2^q` for `q ≤ q'`. -/
private theorem magVal_shift (m' : Nat) (q q' : Int) (h : q ≤ q') :
    magVal m' q' = ((m' * 2 ^ (q' - q).toNat : Nat) : ℚ) * (2 : ℚ) ^ q := by
  unfold magVal
  push_cast
  rw [show (2 : ℚ) ^ ((q' - q).toNat) = (2 : ℚ) ^ ((q' - q : Int)) from by
        rw [← Rat.zpow_natCast]
        congr 1
        omega,
      Rat.mul_assoc, ← Rat.zpow_add (by grind : (2:ℚ) ≠ 0)]
  congr 2
  omega

/-- **Grid discreteness, upward.** Any finite-shape magnitude strictly
above `magVal m q` is at least one step `2^q` above it. -/
theorem magVal_gap_up (m m' : Nat) (q q' : Int)
    (hs : FinShape m q) (hs' : FinShape m' q')
    (hlt : magVal m q < magVal m' q') :
    magVal m q + (2 : ℚ) ^ q ≤ magVal m' q' := by
  rcases le_or_gt q q' with hq | hq
  · -- q ≤ q': compare coefficients at scale 2^q.
    rw [magVal_shift m' q q' hq] at hlt ⊢
    have hcoeff : (m : ℚ) < ((m' * 2 ^ (q' - q).toNat : Nat) : ℚ) := by
      unfold magVal at hlt
      exact (Rat.mul_lt_mul_right (two_zpow_pos q)).mp hlt
    have hnat : m < m' * 2 ^ (q' - q).toNat := by exact_mod_cast hcoeff
    have hnat1 : (m : ℚ) + 1 ≤ ((m' * 2 ^ (q' - q).toNat : Nat) : ℚ) := by
      have : m + 1 ≤ m' * 2 ^ (q' - q).toNat := hnat
      exact_mod_cast this
    unfold magVal
    have hstep : ((m : ℚ) + 1) * (2:ℚ) ^ q ≤ ((m' * 2 ^ (q' - q).toNat : Nat) : ℚ) * (2:ℚ) ^ q :=
      Rat.mul_le_mul_of_nonneg_right hnat1 (Rat.le_of_lt (two_zpow_pos q))
    grind
  · -- q' < q: impossible for a strictly larger magnitude.
    exfalso
    -- q' < q forces q > -1074, so (m, q) is a normal legal pair: m ≥ 2^52.
    have hq_min : -1074 ≤ q' := hs'.q_ge
    have hm_ge : 2 ^ 52 ≤ m := by
      rcases hs with ⟨rfl, rfl⟩ | hleg
      · omega
      · rcases hleg with ⟨_, _, hqe⟩ | ⟨hge, _⟩
        · omega
        · exact hge
    -- magVal m' q' < 2^53 · 2^q' ≤ 2^52 · 2^q ≤ magVal m q.
    have h1 : magVal m' q' < magVal (2 ^ 53) q' := by
      unfold magVal
      have h2 := two_zpow_pos q'
      have hlt' : (m' : ℚ) < ((2 ^ 53 : Nat) : ℚ) := by
        exact_mod_cast hs'.m_lt
      exact Rat.mul_lt_mul_of_pos_right hlt' h2
    have h2 : magVal (2 ^ 53) q' ≤ magVal (2 ^ 52) q := by
      unfold magVal
      -- 2^53 · 2^q' = 2^52 · 2^(q'+1) ≤ 2^52 · 2^q.
      have hstep : (2 : ℚ) ^ (q' + 1) ≤ (2 : ℚ) ^ q :=
        zpow_le_zpow_right₀ (by grind) (by omega)
      have h52 : (0 : ℚ) < ((2 ^ 52 : Nat) : ℚ) := by (first | exact Rat.zpow_pos (by decide) | exact Rat.pow_pos (by decide) | exact Int.pow_nonneg (by omega) | exact Int.pow_pos (by omega) | exact Nat.pow_pos (by omega) | grind)
      have hsplit : ((2 ^ 53 : Nat) : ℚ) * (2 : ℚ) ^ q'
          = ((2 ^ 52 : Nat) : ℚ) * (2 : ℚ) ^ (q' + 1) := by
        rw [Rat.zpow_add (by grind : (2:ℚ) ≠ 0)]
        push_cast
        grind
      rw [hsplit]
      exact Rat.mul_le_mul_of_nonneg_left hstep (Rat.le_of_lt h52)
    have h3 : magVal (2 ^ 52) q ≤ magVal m q := by
      unfold magVal
      have h2q := two_zpow_pos q
      have hle : ((2 ^ 52 : Nat) : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm_ge
      exact Rat.mul_le_mul_of_nonneg_right hle (Rat.le_of_lt h2q)
    grind

/-- Cancel a shared positive `2^q` factor in an equality. -/
private theorem coeff_eq_of_magVal (a b : Nat) (q : Int)
    (h : (a : ℚ) * (2 : ℚ) ^ q = (b : ℚ) * (2 : ℚ) ^ q) : a = b := by
  have := (mul_left_inj' (Rat.ne_of_gt (two_zpow_pos q))).mp h
  exact_mod_cast this

/-- **Grid discreteness, downward.** Any finite-shape magnitude strictly
below a legal `magVal m q` is at least the half-step below it at the
irregular binade bottom, a full step otherwise. -/
theorem magVal_gap_down (m m' : Nat) (q q' : Int)
    (hleg : LegalIEEE m q) (hs' : FinShape m' q')
    (hlt : magVal m' q' < magVal m q) :
    magVal m' q'
      ≤ magVal m q - (if isIrregular m q then (2 : ℚ) ^ (q - 1) else (2 : ℚ) ^ q) := by
  have hstep_le : (if isIrregular m q then (2 : ℚ) ^ (q - 1) else (2 : ℚ) ^ q)
      ≤ (2 : ℚ) ^ q := by
    split
    · exact zpow_le_zpow_right₀ (by grind) (by omega)
    · exact le_refl _
  have hq_min : (-1074 : Int) ≤ q' := hs'.q_ge
  have hq_min_m : (-1074 : Int) ≤ q := by
    rcases hleg with ⟨_, _, hqe⟩ | ⟨_, _, hge, _⟩ <;> omega
  rcases lt_trichotomy q' q with hq | hq | hq
  · -- q' < q: bound mag' by (2^53 - 1) · 2^(q-1) and compare.
    have hm'_le : (m' : ℚ) ≤ (2 : ℚ) ^ (53 : ℕ) - 1 := by
      have h1 : m' ≤ 2 ^ 53 - 1 := by have := hs'.m_lt; omega
      have h2 : (m' : ℚ) ≤ ((2 ^ 53 - 1 : Nat) : ℚ) := by exact_mod_cast h1
      have h3 : ((2 ^ 53 - 1 : Nat) : ℚ) = (2 : ℚ) ^ (53 : ℕ) - 1 := by
        have h1 : ((2 ^ 53 - 1 : Nat) : ℚ) + 1 = (2 : ℚ) ^ (53 : ℕ) := by
          rw [show (1:ℚ) = ((1 : Nat) : ℚ) from rfl, ← Rat.natCast_add,
              show (2 ^ 53 - 1 + 1 : Nat) = 2 ^ 53 from by omega, Rat.natCast_pow]
          rfl
        grind
      grind
    have hpow_le : (2 : ℚ) ^ q' ≤ (2 : ℚ) ^ (q - 1) :=
      zpow_le_zpow_right₀ (by grind) (by omega)
    have hmag'_le : (m' : ℚ) * (2 : ℚ) ^ q'
        ≤ ((2 : ℚ) ^ (53 : ℕ) - 1) * (2 : ℚ) ^ (q - 1) := by
      have h1 : (0 : ℚ) ≤ (m' : ℚ) := Rat.natCast_nonneg
      calc (m' : ℚ) * (2:ℚ)^q' ≤ (m' : ℚ) * (2:ℚ)^(q-1) :=
            Rat.mul_le_mul_of_nonneg_left hpow_le h1
        _ ≤ ((2:ℚ)^(53:ℕ) - 1) * (2:ℚ)^(q-1) :=
            Rat.mul_le_mul_of_nonneg_right hm'_le (Rat.le_of_lt (two_zpow_pos (q-1)))
    -- q' < q forces m normal (q > -1074).
    have hm_norm : 2 ^ 52 ≤ m := by
      rcases hleg with ⟨_, _, hqe⟩ | ⟨hge, _⟩
      · omega
      · exact hge
    have hsplit : (2 : ℚ) ^ q = 2 * (2 : ℚ) ^ (q - 1) := by
      rw [show q = (q - 1) + 1 from by omega, Rat.zpow_add (by grind : (2:ℚ) ≠ 0),
          Rat.zpow_one]
      grind
    unfold magVal
    by_cases hirr : isIrregular m q = true
    · -- m = 2^52: mag - 2^(q-1) = (2^53 - 1) · 2^(q-1) exactly.
      have hm_eq : m = 2 ^ 52 := by
        unfold isIrregular minNormalSignificand at hirr
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hirr
        have := hirr.1
        omega
      rw [if_pos hirr, hm_eq, hsplit]
      have hcast : ((2 ^ 52 : Nat) : ℚ) * (2 * (2 : ℚ) ^ (q - 1)) - (2 : ℚ) ^ (q - 1)
          = ((2 : ℚ) ^ (53 : ℕ) - 1) * (2 : ℚ) ^ (q - 1) := by
        push_cast
        grind
      rw [hcast]
      exact hmag'_le
    · -- m ≥ 2^52 + 1: mag - 2^q ≥ 2^52 · 2^q > (2^53 - 1) · 2^(q-1).
      have hm_gt : 2 ^ 52 + 1 ≤ m := by
        unfold isIrregular minNormalSignificand at hirr
        simp only [Bool.and_eq_true, decide_eq_true_eq, not_and] at hirr
        by_cases hm52 : m = 2 ^ 52
        · exfalso
          have hq_gt : q > minBinaryExp := by
            unfold minBinaryExp
            rcases hleg with ⟨_, _, hqe⟩ | _
            · omega
            · omega
          have := hirr (by omega : m = 1 <<< 52)
          omega
        · omega
      rw [if_neg hirr, hsplit]
      have hm_cast : (2 : ℚ) ^ (52 : ℕ) + 1 ≤ (m : ℚ) := by
        have h1 : ((2 ^ 52 + 1 : Nat) : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm_gt
        have h2 : ((2 ^ 52 + 1 : Nat) : ℚ) = (2 : ℚ) ^ (52 : ℕ) + 1 := by
          rw [show (2 ^ 52 + 1 : Nat) = 2 ^ 52 + 1 from rfl, Rat.natCast_add, Rat.natCast_pow]
          rfl
        grind
      have hpow53 : (2 : ℚ) ^ (53 : ℕ) = 2 * (2 : ℚ) ^ (52 : ℕ) := by grind
      have hb : ((2:ℚ)^(53:ℕ) - 1) * (2:ℚ)^(q-1) ≤ ((m : ℚ) * 2 - 2) * (2:ℚ)^(q-1) :=
        Rat.mul_le_mul_of_nonneg_right (by grind) (Rat.le_of_lt (two_zpow_pos (q-1)))
      grind
  · -- q' = q: integer coefficient drop.
    subst hq
    have hcoeff : (m' : ℚ) < (m : ℚ) := by
      unfold magVal at hlt
      exact (Rat.mul_lt_mul_right (two_zpow_pos q')).mp hlt
    have hnat : m' < m := by exact_mod_cast hcoeff
    have hle : (m' : ℚ) ≤ (m : ℚ) - 1 := by
      have : m' + 1 ≤ m := hnat
      have : (m' : ℚ) + 1 ≤ (m : ℚ) := by exact_mod_cast this
      grind
    have : magVal m' q' ≤ magVal m q' - (2 : ℚ) ^ q' := by
      unfold magVal
      have h2 := two_zpow_pos q'
      have hstep : ((m' : ℚ) + 1) * (2:ℚ)^q' ≤ (m : ℚ) * (2:ℚ)^q' :=
        Rat.mul_le_mul_of_nonneg_right (by grind) (Rat.le_of_lt h2)
      grind
    grind
  · -- q < q': a strictly larger exponent forces a larger magnitude.
    exfalso
    have hm'_norm : 2 ^ 52 ≤ m' := by
      rcases hs' with ⟨rfl, rfl⟩ | ⟨_, _, hqe⟩ | ⟨hge, _⟩
      · omega
      · omega
      · exact hge
    have h1 : magVal (2 ^ 52) q' ≤ magVal m' q' := by
      unfold magVal
      have h2 := two_zpow_pos q'
      have : ((2 ^ 52 : Nat) : ℚ) ≤ (m' : ℚ) := by exact_mod_cast hm'_norm
      grind
    have h2 : magVal m q < magVal (2 ^ 52) q' := by
      unfold magVal
      -- m · 2^q < 2^53 · 2^q = 2^52 · 2^(q+1) ≤ 2^52 · 2^q'.
      have hstep : (2 : ℚ) ^ (q + 1) ≤ (2 : ℚ) ^ q' :=
        zpow_le_zpow_right₀ (by grind) (by omega)
      have hm_lt : (m : ℚ) < ((2 ^ 53 : Nat) : ℚ) := by
        have : m < 2 ^ 53 := by
          rcases hleg with ⟨_, hlt', _⟩ | ⟨_, hlt', _⟩ <;> omega
        exact_mod_cast this
      have hsplit : ((2 ^ 53 : Nat) : ℚ) * (2 : ℚ) ^ q
          = ((2 ^ 52 : Nat) : ℚ) * (2 : ℚ) ^ (q + 1) := by
        rw [Rat.zpow_add (by grind : (2:ℚ) ≠ 0)]
        push_cast
        grind
      have h2q := two_zpow_pos q
      have h52 : (0 : ℚ) < ((2 ^ 52 : Nat) : ℚ) := by
        have h := Nat.pow_pos (n := 52) (show 0 < 2 by omega)
        exact_mod_cast h
      have hb1 : (m : ℚ) * (2:ℚ)^q < ((2^53 : Nat) : ℚ) * (2:ℚ)^q :=
        Rat.mul_lt_mul_of_pos_right hm_lt h2q
      have hb2 : ((2^52 : Nat) : ℚ) * (2:ℚ)^(q+1) ≤ ((2^52 : Nat) : ℚ) * (2:ℚ)^q' :=
        Rat.mul_le_mul_of_nonneg_left hstep (Rat.le_of_lt h52)
      grind
    grind

/-- **Value injectivity on finite shapes.** -/
theorem magVal_inj (m m' : Nat) (q q' : Int)
    (hs : FinShape m q) (hs' : FinShape m' q')
    (heq : magVal m q = magVal m' q') : m = m' ∧ q = q' := by
  -- Zero shapes first.
  by_cases hm : m = 0
  · subst hm
    rw [magVal_zero_eq] at heq
    have hm' : m' = 0 := by
      by_contra hne
      have hpos : (0 : ℚ) < magVal m' q' := by
        unfold magVal
        have h2 := two_zpow_pos q'
        have : (0 : ℚ) < (m' : ℚ) := by
          exact_mod_cast Nat.pos_of_ne_zero hne
        grind
      grind
    subst hm'
    have hq : q = -1074 := by
      rcases hs with ⟨_, hq⟩ | hleg
      · exact hq
      · rcases hleg with ⟨h1, _, _⟩ | ⟨h1, _⟩ <;> omega
    have hq' : q' = -1074 := by
      rcases hs' with ⟨_, hq'⟩ | hleg
      · exact hq'
      · rcases hleg with ⟨h1, _, _⟩ | ⟨h1, _⟩ <;> omega
    exact ⟨rfl, by omega⟩
  · have hm' : m' ≠ 0 := by
      intro h0
      subst h0
      rw [magVal_zero_eq] at heq
      have hpos : (0 : ℚ) < magVal m q := by
        unfold magVal
        have h2 := two_zpow_pos q
        have : (0 : ℚ) < (m : ℚ) := by exact_mod_cast Nat.pos_of_ne_zero hm
        grind
      grind
    -- Both legal; wlog via trichotomy on q, q'.
    have hleg := hs.legal_of_ne hm
    have hleg' := hs'.legal_of_ne hm'
    rcases lt_trichotomy q q' with hq | hq | hq
    · -- q < q': q' > -1074 so m' normal; m = m' · 2^(q'-q) ≥ 2^53, illegal.
      exfalso
      have hm'_norm : 2 ^ 52 ≤ m' := by
        rcases hleg' with ⟨_, _, hqe⟩ | ⟨hge, _⟩
        · have := hs.q_ge; omega
        · exact hge
      rw [magVal_shift m' q q' (Int.le_of_lt hq)] at heq
      have hj : 1 ≤ (q' - q).toNat := by omega
      have hnat : m = m' * 2 ^ (q' - q).toNat :=
        coeff_eq_of_magVal m _ q (by exact_mod_cast heq)
      have hge : 2 ^ 53 ≤ m := by
        calc 2 ^ 53 = 2 ^ 52 * 2 ^ 1 := by grind
        _ ≤ m' * 2 ^ (q' - q).toNat :=
            Nat.mul_le_mul hm'_norm (Nat.pow_le_pow_right (by omega) hj)
        _ = m := hnat.symm
      have := hs.m_lt
      omega
    · subst hq
      exact ⟨coeff_eq_of_magVal m m' q heq, rfl⟩
    · -- symmetric.
      exfalso
      have hm_norm : 2 ^ 52 ≤ m := by
        rcases hleg with ⟨_, _, hqe⟩ | ⟨hge, _⟩
        · have := hs'.q_ge; omega
        · exact hge
      rw [magVal_shift m q' q (Int.le_of_lt hq)] at heq
      have hj : 1 ≤ (q - q').toNat := by omega
      have hnat : m * 2 ^ (q - q').toNat = m' :=
        coeff_eq_of_magVal _ m' q' (by exact_mod_cast heq)
      have hge : 2 ^ 53 ≤ m' := by
        calc 2 ^ 53 = 2 ^ 52 * 2 ^ 1 := by grind
        _ ≤ m * 2 ^ (q - q').toNat :=
            Nat.mul_le_mul hm_norm (Nat.pow_le_pow_right (by omega) hj)
        _ = m' := hnat
      have := hs'.m_lt
      omega

/-- **Successor parity.** A legal magnitude exactly one step `2^q` above a
finite-shape `magVal m q` has mantissa parity opposite to `m`'s. -/
theorem magVal_succ_parity (m m' : Nat) (q q' : Int)
    (hs : FinShape m q) (hleg' : LegalIEEE m' q')
    (heq : magVal m' q' = magVal m q + (2 : ℚ) ^ q) :
    m' % 2 ≠ m % 2 := by
  have hsucc : magVal m' q' = magVal (m + 1) q := by
    rw [heq]
    unfold magVal
    push_cast
    grind
  have hq'_ge : (-1074 : Int) ≤ q' := by
    rcases hleg' with ⟨_, _, hqe⟩ | ⟨_, _, hge, _⟩ <;> omega
  rcases lt_trichotomy q q' with hq | hq | hq
  · -- q < q': m' · 2^j = m + 1 with m' normal ⇒ m + 1 = 2^53, m' = 2^52.
    have hm'_norm : 2 ^ 52 ≤ m' := by
      rcases hleg' with ⟨_, _, hqe⟩ | ⟨hge, _⟩
      · have := hs.q_ge; omega
      · exact hge
    rw [magVal_shift m' q q' (Int.le_of_lt hq)] at hsucc
    have hnat : m' * 2 ^ (q' - q).toNat = m + 1 :=
      coeff_eq_of_magVal _ _ q hsucc
    have hj : 1 ≤ (q' - q).toNat := by omega
    have hge : 2 ^ 53 ≤ m + 1 := by
      calc 2 ^ 53 = 2 ^ 52 * 2 ^ 1 := by grind
      _ ≤ m' * 2 ^ (q' - q).toNat :=
          Nat.mul_le_mul hm'_norm (Nat.pow_le_pow_right (by omega) hj)
      _ = m + 1 := hnat
    have hm_lt := hs.m_lt
    have hm_eq : m + 1 = 2 ^ 53 := by omega
    -- m odd; m' = 2^53 / 2^j with m' ≥ 2^52 ⇒ j = 1, m' = 2^52, even.
    have hj_eq : (q' - q).toNat = 1 := by
      by_contra hne
      have hj2 : 2 ≤ (q' - q).toNat := by omega
      have hge4 : 2 ^ 52 * 2 ^ 2 ≤ m' * 2 ^ (q' - q).toNat :=
        Nat.mul_le_mul hm'_norm (Nat.pow_le_pow_right (by omega) hj2)
      omega
    rw [hj_eq] at hnat
    have hm'_eq : m' = 2 ^ 52 := by omega
    omega
  · -- q' = q: m' = m + 1.
    subst hq
    have hnat : m' = m + 1 := coeff_eq_of_magVal m' (m + 1) q hsucc
    omega
  · -- q' < q: m' = (m+1) · 2^j ≥ 2^53 + 2, illegal.
    exfalso
    have hm_norm : 2 ^ 52 ≤ m := by
      rcases hs with ⟨rfl, rfl⟩ | (⟨_, _, hqe⟩ | ⟨hge, _, _, _⟩)
      · omega
      · omega
      · exact hge
    rw [magVal_shift (m + 1) q' q (Int.le_of_lt hq)] at hsucc
    have hnat : m' = (m + 1) * 2 ^ (q - q').toNat :=
      coeff_eq_of_magVal m' _ q' hsucc
    have hj : 1 ≤ (q - q').toNat := by omega
    have hge : 2 ^ 53 + 2 ≤ m' := by
      calc 2 ^ 53 + 2 = (2 ^ 52 + 1) * 2 ^ 1 := by grind
      _ ≤ (m + 1) * 2 ^ (q - q').toNat :=
          Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) hj)
      _ = m' := hnat.symm
    have : m' < 2 ^ 53 := by
      rcases hleg' with ⟨_, h, _⟩ | ⟨_, h, _⟩ <;> omega
    omega

/-! ## `R_v` membership in ℚ

`inRoundingInterval s k m q irreg` says the decimal grid value
`u = gridVal s k` lies between the rounding-interval endpoints of
`v = magVal m q`, endpoints included exactly when `m` is even. Scaled
by 4: `4·v_l = 4v - c·2^q` with `c = 1` (irregular) or `2` (regular),
and `4·v_r = 4v + 2·2^q`. -/

theorem rv_left_rat (s : Nat) (k : Int) (m : Nat) (q : Int) (irreg : Bool)
    (h : inRoundingInterval s k m q irreg = true) :
    4 * magVal m q - (if irreg then (1 : ℚ) else 2) * (2 : ℚ) ^ q < 4 * gridVal s k
    ∨ (4 * magVal m q - (if irreg then (1 : ℚ) else 2) * (2 : ℚ) ^ q = 4 * gridVal s k
       ∧ m % 2 = 0) := by
  have hL := ((inRoundingInterval_iff s k m q irreg).mp h).1
  rcases hL with hlt | ⟨heq, heven⟩
  · left
    have hq := (cmpScaledMixed_lhs_lt_rhs_iff_rat
        (if irreg then 4 * (m : Int) - 1 else 4 * (m : Int) - 2) q
        (4 * (s : Int)) k).mp hlt
    unfold magVal gridVal
    cases irreg <;> simp only [if_true, if_false, Bool.false_eq_true] at hq ⊢ <;>
      · push_cast at hq
        grind
  · right
    refine ⟨?_, heven⟩
    have hq := (cmpScaledMixed_lhs_eq_rhs_iff_rat
        (if irreg then 4 * (m : Int) - 1 else 4 * (m : Int) - 2) q
        (4 * (s : Int)) k).mp heq
    unfold magVal gridVal
    cases irreg <;> simp only [if_true, if_false, Bool.false_eq_true] at hq ⊢ <;>
      · push_cast at hq
        grind

theorem rv_right_rat (s : Nat) (k : Int) (m : Nat) (q : Int) (irreg : Bool)
    (h : inRoundingInterval s k m q irreg = true) :
    4 * gridVal s k < 4 * magVal m q + 2 * (2 : ℚ) ^ q
    ∨ (4 * gridVal s k = 4 * magVal m q + 2 * (2 : ℚ) ^ q ∧ m % 2 = 0) := by
  have hR := ((inRoundingInterval_iff s k m q irreg).mp h).2
  rcases hR with hlt | ⟨heq, heven⟩
  · left
    have hq := (cmpScaledMixed_lhs_gt_rhs_iff_rat
        (4 * (m : Int) + 2) q (4 * (s : Int)) k).mp hlt
    unfold magVal gridVal
    push_cast at hq
    grind
  · right
    refine ⟨?_, heven⟩
    have hq := (cmpScaledMixed_lhs_eq_rhs_iff_rat
        (4 * (m : Int) + 2) q (4 * (s : Int)) k).mp heq.symm
    unfold magVal gridVal
    push_cast at hq
    grind

/-! ## The nearest-float property of `R_v` membership -/

/-- **Global nearest.** If `u = gridVal s k` is in the rounding interval
of `v = magVal m q`, then `v` is at least as close to `u` as any other
finite-shape magnitude. -/
theorem rv_nearest_mag (s : Nat) (k : Int) (m m' : Nat) (q q' : Int)
    (hs : FinShape m q) (hs' : FinShape m' q')
    (h_rv : inRoundingInterval s k m q (isIrregular m q) = true) :
    |magVal m q - gridVal s k| ≤ |magVal m' q' - gridVal s k| := by
  set v := magVal m q with hv
  set w := magVal m' q' with hw
  set u := gridVal s k with hu
  set c : ℚ := if isIrregular m q then 1 else 2 with hc
  have h2q := two_zpow_pos q
  have hc_pos : 0 < c := by rw [hc]; split <;> grind
  have hL : 4 * v - c * (2 : ℚ) ^ q ≤ 4 * u := by
    rcases rv_left_rat s k m q _ h_rv with h | ⟨h, _⟩
    · rw [hc]; grind
    · rw [hc]; grind
  have hR : 4 * u ≤ 4 * v + 2 * (2 : ℚ) ^ q := by
    rcases rv_right_rat s k m q _ h_rv with h | ⟨h, _⟩
    · grind
    · grind
  rcases Rat.lt_trichotomy w v with hwv | hwv | hwv
  · -- w < v: v is positive, m legal; grid gap downward.
    have hm_pos : m ≠ 0 := by
      intro h0
      have hv0 : v = 0 := by rw [hv, h0]; exact magVal_zero_eq q
      have hw0 : (0 : ℚ) ≤ w := hw ▸ magVal_nonneg m' q'
      grind
    have hgap := magVal_gap_down m m' q q' (hs.legal_of_ne hm_pos) hs' hwv
    have hsplit : (2 : ℚ) ^ q = 2 * (2 : ℚ) ^ (q - 1) := by
      rw [show q = (q - 1) + 1 from by omega, Rat.zpow_add (by grind : (2:ℚ) ≠ 0),
          Rat.zpow_one]
      grind
    have hgap4 : 4 * w ≤ 4 * v - 2 * c * (2 : ℚ) ^ q := by
      by_cases hirr : isIrregular m q = true
      · rw [if_pos hirr] at hgap
        rw [hc, if_pos hirr]
        grind
      · rw [if_neg hirr] at hgap
        rw [hc, if_neg hirr]
        grind
    have huw : w < u := by grind
    rw [show |w - u| = u - w from by rw [abs_of_nonpos (by grind)]; grind]
    refine abs_le.mpr ⟨by grind, by grind⟩
  · exact le_of_eq (by rw [hwv])
  · -- v < w: grid gap upward.
    have hgap := magVal_gap_up m m' q q' hs hs' hwv
    have huw : u < w := by grind
    rw [show |w - u| = w - u from abs_of_nonneg (by grind)]
    refine abs_le.mpr ⟨by grind, by grind⟩

/-- **Exact ties force the even mantissa.** If a different finite-shape
magnitude is exactly as close to `u`, then `u` sits on an interval
endpoint, whose inclusion demanded `m` even. -/
theorem rv_tie_even_mag (s : Nat) (k : Int) (m m' : Nat) (q q' : Int)
    (hs : FinShape m q) (hs' : FinShape m' q')
    (h_rv : inRoundingInterval s k m q (isIrregular m q) = true)
    (h_ne : magVal m' q' ≠ magVal m q)
    (h_eq : |magVal m' q' - gridVal s k| = |magVal m q - gridVal s k|) :
    m % 2 = 0 := by
  set v := magVal m q with hv
  set w := magVal m' q' with hw
  set u := gridVal s k with hu
  set c : ℚ := if isIrregular m q then 1 else 2 with hc
  have h2q := two_zpow_pos q
  have hc_pos : 0 < c := by rw [hc]; split <;> grind
  have hL : 4 * v - c * (2 : ℚ) ^ q ≤ 4 * u := by
    rcases rv_left_rat s k m q _ h_rv with h | ⟨h, _⟩
    · rw [hc]; grind
    · rw [hc]; grind
  have hR : 4 * u ≤ 4 * v + 2 * (2 : ℚ) ^ q := by
    rcases rv_right_rat s k m q _ h_rv with h | ⟨h, _⟩
    · grind
    · grind
  rcases Rat.lt_trichotomy w v with hwv | hwv | hwv
  · -- w < v: the tie pins u to the left endpoint.
    have hm_pos : m ≠ 0 := by
      intro h0
      have hv0 : v = 0 := by rw [hv, h0]; exact magVal_zero_eq q
      have hw0 : (0 : ℚ) ≤ w := hw ▸ magVal_nonneg m' q'
      grind
    have hgap := magVal_gap_down m m' q q' (hs.legal_of_ne hm_pos) hs' hwv
    have hsplit : (2 : ℚ) ^ q = 2 * (2 : ℚ) ^ (q - 1) := by
      rw [show q = (q - 1) + 1 from by omega, Rat.zpow_add (by grind : (2:ℚ) ≠ 0),
          Rat.zpow_one]
      grind
    have hgap4 : 4 * w ≤ 4 * v - 2 * c * (2 : ℚ) ^ q := by
      by_cases hirr : isIrregular m q = true
      · rw [if_pos hirr] at hgap
        rw [hc, if_pos hirr]
        grind
      · rw [if_neg hirr] at hgap
        rw [hc, if_neg hirr]
        grind
    have huw : w < u := by grind
    rw [show |w - u| = u - w from by rw [abs_of_nonpos (by grind)]; grind] at h_eq
    rcases Rat.le_or_gt u v with huv | huv
    · -- u ≤ v: |v - u| = v - u; equality chain pins 4u = 4v - c·2^q.
      rw [show |v - u| = v - u from abs_of_nonneg (by grind)] at h_eq
      have h4 : 4 * u = 4 * v - c * (2 : ℚ) ^ q := by grind
      rcases rv_left_rat s k m q _ h_rv with h | ⟨_, heven⟩
      · exfalso
        rw [← hc] at h
        grind
      · exact heven
    · -- u > v: u - v = u - w forces w = v, contradiction.
      exfalso
      rw [show |v - u| = u - v from by rw [abs_of_nonpos (by grind)]; grind] at h_eq
      have : w = v := by grind
      exact h_ne (by rw [hw, hv] at this; exact this)
  · exact absurd (hw ▸ hv ▸ hwv) h_ne
  · -- v < w: the tie pins u to the right endpoint.
    have hgap := magVal_gap_up m m' q q' hs hs' hwv
    have huw : u < w := by grind
    rw [show |w - u| = w - u from abs_of_nonneg (by grind)] at h_eq
    rcases Rat.le_or_gt u v with huv | huv
    · -- u ≤ v: v - u = w - u forces w = v, contradiction.
      exfalso
      rw [show |v - u| = v - u from abs_of_nonneg (by grind)] at h_eq
      have : w = v := by grind
      exact h_ne (by rw [hw, hv] at this; exact this)
    · -- u > v: equality chain pins 4u = 4v + 2·2^q.
      rw [show |v - u| = u - v from by rw [abs_of_nonpos (by grind)]; grind] at h_eq
      have h4 : 4 * u = 4 * v + 2 * (2 : ℚ) ^ q := by grind
      rcases rv_right_rat s k m q _ h_rv with h | ⟨_, heven⟩
      · exfalso
        grind
      · exact heven

/-! ## The overflow boundary

The elementary threshold is `2^1024 - 2^970`: the midpoint between the
largest finite float `(2^53 - 1)·2^971` and its would-be successor
`2^53·2^971`. `IsFiniteAbs` (the algorithm's overflow test) matches it
exactly: values strictly below produce a finite float, values at or
above produce `±∞` (the midpoint itself rounds up, to the even
`m = 2^53`). -/

theorem gridVal_nonneg (s : Nat) (k : Int) : (0 : ℚ) ≤ gridVal s k :=
  Rat.mul_nonneg Rat.natCast_nonneg (le_of_lt (Rat.zpow_pos (by decide)))

/-- `|toRat d|` is the unsigned decimal grid value. -/
theorem abs_toRat_eq_gridVal (d : Decimal) :
    |Decimal.toRat d| = gridVal d.significand d.exponent := by
  rw [toRat_eq_signFactor_gridVal, abs_mul]
  have h1 : |signFactor d.sign| = 1 := by
    unfold signFactor
    cases d.sign <;> decide
  rw [h1, one_mul, abs_of_nonneg (gridVal_nonneg _ _)]

set_option exponentiation.threshold 2048 in
/-- Overflow at the `(a, b)` level: the quotient `a/b` is at least
`(2^54 - 1)·2^970`, in cleared `Nat` form. -/
private theorem overflow_bound_AB (sign : Bool) (a b : Nat) (ha : 0 < a) (hb : 0 < b)
    (h_not : ¬ (decodedAbsAB sign a b).q ≤ 971) :
    (2 ^ 54 - 1) * 2 ^ 970 * b ≤ a := by
  unfold decodedAbsAB at h_not
  simp only at h_not
  by_cases h_e : findBinaryExp a b > 1023
  · rw [if_pos h_e] at h_not
    have hle := findBinaryExp_le a b ha hb
    rw [leBy2e_eq_true_iff] at hle
    rw [if_pos (by omega : findBinaryExp a b ≥ 0)] at hle
    have h_pow : (2 : Nat) ^ 1024 ≤ 2 ^ (findBinaryExp a b).toNat :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have h_lit : (2 ^ 54 - 1) * 2 ^ 970 ≤ (2 : Nat) ^ 1024 := by
      have h1 : (2 ^ 54 - 1) * 2 ^ 970 ≤ 2 ^ 54 * 2 ^ 970 :=
        Nat.mul_le_mul_right _ (by omega)
      have h2 : (2 : Nat) ^ 54 * 2 ^ 970 = 2 ^ 1024 := by
        rw [← Nat.pow_add]
      omega
    calc (2 ^ 54 - 1) * 2 ^ 970 * b ≤ 2 ^ 1024 * b := Nat.mul_le_mul_right b h_lit
    _ ≤ 2 ^ (findBinaryExp a b).toNat * b := Nat.mul_le_mul_right b h_pow
    _ = b * 2 ^ (findBinaryExp a b).toNat := Nat.mul_comm _ _
    _ ≤ a := hle
  · rw [if_neg h_e] at h_not
    by_cases h_e2 : findBinaryExp a b ≥ -1022
    · rw [if_pos h_e2] at h_not
      by_cases h_m : roundNearestEven (scaleByPow2 a b (52 - findBinaryExp a b)).1
          (scaleByPow2 a b (52 - findBinaryExp a b)).2 ≥ 2 ^ 53
      · rw [if_pos h_m] at h_not
        by_cases h_e' : findBinaryExp a b + 1 > 1023
        · rw [if_pos h_e'] at h_not
          have h_e_eq : findBinaryExp a b = 1023 := by omega
          -- num = a, denom = b · 2^971.
          have h_scale : scaleByPow2 a b (52 - findBinaryExp a b) = (a, b * 2 ^ 971) := by
            rw [h_e_eq]
            rw [scaleByPow2_neg (by omega : ¬ (52 - (1023 : Int)) ≥ 0)]
            have h971 : (-(52 - (1023 : Int))).toNat = 971 := by decide
            rw [h971]
          rw [h_scale] at h_m
          set P : Nat := b * 2 ^ 971 with hP
          have hP_pos : 0 < P := by
            rw [hP]
            exact Nat.mul_pos hb (Nat.pow_pos (by omega))
          have hp971 : (2 : Nat) ^ 971 = 2 ^ 970 * 2 := by
            rw [show (971 : ℕ) = 970 + 1 from rfl, Nat.pow_succ]
          rcases roundNearestEven_eq_floor_or_ceil a P with h_fl | h_ce
          · -- floor: a / P ≥ 2^53 forces a ≥ 2^53 · P.
            rw [h_fl] at h_m
            have : 2 ^ 53 * P ≤ a / P * P := Nat.mul_le_mul_right P h_m
            have hdiv : a / P * P ≤ a := Nat.div_mul_le_self a P
            have hgoal : (2 ^ 54 - 1) * 2 ^ 970 * b ≤ 2 ^ 53 * P := by
              rw [hP, hp971]
              calc (2 ^ 54 - 1) * 2 ^ 970 * b ≤ 2 ^ 54 * 2 ^ 970 * b :=
                    Nat.mul_le_mul_right b (Nat.mul_le_mul_right _ (by omega))
              _ = 2 ^ 53 * (b * (2 ^ 970 * 2)) := by grind
            omega
          · -- ceil: the half-ULP bound gives 2a ≥ (2^54 - 1) · P.
            have h_bound := roundNearestEven_ceil_bound a P hP_pos h_ce
            set M : Nat := roundNearestEven a P with hM
            have h_MP : 2 ^ 53 * P ≤ M * P := Nat.mul_le_mul_right P h_m
            -- 2·(M·P - a) ≤ P and M·P ≥ 2^53·P give 2a ≥ (2^54 - 1)·P.
            have h_lin : (2 ^ 54 - 1) * P ≤ 2 * a := by
              have h53 : (2 : Nat) ^ 54 = 2 * 2 ^ 53 := by grind
              omega
            rw [hP] at h_lin
            have hgoal : 2 * ((2 ^ 54 - 1) * 2 ^ 970 * b) = (2 ^ 54 - 1) * (b * 2 ^ 971) := by
              rw [hp971]
              grind
            omega
        · rw [if_neg h_e'] at h_not
          exact absurd (by omega : findBinaryExp a b + 1 - 52 ≤ 971) h_not
      · rw [if_neg h_m] at h_not
        exact absurd (by omega : findBinaryExp a b - 52 ≤ 971) h_not
    · rw [if_neg h_e2] at h_not
      by_cases hm0 : roundNearestEven (scaleByPow2 a b 1074).1 (scaleByPow2 a b 1074).2 = 0
      · rw [if_pos hm0] at h_not
        exact absurd (by grind : (-1074 : Int) ≤ 971) h_not
      · rw [if_neg hm0] at h_not
        by_cases hm52 : roundNearestEven (scaleByPow2 a b 1074).1 (scaleByPow2 a b 1074).2 ≥ 2 ^ 52
        · rw [if_pos hm52] at h_not
          exact absurd (by grind : (-1074 : Int) ≤ 971) h_not
        · rw [if_neg hm52] at h_not
          exact absurd (by grind : (-1074 : Int) ≤ 971) h_not

set_option exponentiation.threshold 2048 in
/-- **Boundary, overflow side.** A nonzero decimal the algorithm rejects
as overflow has `|value| ≥ 2^1024 - 2^970`. -/
theorem bound_le_gridVal_of_not_finite (sign : Bool) (sig : Nat) (exp : Int)
    (h_sig : sig ≠ 0) (h_not : ¬ IsFiniteAbs sign sig exp) :
    (2 : ℚ) ^ (1024 : ℕ) - (2 : ℚ) ^ (970 : ℕ) ≤ gridVal sig exp := by
  unfold IsFiniteAbs at h_not
  have hB_cast : ((( 2 ^ 54 - 1) * 2 ^ 970 : Nat) : ℚ)
      = (2 : ℚ) ^ (1024 : ℕ) - (2 : ℚ) ^ (970 : ℕ) := by
    push_cast
    rw [show (1024 : ℕ) = 54 + 970 from by grind, Rat.pow_add]
    grind
  by_cases hexp : exp ≥ 0
  · rw [decodedAbs_eq_decodedAbsAB_pos sign sig exp h_sig hexp] at h_not
    have hbound := overflow_bound_AB sign (sig * 10 ^ exp.toNat) 1
      (Nat.mul_pos (Nat.pos_of_ne_zero h_sig) (Nat.pow_pos (by omega))) (by omega) h_not
    -- gridVal sig exp = (sig · 10^exp.toNat : ℚ).
    have h_grid : gridVal sig exp = ((sig * 10 ^ exp.toNat : Nat) : ℚ) := by
      unfold gridVal
      push_cast
      rw [show (10 : ℚ) ^ exp = (10 : ℚ) ^ exp.toNat from by
            rw [← Rat.zpow_natCast]
            congr 1
            omega]
    rw [h_grid, ← hB_cast]
    exact_mod_cast (by omega : (2 ^ 54 - 1) * 2 ^ 970 ≤ sig * 10 ^ exp.toNat)
  · rw [decodedAbs_eq_decodedAbsAB_neg sign sig exp h_sig hexp] at h_not
    have hbound := overflow_bound_AB sign sig (10 ^ (-exp).toNat)
      (Nat.pos_of_ne_zero h_sig) (by (first | exact Rat.zpow_pos (by decide) | exact Rat.pow_pos (by decide) | exact Int.pow_nonneg (by omega) | exact Int.pow_pos (by omega) | exact Nat.pow_pos (by omega) | grind)) h_not
    -- gridVal sig exp · 10^(-exp).toNat = sig.
    have h_clear : gridVal sig exp * ((10 ^ (-exp).toNat : Nat) : ℚ) = (sig : ℚ) := by
      unfold gridVal
      push_cast
      rw [Rat.mul_assoc, show (10 : ℚ) ^ exp * (10 : ℚ) ^ ((-exp).toNat : ℕ) = 1 from by
            rw [← Rat.zpow_natCast, ← Rat.zpow_add (by grind : (10:ℚ) ≠ 0)]
            rw [show exp + ((-exp).toNat : ℤ) = 0 from by omega]
            rfl,
          mul_one]
    have h10_pos : (0 : ℚ) < ((10 ^ (-exp).toNat : Nat) : ℚ) := by
      have h := Nat.pow_pos (n := (-exp).toNat) (show 0 < 10 by omega)
      exact_mod_cast h
    have hbound_q : ((( 2 ^ 54 - 1) * 2 ^ 970 : Nat) : ℚ) * ((10 ^ (-exp).toNat : Nat) : ℚ)
        ≤ (sig : ℚ) := by
      rw [show ((( 2 ^ 54 - 1) * 2 ^ 970 : Nat) : ℚ) * ((10 ^ (-exp).toNat : Nat) : ℚ)
            = (((2 ^ 54 - 1) * 2 ^ 970 * 10 ^ (-exp).toNat : Nat) : ℚ) from by push_cast; grind]
      exact_mod_cast hbound
    rw [← hB_cast]
    rw [← h_clear] at hbound_q
    exact le_of_mul_le_mul_right hbound_q h10_pos

set_option maxRecDepth 4096 in
/-- **Boundary, finite side.** A decimal value carried by an `R_v`
membership witness is strictly below the threshold. -/
theorem gridVal_lt_bound_of_rv (s : Nat) (k : Int) (m : Nat) (q : Int)
    (hs : FinShape m q)
    (h_rv : inRoundingInterval s k m q (isIrregular m q) = true) :
    gridVal s k < (2 : ℚ) ^ (1024 : ℕ) - (2 : ℚ) ^ (970 : ℕ) := by
  have h2q := two_zpow_pos q
  have hX : (2 : ℚ) ^ q ≤ (2 : ℚ) ^ (971 : ℤ) :=
    zpow_le_zpow_right₀ (by grind) hs.q_le
  have hX_eq : (2 : ℚ) ^ (971 : ℤ) = (2 : ℚ) ^ (971 : ℕ) := by
    rw [← Rat.zpow_natCast]
    grind
  have hXpos : (0 : ℚ) < (2 : ℚ) ^ (971 : ℕ) := Rat.pow_pos (by decide)
  have h_pow_split : (2 : ℚ) ^ (1024 : ℕ) = (2 : ℚ) ^ (53 : ℕ) * (2 : ℚ) ^ (971 : ℕ) := by
    rw [← Rat.pow_add]
  have h_pow_split' : (2 : ℚ) ^ (971 : ℕ) = 2 * (2 : ℚ) ^ (970 : ℕ) := by
    rw [show (971 : ℕ) = 1 + 970 from rfl, Rat.pow_add]
    grind
  have hv_le : magVal m q ≤ ((2 : ℚ) ^ (53 : ℕ) - 1) * (2 : ℚ) ^ q := by
    unfold magVal
    have hm : (m : ℚ) ≤ (2 : ℚ) ^ (53 : ℕ) - 1 := by
      have h1 : m ≤ 2 ^ 53 - 1 := by have := hs.m_lt; omega
      have h2 : (m : ℚ) ≤ ((2 ^ 53 - 1 : Nat) : ℚ) := by exact_mod_cast h1
      have h3 : ((2 ^ 53 - 1 : Nat) : ℚ) = (2 : ℚ) ^ (53 : ℕ) - 1 := by
        have h1 : ((2 ^ 53 - 1 : Nat) : ℚ) + 1 = (2 : ℚ) ^ (53 : ℕ) := by
          rw [show (1:ℚ) = ((1 : Nat) : ℚ) from rfl, ← Rat.natCast_add,
              show (2 ^ 53 - 1 + 1 : Nat) = 2 ^ 53 from by omega, Rat.natCast_pow]
          rfl
        grind
      grind
    grind
  have h970pos : (0 : ℚ) < (2 : ℚ) ^ (970 : ℕ) := Rat.pow_pos (by decide)
  rcases rv_right_rat s k m q _ h_rv with h | ⟨h, heven⟩
  · -- Strict right bracket: 4u < 4v + 2·2^q ≤ (2^55 - 2)·2^971 = 4·bound.
    have h1 : 4 * magVal m q + 2 * (2 : ℚ) ^ q
        ≤ (4 * ((2 : ℚ) ^ (53 : ℕ) - 1) + 2) * (2 : ℚ) ^ q := by grind
    have h2 : (4 * ((2 : ℚ) ^ (53 : ℕ) - 1) + 2) * (2 : ℚ) ^ q
        ≤ (4 * ((2 : ℚ) ^ (53 : ℕ) - 1) + 2) * (2 : ℚ) ^ (971 : ℕ) := by
      rw [← hX_eq]
      grind
    have hkey : (4 * ((2 : ℚ) ^ (53 : ℕ) - 1) + 2) * (2 : ℚ) ^ (971 : ℕ)
        = 4 * ((2 : ℚ) ^ (1024 : ℕ) - (2 : ℚ) ^ (970 : ℕ)) := by
      rw [h_pow_split, h_pow_split']
      grind
    have hchain := lt_of_lt_of_le (lt_of_lt_of_le h h1) h2
    rw [hkey] at hchain
    exact Rat.lt_of_mul_lt_mul_left hchain (by grind : (0 : ℚ) ≤ 4)
  · -- Endpoint: m even, so m ≤ 2^53 - 2 and the bound tightens.
    have hm : (m : ℚ) ≤ (2 : ℚ) ^ (53 : ℕ) - 2 := by
      have h1 : m ≤ 2 ^ 53 - 2 := by
        have := hs.m_lt
        omega
      have h2 : (m : ℚ) ≤ ((2 ^ 53 - 2 : Nat) : ℚ) := by exact_mod_cast h1
      have h3 : ((2 ^ 53 - 2 : Nat) : ℚ) = (2 : ℚ) ^ (53 : ℕ) - 2 := by
        push_cast
        grind
      grind
    have hv_le' : magVal m q ≤ ((2 : ℚ) ^ (53 : ℕ) - 2) * (2 : ℚ) ^ q := by
      unfold magVal
      grind
    have h1 : 4 * magVal m q + 2 * (2 : ℚ) ^ q
        ≤ (4 * ((2 : ℚ) ^ (53 : ℕ) - 2) + 2) * (2 : ℚ) ^ q := by grind
    have h2 : (4 * ((2 : ℚ) ^ (53 : ℕ) - 2) + 2) * (2 : ℚ) ^ q
        ≤ (4 * ((2 : ℚ) ^ (53 : ℕ) - 2) + 2) * (2 : ℚ) ^ (971 : ℕ) := by
      rw [← hX_eq]
      have hcoef : (0 : ℚ) < 4 * ((2 : ℚ) ^ (53 : ℕ) - 2) + 2 := by (first | exact Rat.zpow_pos (by decide) | exact Rat.pow_pos (by decide) | exact Int.pow_nonneg (by omega) | exact Int.pow_pos (by omega) | exact Nat.pow_pos (by omega) | grind)
      grind
    have hkey : (4 * ((2 : ℚ) ^ (53 : ℕ) - 2) + 2) * (2 : ℚ) ^ (971 : ℕ)
        = 4 * (2 : ℚ) ^ (1024 : ℕ) - 12 * (2 : ℚ) ^ (970 : ℕ) := by
      rw [h_pow_split, h_pow_split']
      grind
    have hchain := le_trans (le_of_eq h) (le_trans h1 h2)
    rw [hkey] at hchain
    have hstep : 4 * (2 : ℚ) ^ (1024 : ℕ) - 12 * (2 : ℚ) ^ (970 : ℕ)
        < 4 * ((2 : ℚ) ^ (1024 : ℕ) - (2 : ℚ) ^ (970 : ℕ)) := by
      have h412 : 4 * (2 : ℚ) ^ (970 : ℕ) < 12 * (2 : ℚ) ^ (970 : ℕ) :=
        Rat.mul_lt_mul_of_pos_right (by grind) h970pos
      have := sub_lt_sub_left h412 (4 * (2 : ℚ) ^ (1024 : ℕ))
      calc 4 * (2 : ℚ) ^ (1024 : ℕ) - 12 * (2 : ℚ) ^ (970 : ℕ)
          < 4 * (2 : ℚ) ^ (1024 : ℕ) - 4 * (2 : ℚ) ^ (970 : ℕ) := this
      _ = 4 * ((2 : ℚ) ^ (1024 : ℕ) - (2 : ℚ) ^ (970 : ℕ)) := by grind
    exact Rat.lt_of_mul_lt_mul_left (lt_of_le_of_lt hchain hstep) (by grind : (0 : ℚ) ≤ 4)

/-! ## Float-level plumbing -/

theorem toRat_of_sig_zero (d : Decimal) (h : d.significand = 0) :
    Decimal.toRat d = 0 := by
  unfold Decimal.toRat
  rw [h]
  simp

/-- `decode` preserves mantissa parity: the implicit leading bit is even. -/
theorem decode_m_parity (w : UInt64) :
    (Word.decode w).m % 2 = Word.mantissa w % 2 := by
  unfold Word.decode
  by_cases he : Word.biasedExp w = 0
  · rw [if_pos he]
  · rw [if_neg he]
    simp only
    have h52 : (1 <<< 52 : Nat) = 2 ^ 52 := rfl
    omega

/-- `ofDecimal` of a finite-range decimal is bit-level finite. -/
theorem isFiniteBits_ofDecimal (d : Decimal)
    (h_fin : IsFiniteAbs d.sign d.significand d.exponent) :
    Word.isFinite (Clinger.ofDecimalBits d) = true := by
  have h_bridge := Clinger.decode_of_decimal_bridge_bits d h_fin
  have h_dec_q : (Word.decode (Clinger.ofDecimalBits d)).q ≤ 971 := by
    rw [h_bridge]
    exact h_fin
  unfold Word.isFinite
  by_cases he : Word.biasedExp (Clinger.ofDecimalBits d) = 0
  · simp [he]
  · have h_q_def : (Word.decode (Clinger.ofDecimalBits d)).q
        = (Word.biasedExp (Clinger.ofDecimalBits d) : Int) - 1023 - 52 := by
      unfold Word.decode
      rw [if_neg he]
    rw [h_q_def] at h_dec_q
    simp only [decide_eq_true_eq]
    omega

/-- On a zero significand, `ofDecimal` is the signed zero. -/
theorem ofDecimal_sig_zero (d : Decimal) (h : d.significand = 0) :
    Clinger.ofDecimalBits d = Word.pack d.sign 0 0 := by
  unfold Clinger.ofDecimalBits Clinger.decimalToFloatBits
  rw [h]
  rfl

/-- Same-sign distance reduction: `|wordVal w - toRat d|` is the
unsigned grid distance. -/
theorem floatVal_dist_reduce (d : Decimal) (w : UInt64)
    (h_sign : (Word.decode w).sign = d.sign) :
    |wordVal w - Decimal.toRat d|
      = |magVal (Word.decode w).m (Word.decode w).q - gridVal d.significand d.exponent| := by
  rw [abs_sub_comm]
  exact toRat_dist_eq_grid_dist d w h_sign.symm

/-- Opposite-sign distance: magnitudes add. -/
theorem floatVal_dist_opp (d : Decimal) (w : UInt64)
    (h_sign : (Word.decode w).sign ≠ d.sign) :
    |wordVal w - Decimal.toRat d|
      = magVal (Word.decode w).m (Word.decode w).q + gridVal d.significand d.exponent := by
  rw [floatVal_eq_signFactor_magVal, toRat_eq_signFactor_gridVal]
  have hmag := magVal_nonneg (Word.decode w).m (Word.decode w).q
  have hgrid := gridVal_nonneg d.significand d.exponent
  rcases Bool.eq_false_or_eq_true (Word.decode w).sign with hf | hf <;>
    rcases Bool.eq_false_or_eq_true d.sign with hd | hd
  · exact absurd (hf.trans hd.symm) h_sign
  · -- f negative, d positive: (-1)·mag - 1·u = -(mag + u) ≤ 0.
    rw [hf, hd]
    unfold signFactor
    rw [if_pos rfl, if_neg (by decide : ¬ ((false : Bool) = true))]
    rw [abs_of_nonpos (by grind)]
    grind
  · -- f positive, d negative: 1·mag - (-1)·u = mag + u ≥ 0.
    rw [hf, hd]
    unfold signFactor
    rw [if_neg (by decide : ¬ ((false : Bool) = true)), if_pos rfl]
    rw [abs_of_nonneg (by grind)]
    grind
  · exact absurd (hf.trans hd.symm) h_sign

/-- The rounded float is never farther from `u` than `u` is from zero. -/
theorem rv_dist_le_u (s : Nat) (k : Int) (m : Nat) (q : Int)
    (h_rv : inRoundingInterval s k m q (isIrregular m q) = true) :
    |magVal m q - gridVal s k| ≤ gridVal s k := by
  have hu0 := gridVal_nonneg s k
  by_cases hm : m = 0
  · subst hm
    rw [magVal_zero_eq, abs_of_nonpos (by grind)]
    grind
  · have h2q := two_zpow_pos q
    have hc_le : (if isIrregular m q then (1 : ℚ) else 2) * (2 : ℚ) ^ q
        ≤ 2 * (2 : ℚ) ^ q := by
      have : (if isIrregular m q then (1 : ℚ) else 2) ≤ 2 := by
        split <;> grind
      grind
    have hL : 4 * magVal m q - 2 * (2 : ℚ) ^ q ≤ 4 * gridVal s k := by
      rcases rv_left_rat s k m q _ h_rv with h | ⟨h, _⟩ <;> grind
    have hstep_le_v : (2 : ℚ) ^ q ≤ magVal m q := by
      unfold magVal
      have h1 : (1 : ℚ) ≤ (m : ℚ) := by
        exact_mod_cast Nat.pos_of_ne_zero hm
      have := Rat.mul_le_mul_of_nonneg_right h1 (Rat.le_of_lt (two_zpow_pos q))
      grind
    have hv0 := magVal_nonneg m q
    rw [abs_le]
    constructor <;> grind

/-! ## Backward direction: `ofDecimal` satisfies the reader spec -/

/-- In-range decimals: `ofDecimal` is the nearest float. -/
theorem ofDecimal_isNearestFloat (d : Decimal)
    (h_in : |Decimal.toRat d| < 2 ^ 1024 - 2 ^ 970) :
    IsNearestWord d (Clinger.ofDecimalBits d) := by
  by_cases h_sig : d.significand = 0
  · -- Signed zero.
    have h_eq := ofDecimal_sig_zero d h_sig
    obtain ⟨h_sb, h_be, h_mb⟩ :=
      pack_proj d.sign 0 0 (by grind) (by (first | exact Rat.zpow_pos (by decide) | exact Rat.pow_pos (by decide) | exact Int.pow_nonneg (by omega) | exact Int.pow_pos (by omega) | exact Nat.pow_pos (by omega) | grind)) 
    have h_toRat : Decimal.toRat d = 0 := toRat_of_sig_zero d h_sig
    have h_m0 : (Word.decode (Word.pack d.sign 0 0)).m = 0 := by
      unfold Word.decode
      rw [if_pos h_be]
      exact h_mb
    have h_fv : wordVal (Word.pack d.sign 0 0) = 0 := by
      unfold wordVal
      rw [h_m0, magVal_zero_eq, mul_zero]
    rw [h_eq]
    refine ⟨?_, h_sb, ?_, ?_⟩
    · unfold Word.isFinite
      rw [h_be]
      decide
    · intro v hg
      rw [h_fv, h_toRat]
      rw [show (0:ℚ) - 0 = 0 from by grind, abs_zero]
      exact abs_nonneg _
    · intro v hg h_ne h_eq'
      exfalso
      rw [h_fv] at h_ne h_eq'
      rw [h_toRat] at h_eq'
      simp only [sub_zero, abs_zero] at h_eq'
      exact h_ne (abs_eq_zero.mp h_eq')
  · -- Nonzero significand: in finite range by the boundary lemma.
    have h_fin : IsFiniteAbs d.sign d.significand d.exponent := by
      by_contra h_not
      have h_ge := bound_le_gridVal_of_not_finite d.sign d.significand d.exponent h_sig h_not
      rw [abs_toRat_eq_gridVal] at h_in
      exact absurd (lt_of_lt_of_le h_in h_ge) (lt_irrefl _)
    have h_finBits : Word.isFinite (Clinger.ofDecimalBits d) = true :=
      isFiniteBits_ofDecimal d h_fin
    have h_sign_f : (Word.decode (Clinger.ofDecimalBits d)).sign = d.sign := by
      rw [Clinger.decode_of_decimal_bridge_bits d h_fin]
      exact decodedAbs_sign d.sign d.significand d.exponent
    have h_rv := Clinger.ofDecimalBits_in_Rv d h_sig h_fin
    simp only at h_rv
    have h_shape_f := decode_finShape _ h_finBits
    have h_df := floatVal_dist_reduce d _ h_sign_f
    refine ⟨h_finBits, ?_, ?_, ?_⟩
    · rw [signBit_eq_decode_sign, h_sign_f]
    · -- nearest
      intro v hg
      rw [h_df]
      by_cases hgs : (Word.decode v).sign = d.sign
      · rw [floatVal_dist_reduce d v hgs]
        exact rv_nearest_mag _ _ _ _ _ _ h_shape_f (decode_finShape v hg) h_rv
      · rw [floatVal_dist_opp d v hgs]
        have h1 := rv_dist_le_u _ _ _ _ h_rv
        have h2 := magVal_nonneg (Word.decode v).m (Word.decode v).q
        grind
    · -- ties to even
      intro v hg h_ne h_eq'
      rw [← decode_m_parity]
      by_cases hgs : (Word.decode v).sign = d.sign
      · rw [h_df, floatVal_dist_reduce d v hgs] at h_eq'
        have h_mag_ne : magVal (Word.decode v).m (Word.decode v).q
            ≠ magVal (Word.decode (Clinger.ofDecimalBits d)).m (Word.decode (Clinger.ofDecimalBits d)).q := by
          intro hmm
          apply h_ne
          rw [floatVal_eq_signFactor_magVal, floatVal_eq_signFactor_magVal,
              hgs, h_sign_f, hmm]
        exact rv_tie_even_mag _ _ _ _ _ _ h_shape_f (decode_finShape v hg) h_rv h_mag_ne h_eq'
      · -- Opposite-sign exact tie: impossible.
        exfalso
        rw [h_df, floatVal_dist_opp d v hgs] at h_eq'
        have h1 := rv_dist_le_u _ _ _ _ h_rv
        have h2 := magVal_nonneg (Word.decode v).m (Word.decode v).q
        have hu0 := gridVal_nonneg d.significand d.exponent
        -- The tie forces mag_g = 0 and |v - u| = u.
        have h_magg : magVal (Word.decode v).m (Word.decode v).q = 0 := by grind
        have h_fvg : wordVal v = 0 := by
          rw [floatVal_eq_signFactor_magVal, h_magg, mul_zero]
        set mval := magVal (Word.decode (Clinger.ofDecimalBits d)).m (Word.decode (Clinger.ofDecimalBits d)).q
          with hmval
        set u := gridVal d.significand d.exponent with hu
        have h_dist_u : |mval - u| = u := by grind
        -- wordVal w ≠ 0, so mval ≠ 0 and m_f ≥ 1.
        have h_v_ne : mval ≠ 0 := by
          intro hmval0
          apply h_ne
          rw [h_fvg, floatVal_eq_signFactor_magVal, ← hmval, hmval0, mul_zero]
        have h_v_pos : 0 < mval := lt_of_le_of_ne (hmval ▸ magVal_nonneg _ _) (Ne.symm h_v_ne)
        -- |mval - u| = u with mval > 0 forces mval = 2u.
        have h_v2u : mval = 2 * u := by
          rcases abs_cases (mval - u) with ⟨habs, _⟩ | ⟨habs, _⟩
          · grind
          · have : u - mval = u := by grind
            grind
        -- The left endpoint analysis kills every branch.
        have hm_pos : (Word.decode (Clinger.ofDecimalBits d)).m ≠ 0 := by
          intro h0
          rw [hmval, h0, magVal_zero_eq] at h_v_pos
          exact lt_irrefl _ h_v_pos
        have h2q := two_zpow_pos (Word.decode (Clinger.ofDecimalBits d)).q
        have h_m_ge1 : (1 : ℚ) ≤ ((Word.decode (Clinger.ofDecimalBits d)).m : ℚ) := by
          exact_mod_cast Nat.pos_of_ne_zero hm_pos
        have h_v_ge : (2 : ℚ) ^ (Word.decode (Clinger.ofDecimalBits d)).q ≤ mval := by
          rw [hmval]
          unfold magVal
          have := Rat.mul_le_mul_of_nonneg_right h_m_ge1
            (Rat.le_of_lt h2q)
          grind
        rcases rv_left_rat d.significand d.exponent _ _ _ h_rv with h | ⟨h, heven⟩
        · -- Strict: 4mval - c·2^q < 4u = 2mval gives mval < 2^q, i.e. m < 1.
          have hc_le : (if isIrregular (Word.decode (Clinger.ofDecimalBits d)).m
                (Word.decode (Clinger.ofDecimalBits d)).q then (1 : ℚ) else 2)
                * (2 : ℚ) ^ (Word.decode (Clinger.ofDecimalBits d)).q
              ≤ 2 * (2 : ℚ) ^ (Word.decode (Clinger.ofDecimalBits d)).q := by
            have : (if isIrregular (Word.decode (Clinger.ofDecimalBits d)).m
                (Word.decode (Clinger.ofDecimalBits d)).q then (1 : ℚ) else 2) ≤ 2 := by
              split <;> grind
            grind
          rw [← hmval, ← hu] at h
          grind
        · -- Endpoint: 2mval = c·2^q with c ∈ {1, 2}; c = 2 gives m = 1, odd;
          -- c = 1 gives 2m = 1, impossible.
          rw [← hmval, ← hu] at h
          by_cases hirr : isIrregular (Word.decode (Clinger.ofDecimalBits d)).m
              (Word.decode (Clinger.ofDecimalBits d)).q = true
          · rw [if_pos hirr] at h
            -- 2mval = 2^q: 2m·2^q = 2^q so 2m = 1.
            have h2m : 2 * ((Word.decode (Clinger.ofDecimalBits d)).m : ℚ) = 1 := by
              have hveq : 2 * mval = (2 : ℚ) ^ (Word.decode (Clinger.ofDecimalBits d)).q := by
                grind
              rw [hmval] at hveq
              unfold magVal at hveq
              have hcanc := (mul_left_inj' (a := 2 * ((Word.decode (Clinger.ofDecimalBits d)).m : ℚ))
                  (b := 1) (Rat.ne_of_gt h2q)).mp
                (by grind : 2 * ((Word.decode (Clinger.ofDecimalBits d)).m : ℚ)
                    * (2 : ℚ) ^ (Word.decode (Clinger.ofDecimalBits d)).q
                  = 1 * (2 : ℚ) ^ (Word.decode (Clinger.ofDecimalBits d)).q)
              grind
            have : (2 * (Word.decode (Clinger.ofDecimalBits d)).m : ℚ) = 1 := by
              grind
            have hnat : 2 * (Word.decode (Clinger.ofDecimalBits d)).m = 1 := by
              exact_mod_cast this
            omega
          · rw [if_neg hirr] at h
            -- 2mval = 2·2^q: m = 1, but the endpoint demands m even.
            have hveq : mval = (2 : ℚ) ^ (Word.decode (Clinger.ofDecimalBits d)).q := by
              grind
            have hm1 : ((Word.decode (Clinger.ofDecimalBits d)).m : ℚ) = 1 := by
              rw [hmval] at hveq
              unfold magVal at hveq
              have hcanc := (mul_left_inj' (a := ((Word.decode (Clinger.ofDecimalBits d)).m : ℚ))
                  (b := 1) (Rat.ne_of_gt h2q)).mp
                (by grind : ((Word.decode (Clinger.ofDecimalBits d)).m : ℚ)
                    * (2 : ℚ) ^ (Word.decode (Clinger.ofDecimalBits d)).q
                  = 1 * (2 : ℚ) ^ (Word.decode (Clinger.ofDecimalBits d)).q)
              grind
            have hnat : (Word.decode (Clinger.ofDecimalBits d)).m = 1 := by exact_mod_cast hm1
            omega

/-- Out-of-range decimals: `ofDecimal` is exactly the signed-infinity
bit pattern. -/
theorem ofDecimal_overflow_eq (d : Decimal)
    (h_out : (2 : ℚ) ^ 1024 - 2 ^ 970 ≤ |Decimal.toRat d|) :
    Clinger.ofDecimalBits d = Word.pack d.sign 2047 0 := by
  have hBpos : (0 : ℚ) < 2 ^ 1024 - 2 ^ 970 :=
    sub_pos.mpr (rat_pow_lt_pow_right (show (1 : ℚ) < 2 by grind)
      (show (970 : ℕ) < 1024 by grind))
  have h_sig : d.significand ≠ 0 := by
    intro h0
    rw [toRat_of_sig_zero d h0] at h_out
    simp only [abs_zero] at h_out
    exact absurd (lt_of_lt_of_le hBpos h_out) (lt_irrefl _)
  have h_not : ¬ IsFiniteAbs d.sign d.significand d.exponent := by
    intro h_fin
    have h_rv := Clinger.ofDecimalBits_in_Rv d h_sig h_fin
    simp only at h_rv
    have h_fb := isFiniteBits_ofDecimal d h_fin
    have h_lt := gridVal_lt_bound_of_rv _ _ _ _ (decode_finShape _ h_fb) h_rv
    rw [abs_toRat_eq_gridVal] at h_out
    exact absurd (lt_of_lt_of_le h_lt h_out) (lt_irrefl _)
  exact Clinger.decimalToFloatBits_overflow_inf d.sign d.significand d.exponent h_sig h_not

/-- Out-of-range decimals: `ofDecimal` is the signed infinity. -/
theorem ofDecimal_overflow (d : Decimal)
    (h_out : (2 : ℚ) ^ 1024 - 2 ^ 970 ≤ |Decimal.toRat d|) :
    Word.isInf (Clinger.ofDecimalBits d) = true ∧ Word.signBit (Clinger.ofDecimalBits d) = d.sign := by
  obtain ⟨h_sb, h_be, h_mb⟩ :=
    pack_proj d.sign 2047 0 (by grind) (by (first | exact Rat.zpow_pos (by decide) | exact Rat.pow_pos (by decide) | exact Int.pow_nonneg (by omega) | exact Int.pow_pos (by omega) | exact Nat.pow_pos (by omega) | grind))
  rw [ofDecimal_overflow_eq d h_out]
  constructor
  · unfold Word.isInf
    rw [h_be, h_mb]
    decide
  · exact h_sb

/-- **`Clinger.ofDecimal` is a correct reader.** -/
theorem isCorrectReader_ofDecimal : IsCorrectReaderBits Clinger.ofDecimalBits :=
  fun d => ⟨ofDecimal_isNearestFloat d, ofDecimal_overflow d⟩

/-! ## Forward direction: the spec pins the bits down -/

/-- Every finite shape is realized by a float of either sign. -/
theorem exists_float_of_finShape (sign : Bool) (m : Nat) (q : Int)
    (hs : FinShape m q) :
    ∃ v : UInt64, Word.isFinite v = true ∧ (Word.decode v).sign = sign
      ∧ (Word.decode v).m = m ∧ (Word.decode v).q = q := by
  by_cases hm : m < 2 ^ 52
  · -- Subnormal or zero: biased exponent 0.
    have hq : q = -1074 := hs.q_eq_of_small hm
    obtain ⟨h_sb, h_be, h_mb⟩ := pack_proj sign 0 m (by grind) hm
    refine ⟨Word.pack sign 0 m, ?_, ?_, ?_, ?_⟩
    · unfold Word.isFinite
      rw [h_be]
      decide
    · rw [← signBit_eq_decode_sign]
      exact h_sb
    · unfold Word.decode
      rw [if_pos h_be]
      exact h_mb
    · unfold Word.decode
      rw [if_pos h_be, hq]
  · -- Normal: biased exponent q + 1075.
    have hm_ge : 2 ^ 52 ≤ m := by omega
    have hm_lt : m < 2 ^ 53 := hs.m_lt
    have hq_ge := hs.q_ge
    have hq_le := hs.q_le
    set be : Nat := (q + 1075).toNat with hbe_def
    have hbe_val : (be : Int) = q + 1075 := Int.toNat_of_nonneg (by omega)
    have hbe_lt : be < 2048 := by omega
    have hbe_ne : be ≠ 0 := by omega
    have hmb_lt : m - 2 ^ 52 < 2 ^ 52 := by omega
    have h_nan : be = 2047 → m - 2 ^ 52 = 0 := by
      intro h2047
      exfalso
      omega
    obtain ⟨h_sb, h_be, h_mb⟩ := pack_proj sign be (m - 2 ^ 52) hbe_lt hmb_lt
    have h_be_ne : ¬ (Word.biasedExp (Word.pack sign be (m - 2 ^ 52)) = 0) := by
      rw [h_be]
      exact hbe_ne
    refine ⟨Word.pack sign be (m - 2 ^ 52), ?_, ?_, ?_, ?_⟩
    · unfold Word.isFinite
      rw [h_be]
      simp only [decide_eq_true_eq]
      omega
    · rw [← signBit_eq_decode_sign]
      exact h_sb
    · unfold Word.decode
      rw [if_neg h_be_ne]
      simp only
      rw [h_mb]
      have h52 : (1 <<< 52 : Nat) = 2 ^ 52 := rfl
      omega
    · unfold Word.decode
      rw [if_neg h_be_ne]
      simp only
      rw [h_be]
      omega

set_option exponentiation.threshold 2048 in
/-- The immediate grid successor: one step `2^q` up from a finite shape
is again a finite-shape value, provided some legal value lies above. -/
theorem succ_finShape (m : Nat) (q : Int) (m' : Nat) (q' : Int)
    (hs : FinShape m q) (hleg' : LegalIEEE m' q')
    (h_lt : magVal m q < magVal m' q') :
    ∃ (ms : Nat) (qs : Int), FinShape ms qs
      ∧ magVal ms qs = magVal m q + (2 : ℚ) ^ q := by
  by_cases hm1 : m + 1 < 2 ^ 53
  · refine ⟨m + 1, q, ?_, ?_⟩
    · rcases hs with ⟨rfl, rfl⟩ | (⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩)
      · exact Or.inr (Or.inl ⟨by omega, by grind, rfl⟩)
      · by_cases h52 : m + 1 < 2 ^ 52
        · exact Or.inr (Or.inl ⟨by omega, h52, h3⟩)
        · exact Or.inr (Or.inr ⟨by omega, by omega, by omega, by omega⟩)
      · exact Or.inr (Or.inr ⟨by omega, hm1, h3, h4⟩)
    · unfold magVal
      push_cast
      grind
  · -- m + 1 = 2^53: renormalise into the next binade.
    have hm_lt := hs.m_lt
    have hm_eq : m + 1 = 2 ^ 53 := by omega
    have hm_cast : ((m : ℚ)) + 1 = 2 ^ (53 : ℕ) := by
      have h1 : ((m + 1 : Nat) : ℚ) = ((2 ^ 53 : Nat) : ℚ) := by rw [hm_eq]
      push_cast at h1
      grind
    have h_val_id : magVal m q + (2 : ℚ) ^ q
        = ((2 ^ 52 : Nat) : ℚ) * (2 : ℚ) ^ (q + 1) := by
      unfold magVal
      rw [Rat.zpow_add (by grind : (2 : ℚ) ≠ 0), Rat.zpow_one]
      push_cast
      have hm' : (m : ℚ) = 2 ^ (53 : ℕ) - 1 := by grind
      rw [hm', show (2 : ℚ) ^ (53 : ℕ) = 2 ^ (52 : ℕ) * 2 from by grind]
      grind
    have hgap := magVal_gap_up m m' q q' hs (Or.inr hleg') h_lt
    have hq1_le : q + 1 ≤ 971 := by
      by_contra hgt
      -- Then v + 2^q = 2^52·2^(q+1) ≥ 2^52·2^972 = 2^1024 exceeds every legal value.
      have h972 : (2 : ℚ) ^ (972 : ℤ) ≤ (2 : ℚ) ^ (q + 1) :=
        zpow_le_zpow_right₀ (by grind) (by omega)
      have h_v'_lt : magVal m' q' < ((2 ^ 53 : Nat) : ℚ) * (2 : ℚ) ^ (971 : ℤ) := by
        unfold magVal
        have hm'_lt : (m' : ℚ) < ((2 ^ 53 : Nat) : ℚ) := by
          have : m' < 2 ^ 53 := by
            rcases hleg' with ⟨_, h, _⟩ | ⟨_, h, _⟩ <;> omega
          exact_mod_cast this
        have hq'_le : (2 : ℚ) ^ q' ≤ (2 : ℚ) ^ (971 : ℤ) :=
          zpow_le_zpow_right₀ (by grind) (by
            rcases hleg' with ⟨_, _, hqe⟩ | ⟨_, _, _, hle⟩ <;> omega)
        have h2_971 := two_zpow_pos (971 : ℤ)
        calc (m' : ℚ) * (2 : ℚ) ^ q' ≤ (m' : ℚ) * (2 : ℚ) ^ (971 : ℤ) :=
              Rat.mul_le_mul_of_nonneg_left hq'_le (Rat.natCast_nonneg)
        _ < ((2 ^ 53 : Nat) : ℚ) * (2 : ℚ) ^ (971 : ℤ) :=
              Rat.mul_lt_mul_of_pos_right hm'_lt h2_971
      have h_id : ((2 ^ 53 : Nat) : ℚ) * (2 : ℚ) ^ (971 : ℤ)
          = ((2 ^ 52 : Nat) : ℚ) * (2 : ℚ) ^ (972 : ℤ) := by
        rw [show (972 : ℤ) = 971 + 1 from rfl, Rat.zpow_add (by grind : (2 : ℚ) ≠ 0),
            Rat.zpow_one]
        push_cast
        grind
      have h_52_pos : (0 : ℚ) < ((2 ^ 52 : Nat) : ℚ) := by (first | exact Rat.zpow_pos (by decide) | exact Rat.pow_pos (by decide) | exact Int.pow_nonneg (by omega) | exact Int.pow_pos (by omega) | exact Nat.pow_pos (by omega) | grind)
      have h_chain : magVal m' q' < magVal m q + (2 : ℚ) ^ q := by
        rw [h_val_id]
        calc magVal m' q' < ((2 ^ 53 : Nat) : ℚ) * (2 : ℚ) ^ (971 : ℤ) := h_v'_lt
        _ = ((2 ^ 52 : Nat) : ℚ) * (2 : ℚ) ^ (972 : ℤ) := h_id
        _ ≤ ((2 ^ 52 : Nat) : ℚ) * (2 : ℚ) ^ (q + 1) :=
              Rat.mul_le_mul_of_nonneg_left h972 (le_of_lt h_52_pos)
      grind
    refine ⟨2 ^ 52, q + 1,
      Or.inr (Or.inr ⟨Nat.le_refl _, by grind, by have := hs.q_ge; omega, hq1_le⟩), ?_⟩
    rw [h_val_id]
    rfl

/-- Two spec-satisfying floats at the same in-range decimal carry the
same value: a genuine two-sided tie would demand even mantissas on two
grid-adjacent magnitudes, which alternate parity. -/
private theorem tie_values_eq (d : Decimal) (wf wg : UInt64)
    (hfF : Word.isFinite wf = true) (hgF : Word.isFinite wg = true)
    (hfs' : (Word.decode wf).sign = d.sign) (hgs' : (Word.decode wg).sign = d.sign)
    (hf_near : ∀ v' : UInt64, Word.isFinite v' = true →
       |wordVal wf - Decimal.toRat d| ≤ |wordVal v' - Decimal.toRat d|)
    (hg_near : ∀ v' : UInt64, Word.isFinite v' = true →
       |wordVal wg - Decimal.toRat d| ≤ |wordVal v' - Decimal.toRat d|)
    (hf_even : Word.mantissa wf % 2 = 0) (hg_even : Word.mantissa wg % 2 = 0)
    (h_dist : |wordVal wg - Decimal.toRat d| = |wordVal wf - Decimal.toRat d|) :
    wordVal wg = wordVal wf := by
  by_contra h_val
  have h_shape_f := decode_finShape wf hfF
  have h_shape_g := decode_finShape wg hgF
  have h_mf_even : (Word.decode wf).m % 2 = 0 := by rw [decode_m_parity]; exact hf_even
  have h_mg_even : (Word.decode wg).m % 2 = 0 := by rw [decode_m_parity]; exact hg_even
  set u := gridVal d.significand d.exponent with hu
  set v := magVal (Word.decode wf).m (Word.decode wf).q with hv
  set w := magVal (Word.decode wg).m (Word.decode wg).q with hw
  have h_dist' : |w - u| = |v - u| := by
    rw [floatVal_dist_reduce d wg hgs', floatVal_dist_reduce d wf hfs'] at h_dist
    exact h_dist
  have h_mag_ne : w ≠ v := by
    intro hmm
    apply h_val
    rw [floatVal_eq_signFactor_magVal, floatVal_eq_signFactor_magVal, hgs', hfs',
        ← hv, ← hw, hmm]
  rcases Rat.lt_trichotomy w v with hwv | hwv | hwv
  · -- w < v: u is the exact midpoint; g's successor breaks the tie.
    have h2u : 2 * u = w + v := by
      rw [abs_sub_comm w u, abs_sub_comm v u] at h_dist'
      exact (abs_eq_abs_iff_two_eq u w v hwv).mp h_dist'
    have h_mf_ne : (Word.decode wf).m ≠ 0 := by
      intro h0
      have : v = 0 := by rw [hv, h0]; exact magVal_zero_eq _
      have := hw ▸ magVal_nonneg (Word.decode wg).m (Word.decode wg).q
      grind
    obtain ⟨ms, qs, hss, hsval⟩ := succ_finShape (Word.decode wg).m (Word.decode wg).q
      (Word.decode wf).m (Word.decode wf).q h_shape_g (h_shape_f.legal_of_ne h_mf_ne) (hw ▸ hv ▸ hwv)
    have h_le : magVal ms qs ≤ v := by
      rw [hsval]
      exact hv ▸ magVal_gap_up (Word.decode wg).m (Word.decode wf).m (Word.decode wg).q (Word.decode wf).q
        h_shape_g h_shape_f (hw ▸ hv ▸ hwv)
    have h2qg := two_zpow_pos (Word.decode wg).q
    rcases Rat.eq_or_lt_of_le h_le with h_eq | h_lt
    · -- Exactly the successor: parity alternation contradicts both-even.
      have h_parity := magVal_succ_parity (Word.decode wg).m (Word.decode wf).m
        (Word.decode wg).q (Word.decode wf).q h_shape_g (h_shape_f.legal_of_ne h_mf_ne)
        (by rw [← hsval, h_eq, hv])
      omega
    · -- Strictly between w and v: strictly closer to u than the tie distance.
      obtain ⟨g₂, hg₂F, hg₂s, hg₂m, hg₂q⟩ := exists_float_of_finShape d.sign ms qs hss
      have h_w_le_u : w ≤ u := by grind
      have h_dist_g : |wordVal wg - Decimal.toRat d| = u - w := by
        rw [floatVal_dist_reduce d wg hgs', ← hw, ← hu,
            abs_of_nonpos (by grind : w - u ≤ 0)]
        grind
      have h_dist_g₂ : |wordVal g₂ - Decimal.toRat d| < u - w := by
        rw [floatVal_dist_reduce d g₂ hg₂s, hg₂m, hg₂q, ← hu]
        have h_s_gt : w < magVal ms qs := by
          rw [hsval, ← hw]
          grind
        rcases abs_cases (magVal ms qs - u) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
          · rw [h1]
            grind
      have := hg_near g₂ hg₂F
      rw [h_dist_g] at this
      exact absurd (lt_of_le_of_lt this h_dist_g₂) (lt_irrefl _)
  · exact h_mag_ne hwv
  · -- v < w: mirror image, using f's successor and f's minimality.
    have h2u : 2 * u = v + w := by
      rw [abs_sub_comm w u, abs_sub_comm v u] at h_dist'
      exact (abs_eq_abs_iff_two_eq u v w hwv).mp h_dist'.symm
    have h_mg_ne : (Word.decode wg).m ≠ 0 := by
      intro h0
      have : w = 0 := by rw [hw, h0]; exact magVal_zero_eq _
      have := hv ▸ magVal_nonneg (Word.decode wf).m (Word.decode wf).q
      grind
    obtain ⟨ms, qs, hss, hsval⟩ := succ_finShape (Word.decode wf).m (Word.decode wf).q
      (Word.decode wg).m (Word.decode wg).q h_shape_f (h_shape_g.legal_of_ne h_mg_ne) (hv ▸ hw ▸ hwv)
    have h_le : magVal ms qs ≤ w := by
      rw [hsval]
      exact hw ▸ magVal_gap_up (Word.decode wf).m (Word.decode wg).m (Word.decode wf).q (Word.decode wg).q
        h_shape_f h_shape_g (hv ▸ hw ▸ hwv)
    have h2qf := two_zpow_pos (Word.decode wf).q
    rcases Rat.eq_or_lt_of_le h_le with h_eq | h_lt
    · have h_parity := magVal_succ_parity (Word.decode wf).m (Word.decode wg).m
        (Word.decode wf).q (Word.decode wg).q h_shape_f (h_shape_g.legal_of_ne h_mg_ne)
        (by rw [← hsval, h_eq, hw])
      omega
    · obtain ⟨g₂, hg₂F, hg₂s, hg₂m, hg₂q⟩ := exists_float_of_finShape d.sign ms qs hss
      have h_v_le_u : v ≤ u := by grind
      have h_dist_f : |wordVal wf - Decimal.toRat d| = u - v := by
        rw [floatVal_dist_reduce d wf hfs', ← hv, ← hu,
            abs_of_nonpos (by grind : v - u ≤ 0)]
        grind
      have h_dist_g₂ : |wordVal g₂ - Decimal.toRat d| < u - v := by
        rw [floatVal_dist_reduce d g₂ hg₂s, hg₂m, hg₂q, ← hu]
        have h_s_gt : v < magVal ms qs := by
          rw [hsval, ← hv]
          grind
        rcases abs_cases (magVal ms qs - u) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
          · rw [h1]
            grind
      have := hf_near g₂ hg₂F
      rw [h_dist_f] at this
      exact absurd (lt_of_le_of_lt this h_dist_g₂) (lt_irrefl _)

/-- **Forward direction.** A float satisfying the reader spec at `d` has
exactly `ofDecimal d`'s bits. -/
theorem spec_toBits_eq (d : Decimal) (v : UInt64)
    (h_near : |Decimal.toRat d| < 2 ^ 1024 - 2 ^ 970 → IsNearestWord d v)
    (h_over : (2 : ℚ) ^ 1024 - 2 ^ 970 ≤ |Decimal.toRat d| →
       Word.isInf v = true ∧ Word.signBit v = d.sign) :
    v = Clinger.ofDecimalBits d := by
  rcases lt_or_ge |Decimal.toRat d| ((2 : ℚ) ^ 1024 - 2 ^ 970) with h_in | h_out
  · -- In range: both are nearest floats, tie analysis forces equal values.
    obtain ⟨hgF, hgs, hg_near, hg_tie⟩ := h_near h_in
    obtain ⟨hfF, hfs, hf_near, hf_tie⟩ := ofDecimal_isNearestFloat d h_in
    have hgs' : (Word.decode v).sign = d.sign := by
      rw [← signBit_eq_decode_sign]; exact hgs
    have hfs' : (Word.decode (Clinger.ofDecimalBits d)).sign = d.sign := by
      rw [← signBit_eq_decode_sign]; exact hfs
    have h_dist : |wordVal v - Decimal.toRat d|
        = |wordVal (Clinger.ofDecimalBits d) - Decimal.toRat d| :=
      Rat.le_antisymm (hg_near _ hfF) (hf_near v hgF)
    have h_val : wordVal v = wordVal (Clinger.ofDecimalBits d) := by
      by_cases h : wordVal v = wordVal (Clinger.ofDecimalBits d)
      · exact h
      · -- An exact two-sided tie: both tie clauses fire.
        have h_mg_even : Word.mantissa v % 2 = 0 :=
          hg_tie _ hfF (fun hh => h hh.symm) h_dist.symm
        have h_mf_even : Word.mantissa (Clinger.ofDecimalBits d) % 2 = 0 :=
          hf_tie v hgF h h_dist
        exact tie_values_eq d (Clinger.ofDecimalBits d) v hfF hgF hfs' hgs'
          hf_near hg_near h_mf_even h_mg_even h_dist
    -- Equal values, equal signs: identical decode, identical bits.
    have h_mag : magVal (Word.decode v).m (Word.decode v).q
        = magVal (Word.decode (Clinger.ofDecimalBits d)).m (Word.decode (Clinger.ofDecimalBits d)).q := by
      rw [floatVal_eq_signFactor_magVal, floatVal_eq_signFactor_magVal,
          hgs', hfs'] at h_val
      have hsf : signFactor d.sign ≠ 0 := by
        unfold signFactor
        split <;> grind
      exact mul_left_cancel₀ hsf h_val
    obtain ⟨hm_eq, hq_eq⟩ := magVal_inj _ _ _ _ (decode_finShape v hgF)
      (decode_finShape _ hfF) h_mag
    exact toBits_eq_of_decode_eq v _ hgF hfF (hgs.trans hfs.symm) hm_eq hq_eq
  · -- Overflow: both are the signed-infinity pattern.
    obtain ⟨hg_inf, hg_sb⟩ := h_over h_out
    have hg_fields : Word.biasedExp v = 2047 ∧ Word.mantissa v = 0 := by
      unfold Word.isInf at hg_inf
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hg_inf
      exact hg_inf
    have hg_nan : Word.isNaN v = false := by
      unfold Word.isNaN
      rw [hg_fields.2]
      simp
    have h1 := pack_decode_eq v hg_nan
    rw [hg_sb, hg_fields.1, hg_fields.2] at h1
    rw [ofDecimal_overflow_eq d h_out]
    exact h1.symm

/-- The reader spec transports along bit equality. -/
private theorem isNearestFloat_congr_bits (d : Decimal) (w₁ w₂ : UInt64)
    (h : w₂ = w₁) (h₁ : IsNearestWord d w₁) :
    IsNearestWord d w₂ := by
  have hfv : wordVal w₂ = wordVal w₁ := by rw [h]
  have hsb : Word.signBit w₂ = Word.signBit w₁ := by rw [h]
  have hfin : Word.isFinite w₂ = Word.isFinite w₁ := by rw [h]
  have hmb : Word.mantissa w₂ = Word.mantissa w₁ := by rw [h]
  obtain ⟨c1, c2, c3, c4⟩ := h₁
  refine ⟨hfin ▸ c1, hsb ▸ c2, ?_, ?_⟩
  · intro g' hg'
    rw [hfv]
    exact c3 g' hg'
  · intro g' hg' h_ne h_eq
    rw [hfv] at h_ne h_eq
    rw [hmb]
    exact c4 g' hg' h_ne h_eq

/-- **The reader correctness theorem, internal form.** A function
satisfies the round-to-nearest reader spec iff it agrees with
`Clinger.ofDecimal` on every decimal, bit for bit. -/
theorem correct_iff_ofDecimal_proof (p : Decimal → UInt64) :
    IsCorrectReaderBits p
      ↔ ∀ d : Decimal, p d = Clinger.ofDecimalBits d := by
  constructor
  · intro h d
    exact spec_toBits_eq d (p d) (h d).1 (h d).2
  · intro h d
    refine ⟨?_, ?_⟩
    · intro h_in
      exact isNearestFloat_congr_bits d (Clinger.ofDecimalBits d) (p d) (h d)
        (ofDecimal_isNearestFloat d h_in)
    · intro h_out
      obtain ⟨hf_inf, hf_sb⟩ := ofDecimal_overflow d h_out
      have hb := h d
      constructor
      · rw [show Word.isInf (p d) = Word.isInf (Clinger.ofDecimalBits d) from by rw [hb]]
        exact hf_inf
      · rw [show Word.signBit (p d) = Word.signBit (Clinger.ofDecimalBits d) from by rw [hb]]
        exact hf_sb

end Srtfp.Clinger

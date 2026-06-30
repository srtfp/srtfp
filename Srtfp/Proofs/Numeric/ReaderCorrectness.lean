/- Reader correctness: `Clinger.ofDecimal` is THE round-to-nearest,
   ties-to-even `Decimal → Float` reader.

   Public statement: `PP.Numeric.Spec.correct_iff_ofDecimal`
   (`PP/Numeric/Correctness.lean`); internal vocabulary
   (`IsNearestFloat`, `IsCorrectReader`) in `CorrectnessSpec.lean`.

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
     `decimalToFloat_overflow_inf`; zeros via `fromBits_proj`. -/

import Srtfp.Proofs.Numeric.CorrectnessSpec
import Srtfp.Proofs.Numeric.RoundTrip
import Srtfp.Proofs.Numeric.Schubfach.TieBreak

namespace PP.Numeric.Clinger

open PP.Numeric.Float
open PP.Numeric.Schubfach
open PP.Numeric

/-! ## Finite decode shapes

`decode` of a finite float is either the zero pair `(0, -1074)` or a
`LegalIEEE` pair. -/

/-- The `(m, q)` shapes `decode` produces on finite floats. -/
def FinShape (m : Nat) (q : Int) : Prop :=
  (m = 0 ∧ q = -1074) ∨ LegalIEEE m q

theorem finShape_zero : FinShape 0 (-1074) := Or.inl ⟨rfl, rfl⟩

theorem FinShape.m_lt (h : FinShape m q) : m < 2 ^ 53 := by
  rcases h with ⟨rfl, rfl⟩ | h | h <;> omega

theorem FinShape.q_ge (h : FinShape m q) : -1074 ≤ q := by
  rcases h with ⟨rfl, rfl⟩ | h | h <;> omega

theorem FinShape.q_le (h : FinShape m q) : q ≤ 971 := by
  rcases h with ⟨rfl, rfl⟩ | h | h <;> omega

/-- A nonzero shape is legal. -/
theorem FinShape.legal_of_ne (h : FinShape m q) (hm : m ≠ 0) : LegalIEEE m q := by
  rcases h with ⟨rfl, rfl⟩ | h
  · exact absurd rfl hm
  · exact h

/-- Small `m` in a shape forces the subnormal exponent. -/
theorem FinShape.q_eq_of_small (h : FinShape m q) (hm : m < 2 ^ 52) : q = -1074 := by
  rcases h with ⟨rfl, rfl⟩ | h | h
  · rfl
  · omega
  · omega

/-- `decode` of a finite float has a `FinShape`. -/
theorem decode_finShape (g : _root_.Float) (h_fin : isFiniteBits g = true) :
    FinShape (decode g).m (decode g).q := by
  by_cases hm : (decode g).m = 0
  · left
    refine ⟨hm, ?_⟩
    -- m = 0 forces the subnormal branch of decode.
    unfold decode at hm ⊢
    by_cases he : biasedExpBits g = 0
    · rw [if_pos he]
    · rw [if_neg he] at hm
      simp only at hm
      omega
  · exact Or.inr (decode_legalIEEE g h_fin hm)

/-! ## Grid geometry in ℚ -/

private theorem two_zpow_pos (q : Int) : (0 : ℚ) < (2 : ℚ) ^ q :=
  zpow_pos (by norm_num) q

theorem magVal_nonneg (m : Nat) (q : Int) : (0 : ℚ) ≤ magVal m q :=
  mul_nonneg (Nat.cast_nonneg m) (le_of_lt (two_zpow_pos q))

theorem magVal_zero_eq (q : Int) : magVal 0 q = 0 := by
  unfold magVal; simp

/-- Rescale a magnitude to a lower exponent:
`magVal m' q' = (m' · 2^(q'-q)) · 2^q` for `q ≤ q'`. -/
private theorem magVal_shift (m' : Nat) (q q' : Int) (h : q ≤ q') :
    magVal m' q' = ((m' * 2 ^ (q' - q).toNat : Nat) : ℚ) * (2 : ℚ) ^ q := by
  unfold magVal
  push_cast
  rw [show (2 : ℚ) ^ ((q' - q).toNat) = (2 : ℚ) ^ ((q' - q : Int)) from by
        rw [← zpow_natCast]
        congr 1
        omega,
      mul_assoc, ← zpow_add₀ (by norm_num : (2:ℚ) ≠ 0)]
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
      have h2 := two_zpow_pos q
      nlinarith [hlt]
    have hnat : m < m' * 2 ^ (q' - q).toNat := by exact_mod_cast hcoeff
    have hnat1 : (m : ℚ) + 1 ≤ ((m' * 2 ^ (q' - q).toNat : Nat) : ℚ) := by
      have : m + 1 ≤ m' * 2 ^ (q' - q).toNat := hnat
      exact_mod_cast this
    unfold magVal
    have h2 := two_zpow_pos q
    nlinarith [hnat1]
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
      have : (m' : ℚ) < ((2 : ℚ)) ^ (53 : ℕ) := by
        have := hs'.m_lt
        exact_mod_cast this
      push_cast
      nlinarith
    have h2 : magVal (2 ^ 53) q' ≤ magVal (2 ^ 52) q := by
      unfold magVal
      -- 2^53 · 2^q' = 2^52 · 2^(q'+1) ≤ 2^52 · 2^q.
      have hstep : (2 : ℚ) ^ (q' + 1) ≤ (2 : ℚ) ^ q :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
      have h52 : (0 : ℚ) < ((2 ^ 52 : Nat) : ℚ) := by positivity
      have hsplit : ((2 ^ 53 : Nat) : ℚ) * (2 : ℚ) ^ q'
          = ((2 ^ 52 : Nat) : ℚ) * (2 : ℚ) ^ (q' + 1) := by
        rw [zpow_add₀ (by norm_num : (2:ℚ) ≠ 0)]
        push_cast
        ring
      rw [hsplit]
      nlinarith
    have h3 : magVal (2 ^ 52) q ≤ magVal m q := by
      unfold magVal
      have h2q := two_zpow_pos q
      have : ((2 ^ 52 : Nat) : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm_ge
      nlinarith
    linarith

/-- Cancel a shared positive `2^q` factor in an equality. -/
private theorem coeff_eq_of_magVal (a b : Nat) (q : Int)
    (h : (a : ℚ) * (2 : ℚ) ^ q = (b : ℚ) * (2 : ℚ) ^ q) : a = b := by
  have := mul_right_cancel₀ (ne_of_gt (two_zpow_pos q)) h
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
    · exact zpow_le_zpow_right₀ (by norm_num) (by omega)
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
        push_cast
        norm_num
      linarith [h3 ▸ h2]
    have hpow_le : (2 : ℚ) ^ q' ≤ (2 : ℚ) ^ (q - 1) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    have hmag'_le : (m' : ℚ) * (2 : ℚ) ^ q'
        ≤ ((2 : ℚ) ^ (53 : ℕ) - 1) * (2 : ℚ) ^ (q - 1) := by
      have h1 : (0 : ℚ) ≤ (m' : ℚ) := Nat.cast_nonneg m'
      have h2 := two_zpow_pos q'
      nlinarith
    -- q' < q forces m normal (q > -1074).
    have hm_norm : 2 ^ 52 ≤ m := by
      rcases hleg with ⟨_, _, hqe⟩ | ⟨hge, _⟩
      · omega
      · exact hge
    have hsplit : (2 : ℚ) ^ q = 2 * (2 : ℚ) ^ (q - 1) := by
      rw [show q = (q - 1) + 1 from by omega, zpow_add₀ (by norm_num : (2:ℚ) ≠ 0)]
      ring_nf
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
        ring_nf
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
          push_cast
          norm_num
        linarith [h2 ▸ h1]
      have hpow53 : (2 : ℚ) ^ (53 : ℕ) = 2 * (2 : ℚ) ^ (52 : ℕ) := by norm_num
      nlinarith [hmag'_le, two_zpow_pos (q - 1)]
  · -- q' = q: integer coefficient drop.
    subst hq
    have hcoeff : (m' : ℚ) < (m : ℚ) := by
      unfold magVal at hlt
      have h2 := two_zpow_pos q'
      nlinarith
    have hnat : m' < m := by exact_mod_cast hcoeff
    have hle : (m' : ℚ) ≤ (m : ℚ) - 1 := by
      have : m' + 1 ≤ m := hnat
      have : (m' : ℚ) + 1 ≤ (m : ℚ) := by exact_mod_cast this
      linarith
    have : magVal m' q' ≤ magVal m q' - (2 : ℚ) ^ q' := by
      unfold magVal
      have h2 := two_zpow_pos q'
      nlinarith
    linarith
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
      nlinarith
    have h2 : magVal m q < magVal (2 ^ 52) q' := by
      unfold magVal
      -- m · 2^q < 2^53 · 2^q = 2^52 · 2^(q+1) ≤ 2^52 · 2^q'.
      have hstep : (2 : ℚ) ^ (q + 1) ≤ (2 : ℚ) ^ q' :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
      have hm_lt : (m : ℚ) < ((2 ^ 53 : Nat) : ℚ) := by
        have : m < 2 ^ 53 := by
          rcases hleg with ⟨_, hlt', _⟩ | ⟨_, hlt', _⟩ <;> omega
        exact_mod_cast this
      have hsplit : ((2 ^ 53 : Nat) : ℚ) * (2 : ℚ) ^ q
          = ((2 ^ 52 : Nat) : ℚ) * (2 : ℚ) ^ (q + 1) := by
        rw [zpow_add₀ (by norm_num : (2:ℚ) ≠ 0)]
        push_cast
        ring
      have h2q := two_zpow_pos q
      have h52 : (0 : ℚ) < ((2 ^ 52 : Nat) : ℚ) := by positivity
      nlinarith
    linarith

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
        nlinarith
      linarith [heq.symm, hpos]
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
        nlinarith
      linarith
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
      rw [magVal_shift m' q q' (le_of_lt hq)] at heq
      have hj : 1 ≤ (q' - q).toNat := by omega
      have hnat : m = m' * 2 ^ (q' - q).toNat :=
        coeff_eq_of_magVal m _ q (by exact_mod_cast heq)
      have hge : 2 ^ 53 ≤ m := by
        calc 2 ^ 53 = 2 ^ 52 * 2 ^ 1 := by norm_num
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
      rw [magVal_shift m q' q (le_of_lt hq)] at heq
      have hj : 1 ≤ (q - q').toNat := by omega
      have hnat : m * 2 ^ (q - q').toNat = m' :=
        coeff_eq_of_magVal _ m' q' (by exact_mod_cast heq)
      have hge : 2 ^ 53 ≤ m' := by
        calc 2 ^ 53 = 2 ^ 52 * 2 ^ 1 := by norm_num
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
    ring
  have hq'_ge : (-1074 : Int) ≤ q' := by
    rcases hleg' with ⟨_, _, hqe⟩ | ⟨_, _, hge, _⟩ <;> omega
  rcases lt_trichotomy q q' with hq | hq | hq
  · -- q < q': m' · 2^j = m + 1 with m' normal ⇒ m + 1 = 2^53, m' = 2^52.
    have hm'_norm : 2 ^ 52 ≤ m' := by
      rcases hleg' with ⟨_, _, hqe⟩ | ⟨hge, _⟩
      · have := hs.q_ge; omega
      · exact hge
    rw [magVal_shift m' q q' (le_of_lt hq)] at hsucc
    have hnat : m' * 2 ^ (q' - q).toNat = m + 1 :=
      coeff_eq_of_magVal _ _ q hsucc
    have hj : 1 ≤ (q' - q).toNat := by omega
    have hge : 2 ^ 53 ≤ m + 1 := by
      calc 2 ^ 53 = 2 ^ 52 * 2 ^ 1 := by norm_num
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
    rw [magVal_shift (m + 1) q' q (le_of_lt hq)] at hsucc
    have hnat : m' = (m + 1) * 2 ^ (q - q').toNat :=
      coeff_eq_of_magVal m' _ q' hsucc
    have hj : 1 ≤ (q - q').toNat := by omega
    have hge : 2 ^ 53 + 2 ≤ m' := by
      calc 2 ^ 53 + 2 = (2 ^ 52 + 1) * 2 ^ 1 := by norm_num
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
        linarith
  · right
    refine ⟨?_, heven⟩
    have hq := (cmpScaledMixed_lhs_eq_rhs_iff_rat
        (if irreg then 4 * (m : Int) - 1 else 4 * (m : Int) - 2) q
        (4 * (s : Int)) k).mp heq
    unfold magVal gridVal
    cases irreg <;> simp only [if_true, if_false, Bool.false_eq_true] at hq ⊢ <;>
      · push_cast at hq
        linarith

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
    linarith
  · right
    refine ⟨?_, heven⟩
    have hq := (cmpScaledMixed_lhs_eq_rhs_iff_rat
        (4 * (m : Int) + 2) q (4 * (s : Int)) k).mp heq.symm
    unfold magVal gridVal
    push_cast at hq
    linarith

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
  have hc_pos : 0 < c := by rw [hc]; split <;> norm_num
  have hL : 4 * v - c * (2 : ℚ) ^ q ≤ 4 * u := by
    rcases rv_left_rat s k m q _ h_rv with h | ⟨h, _⟩
    · rw [hc]; linarith
    · rw [hc]; linarith
  have hR : 4 * u ≤ 4 * v + 2 * (2 : ℚ) ^ q := by
    rcases rv_right_rat s k m q _ h_rv with h | ⟨h, _⟩
    · linarith
    · linarith
  rcases lt_trichotomy w v with hwv | hwv | hwv
  · -- w < v: v is positive, m legal; grid gap downward.
    have hm_pos : m ≠ 0 := by
      intro h0
      have hv0 : v = 0 := by rw [hv, h0]; exact magVal_zero_eq q
      have hw0 : (0 : ℚ) ≤ w := hw ▸ magVal_nonneg m' q'
      linarith
    have hgap := magVal_gap_down m m' q q' (hs.legal_of_ne hm_pos) hs' hwv
    have hsplit : (2 : ℚ) ^ q = 2 * (2 : ℚ) ^ (q - 1) := by
      rw [show q = (q - 1) + 1 from by omega, zpow_add₀ (by norm_num : (2:ℚ) ≠ 0)]
      ring_nf
    have hgap4 : 4 * w ≤ 4 * v - 2 * c * (2 : ℚ) ^ q := by
      by_cases hirr : isIrregular m q = true
      · rw [if_pos hirr] at hgap
        rw [hc, if_pos hirr]
        linarith
      · rw [if_neg hirr] at hgap
        rw [hc, if_neg hirr]
        linarith
    have huw : w < u := by nlinarith
    rw [show |w - u| = u - w from by rw [abs_of_nonpos (by linarith)]; ring]
    refine abs_le.mpr ⟨by linarith, by linarith⟩
  · exact le_of_eq (by rw [hwv])
  · -- v < w: grid gap upward.
    have hgap := magVal_gap_up m m' q q' hs hs' hwv
    have huw : u < w := by nlinarith
    rw [show |w - u| = w - u from abs_of_nonneg (by linarith)]
    refine abs_le.mpr ⟨by linarith, by linarith⟩

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
  have hc_pos : 0 < c := by rw [hc]; split <;> norm_num
  have hL : 4 * v - c * (2 : ℚ) ^ q ≤ 4 * u := by
    rcases rv_left_rat s k m q _ h_rv with h | ⟨h, _⟩
    · rw [hc]; linarith
    · rw [hc]; linarith
  have hR : 4 * u ≤ 4 * v + 2 * (2 : ℚ) ^ q := by
    rcases rv_right_rat s k m q _ h_rv with h | ⟨h, _⟩
    · linarith
    · linarith
  rcases lt_trichotomy w v with hwv | hwv | hwv
  · -- w < v: the tie pins u to the left endpoint.
    have hm_pos : m ≠ 0 := by
      intro h0
      have hv0 : v = 0 := by rw [hv, h0]; exact magVal_zero_eq q
      have hw0 : (0 : ℚ) ≤ w := hw ▸ magVal_nonneg m' q'
      linarith
    have hgap := magVal_gap_down m m' q q' (hs.legal_of_ne hm_pos) hs' hwv
    have hsplit : (2 : ℚ) ^ q = 2 * (2 : ℚ) ^ (q - 1) := by
      rw [show q = (q - 1) + 1 from by omega, zpow_add₀ (by norm_num : (2:ℚ) ≠ 0)]
      ring_nf
    have hgap4 : 4 * w ≤ 4 * v - 2 * c * (2 : ℚ) ^ q := by
      by_cases hirr : isIrregular m q = true
      · rw [if_pos hirr] at hgap
        rw [hc, if_pos hirr]
        linarith
      · rw [if_neg hirr] at hgap
        rw [hc, if_neg hirr]
        linarith
    have huw : w < u := by nlinarith
    rw [show |w - u| = u - w from by rw [abs_of_nonpos (by linarith)]; ring] at h_eq
    rcases le_or_gt u v with huv | huv
    · -- u ≤ v: |v - u| = v - u; equality chain pins 4u = 4v - c·2^q.
      rw [show |v - u| = v - u from abs_of_nonneg (by linarith)] at h_eq
      have h4 : 4 * u = 4 * v - c * (2 : ℚ) ^ q := by linarith
      rcases rv_left_rat s k m q _ h_rv with h | ⟨_, heven⟩
      · exfalso
        rw [← hc] at h
        linarith
      · exact heven
    · -- u > v: u - v = u - w forces w = v, contradiction.
      exfalso
      rw [show |v - u| = u - v from by rw [abs_of_nonpos (by linarith)]; ring] at h_eq
      have : w = v := by linarith
      exact h_ne (by rw [hw, hv] at this; exact this)
  · exact absurd (hw ▸ hv ▸ hwv) h_ne
  · -- v < w: the tie pins u to the right endpoint.
    have hgap := magVal_gap_up m m' q q' hs hs' hwv
    have huw : u < w := by nlinarith
    rw [show |w - u| = w - u from abs_of_nonneg (by linarith)] at h_eq
    rcases le_or_gt u v with huv | huv
    · -- u ≤ v: v - u = w - u forces w = v, contradiction.
      exfalso
      rw [show |v - u| = v - u from abs_of_nonneg (by linarith)] at h_eq
      have : w = v := by linarith
      exact h_ne (by rw [hw, hv] at this; exact this)
    · -- u > v: equality chain pins 4u = 4v + 2·2^q.
      rw [show |v - u| = u - v from by rw [abs_of_nonpos (by linarith)]; ring] at h_eq
      have h4 : 4 * u = 4 * v + 2 * (2 : ℚ) ^ q := by linarith
      rcases rv_right_rat s k m q _ h_rv with h | ⟨_, heven⟩
      · exfalso
        linarith
      · exact heven

/-! ## The overflow boundary

The elementary threshold is `2^1024 - 2^970`: the midpoint between the
largest finite float `(2^53 - 1)·2^971` and its would-be successor
`2^53·2^971`. `IsFiniteAbs` (the algorithm's overflow test) matches it
exactly: values strictly below produce a finite float, values at or
above produce `±∞` (the midpoint itself rounds up, to the even
`m = 2^53`). -/

theorem gridVal_nonneg (s : Nat) (k : Int) : (0 : ℚ) ≤ gridVal s k :=
  mul_nonneg (Nat.cast_nonneg s) (le_of_lt (zpow_pos (by norm_num) k))

/-- `|toRat d|` is the unsigned decimal grid value. -/
theorem abs_toRat_eq_gridVal (d : Decimal) :
    |Decimal.toRat d| = gridVal d.significand d.exponent := by
  rw [toRat_eq_signFactor_gridVal, abs_mul]
  have h1 : |signFactor d.sign| = 1 := by
    unfold signFactor
    cases d.sign <;> simp
  rw [h1, one_mul, abs_of_nonneg (gridVal_nonneg _ _)]

/-- Overflow at the `(a, b)` level: the quotient `a/b` is at least
`(2^54 - 1)·2^970`, in cleared `Nat` form. -/
private theorem overflow_bound_AB (sign : Bool) (a b : Nat) (ha : 0 < a) (hb : 0 < b)
    (h_not : ¬ (decodedAbsAB sign a b).q ≤ 971) :
    (2 ^ 54 - 1) * 2 ^ 970 * b ≤ a := by
  unfold decodedAbsAB at h_not
  simp only at h_not
  split_ifs at h_not with h_e h_e2 h_m h_e'
  · -- e > 1023: b · 2^e ≤ a with e ≥ 1024.
    have hle := findBinaryExp_le a b ha hb
    rw [leBy2e_eq_true_iff] at hle
    rw [if_pos (by omega : findBinaryExp a b ≥ 0)] at hle
    have h_pow : (2 : Nat) ^ 1024 ≤ 2 ^ (findBinaryExp a b).toNat :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have h_lit : (2 ^ 54 - 1) * 2 ^ 970 ≤ (2 : Nat) ^ 1024 := by
      have h1 : (2 ^ 54 - 1) * 2 ^ 970 ≤ 2 ^ 54 * 2 ^ 970 :=
        Nat.mul_le_mul_right _ (by omega)
      have h2 : (2 : Nat) ^ 54 * 2 ^ 970 = 2 ^ 1024 := by
        rw [← pow_add]
      omega
    calc (2 ^ 54 - 1) * 2 ^ 970 * b ≤ 2 ^ 1024 * b := Nat.mul_le_mul_right b h_lit
    _ ≤ 2 ^ (findBinaryExp a b).toNat * b := Nat.mul_le_mul_right b h_pow
    _ = b * 2 ^ (findBinaryExp a b).toNat := Nat.mul_comm _ _
    _ ≤ a := hle
  · -- Carry overflow: e = 1023 and the rounded m reached 2^53.
    have h_e_eq : findBinaryExp a b = 1023 := by omega
    -- num = a, denom = b · 2^971.
    have h_scale : scaleByPow2 a b (52 - findBinaryExp a b) = (a, b * 2 ^ 971) := by
      rw [h_e_eq]
      rw [scaleByPow2_neg (by omega : ¬ (52 - (1023 : Int)) ≥ 0)]
      have h971 : (-(52 - (1023 : Int))).toNat = 971 := by decide
      rw [h971]
    rw [h_scale] at h_m
    set P : Nat := b * 2 ^ 971 with hP
    have hP_pos : 0 < P := by positivity
    have hp971 : (2 : Nat) ^ 971 = 2 ^ 970 * 2 := by
      rw [show (971 : ℕ) = 970 + 1 from rfl, pow_succ]
    rcases roundNearestEven_eq_floor_or_ceil a P with h_fl | h_ce
    · -- floor: a / P ≥ 2^53 forces a ≥ 2^53 · P.
      rw [h_fl] at h_m
      have : 2 ^ 53 * P ≤ a / P * P := Nat.mul_le_mul_right P h_m
      have hdiv : a / P * P ≤ a := Nat.div_mul_le_self a P
      have hgoal : (2 ^ 54 - 1) * 2 ^ 970 * b ≤ 2 ^ 53 * P := by
        rw [hP, hp971]
        calc (2 ^ 54 - 1) * 2 ^ 970 * b ≤ 2 ^ 54 * 2 ^ 970 * b :=
              Nat.mul_le_mul_right b (Nat.mul_le_mul_right _ (by omega))
        _ = 2 ^ 53 * (b * (2 ^ 970 * 2)) := by ring
      omega
    · -- ceil: the half-ULP bound gives 2a ≥ (2^54 - 1) · P.
      have h_bound := roundNearestEven_ceil_bound a P hP_pos h_ce
      set M : Nat := roundNearestEven a P with hM
      have h_MP : 2 ^ 53 * P ≤ M * P := Nat.mul_le_mul_right P h_m
      -- 2·(M·P - a) ≤ P and M·P ≥ 2^53·P give 2a ≥ (2^54 - 1)·P.
      have h_lin : (2 ^ 54 - 1) * P ≤ 2 * a := by
        have h53 : (2 : Nat) ^ 54 = 2 * 2 ^ 53 := by norm_num
        omega
      rw [hP] at h_lin
      have hgoal : 2 * ((2 ^ 54 - 1) * 2 ^ 970 * b) = (2 ^ 54 - 1) * (b * 2 ^ 971) := by
        rw [hp971]
        ring
      omega
  · -- Renormalised but in range: q = e + 1 - 52 ≤ 971.
    exact absurd (by omega : findBinaryExp a b + 1 - 52 ≤ 971) h_not
  · -- Regular normal: q = e - 52 ≤ 971.
    exact absurd (by omega : findBinaryExp a b - 52 ≤ 971) h_not
  all_goals
    exact absurd (by norm_num : (-1074 : Int) ≤ 971) h_not

/-- **Boundary, overflow side.** A nonzero decimal the algorithm rejects
as overflow has `|value| ≥ 2^1024 - 2^970`. -/
theorem bound_le_gridVal_of_not_finite (sign : Bool) (sig : Nat) (exp : Int)
    (h_sig : sig ≠ 0) (h_not : ¬ IsFiniteAbs sign sig exp) :
    (2 : ℚ) ^ (1024 : ℕ) - (2 : ℚ) ^ (970 : ℕ) ≤ gridVal sig exp := by
  unfold IsFiniteAbs at h_not
  have hB_cast : ((( 2 ^ 54 - 1) * 2 ^ 970 : Nat) : ℚ)
      = (2 : ℚ) ^ (1024 : ℕ) - (2 : ℚ) ^ (970 : ℕ) := by
    push_cast
    rw [show (1024 : ℕ) = 54 + 970 from by norm_num, pow_add]
    ring
  by_cases hexp : exp ≥ 0
  · rw [decodedAbs_eq_decodedAbsAB_pos sign sig exp h_sig hexp] at h_not
    have hbound := overflow_bound_AB sign (sig * 10 ^ exp.toNat) 1
      (by positivity) (by omega) h_not
    -- gridVal sig exp = (sig · 10^exp.toNat : ℚ).
    have h_grid : gridVal sig exp = ((sig * 10 ^ exp.toNat : Nat) : ℚ) := by
      unfold gridVal
      push_cast
      rw [show (10 : ℚ) ^ exp = (10 : ℚ) ^ exp.toNat from by
            rw [← zpow_natCast]
            congr 1
            omega]
    rw [h_grid, ← hB_cast]
    exact_mod_cast (by omega : (2 ^ 54 - 1) * 2 ^ 970 ≤ sig * 10 ^ exp.toNat)
  · rw [decodedAbs_eq_decodedAbsAB_neg sign sig exp h_sig hexp] at h_not
    have hbound := overflow_bound_AB sign sig (10 ^ (-exp).toNat)
      (Nat.pos_of_ne_zero h_sig) (by positivity) h_not
    -- gridVal sig exp · 10^(-exp).toNat = sig.
    have h_clear : gridVal sig exp * ((10 ^ (-exp).toNat : Nat) : ℚ) = (sig : ℚ) := by
      unfold gridVal
      push_cast
      rw [mul_assoc, show (10 : ℚ) ^ exp * (10 : ℚ) ^ ((-exp).toNat : ℕ) = 1 from by
            rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (10:ℚ) ≠ 0)]
            rw [show exp + ((-exp).toNat : ℤ) = 0 from by omega]
            rfl,
          mul_one]
    have h10_pos : (0 : ℚ) < ((10 ^ (-exp).toNat : Nat) : ℚ) := by positivity
    have hbound_q : ((( 2 ^ 54 - 1) * 2 ^ 970 : Nat) : ℚ) * ((10 ^ (-exp).toNat : Nat) : ℚ)
        ≤ (sig : ℚ) := by
      rw [show ((( 2 ^ 54 - 1) * 2 ^ 970 : Nat) : ℚ) * ((10 ^ (-exp).toNat : Nat) : ℚ)
            = (((2 ^ 54 - 1) * 2 ^ 970 * 10 ^ (-exp).toNat : Nat) : ℚ) from by push_cast; ring]
      exact_mod_cast hbound
    rw [← hB_cast]
    rw [← h_clear] at hbound_q
    exact le_of_mul_le_mul_right hbound_q h10_pos

/-- **Boundary, finite side.** A decimal value carried by an `R_v`
membership witness is strictly below the threshold. -/
theorem gridVal_lt_bound_of_rv (s : Nat) (k : Int) (m : Nat) (q : Int)
    (hs : FinShape m q)
    (h_rv : inRoundingInterval s k m q (isIrregular m q) = true) :
    gridVal s k < (2 : ℚ) ^ (1024 : ℕ) - (2 : ℚ) ^ (970 : ℕ) := by
  have h2q := two_zpow_pos q
  have hX : (2 : ℚ) ^ q ≤ (2 : ℚ) ^ (971 : ℤ) :=
    zpow_le_zpow_right₀ (by norm_num) hs.q_le
  have hX_eq : (2 : ℚ) ^ (971 : ℤ) = (2 : ℚ) ^ (971 : ℕ) := by
    rw [← zpow_natCast]
    norm_num
  have hXpos : (0 : ℚ) < (2 : ℚ) ^ (971 : ℕ) := by positivity
  have h_pow_split : (2 : ℚ) ^ (1024 : ℕ) = (2 : ℚ) ^ (53 : ℕ) * (2 : ℚ) ^ (971 : ℕ) := by
    rw [← pow_add]
  have h_pow_split' : (2 : ℚ) ^ (971 : ℕ) = 2 * (2 : ℚ) ^ (970 : ℕ) := by
    rw [show (971 : ℕ) = 1 + 970 from rfl, pow_add]
    ring
  have hv_le : magVal m q ≤ ((2 : ℚ) ^ (53 : ℕ) - 1) * (2 : ℚ) ^ q := by
    unfold magVal
    have hm : (m : ℚ) ≤ (2 : ℚ) ^ (53 : ℕ) - 1 := by
      have h1 : m ≤ 2 ^ 53 - 1 := by have := hs.m_lt; omega
      have h2 : (m : ℚ) ≤ ((2 ^ 53 - 1 : Nat) : ℚ) := by exact_mod_cast h1
      have h3 : ((2 ^ 53 - 1 : Nat) : ℚ) = (2 : ℚ) ^ (53 : ℕ) - 1 := by
        push_cast
        norm_num
      linarith [h3 ▸ h2]
    nlinarith
  have h970pos : (0 : ℚ) < (2 : ℚ) ^ (970 : ℕ) := by positivity
  rcases rv_right_rat s k m q _ h_rv with h | ⟨h, heven⟩
  · -- Strict right bracket: 4u < 4v + 2·2^q ≤ (2^55 - 2)·2^971 = 4·bound.
    have h1 : 4 * magVal m q + 2 * (2 : ℚ) ^ q
        ≤ (4 * ((2 : ℚ) ^ (53 : ℕ) - 1) + 2) * (2 : ℚ) ^ q := by nlinarith
    have h2 : (4 * ((2 : ℚ) ^ (53 : ℕ) - 1) + 2) * (2 : ℚ) ^ q
        ≤ (4 * ((2 : ℚ) ^ (53 : ℕ) - 1) + 2) * (2 : ℚ) ^ (971 : ℕ) := by
      rw [← hX_eq]
      nlinarith
    have hkey : (4 * ((2 : ℚ) ^ (53 : ℕ) - 1) + 2) * (2 : ℚ) ^ (971 : ℕ)
        = 4 * ((2 : ℚ) ^ (1024 : ℕ) - (2 : ℚ) ^ (970 : ℕ)) := by
      rw [h_pow_split, h_pow_split']
      ring
    have hchain := lt_of_lt_of_le (lt_of_lt_of_le h h1) h2
    rw [hkey] at hchain
    exact lt_of_mul_lt_mul_left hchain (by norm_num : (0 : ℚ) ≤ 4)
  · -- Endpoint: m even, so m ≤ 2^53 - 2 and the bound tightens.
    have hm : (m : ℚ) ≤ (2 : ℚ) ^ (53 : ℕ) - 2 := by
      have h1 : m ≤ 2 ^ 53 - 2 := by
        have := hs.m_lt
        omega
      have h2 : (m : ℚ) ≤ ((2 ^ 53 - 2 : Nat) : ℚ) := by exact_mod_cast h1
      have h3 : ((2 ^ 53 - 2 : Nat) : ℚ) = (2 : ℚ) ^ (53 : ℕ) - 2 := by
        push_cast
        norm_num
      linarith [h3 ▸ h2]
    have hv_le' : magVal m q ≤ ((2 : ℚ) ^ (53 : ℕ) - 2) * (2 : ℚ) ^ q := by
      unfold magVal
      nlinarith
    have h1 : 4 * magVal m q + 2 * (2 : ℚ) ^ q
        ≤ (4 * ((2 : ℚ) ^ (53 : ℕ) - 2) + 2) * (2 : ℚ) ^ q := by nlinarith
    have h2 : (4 * ((2 : ℚ) ^ (53 : ℕ) - 2) + 2) * (2 : ℚ) ^ q
        ≤ (4 * ((2 : ℚ) ^ (53 : ℕ) - 2) + 2) * (2 : ℚ) ^ (971 : ℕ) := by
      rw [← hX_eq]
      have hcoef : (0 : ℚ) < 4 * ((2 : ℚ) ^ (53 : ℕ) - 2) + 2 := by positivity
      nlinarith
    have hkey : (4 * ((2 : ℚ) ^ (53 : ℕ) - 2) + 2) * (2 : ℚ) ^ (971 : ℕ)
        = 4 * (2 : ℚ) ^ (1024 : ℕ) - 12 * (2 : ℚ) ^ (970 : ℕ) := by
      rw [h_pow_split, h_pow_split']
      ring
    have hchain := le_trans (le_of_eq h) (le_trans h1 h2)
    rw [hkey] at hchain
    have hstep : 4 * (2 : ℚ) ^ (1024 : ℕ) - 12 * (2 : ℚ) ^ (970 : ℕ)
        < 4 * ((2 : ℚ) ^ (1024 : ℕ) - (2 : ℚ) ^ (970 : ℕ)) := by
      have h412 : 4 * (2 : ℚ) ^ (970 : ℕ) < 12 * (2 : ℚ) ^ (970 : ℕ) :=
        mul_lt_mul_of_pos_right (by norm_num) h970pos
      have := sub_lt_sub_left h412 (4 * (2 : ℚ) ^ (1024 : ℕ))
      calc 4 * (2 : ℚ) ^ (1024 : ℕ) - 12 * (2 : ℚ) ^ (970 : ℕ)
          < 4 * (2 : ℚ) ^ (1024 : ℕ) - 4 * (2 : ℚ) ^ (970 : ℕ) := this
      _ = 4 * ((2 : ℚ) ^ (1024 : ℕ) - (2 : ℚ) ^ (970 : ℕ)) := by ring
    exact lt_of_mul_lt_mul_left (lt_of_le_of_lt hchain hstep) (by norm_num : (0 : ℚ) ≤ 4)

/-! ## Float-level plumbing -/

theorem toRat_of_sig_zero (d : Decimal) (h : d.significand = 0) :
    Decimal.toRat d = 0 := by
  unfold Decimal.toRat
  rw [h]
  simp

/-- `decode` preserves mantissa parity: the implicit leading bit is even. -/
theorem decode_m_parity (f : _root_.Float) :
    (decode f).m % 2 = mantissaBits f % 2 := by
  unfold decode
  by_cases he : biasedExpBits f = 0
  · rw [if_pos he]
  · rw [if_neg he]
    simp only
    have h52 : (1 <<< 52 : Nat) = 2 ^ 52 := rfl
    omega

/-- `ofDecimal` of a finite-range decimal is bit-level finite. -/
theorem isFiniteBits_ofDecimal (d : Decimal)
    (h_fin : IsFiniteAbs d.sign d.significand d.exponent) :
    isFiniteBits (Clinger.ofDecimal d) = true := by
  have h_bridge := Clinger.decode_of_decimal_bridge d h_fin
  have h_dec_q : (decode (Clinger.ofDecimal d)).q ≤ 971 := by
    rw [h_bridge]
    exact h_fin
  unfold isFiniteBits
  by_cases he : biasedExpBits (Clinger.ofDecimal d) = 0
  · simp [he]
  · have h_q_def : (decode (Clinger.ofDecimal d)).q
        = (biasedExpBits (Clinger.ofDecimal d) : Int) - 1023 - 52 := by
      unfold decode
      rw [if_neg he]
    rw [h_q_def] at h_dec_q
    simp only [decide_eq_true_eq]
    omega

/-- On a zero significand, `ofDecimal` is the signed zero. -/
theorem ofDecimal_sig_zero (d : Decimal) (h : d.significand = 0) :
    Clinger.ofDecimal d = fromBits d.sign 0 0 := by
  unfold Clinger.ofDecimal Clinger.decimalToFloat
  rw [h]
  rfl

/-- Same-sign distance reduction: `|floatVal f - toRat d|` is the
unsigned grid distance. -/
theorem floatVal_dist_reduce (d : Decimal) (f : _root_.Float)
    (h_sign : (decode f).sign = d.sign) :
    |floatVal f - Decimal.toRat d|
      = |magVal (decode f).m (decode f).q - gridVal d.significand d.exponent| := by
  rw [abs_sub_comm]
  exact toRat_dist_eq_grid_dist d f h_sign.symm

/-- Opposite-sign distance: magnitudes add. -/
theorem floatVal_dist_opp (d : Decimal) (f : _root_.Float)
    (h_sign : (decode f).sign ≠ d.sign) :
    |floatVal f - Decimal.toRat d|
      = magVal (decode f).m (decode f).q + gridVal d.significand d.exponent := by
  rw [floatVal_eq_signFactor_magVal, toRat_eq_signFactor_gridVal]
  have hmag := magVal_nonneg (decode f).m (decode f).q
  have hgrid := gridVal_nonneg d.significand d.exponent
  rcases Bool.eq_false_or_eq_true (decode f).sign with hf | hf <;>
    rcases Bool.eq_false_or_eq_true d.sign with hd | hd
  · exact absurd (hf.trans hd.symm) h_sign
  · -- f negative, d positive: (-1)·mag - 1·u = -(mag + u) ≤ 0.
    rw [hf, hd]
    unfold signFactor
    rw [if_pos rfl, if_neg (by decide : ¬ ((false : Bool) = true))]
    rw [abs_of_nonpos (by linarith)]
    ring
  · -- f positive, d negative: 1·mag - (-1)·u = mag + u ≥ 0.
    rw [hf, hd]
    unfold signFactor
    rw [if_neg (by decide : ¬ ((false : Bool) = true)), if_pos rfl]
    rw [abs_of_nonneg (by linarith)]
    ring
  · exact absurd (hf.trans hd.symm) h_sign

/-- The rounded float is never farther from `u` than `u` is from zero. -/
theorem rv_dist_le_u (s : Nat) (k : Int) (m : Nat) (q : Int)
    (h_rv : inRoundingInterval s k m q (isIrregular m q) = true) :
    |magVal m q - gridVal s k| ≤ gridVal s k := by
  have hu0 := gridVal_nonneg s k
  by_cases hm : m = 0
  · subst hm
    rw [magVal_zero_eq, abs_of_nonpos (by linarith)]
    linarith
  · have h2q := two_zpow_pos q
    have hc_le : (if isIrregular m q then (1 : ℚ) else 2) * (2 : ℚ) ^ q
        ≤ 2 * (2 : ℚ) ^ q := by
      have : (if isIrregular m q then (1 : ℚ) else 2) ≤ 2 := by
        split <;> norm_num
      nlinarith
    have hL : 4 * magVal m q - 2 * (2 : ℚ) ^ q ≤ 4 * gridVal s k := by
      rcases rv_left_rat s k m q _ h_rv with h | ⟨h, _⟩ <;> linarith
    have hstep_le_v : (2 : ℚ) ^ q ≤ magVal m q := by
      unfold magVal
      have h1 : (1 : ℚ) ≤ (m : ℚ) := by
        exact_mod_cast Nat.pos_of_ne_zero hm
      nlinarith
    have hv0 := magVal_nonneg m q
    rw [abs_le]
    constructor <;> linarith

/-! ## Backward direction: `ofDecimal` satisfies the reader spec -/

/-- In-range decimals: `ofDecimal` is the nearest float. -/
theorem ofDecimal_isNearestFloat (d : Decimal)
    (h_in : |Decimal.toRat d| < 2 ^ 1024 - 2 ^ 970) :
    IsNearestFloat d (Clinger.ofDecimal d) := by
  by_cases h_sig : d.significand = 0
  · -- Signed zero.
    have h_eq := ofDecimal_sig_zero d h_sig
    obtain ⟨h_sb, h_be, h_mb⟩ :=
      fromBits_proj d.sign 0 0 (by norm_num) (by positivity) (fun _ => rfl)
    have h_toRat : Decimal.toRat d = 0 := toRat_of_sig_zero d h_sig
    have h_m0 : (decode (fromBits d.sign 0 0)).m = 0 := by
      unfold decode
      rw [if_pos h_be]
      exact h_mb
    have h_fv : floatVal (fromBits d.sign 0 0) = 0 := by
      unfold floatVal
      rw [h_m0, magVal_zero_eq, mul_zero]
    rw [h_eq]
    refine ⟨?_, h_sb, ?_, ?_⟩
    · unfold isFiniteBits
      rw [h_be]
      decide
    · intro g hg
      rw [h_fv, h_toRat]
      simp
    · intro g hg h_ne h_eq'
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
    have h_finBits : isFiniteBits (Clinger.ofDecimal d) = true :=
      isFiniteBits_ofDecimal d h_fin
    have h_sign_f : (decode (Clinger.ofDecimal d)).sign = d.sign := by
      rw [Clinger.decode_of_decimal_bridge d h_fin]
      exact decodedAbs_sign d.sign d.significand d.exponent
    have h_rv := Clinger.ofDecimal_in_Rv d h_sig h_fin
    simp only at h_rv
    have h_shape_f := decode_finShape _ h_finBits
    have h_df := floatVal_dist_reduce d _ h_sign_f
    refine ⟨h_finBits, ?_, ?_, ?_⟩
    · rw [signBit_eq_decode_sign, h_sign_f]
    · -- nearest
      intro g hg
      rw [h_df]
      by_cases hgs : (decode g).sign = d.sign
      · rw [floatVal_dist_reduce d g hgs]
        exact rv_nearest_mag _ _ _ _ _ _ h_shape_f (decode_finShape g hg) h_rv
      · rw [floatVal_dist_opp d g hgs]
        have h1 := rv_dist_le_u _ _ _ _ h_rv
        have h2 := magVal_nonneg (decode g).m (decode g).q
        linarith
    · -- ties to even
      intro g hg h_ne h_eq'
      rw [← decode_m_parity]
      by_cases hgs : (decode g).sign = d.sign
      · rw [h_df, floatVal_dist_reduce d g hgs] at h_eq'
        have h_mag_ne : magVal (decode g).m (decode g).q
            ≠ magVal (decode (Clinger.ofDecimal d)).m (decode (Clinger.ofDecimal d)).q := by
          intro hmm
          apply h_ne
          rw [floatVal_eq_signFactor_magVal, floatVal_eq_signFactor_magVal,
              hgs, h_sign_f, hmm]
        exact rv_tie_even_mag _ _ _ _ _ _ h_shape_f (decode_finShape g hg) h_rv h_mag_ne h_eq'
      · -- Opposite-sign exact tie: impossible.
        exfalso
        rw [h_df, floatVal_dist_opp d g hgs] at h_eq'
        have h1 := rv_dist_le_u _ _ _ _ h_rv
        have h2 := magVal_nonneg (decode g).m (decode g).q
        have hu0 := gridVal_nonneg d.significand d.exponent
        -- The tie forces mag_g = 0 and |v - u| = u.
        have h_magg : magVal (decode g).m (decode g).q = 0 := by linarith
        have h_fvg : floatVal g = 0 := by
          rw [floatVal_eq_signFactor_magVal, h_magg, mul_zero]
        set v := magVal (decode (Clinger.ofDecimal d)).m (decode (Clinger.ofDecimal d)).q
          with hv
        set u := gridVal d.significand d.exponent with hu
        have h_dist_u : |v - u| = u := by linarith [h_eq']
        -- floatVal f ≠ 0, so v ≠ 0 and m_f ≥ 1.
        have h_v_ne : v ≠ 0 := by
          intro hv0
          apply h_ne
          rw [h_fvg, floatVal_eq_signFactor_magVal, ← hv, hv0, mul_zero]
        have h_v_pos : 0 < v := lt_of_le_of_ne (hv ▸ magVal_nonneg _ _) (Ne.symm h_v_ne)
        -- |v - u| = u with v > 0 forces v = 2u.
        have h_v2u : v = 2 * u := by
          rcases abs_cases (v - u) with ⟨habs, _⟩ | ⟨habs, _⟩
          · linarith [habs ▸ h_dist_u]
          · have : u - v = u := by linarith [habs ▸ h_dist_u]
            linarith
        -- The left endpoint analysis kills every branch.
        have hm_pos : (decode (Clinger.ofDecimal d)).m ≠ 0 := by
          intro h0
          rw [hv, h0, magVal_zero_eq] at h_v_pos
          exact lt_irrefl _ h_v_pos
        have h2q := two_zpow_pos (decode (Clinger.ofDecimal d)).q
        have h_m_ge1 : (1 : ℚ) ≤ ((decode (Clinger.ofDecimal d)).m : ℚ) := by
          exact_mod_cast Nat.pos_of_ne_zero hm_pos
        have h_v_ge : (2 : ℚ) ^ (decode (Clinger.ofDecimal d)).q ≤ v := by
          rw [hv]
          unfold magVal
          nlinarith
        rcases rv_left_rat d.significand d.exponent _ _ _ h_rv with h | ⟨h, heven⟩
        · -- Strict: 4v - c·2^q < 4u = 2v gives v < 2^q, i.e. m < 1.
          have hc_le : (if isIrregular (decode (Clinger.ofDecimal d)).m
                (decode (Clinger.ofDecimal d)).q then (1 : ℚ) else 2)
                * (2 : ℚ) ^ (decode (Clinger.ofDecimal d)).q
              ≤ 2 * (2 : ℚ) ^ (decode (Clinger.ofDecimal d)).q := by
            have : (if isIrregular (decode (Clinger.ofDecimal d)).m
                (decode (Clinger.ofDecimal d)).q then (1 : ℚ) else 2) ≤ 2 := by
              split <;> norm_num
            nlinarith
          rw [← hv, ← hu] at h
          linarith
        · -- Endpoint: 2v = c·2^q with c ∈ {1, 2}; c = 2 gives m = 1, odd;
          -- c = 1 gives 2m = 1, impossible.
          rw [← hv, ← hu] at h
          by_cases hirr : isIrregular (decode (Clinger.ofDecimal d)).m
              (decode (Clinger.ofDecimal d)).q = true
          · rw [if_pos hirr] at h
            -- 2v = 2^q: 2m·2^q = 2^q so 2m = 1.
            have h2m : 2 * ((decode (Clinger.ofDecimal d)).m : ℚ) = 1 := by
              have hveq : 2 * v = (2 : ℚ) ^ (decode (Clinger.ofDecimal d)).q := by
                linarith
              rw [hv] at hveq
              unfold magVal at hveq
              have := mul_right_cancel₀ (ne_of_gt h2q)
                (by linarith : 2 * ((decode (Clinger.ofDecimal d)).m : ℚ)
                    * (2 : ℚ) ^ (decode (Clinger.ofDecimal d)).q
                  = 1 * (2 : ℚ) ^ (decode (Clinger.ofDecimal d)).q)
              linarith
            have : (2 * (decode (Clinger.ofDecimal d)).m : ℚ) = 1 := by
              linarith
            have hnat : 2 * (decode (Clinger.ofDecimal d)).m = 1 := by
              exact_mod_cast this
            omega
          · rw [if_neg hirr] at h
            -- 2v = 2·2^q: m = 1, but the endpoint demands m even.
            have hveq : v = (2 : ℚ) ^ (decode (Clinger.ofDecimal d)).q := by
              linarith
            have hm1 : ((decode (Clinger.ofDecimal d)).m : ℚ) = 1 := by
              rw [hv] at hveq
              unfold magVal at hveq
              have := mul_right_cancel₀ (ne_of_gt h2q)
                (by linarith : ((decode (Clinger.ofDecimal d)).m : ℚ)
                    * (2 : ℚ) ^ (decode (Clinger.ofDecimal d)).q
                  = 1 * (2 : ℚ) ^ (decode (Clinger.ofDecimal d)).q)
              linarith
            have hnat : (decode (Clinger.ofDecimal d)).m = 1 := by exact_mod_cast hm1
            omega

/-- Out-of-range decimals: `ofDecimal` is exactly the signed-infinity
bit pattern. -/
theorem ofDecimal_overflow_eq (d : Decimal)
    (h_out : (2 : ℚ) ^ 1024 - 2 ^ 970 ≤ |Decimal.toRat d|) :
    Clinger.ofDecimal d = fromBits d.sign 2047 0 := by
  have hBpos : (0 : ℚ) < 2 ^ 1024 - 2 ^ 970 :=
    sub_pos.mpr (pow_lt_pow_right₀ (show (1 : ℚ) < 2 by norm_num)
      (show (970 : ℕ) < 1024 by norm_num))
  have h_sig : d.significand ≠ 0 := by
    intro h0
    rw [toRat_of_sig_zero d h0] at h_out
    simp only [abs_zero] at h_out
    exact absurd (lt_of_lt_of_le hBpos h_out) (lt_irrefl _)
  have h_not : ¬ IsFiniteAbs d.sign d.significand d.exponent := by
    intro h_fin
    have h_rv := Clinger.ofDecimal_in_Rv d h_sig h_fin
    simp only at h_rv
    have h_fb := isFiniteBits_ofDecimal d h_fin
    have h_lt := gridVal_lt_bound_of_rv _ _ _ _ (decode_finShape _ h_fb) h_rv
    rw [abs_toRat_eq_gridVal] at h_out
    exact absurd (lt_of_lt_of_le h_lt h_out) (lt_irrefl _)
  exact Clinger.decimalToFloat_overflow_inf d.sign d.significand d.exponent h_sig h_not

/-- Out-of-range decimals: `ofDecimal` is the signed infinity. -/
theorem ofDecimal_overflow (d : Decimal)
    (h_out : (2 : ℚ) ^ 1024 - 2 ^ 970 ≤ |Decimal.toRat d|) :
    isInfBits (Clinger.ofDecimal d) = true ∧ signBit (Clinger.ofDecimal d) = d.sign := by
  obtain ⟨h_sb, h_be, h_mb⟩ :=
    fromBits_proj d.sign 2047 0 (by norm_num) (by positivity) (fun _ => rfl)
  rw [ofDecimal_overflow_eq d h_out]
  constructor
  · unfold isInfBits
    rw [h_be, h_mb]
    decide
  · exact h_sb

/-- **`Clinger.ofDecimal` is a correct reader.** -/
theorem isCorrectReader_ofDecimal : IsCorrectReader Clinger.ofDecimal :=
  fun d => ⟨ofDecimal_isNearestFloat d, ofDecimal_overflow d⟩

/-! ## Forward direction: the spec pins the bits down -/

/-- Every finite shape is realized by a float of either sign. -/
theorem exists_float_of_finShape (sign : Bool) (m : Nat) (q : Int)
    (hs : FinShape m q) :
    ∃ g : _root_.Float, isFiniteBits g = true ∧ (decode g).sign = sign
      ∧ (decode g).m = m ∧ (decode g).q = q := by
  by_cases hm : m < 2 ^ 52
  · -- Subnormal or zero: biased exponent 0.
    have hq : q = -1074 := hs.q_eq_of_small hm
    obtain ⟨h_sb, h_be, h_mb⟩ := fromBits_proj sign 0 m (by norm_num) hm (by omega)
    refine ⟨fromBits sign 0 m, ?_, ?_, ?_, ?_⟩
    · unfold isFiniteBits
      rw [h_be]
      decide
    · rw [← signBit_eq_decode_sign]
      exact h_sb
    · unfold decode
      rw [if_pos h_be]
      exact h_mb
    · unfold decode
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
    obtain ⟨h_sb, h_be, h_mb⟩ := fromBits_proj sign be (m - 2 ^ 52) hbe_lt hmb_lt h_nan
    have h_be_ne : ¬ (biasedExpBits (fromBits sign be (m - 2 ^ 52)) = 0) := by
      rw [h_be]
      exact hbe_ne
    refine ⟨fromBits sign be (m - 2 ^ 52), ?_, ?_, ?_, ?_⟩
    · unfold isFiniteBits
      rw [h_be]
      simp only [decide_eq_true_eq]
      omega
    · rw [← signBit_eq_decode_sign]
      exact h_sb
    · unfold decode
      rw [if_neg h_be_ne]
      simp only
      rw [h_mb]
      have h52 : (1 <<< 52 : Nat) = 2 ^ 52 := rfl
      omega
    · unfold decode
      rw [if_neg h_be_ne]
      simp only
      rw [h_be]
      omega

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
      · exact Or.inr (Or.inl ⟨by omega, by norm_num, rfl⟩)
      · by_cases h52 : m + 1 < 2 ^ 52
        · exact Or.inr (Or.inl ⟨by omega, h52, h3⟩)
        · exact Or.inr (Or.inr ⟨by omega, by omega, by omega, by omega⟩)
      · exact Or.inr (Or.inr ⟨by omega, hm1, h3, h4⟩)
    · unfold magVal
      push_cast
      ring
  · -- m + 1 = 2^53: renormalise into the next binade.
    have hm_lt := hs.m_lt
    have hm_eq : m + 1 = 2 ^ 53 := by omega
    have hm_cast : ((m : ℚ)) + 1 = 2 ^ (53 : ℕ) := by
      have h1 : ((m + 1 : Nat) : ℚ) = ((2 ^ 53 : Nat) : ℚ) := by rw [hm_eq]
      push_cast at h1
      linarith
    have h_val_id : magVal m q + (2 : ℚ) ^ q
        = ((2 ^ 52 : Nat) : ℚ) * (2 : ℚ) ^ (q + 1) := by
      unfold magVal
      rw [zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_one]
      push_cast
      have hm' : (m : ℚ) = 2 ^ (53 : ℕ) - 1 := by linarith [hm_cast]
      rw [hm', show (2 : ℚ) ^ (53 : ℕ) = 2 ^ (52 : ℕ) * 2 from by norm_num]
      ring
    have hgap := magVal_gap_up m m' q q' hs (Or.inr hleg') h_lt
    have hq1_le : q + 1 ≤ 971 := by
      by_contra hgt
      -- Then v + 2^q = 2^52·2^(q+1) ≥ 2^52·2^972 = 2^1024 exceeds every legal value.
      have h972 : (2 : ℚ) ^ (972 : ℤ) ≤ (2 : ℚ) ^ (q + 1) :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
      have h_v'_lt : magVal m' q' < ((2 ^ 53 : Nat) : ℚ) * (2 : ℚ) ^ (971 : ℤ) := by
        unfold magVal
        have hm'_lt : (m' : ℚ) < ((2 ^ 53 : Nat) : ℚ) := by
          have : m' < 2 ^ 53 := by
            rcases hleg' with ⟨_, h, _⟩ | ⟨_, h, _⟩ <;> omega
          exact_mod_cast this
        have hq'_le : (2 : ℚ) ^ q' ≤ (2 : ℚ) ^ (971 : ℤ) :=
          zpow_le_zpow_right₀ (by norm_num) (by
            rcases hleg' with ⟨_, _, hqe⟩ | ⟨_, _, _, hle⟩ <;> omega)
        have h2_971 := two_zpow_pos (971 : ℤ)
        calc (m' : ℚ) * (2 : ℚ) ^ q' ≤ (m' : ℚ) * (2 : ℚ) ^ (971 : ℤ) :=
              mul_le_mul_of_nonneg_left hq'_le (Nat.cast_nonneg m')
        _ < ((2 ^ 53 : Nat) : ℚ) * (2 : ℚ) ^ (971 : ℤ) :=
              mul_lt_mul_of_pos_right hm'_lt h2_971
      have h_id : ((2 ^ 53 : Nat) : ℚ) * (2 : ℚ) ^ (971 : ℤ)
          = ((2 ^ 52 : Nat) : ℚ) * (2 : ℚ) ^ (972 : ℤ) := by
        rw [show (972 : ℤ) = 971 + 1 from rfl, zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0),
            zpow_one]
        push_cast
        ring
      have h_52_pos : (0 : ℚ) < ((2 ^ 52 : Nat) : ℚ) := by positivity
      have h_chain : magVal m' q' < magVal m q + (2 : ℚ) ^ q := by
        rw [h_val_id]
        calc magVal m' q' < ((2 ^ 53 : Nat) : ℚ) * (2 : ℚ) ^ (971 : ℤ) := h_v'_lt
        _ = ((2 ^ 52 : Nat) : ℚ) * (2 : ℚ) ^ (972 : ℤ) := h_id
        _ ≤ ((2 ^ 52 : Nat) : ℚ) * (2 : ℚ) ^ (q + 1) :=
              mul_le_mul_of_nonneg_left h972 (le_of_lt h_52_pos)
      linarith [hgap]
    refine ⟨2 ^ 52, q + 1,
      Or.inr (Or.inr ⟨le_refl _, by norm_num, by have := hs.q_ge; omega, hq1_le⟩), ?_⟩
    rw [h_val_id]
    rfl

/-- Two spec-satisfying floats at the same in-range decimal carry the
same value: a genuine two-sided tie would demand even mantissas on two
grid-adjacent magnitudes, which alternate parity. -/
private theorem tie_values_eq (d : Decimal) (f g : _root_.Float)
    (hfF : isFiniteBits f = true) (hgF : isFiniteBits g = true)
    (hfs' : (decode f).sign = d.sign) (hgs' : (decode g).sign = d.sign)
    (hf_near : ∀ g' : _root_.Float, isFiniteBits g' = true →
       |floatVal f - Decimal.toRat d| ≤ |floatVal g' - Decimal.toRat d|)
    (hg_near : ∀ g' : _root_.Float, isFiniteBits g' = true →
       |floatVal g - Decimal.toRat d| ≤ |floatVal g' - Decimal.toRat d|)
    (hf_even : mantissaBits f % 2 = 0) (hg_even : mantissaBits g % 2 = 0)
    (h_dist : |floatVal g - Decimal.toRat d| = |floatVal f - Decimal.toRat d|) :
    floatVal g = floatVal f := by
  by_contra h_val
  have h_shape_f := decode_finShape f hfF
  have h_shape_g := decode_finShape g hgF
  have h_mf_even : (decode f).m % 2 = 0 := by rw [decode_m_parity]; exact hf_even
  have h_mg_even : (decode g).m % 2 = 0 := by rw [decode_m_parity]; exact hg_even
  set u := gridVal d.significand d.exponent with hu
  set v := magVal (decode f).m (decode f).q with hv
  set w := magVal (decode g).m (decode g).q with hw
  have h_dist' : |w - u| = |v - u| := by
    rw [floatVal_dist_reduce d g hgs', floatVal_dist_reduce d f hfs'] at h_dist
    exact h_dist
  have h_mag_ne : w ≠ v := by
    intro hmm
    apply h_val
    rw [floatVal_eq_signFactor_magVal, floatVal_eq_signFactor_magVal, hgs', hfs',
        ← hv, ← hw, hmm]
  rcases lt_trichotomy w v with hwv | hwv | hwv
  · -- w < v: u is the exact midpoint; g's successor breaks the tie.
    have h2u : 2 * u = w + v := by
      rw [abs_sub_comm w u, abs_sub_comm v u] at h_dist'
      exact (abs_eq_abs_iff_two_eq u w v hwv).mp h_dist'
    have h_mf_ne : (decode f).m ≠ 0 := by
      intro h0
      have : v = 0 := by rw [hv, h0]; exact magVal_zero_eq _
      have := hw ▸ magVal_nonneg (decode g).m (decode g).q
      linarith
    obtain ⟨ms, qs, hss, hsval⟩ := succ_finShape (decode g).m (decode g).q
      (decode f).m (decode f).q h_shape_g (h_shape_f.legal_of_ne h_mf_ne) (hw ▸ hv ▸ hwv)
    have h_le : magVal ms qs ≤ v := by
      rw [hsval]
      exact hv ▸ magVal_gap_up (decode g).m (decode f).m (decode g).q (decode f).q
        h_shape_g h_shape_f (hw ▸ hv ▸ hwv)
    have h2qg := two_zpow_pos (decode g).q
    rcases eq_or_lt_of_le h_le with h_eq | h_lt
    · -- Exactly the successor: parity alternation contradicts both-even.
      have h_parity := magVal_succ_parity (decode g).m (decode f).m
        (decode g).q (decode f).q h_shape_g (h_shape_f.legal_of_ne h_mf_ne)
        (by rw [← hsval, h_eq, hv])
      omega
    · -- Strictly between w and v: strictly closer to u than the tie distance.
      obtain ⟨g₂, hg₂F, hg₂s, hg₂m, hg₂q⟩ := exists_float_of_finShape d.sign ms qs hss
      have h_w_le_u : w ≤ u := by linarith
      have h_dist_g : |floatVal g - Decimal.toRat d| = u - w := by
        rw [floatVal_dist_reduce d g hgs', ← hw, ← hu,
            abs_of_nonpos (by linarith : w - u ≤ 0)]
        ring
      have h_dist_g₂ : |floatVal g₂ - Decimal.toRat d| < u - w := by
        rw [floatVal_dist_reduce d g₂ hg₂s, hg₂m, hg₂q, ← hu]
        have h_s_gt : w < magVal ms qs := by
          rw [hsval, ← hw]
          linarith
        rcases abs_cases (magVal ms qs - u) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
          · rw [h1]
            linarith
      have := hg_near g₂ hg₂F
      rw [h_dist_g] at this
      exact absurd (lt_of_le_of_lt this h_dist_g₂) (lt_irrefl _)
  · exact h_mag_ne hwv
  · -- v < w: mirror image, using f's successor and f's minimality.
    have h2u : 2 * u = v + w := by
      rw [abs_sub_comm w u, abs_sub_comm v u] at h_dist'
      exact (abs_eq_abs_iff_two_eq u v w hwv).mp h_dist'.symm
    have h_mg_ne : (decode g).m ≠ 0 := by
      intro h0
      have : w = 0 := by rw [hw, h0]; exact magVal_zero_eq _
      have := hv ▸ magVal_nonneg (decode f).m (decode f).q
      linarith
    obtain ⟨ms, qs, hss, hsval⟩ := succ_finShape (decode f).m (decode f).q
      (decode g).m (decode g).q h_shape_f (h_shape_g.legal_of_ne h_mg_ne) (hv ▸ hw ▸ hwv)
    have h_le : magVal ms qs ≤ w := by
      rw [hsval]
      exact hw ▸ magVal_gap_up (decode f).m (decode g).m (decode f).q (decode g).q
        h_shape_f h_shape_g (hv ▸ hw ▸ hwv)
    have h2qf := two_zpow_pos (decode f).q
    rcases eq_or_lt_of_le h_le with h_eq | h_lt
    · have h_parity := magVal_succ_parity (decode f).m (decode g).m
        (decode f).q (decode g).q h_shape_f (h_shape_g.legal_of_ne h_mg_ne)
        (by rw [← hsval, h_eq, hw])
      omega
    · obtain ⟨g₂, hg₂F, hg₂s, hg₂m, hg₂q⟩ := exists_float_of_finShape d.sign ms qs hss
      have h_v_le_u : v ≤ u := by linarith
      have h_dist_f : |floatVal f - Decimal.toRat d| = u - v := by
        rw [floatVal_dist_reduce d f hfs', ← hv, ← hu,
            abs_of_nonpos (by linarith : v - u ≤ 0)]
        ring
      have h_dist_g₂ : |floatVal g₂ - Decimal.toRat d| < u - v := by
        rw [floatVal_dist_reduce d g₂ hg₂s, hg₂m, hg₂q, ← hu]
        have h_s_gt : v < magVal ms qs := by
          rw [hsval, ← hv]
          linarith
        rcases abs_cases (magVal ms qs - u) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
          · rw [h1]
            linarith
      have := hf_near g₂ hg₂F
      rw [h_dist_f] at this
      exact absurd (lt_of_le_of_lt this h_dist_g₂) (lt_irrefl _)

/-- **Forward direction.** A float satisfying the reader spec at `d` has
exactly `ofDecimal d`'s bits. -/
theorem spec_toBits_eq (d : Decimal) (g : _root_.Float)
    (h_near : |Decimal.toRat d| < 2 ^ 1024 - 2 ^ 970 → IsNearestFloat d g)
    (h_over : (2 : ℚ) ^ 1024 - 2 ^ 970 ≤ |Decimal.toRat d| →
       isInfBits g = true ∧ signBit g = d.sign) :
    g.toBits = (Clinger.ofDecimal d).toBits := by
  rcases lt_or_ge |Decimal.toRat d| ((2 : ℚ) ^ 1024 - 2 ^ 970) with h_in | h_out
  · -- In range: both are nearest floats, tie analysis forces equal values.
    obtain ⟨hgF, hgs, hg_near, hg_tie⟩ := h_near h_in
    obtain ⟨hfF, hfs, hf_near, hf_tie⟩ := ofDecimal_isNearestFloat d h_in
    have hgs' : (decode g).sign = d.sign := by
      rw [← signBit_eq_decode_sign]; exact hgs
    have hfs' : (decode (Clinger.ofDecimal d)).sign = d.sign := by
      rw [← signBit_eq_decode_sign]; exact hfs
    have h_dist : |floatVal g - Decimal.toRat d|
        = |floatVal (Clinger.ofDecimal d) - Decimal.toRat d| :=
      le_antisymm (hg_near _ hfF) (hf_near g hgF)
    have h_val : floatVal g = floatVal (Clinger.ofDecimal d) := by
      by_cases h : floatVal g = floatVal (Clinger.ofDecimal d)
      · exact h
      · -- An exact two-sided tie: both tie clauses fire.
        have h_mg_even : mantissaBits g % 2 = 0 :=
          hg_tie _ hfF (fun hh => h hh.symm) h_dist.symm
        have h_mf_even : mantissaBits (Clinger.ofDecimal d) % 2 = 0 :=
          hf_tie g hgF h h_dist
        exact tie_values_eq d (Clinger.ofDecimal d) g hfF hgF hfs' hgs'
          hf_near hg_near h_mf_even h_mg_even h_dist
    -- Equal values, equal signs: identical decode, identical bits.
    have h_mag : magVal (decode g).m (decode g).q
        = magVal (decode (Clinger.ofDecimal d)).m (decode (Clinger.ofDecimal d)).q := by
      rw [floatVal_eq_signFactor_magVal, floatVal_eq_signFactor_magVal,
          hgs', hfs'] at h_val
      have hsf : signFactor d.sign ≠ 0 := by
        unfold signFactor
        split <;> norm_num
      exact mul_left_cancel₀ hsf h_val
    obtain ⟨hm_eq, hq_eq⟩ := magVal_inj _ _ _ _ (decode_finShape g hgF)
      (decode_finShape _ hfF) h_mag
    exact toBits_eq_of_decode_eq g _ hgF hfF (hgs.trans hfs.symm) hm_eq hq_eq
  · -- Overflow: both are the signed-infinity pattern.
    obtain ⟨hg_inf, hg_sb⟩ := h_over h_out
    have hg_fields : biasedExpBits g = 2047 ∧ mantissaBits g = 0 := by
      unfold isInfBits at hg_inf
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hg_inf
      exact hg_inf
    have hg_nan : isNaNBits g = false := by
      unfold isNaNBits
      rw [hg_fields.2]
      simp
    have h1 := fromBits_decode_eq g hg_nan
    rw [hg_sb, hg_fields.1, hg_fields.2] at h1
    rw [ofDecimal_overflow_eq d h_out]
    exact h1.symm

/-- The reader spec transports along bit equality. -/
private theorem isNearestFloat_congr_bits (d : Decimal) (f₁ f₂ : _root_.Float)
    (h : f₂.toBits = f₁.toBits) (h₁ : IsNearestFloat d f₁) :
    IsNearestFloat d f₂ := by
  have hdec : decode f₂ = decode f₁ := by
    unfold decode biasedExpBits mantissaBits signBit
    rw [h]
  have hfv : floatVal f₂ = floatVal f₁ := by
    unfold floatVal
    rw [hdec]
  have hsb : signBit f₂ = signBit f₁ := by
    unfold signBit
    rw [h]
  have hfin : isFiniteBits f₂ = isFiniteBits f₁ := by
    unfold isFiniteBits biasedExpBits
    rw [h]
  have hmb : mantissaBits f₂ = mantissaBits f₁ := by
    unfold mantissaBits
    rw [h]
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
theorem correct_iff_ofDecimal_proof (p : Decimal → _root_.Float) :
    IsCorrectReader p
      ↔ ∀ d : Decimal, (p d).toBits = (Clinger.ofDecimal d).toBits := by
  constructor
  · intro h d
    exact spec_toBits_eq d (p d) (h d).1 (h d).2
  · intro h d
    refine ⟨?_, ?_⟩
    · intro h_in
      exact isNearestFloat_congr_bits d (Clinger.ofDecimal d) (p d) (h d)
        (ofDecimal_isNearestFloat d h_in)
    · intro h_out
      obtain ⟨hf_inf, hf_sb⟩ := ofDecimal_overflow d h_out
      have hb := h d
      constructor
      · rw [show isInfBits (p d) = isInfBits (Clinger.ofDecimal d) from by
              unfold isInfBits biasedExpBits mantissaBits
              rw [hb]]
        exact hf_inf
      · rw [show signBit (p d) = signBit (Clinger.ofDecimal d) from by
              unfold signBit
              rw [hb]]
        exact hf_sb

end PP.Numeric.Clinger

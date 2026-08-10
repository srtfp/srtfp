/- Native integer continuant theory for the R20 sweep.

   Core-only replacement for the Mathlib continued-fraction machinery
   (`GenContFract`, Legendre via `Real.exists_convs_eq_rat`): everything
   here is elementary `Nat`/`Int` arithmetic about the Euclidean
   remainder sequence of `(u, M)` and its continuant numerators and
   denominators.  The centerpiece is `small_den_is_denN`, the rational
   Legendre theorem in scaled integer form: a coprime fraction `p/d`
   approximating `u/M` to quality `|u·d − M·p| · 2d < M` has `d` equal
   to a continuant denominator.

   The definitions (`rem`, `qt`, `denI`, `numI`, `denN`) moved here
   verbatim from `R20Keystone.lean`; the theory below replaces that
   file's bridge to Mathlib's `GenContFract`. -/

import Srtfp.Rat
import Srtfp.Tactics

namespace Srtfp.Schubfach.R20Sweep

/-! ## The Euclidean remainder sequence and its continuants -/

/-- Euclidean remainder sequence of `(u, M)`: `rem 0 = M`, `rem 1 = u % M`,
`rem (n+2) = rem n % rem (n+1)`. -/
def rem (u M : Nat) : Nat → Nat
  | 0 => M
  | 1 => u % M
  | (n+2) => rem u M n % rem u M (n+1)

theorem rem_add_two (u M n : Nat) : rem u M (n+2) = rem u M n % rem u M (n+1) := rfl

/-- Euclidean partial quotient at continuant index `n`. -/
def qt (u M n : Nat) : Nat := rem u M n / rem u M (n+1)

/-- Integer continuant denominators. -/
def denI (u M : Nat) : Nat → ℤ
  | 0 => 1
  | 1 => (qt u M 0 : ℤ)
  | (n+2) => (qt u M (n+1) : ℤ) * denI u M (n+1) + denI u M n

/-- Integer continuant numerators. -/
def numI (u M : Nat) : Nat → ℤ
  | 0 => (u / M : Nat)
  | 1 => (qt u M 0 : ℤ) * (u / M : Nat) + 1
  | (n+2) => (qt u M (n+1) : ℤ) * numI u M (n+1) + numI u M n

/-- `Nat`-valued continuant denominator `(denI u M n).natAbs`. -/
def denN (u M n : Nat) : Nat := (denI u M n).natAbs

/-- The division identity driving every recurrence:
`qt n · rem (n+1) + rem (n+2) = rem n`. -/
theorem qt_mul_add_rem (u M n : Nat) :
    qt u M n * rem u M (n+1) + rem u M (n+2) = rem u M n := by
  rw [rem_add_two]
  have := Nat.div_add_mod (rem u M n) (rem u M (n+1))
  unfold qt
  grind

/-- `qt_mul_add_rem`, cast to `ℤ` with the product distributed. -/
theorem qt_mul_add_rem_int (u M n : Nat) :
    (qt u M n : ℤ) * ((rem u M (n+1) : Nat) : ℤ) + ((rem u M (n+2) : Nat) : ℤ)
      = ((rem u M n : Nat) : ℤ) := by
  exact_mod_cast qt_mul_add_rem u M n

/-! ## The error term and its invariant -/

/-- Scaled approximation error of the `n`th convergent:
`eI n = u · denI n − M · numI n`. -/
def eI (u M : Nat) (n : Nat) : ℤ := (u : ℤ) * denI u M n - (M : ℤ) * numI u M n

theorem eI_zero (u M : Nat) : eI u M 0 = ((rem u M 1 : Nat) : ℤ) := by
  show (u : ℤ) * 1 - (M : ℤ) * ((u / M : Nat) : ℤ) = ((u % M : Nat) : ℤ)
  have hdm : (M : ℤ) * ((u / M : Nat) : ℤ) + ((u % M : Nat) : ℤ) = (u : ℤ) := by
    exact_mod_cast Nat.div_add_mod u M
  omega

theorem eI_one (u M : Nat) : eI u M 1 = -((rem u M 2 : Nat) : ℤ) := by
  show (u : ℤ) * (qt u M 0 : ℤ) - (M : ℤ) * ((qt u M 0 : ℤ) * ((u / M : Nat) : ℤ) + 1)
      = -((rem u M 2 : Nat) : ℤ)
  have hdm : (M : ℤ) * ((u / M : Nat) : ℤ) + ((u % M : Nat) : ℤ) = (u : ℤ) := by
    exact_mod_cast Nat.div_add_mod u M
  have hq := qt_mul_add_rem_int u M 0
  simp only [Nat.zero_add] at hq
  have hrem0 : ((rem u M 0 : Nat) : ℤ) = (M : ℤ) := rfl
  have hrem1 : ((rem u M 1 : Nat) : ℤ) = ((u % M : Nat) : ℤ) := rfl
  rw [hrem0, hrem1] at hq
  -- u·q0 − M·(q0·(u/M) + 1) = q0·(u − M·(u/M)) − M = q0·(u%M) − M = −rem 2
  have expand : (u : ℤ) * (qt u M 0 : ℤ) - (M : ℤ) * ((qt u M 0 : ℤ) * ((u / M : Nat) : ℤ) + 1)
      = (qt u M 0 : ℤ) * ((u : ℤ) - (M : ℤ) * ((u / M : Nat) : ℤ)) - (M : ℤ) := by grind
  rw [expand]
  have hfrac : (u : ℤ) - (M : ℤ) * ((u / M : Nat) : ℤ) = ((u % M : Nat) : ℤ) := by omega
  rw [hfrac]
  omega

theorem eI_add_two (u M n : Nat) :
    eI u M (n+2) = (qt u M (n+1) : ℤ) * eI u M (n+1) + eI u M n := by
  show (u : ℤ) * ((qt u M (n+1) : ℤ) * denI u M (n+1) + denI u M n)
      - (M : ℤ) * ((qt u M (n+1) : ℤ) * numI u M (n+1) + numI u M n)
      = (qt u M (n+1) : ℤ) * ((u : ℤ) * denI u M (n+1) - (M : ℤ) * numI u M (n+1))
        + ((u : ℤ) * denI u M n - (M : ℤ) * numI u M n)
  grind

/-- The Euclid invariant: `eI n = (−1)ⁿ · rem (n+1)`, phrased by parity. -/
theorem eI_eq (u M : Nat) : ∀ n,
    eI u M n = if n % 2 = 0 then ((rem u M (n+1) : Nat) : ℤ)
               else -((rem u M (n+1) : Nat) : ℤ) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n IH =>
    match n with
    | 0 => simpa using eI_zero u M
    | 1 => simpa using eI_one u M
    | (n+2) =>
      rw [eI_add_two, IH (n+1) (by omega), IH n (by omega)]
      have hq := qt_mul_add_rem_int u M (n+1)
      simp only [show n+1+1 = n+2 from rfl, show n+1+2 = n+3 from rfl] at hq
      have hdist : (qt u M (n+1) : ℤ) * -((rem u M (n+2) : Nat) : ℤ)
          = -((qt u M (n+1) : ℤ) * ((rem u M (n+2) : Nat) : ℤ)) := by grind
      rcases Nat.mod_two_eq_zero_or_one n with hk | hk
      · rw [if_pos hk, if_neg (by omega : ¬((n+1) % 2 = 0)),
            if_pos (by omega : (n+2) % 2 = 0)]
        simp only [show n+1+1 = n+2 from rfl, show n+2+1 = n+3 from rfl, hdist]
        omega
      · rw [if_neg (by omega : ¬(n % 2 = 0)), if_pos (by omega : (n+1) % 2 = 0),
            if_neg (by omega : ¬((n+2) % 2 = 0))]
        simp only [show n+1+1 = n+2 from rfl, show n+2+1 = n+3 from rfl]
        omega

/-! ## Determinant of the continuant pair -/

/-- Continuant determinant: `numI (n+1) · denI n − numI n · denI (n+1) = (−1)ⁿ`. -/
theorem det_eq (u M : Nat) : ∀ n,
    numI u M (n+1) * denI u M n - numI u M n * denI u M (n+1)
      = if n % 2 = 0 then 1 else -1 := by
  intro n
  induction n with
  | zero =>
    show ((qt u M 0 : ℤ) * ((u / M : Nat) : ℤ) + 1) * 1
        - ((u / M : Nat) : ℤ) * (qt u M 0 : ℤ) = _
    simp only [show (0 : Nat) % 2 = 0 from rfl, reduceIte]
    grind
  | succ n IH =>
    have hstep : numI u M (n+2) * denI u M (n+1) - numI u M (n+1) * denI u M (n+2)
        = -(numI u M (n+1) * denI u M n - numI u M n * denI u M (n+1)) := by
      show ((qt u M (n+1) : ℤ) * numI u M (n+1) + numI u M n) * denI u M (n+1)
          - numI u M (n+1) * ((qt u M (n+1) : ℤ) * denI u M (n+1) + denI u M n) = _
      grind
    rw [hstep, IH]
    rcases Nat.mod_two_eq_zero_or_one n with hk | hk
    · rw [if_pos hk, if_neg (by omega : ¬((n+1) % 2 = 0))]
    · rw [if_neg (by omega : ¬(n % 2 = 0)), if_pos (by omega : (n+1) % 2 = 0)]
      decide

/-! ## The fundamental identity `rem (n+1) · denI (n+1) + rem (n+2) · denI n = M` -/

theorem rem_denI_identity (u M : Nat) : ∀ n,
    ((rem u M (n+1) : Nat) : ℤ) * denI u M (n+1) + ((rem u M (n+2) : Nat) : ℤ) * denI u M n
      = (M : ℤ) := by
  intro n
  induction n with
  | zero =>
    show ((rem u M 1 : Nat) : ℤ) * (qt u M 0 : ℤ) + ((rem u M 2 : Nat) : ℤ) * 1 = (M : ℤ)
    have hq := qt_mul_add_rem_int u M 0
    have hrem0 : ((rem u M 0 : Nat) : ℤ) = (M : ℤ) := rfl
    rw [hrem0] at hq
    grind
  | succ n IH =>
    have hexp : ((rem u M (n+2) : Nat) : ℤ) * denI u M (n+2)
        + ((rem u M (n+3) : Nat) : ℤ) * denI u M (n+1)
        = ((rem u M (n+2) : Nat) : ℤ) * denI u M n
          + (((qt u M (n+1) : ℤ) * ((rem u M (n+2) : Nat) : ℤ)
              + ((rem u M (n+3) : Nat) : ℤ)) * denI u M (n+1)) := by
      show ((rem u M (n+2) : Nat) : ℤ) * ((qt u M (n+1) : ℤ) * denI u M (n+1) + denI u M n)
          + _ = _
      grind
    rw [hexp, qt_mul_add_rem_int u M (n+1)]
    -- rem(n+2)·denI n + rem(n+1)·denI(n+1) = M  (IH, commuted)
    grind

end Srtfp.Schubfach.R20Sweep

namespace Srtfp.Schubfach.R20Sweep

/-! ## Regime lemmas: positivity, monotonicity, termination -/

theorem rem_one_lt (u M : Nat) (hM : 0 < M) : rem u M 1 < M := Nat.mod_lt _ hM

theorem rem_succ_lt (u M n : Nat) (h : 0 < rem u M (n+1)) :
    rem u M (n+2) < rem u M (n+1) := by
  rw [rem_add_two]; exact Nat.mod_lt _ h

/-- Partial quotients are `≥ 1` inside the positivity regime. -/
theorem qt_pos (u M : Nat) (hM : 0 < M) :
    ∀ n, (∀ i, i ≤ n+1 → 0 < rem u M i) → 1 ≤ qt u M n := by
  intro n hpos
  have h1 : 0 < rem u M (n+1) := hpos (n+1) (Nat.le_refl _)
  have hle : rem u M (n+1) ≤ rem u M n := by
    match n with
    | 0 => exact Nat.le_of_lt (rem_one_lt u M hM)
    | (m+1) =>
      show rem u M (m+2) ≤ rem u M (m+1)
      have := rem_succ_lt u M m (hpos (m+1) (by omega))
      omega
  unfold qt
  exact (Nat.le_div_iff_mul_le h1).mpr (by omega)

theorem denI_pos (u M : Nat) (hM : 0 < M) :
    ∀ n, (∀ i, i ≤ n → 0 < rem u M i) → 0 < denI u M n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n IH =>
    intro hpos
    match n with
    | 0 => exact Int.zero_lt_one
    | 1 =>
      show (0 : ℤ) < (qt u M 0 : ℤ)
      exact_mod_cast qt_pos u M hM 0 (fun i hi => hpos i hi)
    | (n+2) =>
      have hq : 1 ≤ qt u M (n+1) := qt_pos u M hM (n+1) (fun i hi => hpos i hi)
      have h1 : 0 < denI u M (n+1) := IH (n+1) (by omega) (fun i hi => hpos i (by omega))
      have h0 : 0 < denI u M n := IH n (by omega) (fun i hi => hpos i (by omega))
      show (0 : ℤ) < (qt u M (n+1) : ℤ) * denI u M (n+1) + denI u M n
      have : (1 : ℤ) ≤ (qt u M (n+1) : ℤ) := by exact_mod_cast hq
      have hmul : denI u M (n+1) ≤ (qt u M (n+1) : ℤ) * denI u M (n+1) := by
        calc denI u M (n+1) = 1 * denI u M (n+1) := by grind
          _ ≤ (qt u M (n+1) : ℤ) * denI u M (n+1) :=
              Int.mul_le_mul_of_nonneg_right this (Int.le_of_lt h1)
      omega

/-- Strict growth: `denI n < denI (n+2)` inside the regime (and one-step
monotonicity `denI (n+1) ≤ denI (n+2)`). -/
theorem denI_lt_add_two (u M : Nat) (hM : 0 < M) (n : Nat)
    (hpos : ∀ i, i ≤ n+2 → 0 < rem u M i) :
    denI u M (n+1) < denI u M (n+2) := by
  have hq : 1 ≤ qt u M (n+1) := qt_pos u M hM (n+1) (fun i hi => hpos i (by omega))
  have h1 : 0 < denI u M (n+1) := denI_pos u M hM (n+1) (fun i hi => hpos i (by omega))
  have h0 : 0 < denI u M n := denI_pos u M hM n (fun i hi => hpos i (by omega))
  show denI u M (n+1) < (qt u M (n+1) : ℤ) * denI u M (n+1) + denI u M n
  have : (1 : ℤ) ≤ (qt u M (n+1) : ℤ) := by exact_mod_cast hq
  have hmul : denI u M (n+1) ≤ (qt u M (n+1) : ℤ) * denI u M (n+1) := by
    calc denI u M (n+1) = 1 * denI u M (n+1) := by grind
      _ ≤ (qt u M (n+1) : ℤ) * denI u M (n+1) :=
          Int.mul_le_mul_of_nonneg_right this (Int.le_of_lt h1)
  omega

/-- The gcd of consecutive remainders is invariant (Euclid). -/
theorem gcd_rem_invariant (u M : Nat) :
    ∀ n, Nat.gcd (rem u M (n+1)) (rem u M n) = Nat.gcd (rem u M 1) (rem u M 0) := by
  intro n
  induction n with
  | zero => rfl
  | succ n IH =>
    rw [← IH]
    show Nat.gcd (rem u M n % rem u M (n+1)) (rem u M (n+1)) = _
    exact (Nat.gcd_rec (rem u M (n+1)) (rem u M n)).symm

/-- Termination detection: if `rem (n+2) = 0` inside the regime and `u, M`
are coprime, then `rem (n+1) = 1` and hence `denI (n+1) = M`. -/
theorem denI_eq_M_of_terminated (u M : Nat) (_hM : 0 < M) (hco : Nat.Coprime u M)    (n : Nat) (_hpos : ∀ i, i ≤ n+1 → 0 < rem u M i) (hz : rem u M (n+2) = 0) :
    denI u M (n+1) = (M : ℤ) := by
  have hgcd := gcd_rem_invariant u M (n+1)
  simp only [show n+1+1 = n+2 from rfl] at hgcd
  have hco' : Nat.gcd (rem u M 1) (rem u M 0) = 1 := by
    show Nat.gcd (u % M) M = 1
    have hco'' : Nat.gcd u M = 1 := hco
    rw [← Nat.gcd_rec M u, Nat.gcd_comm]
    exact hco''
  have hone : rem u M (n+1) = 1 := by
    rw [hco', hz, Nat.gcd_zero_left] at hgcd
    exact hgcd
  have hid := rem_denI_identity u M n
  rw [show ((rem u M (n+2) : Nat) : ℤ) = 0 by exact_mod_cast hz, hone] at hid
  simpa using hid

end Srtfp.Schubfach.R20Sweep

namespace Srtfp.Schubfach.R20Sweep

/-! ## The bracketed Legendre step

If `denI n ≤ d < denI (n+1)` inside the regime and the coprime fraction
`p/d` approximates `u/M` to quality `|u·d − M·p| · 2d < M`, then
`d = denI n`.  This is Legendre's theorem for the rational `u/M`,
in scaled integer form. -/

theorem bracket_eq_denI (u M p d n : Nat) (hM : 0 < M)
    (hpos : ∀ i, i ≤ n+1 → 0 < rem u M i)
    (hcop : Nat.gcd p d = 1) (hd : 0 < d)
    (hlo : denI u M n ≤ (d : ℤ)) (hhi : (d : ℤ) < denI u M (n+1))
    (hsmall : ((u : ℤ) * d - (M : ℤ) * p).natAbs * (2 * d) < M) :
    (d : ℤ) = denI u M n := by
  -- Abbreviations.
  have hD0 : 0 < denI u M n := denI_pos u M hM n (fun i hi => hpos i (by omega))
  have hD1 : 0 < denI u M (n+1) := denI_pos u M hM (n+1) hpos
  -- Determinant, as a disjunction.
  have hdet : numI u M (n+1) * denI u M n - numI u M n * denI u M (n+1) = 1
      ∨ numI u M (n+1) * denI u M n - numI u M n * denI u M (n+1) = -1 := by
    have := det_eq u M n
    rcases Nat.mod_two_eq_zero_or_one n with hk | hk
    · left; rw [if_pos hk] at this; exact this
    · right; rw [if_neg (by omega)] at this; exact this
  -- Cramer coefficients.
  set Δ : ℤ := numI u M (n+1) * denI u M n - numI u M n * denI u M (n+1) with hΔ_def
  have hΔsq : Δ * Δ = 1 := by rcases hdet with h | h <;> (try rw [← hΔ_def] at h) <;> rw [h] <;> decide
  set α : ℤ := Δ * ((d : ℤ) * numI u M (n+1) - (p : ℤ) * denI u M (n+1)) with hα_def
  set β : ℤ := Δ * ((p : ℤ) * denI u M n - (d : ℤ) * numI u M n) with hβ_def
  have eq1 : α * denI u M n + β * denI u M (n+1) = (d : ℤ) := by
    rw [hα_def, hβ_def]
    have h1 : Δ * ((d : ℤ) * numI u M (n+1) - (p : ℤ) * denI u M (n+1)) * denI u M n
        + Δ * ((p : ℤ) * denI u M n - (d : ℤ) * numI u M n) * denI u M (n+1)
        = (Δ * Δ) * (d : ℤ) := by rw [← hΔ_def] at *; grind
    rw [h1, hΔsq]; grind
  have eq2 : α * numI u M n + β * numI u M (n+1) = (p : ℤ) := by
    rw [hα_def, hβ_def]
    have h1 : Δ * ((d : ℤ) * numI u M (n+1) - (p : ℤ) * denI u M (n+1)) * numI u M n
        + Δ * ((p : ℤ) * denI u M n - (d : ℤ) * numI u M n) * numI u M (n+1)
        = (Δ * Δ) * (p : ℤ) := by rw [← hΔ_def] at *; grind
    rw [h1, hΔsq]; grind
  -- The error decomposition.
  have heq3 : (u : ℤ) * d - (M : ℤ) * p = α * eI u M n + β * eI u M (n+1) := by
    have h1 : (u : ℤ) * ((d : ℤ)) - (M : ℤ) * ((p : ℤ))
        = (u : ℤ) * (α * denI u M n + β * denI u M (n+1))
          - (M : ℤ) * (α * numI u M n + β * numI u M (n+1)) := by rw [eq1, eq2]
    rw [h1]
    show _ = α * ((u : ℤ) * denI u M n - (M : ℤ) * numI u M n)
        + β * ((u : ℤ) * denI u M (n+1) - (M : ℤ) * numI u M (n+1))
    grind
  by_cases hβ0 : β = 0
  · -- `d = α · denI n` with `gcd p d = 1` forces `α = 1`.
    rw [hβ0] at eq1 eq2
    simp only [Int.zero_mul, Int.add_zero] at eq1 eq2
    have hd_eq : d = α.natAbs * (denI u M n).natAbs := by
      have := congrArg Int.natAbs eq1
      rw [Int.natAbs_mul] at this
      simpa using this.symm
    have hp_eq : p = α.natAbs * (numI u M n).natAbs := by
      have := congrArg Int.natAbs eq2
      rw [Int.natAbs_mul] at this
      simpa using this.symm
    have hdvd_d : α.natAbs ∣ d := ⟨(denI u M n).natAbs, hd_eq⟩
    have hdvd_p : α.natAbs ∣ p := ⟨(numI u M n).natAbs, hp_eq⟩
    have hα1 : α.natAbs = 1 := Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd hdvd_p hdvd_d)
    have : α = 1 ∨ α = -1 := by omega
    rcases this with h1 | h1
    · rw [h1] at eq1; omega
    · rw [h1] at eq1
      exfalso
      omega
  · by_cases hα0 : α = 0
    · -- `d = β · denI (n+1) ≥ denI (n+1) > d`, impossible.
      exfalso
      rw [hα0] at eq1
      simp only [Int.zero_mul, Int.zero_add] at eq1
      have hβ1 : 1 ≤ β.natAbs := by omega
      have hd_eq : d = β.natAbs * (denI u M (n+1)).natAbs := by
        have := congrArg Int.natAbs eq1
        rw [Int.natAbs_mul] at this
        simpa using this.symm
      have hD1' : (denI u M (n+1)).natAbs ≤ d := by
        rw [hd_eq]
        exact Nat.le_mul_of_pos_left _ (by omega)
      omega
    · -- Both nonzero: opposite signs, best approximation, contradiction.
      exfalso
      -- Opposite signs.
      have hsigns : (1 ≤ α ∧ β ≤ -1) ∨ (α ≤ -1 ∧ 1 ≤ β) := by
        rcases Int.lt_or_le 0 β with hβpos | hβnonpos
        · right
          refine ⟨?_, by omega⟩
          -- α·D0 = d − β·D1 ≤ d − D1 < 0
          have hβD1 : denI u M (n+1) ≤ β * denI u M (n+1) := by
            have : 1 * denI u M (n+1) ≤ β * denI u M (n+1) :=
              Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
            omega
          have hαD0_neg : α * denI u M n < 0 := by omega
          by_contra hcon
          push_neg at hcon
          have : 0 ≤ α := by omega
          have : 0 ≤ α * denI u M n := Int.mul_nonneg this (by omega)
          omega
        · left
          have hβneg : β < 0 := by omega
          refine ⟨?_, by omega⟩
          -- α·D0 = d + (−β)·D1 ≥ d + D1 > 0
          have hβD1 : denI u M (n+1) ≤ (-β) * denI u M (n+1) := by
            have : 1 * denI u M (n+1) ≤ (-β) * denI u M (n+1) :=
              Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
            omega
          have hαD0_pos : 0 < α * denI u M n := by
            have hexp : α * denI u M n = (d : ℤ) + (-β) * denI u M (n+1) := by grind
            omega
          by_contra hcon
          push_neg at hcon
          have hα_nonpos : α ≤ 0 := by omega
          have : α * denI u M n ≤ 0 :=
            Int.mul_nonpos_of_nonpos_of_nonneg hα_nonpos (by omega)
          omega
      -- Parity of the error terms.
      have hE0 := eI_eq u M n
      have hE1 := eI_eq u M (n+1)
      set X : ℤ := (u : ℤ) * d - (M : ℤ) * p with hX_def
      set R0 : ℤ := ((rem u M (n+1) : Nat) : ℤ) with hR0_def
      set R1 : ℤ := ((rem u M (n+2) : Nat) : ℤ) with hR1_def
      have hR0nn : 0 ≤ R0 := by rw [hR0_def]; omega
      have hR1nn : 0 ≤ R1 := by rw [hR1_def]; omega
      -- Best approximation: R0 ≤ |X|.
      have hbest : R0 ≤ X ∨ X ≤ -R0 := by
        rcases Nat.mod_two_eq_zero_or_one n with hk | hk
        · -- eI n = R0, eI (n+1) = −R1
          rw [if_pos hk] at hE0
          rw [if_neg (by omega : ¬((n+1) % 2 = 0))] at hE1
          try simp only [show n+1+1 = n+2 from rfl] at hE1
          rcases hsigns with ⟨hα1, hβ1⟩ | ⟨hα1, hβ1⟩
          · -- X = α·R0 + (−β)·R1 ≥ R0
            left
            have h1 : R0 ≤ α * R0 := by
              have : 1 * R0 ≤ α * R0 := Int.mul_le_mul_of_nonneg_right hα1 hR0nn
              omega
            have h2 : 0 ≤ (-β) * R1 := Int.mul_nonneg (by omega) hR1nn
            have hXe : X = α * R0 + (-β) * R1 := by
              rw [heq3, hE0, hE1]; grind
            omega
          · -- X = α·R0 + (−β)·R1 ≤ −R0
            right
            have h1 : α * R0 ≤ -R0 := by
              have : α * R0 ≤ (-1) * R0 := Int.mul_le_mul_of_nonneg_right hα1 hR0nn
              omega
            have h2 : (-β) * R1 ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg (by omega) hR1nn
            have hXe : X = α * R0 + (-β) * R1 := by
              rw [heq3, hE0, hE1]; grind
            omega
        · -- eI n = −R0, eI (n+1) = R1
          rw [if_neg (by omega : ¬(n % 2 = 0))] at hE0
          rw [if_pos (by omega : (n+1) % 2 = 0)] at hE1
          try simp only [show n+1+1 = n+2 from rfl] at hE1
          rcases hsigns with ⟨hα1, hβ1⟩ | ⟨hα1, hβ1⟩
          · -- X = −α·R0 + β·R1 ≤ −R0
            right
            have h1 : α * (-R0) ≤ -R0 := by
              have : 1 * R0 ≤ α * R0 := Int.mul_le_mul_of_nonneg_right hα1 hR0nn
              grind
            have h2 : β * R1 ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg (by omega) hR1nn
            have hXe : X = α * (-R0) + β * R1 := by
              rw [heq3, hE0, hE1]
            omega
          · left
            have h1 : R0 ≤ α * (-R0) := by
              have : α * R0 ≤ (-1) * R0 := Int.mul_le_mul_of_nonneg_right hα1 hR0nn
              grind
            have h2 : 0 ≤ β * R1 := Int.mul_nonneg (by omega) hR1nn
            have hXe : X = α * (-R0) + β * R1 := by
              rw [heq3, hE0, hE1]
            omega
      have hbestN : rem u M (n+1) ≤ X.natAbs := by
        rw [hR0_def] at hbest
        omega
      -- The contradiction: M ≤ M·|β| = |d·eI n − denI n·X| ≤ 2d·|X| < M.
      have hkey : (M : ℤ) * Δ * β = (d : ℤ) * eI u M n - denI u M n * X := by
        rw [hβ_def, hX_def]
        show (M : ℤ) * Δ * (Δ * ((p : ℤ) * denI u M n - (d : ℤ) * numI u M n)) = _
        have h1 : (M : ℤ) * Δ * (Δ * ((p : ℤ) * denI u M n - (d : ℤ) * numI u M n))
            = (Δ * Δ) * ((M : ℤ) * ((p : ℤ) * denI u M n - (d : ℤ) * numI u M n)) := by grind
        rw [h1, hΔsq, Int.one_mul]
        show (M : ℤ) * ((p : ℤ) * denI u M n - (d : ℤ) * numI u M n)
            = (d : ℤ) * ((u : ℤ) * denI u M n - (M : ℤ) * numI u M n)
              - denI u M n * ((u : ℤ) * d - (M : ℤ) * p)
        grind
      -- Pass to natAbs.
      have hMβ_natAbs : M * β.natAbs = ((d : ℤ) * eI u M n - denI u M n * X).natAbs := by
        have := congrArg Int.natAbs hkey
        rw [Int.natAbs_mul, Int.natAbs_mul] at this
        have hΔabs : Δ.natAbs = 1 := by rcases hdet with h | h <;> (try rw [← hΔ_def] at h) <;> rw [h] <;> rfl
        rw [hΔabs] at this
        simpa using this
      have htri : ((d : ℤ) * eI u M n - denI u M n * X).natAbs
          ≤ ((d : ℤ) * eI u M n).natAbs + (denI u M n * X).natAbs :=
        Int.natAbs_sub_le _ _
      have h1 : ((d : ℤ) * eI u M n).natAbs = d * (eI u M n).natAbs := by
        rw [Int.natAbs_mul]; simp
      have h2 : (denI u M n * X).natAbs = (denI u M n).natAbs * X.natAbs := Int.natAbs_mul _ _
      have hE0abs : (eI u M n).natAbs = rem u M (n+1) := by
        have := eI_eq u M n
        rcases Nat.mod_two_eq_zero_or_one n with hk | hk
        · rw [if_pos hk] at this; rw [this]; simp
        · rw [if_neg (by omega)] at this; rw [this]; simp
      have hD0d : (denI u M n).natAbs ≤ d := by omega
      have hb1 : 1 ≤ β.natAbs := by omega
      -- Chain it all in ℕ.
      have hchain : M ≤ d * rem u M (n+1) + d * X.natAbs := by
        calc M = M * 1 := by omega
          _ ≤ M * β.natAbs := Nat.mul_le_mul_left M hb1
          _ = ((d : ℤ) * eI u M n - denI u M n * X).natAbs := hMβ_natAbs
          _ ≤ ((d : ℤ) * eI u M n).natAbs + (denI u M n * X).natAbs := htri
          _ = d * rem u M (n+1) + (denI u M n).natAbs * X.natAbs := by rw [h1, h2, hE0abs]
          _ ≤ d * rem u M (n+1) + d * X.natAbs := by
              have := Nat.mul_le_mul_right (X.natAbs) hD0d
              omega
      have hfinal : d * rem u M (n+1) + d * X.natAbs ≤ 2 * (d * X.natAbs) := by
        have := Nat.mul_le_mul_left d hbestN
        omega
      have hsmall' : 2 * (d * X.natAbs) < M := by
        have hcomm : X.natAbs * (2 * d) = 2 * (d * X.natAbs) := by grind
        omega
      have hlt : M < M :=
        Nat.lt_of_le_of_lt (Nat.le_trans hchain hfinal) hsmall'
      omega

end Srtfp.Schubfach.R20Sweep

namespace Srtfp.Schubfach.R20Sweep

/-! ## Bracket search and the Legendre theorem proper -/

/-- Remainders decrease at least linearly: `rem k + k ≤ M + 1` in the regime. -/
theorem rem_add_le (u M : Nat) (hM : 0 < M) :
    ∀ k, (∀ i, i ≤ k → 0 < rem u M i) → rem u M k + k ≤ M + 1 := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k IH =>
    intro hreg
    match k with
    | 0 => show M + 0 ≤ M + 1; omega
    | 1 => have := rem_one_lt u M hM; omega
    | (k+2) =>
      have h1 := IH (k+1) (by omega) (fun i hi => hreg i (by omega))
      have h2 := rem_succ_lt u M k (hreg (k+1) (by omega))
      omega

/-- Every `1 ≤ d < M` (with `u, M` coprime) is bracketed by consecutive
continuant denominators inside the positivity regime. -/
theorem exists_bracket (u M d : Nat) (hM : 0 < M) (hco : Nat.Coprime u M)
    (hd : 0 < d) (hdM : d < M) :
    ∃ n, (∀ i, i ≤ n+1 → 0 < rem u M i)
      ∧ denI u M n ≤ (d : ℤ) ∧ (d : ℤ) < denI u M (n+1) := by
  have hM1 : 1 < M := by omega
  have hrem1 : 0 < rem u M 1 := by
    show 0 < u % M
    rcases Nat.eq_zero_or_pos (u % M) with h | h
    · exfalso
      have hdvd : M ∣ u := Nat.dvd_of_mod_eq_zero h
      have : Nat.gcd u M = M := Nat.gcd_eq_right hdvd
      have hco' : Nat.gcd u M = 1 := hco
      omega
    · exact h
  suffices aux : ∀ fuel k, M ≤ k + fuel → (∀ i, i ≤ k+1 → 0 < rem u M i) →
      denI u M k ≤ (d : ℤ) →
      ∃ n, (∀ i, i ≤ n+1 → 0 < rem u M i)
        ∧ denI u M n ≤ (d : ℤ) ∧ (d : ℤ) < denI u M (n+1) by
    apply aux M 0 (by omega)
    · intro i hi
      match i, hi with
      | 0, _ => exact hM
      | 1, _ => exact hrem1
    · show (1 : ℤ) ≤ (d : ℤ)
      omega
  intro fuel
  induction fuel with
  | zero =>
    intro k hk hreg _
    exfalso
    have := rem_add_le u M hM (k+1) hreg
    have := hreg (k+1) (Nat.le_refl _)
    omega
  | succ f IH =>
    intro k hk hreg hle
    by_cases hbr : (d : ℤ) < denI u M (k+1)
    · exact ⟨k, hreg, hle, hbr⟩
    · push_neg at hbr
      by_cases hz : rem u M (k+2) = 0
      · exfalso
        have hMeq := denI_eq_M_of_terminated u M hM hco k hreg hz
        rw [hMeq] at hbr
        omega
      · have hreg' : ∀ i, i ≤ (k+1)+1 → 0 < rem u M i := by
          intro i hi
          rcases Nat.lt_or_ge i (k+2) with h | h
          · exact hreg i (by omega)
          · have : i = k+2 := by omega
            subst this
            exact Nat.pos_of_ne_zero hz
        exact IH (k+1) (by omega) hreg' hbr

/-- **Rational Legendre, scaled integer form.**  A coprime fraction `p/d`
with `1 ≤ d < M` approximating `u/M` to quality `|u·d − M·p| · 2d < M`
has `d` equal to a continuant denominator of the Euclidean expansion of
`(u, M)`, at an index inside the positivity regime. -/
theorem small_den_is_denN (u M p d : Nat) (hM : 0 < M) (hco : Nat.Coprime u M)
    (hcop : Nat.gcd p d = 1) (hd : 0 < d) (hdM : d < M)
    (hsmall : ((u : ℤ) * d - (M : ℤ) * p).natAbs * (2 * d) < M) :
    ∃ n, (∀ i, i ≤ n+1 → 0 < rem u M i) ∧ denN u M n = d := by
  obtain ⟨n, hreg, hlo, hhi⟩ := exists_bracket u M d hM hco hd hdM
  have heq := bracket_eq_denI u M p d n hM hreg hcop hd hlo hhi hsmall
  refine ⟨n, hreg, ?_⟩
  unfold denN
  omega

end Srtfp.Schubfach.R20Sweep

namespace Srtfp.Schubfach.R20Sweep

/-! ## Fibonacci growth and the index bound -/

/-- Iterative Fibonacci pair (`fib n`, `fib (n+1)`) — evaluates linearly,
so `decide`-friendly. -/
def fibP : Nat → Nat × Nat
  | 0 => (0, 1)
  | n+1 => ((fibP n).2, (fibP n).1 + (fibP n).2)

/-- Fibonacci numbers, `fib 0 = 0`, `fib 1 = 1`. -/
def fib (n : Nat) : Nat := (fibP n).1

theorem fib_add_two (n : Nat) : fib (n+2) = fib n + fib (n+1) := by
  show (fibP (n+2)).1 = (fibP n).1 + (fibP (n+1)).1
  show (fibP (n+1)).2 = _
  show (fibP n).1 + (fibP n).2 = _
  rfl

/-- Continuant denominators grow at least as fast as Fibonacci. -/
theorem fib_le_denI (u M : Nat) (hM : 0 < M) :
    ∀ n, (∀ i, i ≤ n → 0 < rem u M i) → (fib (n+1) : ℤ) ≤ denI u M n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n IH =>
    intro hreg
    match n with
    | 0 => show ((1 : Nat) : ℤ) ≤ 1; omega
    | 1 =>
      show ((fib 2 : Nat) : ℤ) ≤ (qt u M 0 : ℤ)
      have h := qt_pos u M hM 0 (fun i hi => hreg i hi)
      have : fib 2 = 1 := rfl
      omega
    | (n+2) =>
      have h1 := IH (n+1) (by omega) (fun i hi => hreg i (by omega))
      simp only [show n+1+1 = n+2 from rfl] at h1
      have h0 := IH n (by omega) (fun i hi => hreg i (by omega))
      have hq : 1 ≤ qt u M (n+1) := qt_pos u M hM (n+1) (fun i hi => hreg i hi)
      have hD1 : 0 < denI u M (n+1) := denI_pos u M hM (n+1) (fun i hi => hreg i (by omega))
      show ((fib (n+3) : Nat) : ℤ) ≤ (qt u M (n+1) : ℤ) * denI u M (n+1) + denI u M n
      have hfib : fib (n+3) = fib (n+1) + fib (n+2) := fib_add_two (n+1)
      have hmul : denI u M (n+1) ≤ (qt u M (n+1) : ℤ) * denI u M (n+1) := by
        have h' : (1 : ℤ) ≤ (qt u M (n+1) : ℤ) := by exact_mod_cast hq
        have := Int.mul_le_mul_of_nonneg_right h' (Int.le_of_lt hD1)
        omega
      have hcast : ((fib (n+3) : Nat) : ℤ) = ((fib (n+1) : Nat) : ℤ) + ((fib (n+2) : Nat) : ℤ) := by
        exact_mod_cast congrArg (Nat.cast : Nat → Int) hfib
      omega

/-- `fib 79 > 2^53`: the index bound for the binary64 sweep. -/
theorem two_pow_53_lt_fib_79 : 2 ^ 53 < fib 79 := by decide

/-- Index bound: a bracketing index for `d < 2^53` is `< 78`. -/
theorem bracket_index_lt_78 (u M d n : Nat) (hM : 0 < M)
    (hreg : ∀ i, i ≤ n+1 → 0 < rem u M i)
    (hden : denN u M n = d) (hd53 : d < 2 ^ 53) : n < 78 := by
  by_contra hge
  push_neg at hge
  have hfib := fib_le_denI u M hM n (fun i hi => hreg i (by omega))
  have hD : 0 < denI u M n := denI_pos u M hM n (fun i hi => hreg i (by omega))
  have hdenIval : denI u M n = (d : ℤ) := by unfold denN at hden; omega
  have hfib78 : fib 79 ≤ fib (n+1) := by
    clear hfib hdenIval hden hd53 hD hreg
    have hmono : ∀ a b, a ≤ b → fib (a+2) ≤ fib (b+2) := by
      intro a b hab
      induction b with
      | zero => have : a = 0 := by omega
                subst this; exact Nat.le_refl _
      | succ b IHb =>
        rcases Nat.lt_or_ge a (b+1) with h | h
        · have step : fib (b+2) ≤ fib (b+3) := by
            have h := fib_add_two (b+1)
            simp only [show b+1+2 = b+3 from rfl, show b+1+1 = b+2 from rfl] at h
            omega
          exact Nat.le_trans (IHb (by omega)) step
        · have : a = b+1 := by omega
          subst this; exact Nat.le_refl _
    have := hmono 77 (n-1) (by omega)
    have hn1 : n - 1 + 2 = n + 1 := by omega
    rw [hn1] at this
    exact this
  have := two_pow_53_lt_fib_79
  omega

end Srtfp.Schubfach.R20Sweep

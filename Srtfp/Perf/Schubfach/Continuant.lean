module
/- Continuants, for Result 20 (Giulietti, Nadezhin).

   Elementary `Nat`/`Int` arithmetic about the Euclidean remainder
   sequence of `(u, M)` and its continuant numerators and denominators.
   The centerpiece is `small_den_is_denN`, the rational Legendre theorem
   in scaled integer form: a coprime fraction `p/d` approximating `u/M`
   to quality `|u·d − M·p| · 2d < M` has `d` equal to a continuant
   denominator. Continuant denominators grow at least as fast as
   Fibonacci numbers, which bounds the index to search. -/

public import Srtfp.Rat
public import Srtfp.Perf.Tactics

@[expose] public section

open Srtfp.Compat

namespace Srtfp.Schubfach.R20

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
def denI (u M : Nat) : Nat → Int
  | 0 => 1
  | 1 => (qt u M 0 : Int)
  | (n+2) => (qt u M (n+1) : Int) * denI u M (n+1) + denI u M n

/-- Integer continuant numerators. -/
def numI (u M : Nat) : Nat → Int
  | 0 => (u / M : Nat)
  | 1 => (qt u M 0 : Int) * (u / M : Nat) + 1
  | (n+2) => (qt u M (n+1) : Int) * numI u M (n+1) + numI u M n

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

/-- `qt_mul_add_rem`, cast to `Int` with the product distributed. -/
theorem qt_mul_add_rem_int (u M n : Nat) :
    (qt u M n : Int) * ((rem u M (n+1) : Nat) : Int) + ((rem u M (n+2) : Nat) : Int)
      = ((rem u M n : Nat) : Int) := by
  exact_mod_cast qt_mul_add_rem u M n

/-! ## The error term and its invariant -/

/-- Scaled approximation error of the `n`th convergent:
`eI n = u · denI n − M · numI n`. -/
def eI (u M : Nat) (n : Nat) : Int := (u : Int) * denI u M n - (M : Int) * numI u M n

theorem eI_zero (u M : Nat) : eI u M 0 = ((rem u M 1 : Nat) : Int) := by
  show (u : Int) * 1 - (M : Int) * ((u / M : Nat) : Int) = ((u % M : Nat) : Int)
  have hdm : (M : Int) * ((u / M : Nat) : Int) + ((u % M : Nat) : Int) = (u : Int) := by
    exact_mod_cast Nat.div_add_mod u M
  omega

theorem eI_one (u M : Nat) : eI u M 1 = -((rem u M 2 : Nat) : Int) := by
  show (u : Int) * (qt u M 0 : Int) - (M : Int) * ((qt u M 0 : Int) * ((u / M : Nat) : Int) + 1)
      = -((rem u M 2 : Nat) : Int)
  have hdm : (M : Int) * ((u / M : Nat) : Int) + ((u % M : Nat) : Int) = (u : Int) := by
    exact_mod_cast Nat.div_add_mod u M
  have hq := qt_mul_add_rem_int u M 0
  simp only [Nat.zero_add] at hq
  have hrem0 : ((rem u M 0 : Nat) : Int) = (M : Int) := rfl
  have hrem1 : ((rem u M 1 : Nat) : Int) = ((u % M : Nat) : Int) := rfl
  rw [hrem0, hrem1] at hq
  -- u·q0 − M·(q0·(u/M) + 1) = q0·(u − M·(u/M)) − M = q0·(u%M) − M = −rem 2
  have expand : (u : Int) * (qt u M 0 : Int) - (M : Int) * ((qt u M 0 : Int) * ((u / M : Nat) : Int) + 1)
      = (qt u M 0 : Int) * ((u : Int) - (M : Int) * ((u / M : Nat) : Int)) - (M : Int) := by grind
  rw [expand]
  have hfrac : (u : Int) - (M : Int) * ((u / M : Nat) : Int) = ((u % M : Nat) : Int) := by omega
  rw [hfrac]
  omega

theorem eI_add_two (u M n : Nat) :
    eI u M (n+2) = (qt u M (n+1) : Int) * eI u M (n+1) + eI u M n := by
  show (u : Int) * ((qt u M (n+1) : Int) * denI u M (n+1) + denI u M n)
      - (M : Int) * ((qt u M (n+1) : Int) * numI u M (n+1) + numI u M n)
      = (qt u M (n+1) : Int) * ((u : Int) * denI u M (n+1) - (M : Int) * numI u M (n+1))
        + ((u : Int) * denI u M n - (M : Int) * numI u M n)
  grind

/-- The Euclid invariant: `eI n = (−1)ⁿ · rem (n+1)`, phrased by parity. -/
theorem eI_eq (u M : Nat) : ∀ n,
    eI u M n = if n % 2 = 0 then ((rem u M (n+1) : Nat) : Int)
               else -((rem u M (n+1) : Nat) : Int) := by
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
      have hdist : (qt u M (n+1) : Int) * -((rem u M (n+2) : Nat) : Int)
          = -((qt u M (n+1) : Int) * ((rem u M (n+2) : Nat) : Int)) := by grind
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
    show ((qt u M 0 : Int) * ((u / M : Nat) : Int) + 1) * 1
        - ((u / M : Nat) : Int) * (qt u M 0 : Int) = _
    simp only [show (0 : Nat) % 2 = 0 from rfl, reduceIte]
    grind
  | succ n IH =>
    have hstep : numI u M (n+2) * denI u M (n+1) - numI u M (n+1) * denI u M (n+2)
        = -(numI u M (n+1) * denI u M n - numI u M n * denI u M (n+1)) := by
      show ((qt u M (n+1) : Int) * numI u M (n+1) + numI u M n) * denI u M (n+1)
          - numI u M (n+1) * ((qt u M (n+1) : Int) * denI u M (n+1) + denI u M n) = _
      grind
    rw [hstep, IH]
    rcases Nat.mod_two_eq_zero_or_one n with hk | hk
    · rw [if_pos hk, if_neg (by omega : ¬((n+1) % 2 = 0))]
    · rw [if_neg (by omega : ¬(n % 2 = 0)), if_pos (by omega : (n+1) % 2 = 0)]
      decide

/-! ## The fundamental identity `rem (n+1) · denI (n+1) + rem (n+2) · denI n = M` -/

theorem rem_denI_identity (u M : Nat) : ∀ n,
    ((rem u M (n+1) : Nat) : Int) * denI u M (n+1) + ((rem u M (n+2) : Nat) : Int) * denI u M n
      = (M : Int) := by
  intro n
  induction n with
  | zero =>
    show ((rem u M 1 : Nat) : Int) * (qt u M 0 : Int) + ((rem u M 2 : Nat) : Int) * 1 = (M : Int)
    have hq := qt_mul_add_rem_int u M 0
    have hrem0 : ((rem u M 0 : Nat) : Int) = (M : Int) := rfl
    rw [hrem0] at hq
    grind
  | succ n IH =>
    have hexp : ((rem u M (n+2) : Nat) : Int) * denI u M (n+2)
        + ((rem u M (n+3) : Nat) : Int) * denI u M (n+1)
        = ((rem u M (n+2) : Nat) : Int) * denI u M n
          + (((qt u M (n+1) : Int) * ((rem u M (n+2) : Nat) : Int)
              + ((rem u M (n+3) : Nat) : Int)) * denI u M (n+1)) := by
      show ((rem u M (n+2) : Nat) : Int) * ((qt u M (n+1) : Int) * denI u M (n+1) + denI u M n)
          + _ = _
      grind
    rw [hexp, qt_mul_add_rem_int u M (n+1)]
    -- rem(n+2)·denI n + rem(n+1)·denI(n+1) = M  (IH, commuted)
    grind

end Srtfp.Schubfach.R20

namespace Srtfp.Schubfach.R20

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
      show (0 : Int) < (qt u M 0 : Int)
      exact_mod_cast qt_pos u M hM 0 (fun i hi => hpos i hi)
    | (n+2) =>
      have hq : 1 ≤ qt u M (n+1) := qt_pos u M hM (n+1) (fun i hi => hpos i hi)
      have h1 : 0 < denI u M (n+1) := IH (n+1) (by omega) (fun i hi => hpos i (by omega))
      have h0 : 0 < denI u M n := IH n (by omega) (fun i hi => hpos i (by omega))
      show (0 : Int) < (qt u M (n+1) : Int) * denI u M (n+1) + denI u M n
      have : (1 : Int) ≤ (qt u M (n+1) : Int) := by exact_mod_cast hq
      have hmul : denI u M (n+1) ≤ (qt u M (n+1) : Int) * denI u M (n+1) := by
        calc denI u M (n+1) = 1 * denI u M (n+1) := by grind
          _ ≤ (qt u M (n+1) : Int) * denI u M (n+1) :=
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
    denI u M (n+1) = (M : Int) := by
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
  rw [show ((rem u M (n+2) : Nat) : Int) = 0 by exact_mod_cast hz, hone] at hid
  simpa using hid

end Srtfp.Schubfach.R20

namespace Srtfp.Schubfach.R20

/-! ## The bracketed Legendre step

If `denI n ≤ d < denI (n+1)` inside the regime and the coprime fraction
`p/d` approximates `u/M` to quality `|u·d − M·p| · 2d < M`, then
`d = denI n`.  This is Legendre's theorem for the rational `u/M`,
in scaled integer form. -/

/-- Two integers of the same sign: the first is no longer than their sum. -/
theorem natAbs_le_natAbs_add {x y : Int} (h : 0 ≤ x * y) : x.natAbs ≤ (x + y).natAbs := by
  rcases Int.le_total 0 x with hx | hx <;> rcases Int.le_total 0 y with hy | hy
  · omega
  · have := Int.mul_nonpos_of_nonneg_of_nonpos hx hy
    rcases Int.mul_eq_zero.mp (by omega : x * y = 0) with rfl | rfl <;> omega
  · have := Int.mul_nonpos_of_nonpos_of_nonneg hx hy
    rcases Int.mul_eq_zero.mp (by omega : x * y = 0) with rfl | rfl <;> omega
  · omega

theorem bracket_eq_denI (u M p d n : Nat) (hM : 0 < M)
    (hpos : ∀ i, i ≤ n+1 → 0 < rem u M i)
    (hcop : Nat.gcd p d = 1) (hd : 0 < d)
    (hlo : denI u M n ≤ (d : Int)) (hhi : (d : Int) < denI u M (n+1))
    (hsmall : ((u : Int) * d - (M : Int) * p).natAbs * (2 * d) < M) :
    (d : Int) = denI u M n := by
  have hD0 : 0 < denI u M n := denI_pos u M hM n (fun i hi => hpos i (by omega))
  have hD1 : 0 < denI u M (n+1) := denI_pos u M hM (n+1) hpos
  obtain ⟨X, hX⟩ : ∃ X : Int, (u : Int) * d - (M : Int) * p = X := ⟨_, rfl⟩
  rw [hX] at hsmall
  -- Cramer's rule with the determinant `Δ = ±1`: `d = α D_n + β D_(n+1)`, `p = α N_n + β N_(n+1)`
  obtain ⟨Δ, hΔ⟩ : ∃ Δ : Int, numI u M (n+1) * denI u M n - numI u M n * denI u M (n+1) = Δ :=
    ⟨_, rfl⟩
  have hΔ1 : Δ = 1 ∨ Δ = -1 := by
    have := det_eq u M n; rw [hΔ] at this; split at this <;> simp_all
  have hΔsq : Δ * Δ = 1 := by rcases hΔ1 with rfl | rfl <;> decide
  have hΔabs : Δ.natAbs = 1 := by rcases hΔ1 with rfl | rfl <;> rfl
  obtain ⟨α, hα⟩ : ∃ α : Int,
      Δ * ((d : Int) * numI u M (n+1) - (p : Int) * denI u M (n+1)) = α := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : Int, Δ * ((p : Int) * denI u M n - (d : Int) * numI u M n) = β :=
    ⟨_, rfl⟩
  have eq1 : α * denI u M n + β * denI u M (n+1) = (d : Int) := by
    have e : α * denI u M n + β * denI u M (n+1) = Δ * Δ * d := by
      subst hα hβ; rw [← hΔ]; grind
    rw [e, hΔsq, Int.one_mul]
  have eq2 : α * numI u M n + β * numI u M (n+1) = (p : Int) := by
    have e : α * numI u M n + β * numI u M (n+1) = Δ * Δ * p := by
      subst hα hβ; rw [← hΔ]; grind
    rw [e, hΔsq, Int.one_mul]
  -- the error decomposes the same way: `X = α e_n + β e_(n+1)`
  have heq3 : X = α * eI u M n + β * eI u M (n+1) := by
    rw [← hX, ← eq1, ← eq2]; simp only [eI]; grind
  by_cases hβ0 : β = 0
  · -- `d = α D_n` and `p = α N_n` with `p, d` coprime: `α = ±1`, and `d > 0` picks `α = 1`
    subst hβ0
    simp only [Int.zero_mul, Int.add_zero] at eq1 eq2
    have hα1 : α.natAbs = 1 := Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd
      (by simpa using Int.natAbs_dvd_natAbs.mpr ⟨_, eq2.symm⟩)
      (by simpa using Int.natAbs_dvd_natAbs.mpr ⟨_, eq1.symm⟩))
    rcases (by omega : α = 1 ∨ α = -1) with rfl | rfl <;> omega
  by_cases hα0 : α = 0
  · -- `d = β D_(n+1)` is at least `D_(n+1) > d`
    subst hα0
    simp only [Int.zero_mul, Int.zero_add] at eq1
    have := Int.natAbs_mul β (denI u M (n+1))
    have := Nat.le_mul_of_pos_left (denI u M (n+1)).natAbs (by omega : 0 < β.natAbs)
    omega
  -- both nonzero: `D_n ≤ d < D_(n+1)` forces opposite signs
  have hsigns : (1 ≤ α ∧ β ≤ -1) ∨ (α ≤ -1 ∧ 1 ≤ β) := by
    have hD1' := Int.le_of_lt hD1
    have hD0' := Int.le_of_lt hD0
    rcases Int.lt_or_le 0 β with hb | hb
    · have := Int.mul_le_mul_of_nonneg_right (by omega : 1 ≤ β) hD1'
      rcases Int.lt_or_le α 0 with ha | ha
      · omega
      · have := Int.mul_nonneg ha hD0'; omega
    · have := Int.mul_le_mul_of_nonneg_right (by omega : β ≤ -1) hD1'
      rcases Int.lt_or_le 0 α with ha | ha
      · omega
      · have := Int.mul_nonpos_of_nonpos_of_nonneg ha hD0'; omega
  -- `e_n` and `e_(n+1)` alternate in sign too, so `α e_n` and `β e_(n+1)` agree: `|X| ≥ |e_n|`
  have hE0 := eI_eq u M n
  have hE1 := eI_eq u M (n+1)
  have hE0abs : (eI u M n).natAbs = rem u M (n+1) := by rw [hE0]; split <;> simp
  have hprod : 0 ≤ (α * eI u M n) * (β * eI u M (n+1)) := by
    have h1 : α * β ≤ 0 := by
      rcases hsigns with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact Int.mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
      · exact Int.mul_nonpos_of_nonpos_of_nonneg (by omega) (by omega)
    have h2 : eI u M n * eI u M (n+1) ≤ 0 := by
      rw [hE0, hE1]
      rcases Nat.mod_two_eq_zero_or_one n with hk | hk
      · rw [if_pos hk, if_neg (by omega)]
        exact Int.mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
      · rw [if_neg (by omega), if_pos (by omega)]
        exact Int.mul_nonpos_of_nonpos_of_nonneg (by omega) (by omega)
    rw [show (α * eI u M n) * (β * eI u M (n+1)) = (α * β) * (eI u M n * eI u M (n+1)) by grind]
    exact Int.mul_nonneg_of_nonpos_of_nonpos h1 h2
  have hbest : rem u M (n+1) ≤ X.natAbs := by
    have h := natAbs_le_natAbs_add hprod
    rw [← heq3, Int.natAbs_mul, hE0abs] at h
    exact Nat.le_trans (Nat.le_mul_of_pos_left _ (by omega)) h
  -- `M ≤ M |β| = |d e_n − D_n X| ≤ d rem (n+1) + d |X| ≤ 2d |X| < M`
  have hkey : (M : Int) * Δ * β = (d : Int) * eI u M n - denI u M n * X := by
    have e : (M : Int) * Δ * β = Δ * Δ * ((d : Int) * eI u M n - denI u M n * X) := by
      subst hβ; rw [← hX]; simp only [eI]; grind
    rw [e, hΔsq, Int.one_mul]
  have hMβ := congrArg Int.natAbs hkey
  rw [Int.natAbs_mul, Int.natAbs_mul, hΔabs, Nat.mul_one, Int.natAbs_natCast] at hMβ
  have htri := Int.natAbs_sub_le ((d : Int) * eI u M n) (denI u M n * X)
  rw [Int.natAbs_mul, Int.natAbs_mul, hE0abs, Int.natAbs_natCast] at htri
  have := Nat.mul_le_mul_right X.natAbs (by omega : (denI u M n).natAbs ≤ d)
  have := Nat.le_mul_of_pos_right M (by omega : 0 < β.natAbs)
  have := Nat.mul_le_mul_left d hbest
  have : X.natAbs * (2 * d) = 2 * (d * X.natAbs) := by grind
  omega

end Srtfp.Schubfach.R20

namespace Srtfp.Schubfach.R20

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
      ∧ denI u M n ≤ (d : Int) ∧ (d : Int) < denI u M (n+1) := by
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
      denI u M k ≤ (d : Int) →
      ∃ n, (∀ i, i ≤ n+1 → 0 < rem u M i)
        ∧ denI u M n ≤ (d : Int) ∧ (d : Int) < denI u M (n+1) by
    apply aux M 0 (by omega)
    · intro i hi
      match i, hi with
      | 0, _ => exact hM
      | 1, _ => exact hrem1
    · show (1 : Int) ≤ (d : Int)
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
    by_cases hbr : (d : Int) < denI u M (k+1)
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
    (hsmall : ((u : Int) * d - (M : Int) * p).natAbs * (2 * d) < M) :
    ∃ n, (∀ i, i ≤ n+1 → 0 < rem u M i) ∧ denN u M n = d := by
  obtain ⟨n, hreg, hlo, hhi⟩ := exists_bracket u M d hM hco hd hdM
  have heq := bracket_eq_denI u M p d n hM hreg hcop hd hlo hhi hsmall
  refine ⟨n, hreg, ?_⟩
  unfold denN
  omega

end Srtfp.Schubfach.R20

namespace Srtfp.Schubfach.R20

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
    ∀ n, (∀ i, i ≤ n → 0 < rem u M i) → (fib (n+1) : Int) ≤ denI u M n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n IH =>
    intro hreg
    match n with
    | 0 => show ((1 : Nat) : Int) ≤ 1; omega
    | 1 =>
      show ((fib 2 : Nat) : Int) ≤ (qt u M 0 : Int)
      have h := qt_pos u M hM 0 (fun i hi => hreg i hi)
      have : fib 2 = 1 := rfl
      omega
    | (n+2) =>
      have h1 := IH (n+1) (by omega) (fun i hi => hreg i (by omega))
      simp only [show n+1+1 = n+2 from rfl] at h1
      have h0 := IH n (by omega) (fun i hi => hreg i (by omega))
      have hq : 1 ≤ qt u M (n+1) := qt_pos u M hM (n+1) (fun i hi => hreg i hi)
      have hD1 : 0 < denI u M (n+1) := denI_pos u M hM (n+1) (fun i hi => hreg i (by omega))
      show ((fib (n+3) : Nat) : Int) ≤ (qt u M (n+1) : Int) * denI u M (n+1) + denI u M n
      have hfib : fib (n+3) = fib (n+1) + fib (n+2) := fib_add_two (n+1)
      have hmul : denI u M (n+1) ≤ (qt u M (n+1) : Int) * denI u M (n+1) := by
        have h' : (1 : Int) ≤ (qt u M (n+1) : Int) := by exact_mod_cast hq
        have := Int.mul_le_mul_of_nonneg_right h' (Int.le_of_lt hD1)
        omega
      have hcast : ((fib (n+3) : Nat) : Int) = ((fib (n+1) : Nat) : Int) + ((fib (n+2) : Nat) : Int) := by
        exact_mod_cast congrArg (Nat.cast : Nat → Int) hfib
      omega

/-- `fib 80 > 2^54`: the index bound for the binary64 sweep, whose
    multipliers are below `2^54`. -/
theorem two_pow_54_lt_fib_80 : 2 ^ 54 < fib 80 := by decide

/-- Index bound: a bracketing index for `d < 2^54` is `< 79`. -/
theorem bracket_index_lt_79 (u M d n : Nat) (hM : 0 < M)
    (hreg : ∀ i, i ≤ n+1 → 0 < rem u M i)
    (hden : denN u M n = d) (hd54 : d < 2 ^ 54) : n < 79 := by
  by_contra hge
  push_neg at hge
  have hfib := fib_le_denI u M hM n (fun i hi => hreg i (by omega))
  have hD : 0 < denI u M n := denI_pos u M hM n (fun i hi => hreg i (by omega))
  have hdenIval : denI u M n = (d : Int) := by unfold denN at hden; omega
  have hfib79 : fib 80 ≤ fib (n+1) := by
    clear hfib hdenIval hden hd54 hD hreg
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
    have := hmono 78 (n-1) (by omega)
    have hn1 : n - 1 + 2 = n + 1 := by omega
    rw [hn1] at this
    exact this
  have := two_pow_54_lt_fib_80
  omega

end Srtfp.Schubfach.R20

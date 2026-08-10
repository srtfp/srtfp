import Mathlib.NumberTheory.DiophantineApproximation.ContinuedFractions
import Mathlib.Data.Rat.Lemmas
import Srtfp.Schubfach.KernelCorrectness

/-!
# R20 Legendre-direct spike

Bridge lemma: a "bad" `m` (where `farFromMultipleBelow M u m 71` fails) forces
the ceiling rational `a/m` to be a convergent of `(u/M : ℝ)`.
-/

namespace Srtfp.Schubfach.R20Legendre

open scoped Classical

/-- The ceiling numerator for `m·u / M`, in `Nat`: `⌈m·u/M⌉`. -/
def ceilNum (M u m : Nat) : Nat := (m * u + (M - 1)) / M

/-- The "gap" `M − (m·u mod M)`: how far `m·u` lies below the next multiple of
`M`.  When this is `< M` (i.e. `m·u` is not already a multiple), it is the
positive distance up; `bad` means it is small relative to `M`. -/
def gap (M u m : Nat) : Nat := M - (m * u) % M

/-- When `m·u` is not a multiple of `M`, `ceilNum · M = m·u + gap`. -/
theorem ceilNum_mul_eq (M u m : Nat) (hM : 0 < M) (hnd : (m * u) % M ≠ 0) :
    ceilNum M u m * M = m * u + gap M u m := by
  unfold ceilNum gap
  set ρ := (m * u) % M with hρ
  set Q := m * u / M with hQ
  have hρlt : ρ < M := Nat.mod_lt _ hM
  have hdm : m * u = M * Q + ρ := (Nat.div_add_mod (m * u) M).symm
  -- ⌈x⌉ when not divisible: (m*u + (M-1))/M = Q + 1
  have hceil : (m * u + (M - 1)) / M = Q + 1 := by
    have key : m * u + (M - 1) = (ρ + (M - 1)) + Q * M := by
      rw [hdm]; ring_nf
    rw [key, Nat.add_mul_div_right _ _ hM]
    have hmid : (ρ + (M - 1)) / M = 1 := by
      have h1 : M ≤ ρ + (M - 1) := by omega
      have h2 : ρ + (M - 1) < M + M := by omega
      rw [Nat.div_eq_of_lt_le] <;> omega
    omega
  rw [hceil]
  -- (Q + 1) * M = m*u + (M - ρ)
  have hexp : (Q + 1) * M = M * Q + M := by ring
  omega

/-- The approximating rational `ceilNum / m` for `u/M`. -/
def approx (M u m : Nat) : ℚ := (ceilNum M u m : ℚ) / (m : ℚ)

/-- Its reduced denominator divides `m`, hence is `≤ m`. -/
theorem approx_den_le (M u m : Nat) (hm : 0 < m) :
    (approx M u m).den ≤ m := by
  unfold approx
  have hdvd : ((approx M u m).den : Int) ∣ (m : Int) := by
    unfold approx
    have := Rat.den_dvd (ceilNum M u m : Int) (m : Int)
    rw [show ((ceilNum M u m : ℚ) / (m : ℚ)) = Rat.divInt (ceilNum M u m) (m : Int) by
      rw [Rat.divInt_eq_div]; push_cast; ring]
    exact this
  have hmpos : (0 : Int) < (m : Int) := by exact_mod_cast hm
  have := Int.le_of_dvd hmpos hdvd
  exact_mod_cast this

/-- Bridge crux: a "bad" `m` (where `farFromMultipleBelow M u m a` fails), with
`2·m < 2^a`, forces the ceiling rational `approx = ⌈m·u/M⌉ / m` to be a
convergent of `(u/M : ℝ)`.  Soundness comes from Legendre
(`Real.exists_convs_eq_rat`); no best-approximation lower bound is used. -/
theorem bad_is_convergent
    (M u m a : Nat) (hM : 0 < M) (hm : 0 < m)
    (hbad : ¬ farFromMultipleBelow M u m a)
    (hsmall : 2 * m < 2 ^ a) :
    ∃ n, (GenContFract.of ((u : ℝ) / M)).convs n = ((approx M u m : ℚ) : ℝ) := by
  -- bad ⟹ gap is small: gap * 2^a < M, and ρ ≠ 0
  have hbad' : (gap M u m) * 2 ^ a < M := by
    unfold farFromMultipleBelow gap at *
    omega
  have hnd : (m * u) % M ≠ 0 := by
    intro h
    unfold gap at hbad'
    rw [h, Nat.sub_zero] at hbad'
    have : M ≤ M * 2 ^ a := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos a)
    omega
  apply Real.exists_convs_eq_rat
  -- Real difference: u/M - approx = -gap/(M*m)
  have hMr : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hmr : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hcast : ((approx M u m : ℚ) : ℝ) = (ceilNum M u m : ℝ) / (m : ℝ) := by
    unfold approx; push_cast; ring
  -- ceilNum*M = m*u + gap  (Nat), cast to ℝ
  have hcm : (ceilNum M u m : ℝ) * (M : ℝ) = (m : ℝ) * (u : ℝ) + (gap M u m : ℝ) := by
    have := ceilNum_mul_eq M u m hM hnd
    exact_mod_cast this
  have hdiff : (u : ℝ) / (M : ℝ) - ((approx M u m : ℚ) : ℝ)
      = - (gap M u m : ℝ) / ((M : ℝ) * (m : ℝ)) := by
    rw [hcast]
    field_simp
    nlinarith [hcm]
  rw [hdiff]
  -- |−gap/(M*m)| = gap/(M*m)
  have hgapnn : (0 : ℝ) ≤ (gap M u m : ℝ) := by positivity
  have habs : |(- (gap M u m : ℝ) / ((M : ℝ) * (m : ℝ)))|
      = (gap M u m : ℝ) / ((M : ℝ) * (m : ℝ)) := by
    rw [abs_div, abs_neg, abs_of_nonneg hgapnn,
        abs_of_pos (mul_pos hMr hmr)]
  rw [habs]
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  -- goal: gap * (2 * den^2) < 1 * (M * m)
  -- Nat facts: den ≤ m, gap ≥ 1, gap * (2*m) < M
  have hden_le : (approx M u m).den ≤ m := approx_den_le M u m hm
  have hgap1 : 1 ≤ gap M u m := by
    unfold gap
    have : (m * u) % M < M := Nat.mod_lt _ hM
    omega
  -- gap * (2*m) < M : since 2*m < 2^a and gap*2^a < M and gap ≥ 1
  have hgap2m : gap M u m * (2 * m) < M := by
    calc gap M u m * (2 * m) ≤ gap M u m * 2 ^ a := by
            apply Nat.mul_le_mul_left
            omega
      _ < M := hbad'
  -- so gap * (2 * m^2) < M * m  (multiply by m)
  have hkeyNat : gap M u m * (2 * m ^ 2) < M * m := by
    have heq : gap M u m * (2 * m ^ 2) = (gap M u m * (2 * m)) * m := by ring
    rw [heq]
    exact (Nat.mul_lt_mul_right hm).mpr hgap2m
  -- den ≤ m ⟹ den^2 ≤ m^2 ⟹ gap * (2*den^2) ≤ gap * (2*m^2) < M*m
  have hden2 : (approx M u m).den ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hden_le 2
  have hkeyNat2 : gap M u m * (2 * (approx M u m).den ^ 2) < M * m := by
    calc gap M u m * (2 * (approx M u m).den ^ 2)
          ≤ gap M u m * (2 * m ^ 2) := by
            apply Nat.mul_le_mul_left
            exact Nat.mul_le_mul_left 2 hden2
      _ < M * m := hkeyNat
  -- cast to ℝ
  have hcastlt : ((gap M u m * (2 * (approx M u m).den ^ 2) : Nat) : ℝ)
      < ((M * m : Nat) : ℝ) := by
    exact_mod_cast hkeyNat2
  push_cast at hcastlt
  nlinarith [hcastlt]

/-- **Sound reduction (contrapositive of the bridge).**  If *every* convergent
`c` of `(u/M : ℝ)` is "far" — meaning whenever `c = approx M u m'` for some
`m'` in range, that `m'` satisfies `farFromMultipleBelow` — then *every* `m` in
range is far.

Concretely: to prove `∀ m < bound, farFromMultipleBelow M u m a`, it suffices to
check the property at each `m'` such that `approx M u m'` is one of the
(finitely many, `O(log M)`) convergents of `u/M`.  This is the formal core of
the Legendre-direct finite-sweep strategy: the bridge confines all potential
counterexamples to convergent denominators. -/
theorem far_of_far_at_convergents
    (M u a : Nat) (hM : 0 < M)
    (hconv : ∀ m, 0 < m → 2 * m < 2 ^ a →
      (∃ n, (GenContFract.of ((u : ℝ) / M)).convs n = ((approx M u m : ℚ) : ℝ)) →
      farFromMultipleBelow M u m a) :
    ∀ m, 0 < m → 2 * m < 2 ^ a → farFromMultipleBelow M u m a := by
  intro m hm hsmall
  by_contra hbad
  exact hbad (hconv m hm hsmall (bad_is_convergent M u m a hM hm hbad hsmall))

end Srtfp.Schubfach.R20Legendre

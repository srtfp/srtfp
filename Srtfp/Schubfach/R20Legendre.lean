import Srtfp.Schubfach.KernelCorrectness
import Srtfp.Tactics

/-!
# R20 ceiling numerator and gap

`Nat`-level vocabulary for the R20 sweep soundness argument: the ceiling
numerator `⌈m·u/M⌉` and the gap `M − (m·u mod M)`.  The continued-fraction
soundness theorem itself lives in `R20Continuant.lean` (`small_den_is_denN`);
the assembly is in `R20Keystone.lean` (`farAll_of_sweep`).
-/

namespace Srtfp.Schubfach.R20Legendre

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
      rw [hdm]; grind
    rw [key, Nat.add_mul_div_right _ _ hM]
    have hmid : (ρ + (M - 1)) / M = 1 := by
      have h1 : M ≤ ρ + (M - 1) := by omega
      have h2 : ρ + (M - 1) < M + M := by omega
      rw [Nat.div_eq_of_lt_le] <;> omega
    omega
  rw [hceil]
  have hexp : (Q + 1) * M = M * Q + M := by grind
  omega

end Srtfp.Schubfach.R20Legendre

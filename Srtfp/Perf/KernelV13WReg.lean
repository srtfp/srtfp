module
/- The window is at least 128 bits wide on every regular band: for
   `k = ⌊log₁₀ 2^q⌋` of a binary64 exponent `q`, the table shift of
   `10^(-(k+1))` exceeds `q` by at least 128. Read off the shift's closed
   form (`pow10Shift`) and the exactness of `floorLog10Pow2`
   (`R15HoldsAt`, `Srtfp/Perf/Schubfach/R14R15.lean`). -/

public import Srtfp.Perf.TableInvariant
public import Srtfp.Perf.Schubfach.R14R15

@[expose] public section

namespace Srtfp.Schubfach

theorem wReg_at (q : Int) (h1 : -1074 ≤ q) (h2 : q ≤ 971)
    (hklo : ¬ floorLog10Pow2 q < pow10Table128_kMin)
    (hkhi : ¬ floorLog10Pow2 q + 1 > pow10Table128_kMax) :
    128 ≤ (pow10Lookup128 (-(floorLog10Pow2 q + 1))).2.2 - q := by
  have h3 : pow10Table128_kMin = -324 := rfl
  have h4 : pow10Table128_kMax = 324 := rfl
  have hR := R15HoldsAt_in_binary64_range q h1 h2
  dsimp only [R15HoldsAt] at hR
  obtain ⟨-, hR⟩ := hR
  rw [pow10Lookup128_eq _ (by omega) (by omega)]
  show 128 ≤ pow10Shift (-(floorLog10Pow2 q + 1)) - q
  generalize hk : floorLog10Pow2 q = k at *
  have h2pos : 0 < 2 ^ q.natAbs := Nat.pow_pos (by decide)
  have h10pos : 0 < 10 ^ (k + 1).natAbs := Nat.pow_pos (by decide)
  unfold pow10Shift
  by_cases hq : q ≥ 0 <;> by_cases hk1 : k + 1 ≥ 0
    <;> simp only [hq, hk1, if_true, if_false, Nat.mul_one, Nat.one_mul] at hR
  · -- q ≥ 0, k + 1 ≥ 0: 2^q < 10^(k+1)
    by_cases hj : -(k + 1) ≥ 0
    · exfalso
      rw [show (k + 1).natAbs = 0 by omega, Nat.pow_zero] at hR
      omega
    · rw [if_neg hj, show (-(-(k + 1))).toNat = (k + 1).natAbs by omega]
      have hL := @Nat.lt_log2_self (10 ^ (k + 1).natAbs)
      have := Nat.lt_trans hR hL
      rw [Nat.pow_lt_pow_iff_right (by decide)] at this
      omega
  · -- q ≥ 0, k + 1 < 0: 2^q · 10^|k+1| < 1 is impossible
    exfalso
    have := Nat.mul_pos h2pos h10pos
    omega
  · -- q < 0, k + 1 ≥ 0: the shift is at least 127 and -q ≥ 1
    by_cases hj : -(k + 1) ≥ 0
    · rw [if_pos hj, show (-(k + 1)).toNat = 0 by omega, Nat.pow_zero]
      have : Nat.log2 1 = 0 := by decide
      omega
    · rw [if_neg hj]
      omega
  · -- q < 0, k + 1 < 0: 10^|k+1| < 2^|q|
    rw [if_pos (by omega)]
    have hL := Nat.log2_self_le (Nat.ne_of_gt h10pos)
    have : 2 ^ Nat.log2 (10 ^ (k + 1).natAbs) < 2 ^ q.natAbs := Nat.lt_of_le_of_lt hL hR
    rw [Nat.pow_lt_pow_iff_right (by decide)] at this
    rw [show (-(k + 1)).toNat = (k + 1).natAbs by omega]
    omega

end Srtfp.Schubfach

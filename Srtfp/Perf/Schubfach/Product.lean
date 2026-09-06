module
/- Algorithm F8 (§9.9 of the paper): `r'_o(4V')` from the two 63-bit halves of
   `g` and the 60-bit `c'`, where `2V' = c'·g / 2^128`.

   Writing `N = c'·g`, the value is `⌊N / 2^127⌋` with its low bit forced on
   when bits 64..126 of `N` are not all zero (bit 127 is the low bit itself,
   and bits 0..63 are below `ε = 2^-64`). -/

public import Srtfp.Perf.MulHigh128
public import Srtfp.Perf.Schubfach.RoundOdd
public import Srtfp.Perf.Schubfach.Table

@[expose] public section

open Srtfp.Compat

namespace Srtfp.Schubfach

theorem eps_eq : eps = (((2 ^ 64 : Nat) : Rat))⁻¹ := two_zpow_neg_toNat (Int.natCast_nonneg _)

theorem two_eps_le_one : 2 * eps ≤ 1 := by
  rw [eps_eq]
  have h : (0 : Rat) < ((2 ^ 64 : Nat) : Rat) := by exact_mod_cast Nat.two_pow_pos 64
  have e := Rat.inv_mul_cancel _ (Rat.ne_of_gt h)
  refine Rat.le_of_mul_le_mul_right (c := ((2 ^ 64 : Nat) : Rat)) ?_ h
  rw [Rat.mul_assoc, e, Rat.mul_one, Rat.one_mul]
  exact_mod_cast (by decide : 2 ≤ 2 ^ 64)

/-! ## Floors of quotients -/

/-! ## The algorithm -/

def MASK63 : UInt64 := 0x7FFFFFFFFFFFFFFF

/-- F8. -/
@[inline] def rop (g1 g0 cp : UInt64) : UInt64 :=
  let x1 := mulHi64 g0 cp
  let y0 := g1 * cp
  let y1 := mulHi64 g1 cp
  let z := (y0 >>> 1) + x1
  let vbp := y1 + (z >>> 63)
  vbp ||| (((z &&& MASK63) + MASK63) >>> 63)

/-- What F8 computes, on `N = c'·g`. -/
def ropNat (N : Nat) : Nat :=
  N / 2 ^ 127 ||| (if (N / 2 ^ 64) % 2 ^ 63 = 0 then 0 else 1)

theorem rop_toNat (g1 g0 cp : UInt64) (hg1 : g1.toNat < 2 ^ 63) (hg0 : g0.toNat < 2 ^ 63)
    (hcp : cp.toNat < 2 ^ 60) (hcp2 : 2 ∣ cp.toNat) :
    (rop g1 g0 cp).toNat = ropNat (cp.toNat * (g1.toNat * 2 ^ 63 + g0.toNat)) := by
  unfold rop ropNat
  have hP : g1.toNat * cp.toNat < 2 ^ 123 :=
    Nat.lt_of_lt_of_le (Nat.mul_lt_mul'' hg1 hcp) (by decide)
  have hQ : g0.toNat * cp.toNat < 2 ^ 123 :=
    Nat.lt_of_lt_of_le (Nat.mul_lt_mul'' hg0 hcp) (by decide)
  have hP2 : 2 ∣ g1.toNat * cp.toNat := Nat.dvd_trans hcp2 (Nat.dvd_mul_left _ _)
  have hN : cp.toNat * (g1.toNat * 2 ^ 63 + g0.toNat)
      = g1.toNat * cp.toNat * 2 ^ 63 + g0.toNat * cp.toNat := by grind
  rw [hN]
  simp only [UInt64.toNat_or, UInt64.toNat_shiftRight, UInt64.toNat_add, UInt64.toNat_and,
    mulHi64_toNat_eq, UInt64.toNat_mul, show MASK63.toNat = 2 ^ 63 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, Nat.pow_one,
    show (63 : UInt64).toNat % 64 = 63 from rfl, show (1 : UInt64).toNat % 64 = 1 from rfl,
    -Nat.reducePow]
  generalize g1.toNat * cp.toNat = P at *
  generalize g0.toNat * cp.toNat = Q at *
  -- `P = y1·2^64 + y0`, `Q = x1·2^64 + x0`
  have hPd := Nat.div_add_mod P (2 ^ 64)
  have hQd := Nat.div_add_mod Q (2 ^ 64)
  have hy0 := Nat.mod_lt P (by decide : 0 < 2 ^ 64)
  have hx0 := Nat.mod_lt Q (by decide : 0 < 2 ^ 64)
  generalize P / 2 ^ 64 = y1 at *
  generalize P % 2 ^ 64 = y0 at *
  generalize Q / 2 ^ 64 = x1 at *
  generalize Q % 2 ^ 64 = x0 at *
  subst hPd hQd
  have hz : (y0 / 2 + x1) % 2 ^ 64 = y0 / 2 + x1 := Nat.mod_eq_of_lt (by omega)
  have hA : ((2 ^ 64 * y1 + y0) * 2 ^ 63 + (2 ^ 64 * x1 + x0)) / 2 ^ 64
      = y1 * 2 ^ 63 + (y0 / 2 + x1) := by
    have hNeq : (2 ^ 64 * y1 + y0) * 2 ^ 63 + (2 ^ 64 * x1 + x0)
        = 2 ^ 64 * (y1 * 2 ^ 63 + (y0 / 2 + x1)) + x0 := by omega
    rw [hNeq, Nat.mul_add_div (by decide), Nat.div_eq_of_lt hx0, Nat.add_zero]
  have hB : ((2 ^ 64 * y1 + y0) * 2 ^ 63 + (2 ^ 64 * x1 + x0)) / 2 ^ 127
      = y1 + (y0 / 2 + x1) / 2 ^ 63 := by
    rw [show (2 ^ 127 : Nat) = 2 ^ 64 * 2 ^ 63 by simp, ← Nat.div_div_eq_div_mul, hA,
      Nat.mul_comm y1, Nat.mul_add_div (by decide)]
  simp only [hz, -Nat.reducePow]
  -- (`rw`/`congr` would try to unify `x * 2^63`-shaped terms and unfold `Nat.mul`)
  refine congr (congrArg HOr.hOr ?_) ?_
  · omega
  · split <;> omega

/-- `r'_o` of `N / 2^127`, in integers. -/
theorem ro'_natDiv (N : Nat) :
    ro' eps ((N : Rat) / ((2 ^ 127 : Nat) : Rat))
      = if N % 2 ^ 128 < 2 ^ 64 then ((N / 2 ^ 127 : Nat) : Int)
        else if (N / 2 ^ 127) % 2 = 0 then ((N / 2 ^ 127 : Nat) : Int) + 1
        else ((N / 2 ^ 127 : Nat) : Int) := by
  rw [R23 two_eps_le_one]
  have h127 : (0 : Rat) < ((2 ^ 127 : Nat) : Rat) := by exact_mod_cast Nat.two_pow_pos 127
  have h128 : (0 : Rat) < ((2 ^ 128 : Nat) : Rat) := by exact_mod_cast Nat.two_pow_pos 128
  have hx2 : (N : Rat) / ((2 ^ 127 : Nat) : Rat) / 2 = (N : Rat) / ((2 ^ 128 : Nat) : Rat) := by
    rw [div_eq_iff (by decide : (0 : Rat) < 2), div_eq_iff h127]
    have hB : ((2 ^ 128 : Nat) : Rat) = ((2 ^ 127 : Nat) : Rat) * 2 := by
      rw [show (2 ^ 128 : Nat) = 2 ^ 127 * 2 from Nat.pow_succ 2 127]; norm_cast
    have e := Rat.div_mul_cancel (a := (N : Rat)) (Rat.ne_of_gt h128)
    rw [hB] at e
    grind
  rw [hx2, floor_natDiv N (2 ^ 128) (Nat.two_pow_pos _), floor_natDiv N (2 ^ 127) (Nat.two_pow_pos _),
    Rat.intCast_natCast, frac_natDiv N (2 ^ 128) (Nat.two_pow_pos _)]
  have hcond : ((N % 2 ^ 128 : Nat) : Rat) / ((2 ^ 128 : Nat) : Rat) < eps ↔ N % 2 ^ 128 < 2 ^ 64 := by
    rw [eps_eq, Rat.div_lt_iff h128]
    have e : (((2 ^ 64 : Nat) : Rat))⁻¹ * ((2 ^ 128 : Nat) : Rat) = ((2 ^ 64 : Nat) : Rat) := by
      have h64 : (0 : Rat) < ((2 ^ 64 : Nat) : Rat) := by exact_mod_cast Nat.two_pow_pos 64
      have e1 := Rat.inv_mul_cancel _ (Rat.ne_of_gt h64)
      have : ((2 ^ 128 : Nat) : Rat) = ((2 ^ 64 : Nat) : Rat) * ((2 ^ 64 : Nat) : Rat) := by
        rw [show (2 ^ 128 : Nat) = 2 ^ 64 * 2 ^ 64 from (Nat.pow_add 2 64 64).symm]; norm_cast
      rw [this, ← Rat.mul_assoc, e1, Rat.one_mul]
    rw [e]
    exact ⟨fun h => by exact_mod_cast h, fun h => by exact_mod_cast h⟩
  by_cases hc : N % 2 ^ 128 < 2 ^ 64
  · rw [if_pos (hcond.mpr hc), if_pos hc]
  · rw [if_neg (fun h => hc (hcond.mp h)), if_neg hc]
    by_cases he : (N / 2 ^ 127) % 2 = 0
    · rw [if_pos (by omega), if_pos he]
    · rw [if_neg (by omega), if_neg he]

theorem or_one_eq (n : Nat) : n ||| 1 = if n % 2 = 0 then n + 1 else n := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or]
  cases i with
  | zero =>
    rw [Nat.testBit_zero, Nat.testBit_zero, Nat.testBit_zero]
    split <;> simp <;> omega
  | succ i =>
    rw [Nat.testBit_add_one, Nat.testBit_add_one, Nat.testBit_add_one,
      show (if n % 2 = 0 then n + 1 else n) / 2 = n / 2 by split <;> omega,
      show (1 : Nat) / 2 = 0 from rfl, Nat.zero_testBit, Bool.or_false]

/-- **R25** in integers: F8 computes `r'_o(4V')`. -/
theorem rop_eq (g1 g0 cp : UInt64) (hg1 : g1.toNat < 2 ^ 63) (hg0 : g0.toNat < 2 ^ 63)
    (hcp : cp.toNat < 2 ^ 60) (hcp2 : 2 ∣ cp.toNat) :
    ((rop g1 g0 cp).toNat : Int)
      = ro' eps (((cp.toNat * (g1.toNat * 2 ^ 63 + g0.toNat) : Nat) : Rat) / ((2 ^ 127 : Nat) : Rat)) := by
  rw [rop_toNat g1 g0 cp hg1 hg0 hcp hcp2, ro'_natDiv]
  generalize cp.toNat * (g1.toNat * 2 ^ 63 + g0.toNat) = N
  unfold ropNat
  by_cases hc : N % 2 ^ 128 < 2 ^ 64
  · rw [if_pos hc, if_pos (by omega), Nat.or_zero]
  · rw [if_neg hc]
    by_cases he : (N / 2 ^ 127) % 2 = 0
    · -- bit 127 clear, so bits 64..126 are not all zero
      rw [if_neg (by omega), or_one_eq, if_pos he, if_pos he]; simp
    · rw [if_neg he]
      by_cases hb : (N / 2 ^ 64) % 2 ^ 63 = 0
      · rw [if_pos hb, Nat.or_zero]
      · rw [if_neg hb, or_one_eq, if_neg he]

end Srtfp.Schubfach

/- 192-bit UInt64-triple arithmetic model for the Schubfach multiply-shift
   kernel.

   `cmpScaledMixed_fast2` and `shiftedSig_fast2` represent intermediate
   192-bit unsigned values as triples `(hi, mid, lo) : UInt64 × UInt64 × UInt64`.
   This file lifts those operations to `Nat`:

     `triple192Nat (hi, mid, lo) = hi.toNat·2^128 + mid.toNat·2^64 + lo.toNat`

   then proves the UInt64-triple operations agree with `Nat` arithmetic
   modulo `2^192`.

   ## Contents

   - `triple192Nat`: the Nat interpretation of a UInt64 triple.
   - `add192_64_toNat`: `add192_64` faithfully adds a UInt64 to a triple,
     modulo `2^192`.
   - `mul192_b_g_toNat`: the four-multiply-and-carry combination in the
     `cmpScaledMixed_fast2` body equals `b · (gHi·2^64 + gLo)` modulo `2^192`.

   These lemmas isolate the pure 192-bit arithmetic from the §9.6–§9.8
   error-bound reasoning that lives in `KernelCorrectness.lean`.
-/
import Srtfp.Schubfach
import Srtfp.Schubfach.MulHigh128
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Srtfp.Schubfach

set_option maxRecDepth 1024
set_option maxHeartbeats 1000000

/-! ## Numerical constants. -/

private theorem pow2_128_split : (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 := by decide
private theorem pow2_192_split : (2 : Nat) ^ 192 = 2 ^ 64 * 2 ^ 64 * 2 ^ 64 := by decide

/-! ## 192-bit Nat interpretation -/

/-- Nat value of a 192-bit (hi, mid, lo) UInt64 triple. -/
def triple192Nat (hi mid lo : UInt64) : Nat :=
  hi.toNat * 2 ^ 128 + mid.toNat * 2 ^ 64 + lo.toNat

/-- A 192-bit triple is bounded by `2^192`. -/
theorem triple192Nat_lt (hi mid lo : UInt64) :
    triple192Nat hi mid lo < 2 ^ 192 := by
  unfold triple192Nat
  have hHi : hi.toNat < 2 ^ 64 := hi.toNat_lt
  have hMid : mid.toNat < 2 ^ 64 := mid.toNat_lt
  have hLo : lo.toNat < 2 ^ 64 := lo.toNat_lt
  have h128 : (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 := pow2_128_split
  have h192 : (2 : Nat) ^ 192 = 2 ^ 64 * 2 ^ 64 * 2 ^ 64 := pow2_192_split
  have hHi_bound : hi.toNat * 2 ^ 128 ≤ (2 ^ 64 - 1) * 2 ^ 128 := by
    apply Nat.mul_le_mul_right; omega
  have hMid_bound : mid.toNat * 2 ^ 64 ≤ (2 ^ 64 - 1) * 2 ^ 64 := by
    apply Nat.mul_le_mul_right; omega
  have hKey : (2 ^ 64 - 1) * 2 ^ 128 + (2 ^ 64 - 1) * 2 ^ 64 + 2 ^ 64 ≤ 2 ^ 192 := by
    rw [h128, h192]
    have h64_pos : 1 ≤ (2 : Nat) ^ 64 := by
      have : (0 : Nat) < 2 ^ 64 := Nat.two_pow_pos _
      omega
    have h1 : (2 ^ 64 - 1) * (2 ^ 64 * 2 ^ 64) = 2 ^ 64 * 2 ^ 64 * 2 ^ 64 - 2 ^ 64 * 2 ^ 64 := by
      rw [Nat.sub_mul]; ring_nf
    have h2 : (2 ^ 64 - 1) * 2 ^ 64 = 2 ^ 64 * 2 ^ 64 - 2 ^ 64 := by
      rw [Nat.sub_mul]; ring_nf
    have hn2_le_n3 : 2 ^ 64 * 2 ^ 64 ≤ 2 ^ 64 * 2 ^ 64 * 2 ^ 64 := by nlinarith
    have hn_le_n2 : (2 : Nat) ^ 64 ≤ 2 ^ 64 * 2 ^ 64 := by nlinarith
    omega
  omega

/-! ## Helper: carry detection in UInt64 -/

/-- UInt64 add is mod 2^64. -/
theorem UInt64_add_toNat (x y : UInt64) :
    (x + y).toNat = (x.toNat + y.toNat) % 2 ^ 64 :=
  UInt64.toNat_add x y

/-- Nat formula for `(x + y).toNat`: either the natural sum (no carry) or
    the sum minus `2^64` (carry). -/
theorem UInt64_add_toNat_eq (x y : UInt64) :
    x.toNat + y.toNat = (x + y).toNat + (if x.toNat + y.toNat < 2 ^ 64 then 0 else 2 ^ 64) := by
  rw [UInt64_add_toNat]
  have hx : x.toNat < 2 ^ 64 := x.toNat_lt
  have hy : y.toNat < 2 ^ 64 := y.toNat_lt
  by_cases h : x.toNat + y.toNat < 2 ^ 64
  · simp only [if_pos h, Nat.add_zero]
    rw [Nat.mod_eq_of_lt h]
  · push_neg at h
    simp only [if_neg (not_lt_of_ge h)]
    have h1 : x.toNat + y.toNat - 2 ^ 64 < 2 ^ 64 := by omega
    have h2 : (x.toNat + y.toNat) = (x.toNat + y.toNat - 2 ^ 64) + 1 * 2 ^ 64 := by omega
    rw [h2, Nat.add_mul_mod_self_right]
    rw [Nat.mod_eq_of_lt h1]
    omega

/-- Carry indicator. `(x + y) < x` (UInt64 comparison) iff `x.toNat + y.toNat ≥ 2^64`. -/
theorem add_carry_iff (x y : UInt64) :
    (x + y) < x ↔ x.toNat + y.toNat ≥ 2 ^ 64 := by
  rw [UInt64.lt_iff_toNat_lt, UInt64_add_toNat]
  have hx : x.toNat < 2 ^ 64 := x.toNat_lt
  have hy : y.toNat < 2 ^ 64 := y.toNat_lt
  by_cases h : x.toNat + y.toNat < 2 ^ 64
  · rw [Nat.mod_eq_of_lt h]
    refine ⟨?_, ?_⟩
    · intro hLt; omega
    · intro hGe; omega
  · push_neg at h
    have h1 : x.toNat + y.toNat - 2 ^ 64 < 2 ^ 64 := by omega
    have h2 : (x.toNat + y.toNat) = (x.toNat + y.toNat - 2 ^ 64) + 1 * 2 ^ 64 := by omega
    rw [h2, Nat.add_mul_mod_self_right]
    rw [Nat.mod_eq_of_lt h1]
    refine ⟨?_, ?_⟩
    · intro _; omega
    · intro _; omega

/-! ## UInt64 = 1 is decidable; bridge to .toNat = 1 -/

private theorem uint64_eq_one_of_toNat_one {c : UInt64} (h : c.toNat = 1) : c = 1 := by
  rw [← UInt64.toNat_inj, h]; decide

/-! ## Addition: `add192_64` lifts to Nat -/

/-- The UInt64 triple in `add192_64 hi mid lo x` represents the Nat
    sum `(triple192Nat hi mid lo + x.toNat) mod 2^192`. -/
theorem add192_64_toNat (hi mid lo x : UInt64) :
    triple192Nat (add192_64 hi mid lo x).1 (add192_64 hi mid lo x).2.1
                 (add192_64 hi mid lo x).2.2
      = (triple192Nat hi mid lo + x.toNat) % 2 ^ 192 := by
  -- Establish bounds.
  have hHi : hi.toNat < 2 ^ 64 := hi.toNat_lt
  have hMid : mid.toNat < 2 ^ 64 := mid.toNat_lt
  have hLo : lo.toNat < 2 ^ 64 := lo.toNat_lt
  have hX : x.toNat < 2 ^ 64 := x.toNat_lt
  have h128 : (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 := pow2_128_split
  have h192 : (2 : Nat) ^ 192 = 2 ^ 64 * 2 ^ 64 * 2 ^ 64 := pow2_192_split
  unfold add192_64 triple192Nat
  -- Use a clean variable for lo'.
  set lo' : UInt64 := lo + x with hlo'_def
  have hLoSum : lo.toNat + x.toNat
                  = lo'.toNat + (if lo.toNat + x.toNat < 2 ^ 64 then 0 else 2 ^ 64) := by
    rw [hlo'_def]; exact UInt64_add_toNat_eq lo x
  set c0 : UInt64 := if lo' < lo then 1 else 0 with hc0_def
  have hc0_toNat : c0.toNat = (if lo.toNat + x.toNat < 2 ^ 64 then 0 else 1) := by
    rw [hc0_def]
    by_cases hC : lo.toNat + x.toNat < 2 ^ 64
    · have hNotLt : ¬ lo' < lo := by rw [hlo'_def, add_carry_iff]; omega
      simp only [hNotLt, if_false, if_pos hC]
      decide
    · have hLt' : lo' < lo := by rw [hlo'_def, add_carry_iff]; omega
      simp only [hLt', if_true, if_neg hC]
      decide
  have hc0_le : c0.toNat ≤ 1 := by rw [hc0_toNat]; split <;> omega
  set mid' : UInt64 := mid + c0 with hmid'_def
  have hMidSum : mid.toNat + c0.toNat
                  = mid'.toNat + (if mid.toNat + c0.toNat < 2 ^ 64 then 0 else 2 ^ 64) := by
    rw [hmid'_def]; exact UInt64_add_toNat_eq mid c0
  set c1 : UInt64 := if c0 = 1 ∧ mid' < mid then 1 else 0 with hc1_def
  have hc1_toNat : c1.toNat = (if mid.toNat + c0.toNat < 2 ^ 64 then 0 else 1) := by
    rw [hc1_def]
    by_cases hC : mid.toNat + c0.toNat < 2 ^ 64
    · have hNotLt : ¬ mid' < mid := by rw [hmid'_def, add_carry_iff]; omega
      have hCond : ¬ (c0 = 1 ∧ mid' < mid) := fun ⟨_, h⟩ => hNotLt h
      simp only [hCond, if_false, if_pos hC]
      decide
    · push_neg at hC
      -- mid + c0 ≥ 2^64.  Since mid < 2^64 and c0 ≤ 1, c0 = 1 and mid = 2^64-1.
      have hc0_eq_one_nat : c0.toNat = 1 := by omega
      have hc0_eq_one : c0 = 1 := uint64_eq_one_of_toNat_one hc0_eq_one_nat
      have hMidLt : mid' < mid := by
        rw [hmid'_def, add_carry_iff]; omega
      have hCond : c0 = 1 ∧ mid' < mid := ⟨hc0_eq_one, hMidLt⟩
      have hIte_pos : (if c0 = 1 ∧ mid' < mid then (1 : UInt64) else 0) = 1 := if_pos hCond
      have hIte_neg : ¬ mid.toNat + c0.toNat < 2 ^ 64 := by omega
      rw [hIte_pos, if_neg hIte_neg]
      decide
  have hc1_le : c1.toNat ≤ 1 := by rw [hc1_toNat]; split <;> omega
  set hi' : UInt64 := hi + c1 with hhi'_def
  have hHiSum : hi.toNat + c1.toNat
                  = hi'.toNat + (if hi.toNat + c1.toNat < 2 ^ 64 then 0 else 2 ^ 64) := by
    rw [hhi'_def]; exact UInt64_add_toNat_eq hi c1
  -- Quantity names.
  set cLo : Nat := (if lo.toNat + x.toNat < 2 ^ 64 then 0 else 2 ^ 64) with hcLo_def
  set cMid : Nat := (if mid.toNat + c0.toNat < 2 ^ 64 then 0 else 2 ^ 64) with hcMid_def
  set cHi : Nat := (if hi.toNat + c1.toNat < 2 ^ 64 then 0 else 2 ^ 64) with hcHi_def
  have hLoSum' : lo.toNat + x.toNat = lo'.toNat + cLo := by rw [hcLo_def]; exact hLoSum
  have hMidSum' : mid.toNat + c0.toNat = mid'.toNat + cMid := by rw [hcMid_def]; exact hMidSum
  have hHiSum' : hi.toNat + c1.toNat = hi'.toNat + cHi := by rw [hcHi_def]; exact hHiSum
  have hc0_x_pow : c0.toNat * 2 ^ 64 = cLo := by
    rw [hc0_toNat, hcLo_def]
    split <;> simp
  have hc1_x_pow : c1.toNat * 2 ^ 64 = cMid := by
    rw [hc1_toNat, hcMid_def]
    split <;> simp
  -- Big arithmetic combine.  Multiply hLoSum' by 1, hMidSum' by 2^64, hHiSum' by 2^128, sum.
  have hCombine :
      hi.toNat * 2 ^ 128 + mid.toNat * 2 ^ 64 + lo.toNat + x.toNat
        = hi'.toNat * 2 ^ 128 + mid'.toNat * 2 ^ 64 + lo'.toNat + cHi * 2 ^ 128 := by
    have hCM_pow : cMid * 2 ^ 64 = c1.toNat * 2 ^ 128 := by
      rw [h128, ← hc1_x_pow]; ring
    -- Goal: ... = ... + cHi · 2^128.
    -- We have:
    --   hLoSum'       : lo + x = lo' + cLo
    --   hMidSum'·2^64 : mid·2^64 + c0·2^64 = mid'·2^64 + cMid·2^64
    --   hHiSum'·2^128 : hi·2^128 + c1·2^128 = hi'·2^128 + cHi·2^128
    -- And c0·2^64 = cLo, cMid·2^64 = c1·2^128.
    nlinarith [hLoSum', hMidSum', hHiSum', hc0_x_pow, hCM_pow, h128]
  have hCHi_cases : cHi * 2 ^ 128 = 0 ∨ cHi * 2 ^ 128 = 2 ^ 192 := by
    by_cases hCC : hi.toNat + c1.toNat < 2 ^ 64
    · left
      have : cHi = 0 := by rw [hcHi_def, if_pos hCC]
      rw [this]; ring
    · right
      have : cHi = 2 ^ 64 := by rw [hcHi_def, if_neg hCC]
      rw [this, h192]; ring
  have hTriple_lt : hi'.toNat * 2 ^ 128 + mid'.toNat * 2 ^ 64 + lo'.toNat < 2 ^ 192 := by
    have hHi' : hi'.toNat < 2 ^ 64 := hi'.toNat_lt
    have hMid' : mid'.toNat < 2 ^ 64 := mid'.toNat_lt
    have hLo' : lo'.toNat < 2 ^ 64 := lo'.toNat_lt
    have hHi_bd : hi'.toNat * 2 ^ 128 ≤ (2 ^ 64 - 1) * 2 ^ 128 := by
      apply Nat.mul_le_mul_right; omega
    have hMid_bd : mid'.toNat * 2 ^ 64 ≤ (2 ^ 64 - 1) * 2 ^ 64 := by
      apply Nat.mul_le_mul_right; omega
    have hKey : (2 ^ 64 - 1) * 2 ^ 128 + (2 ^ 64 - 1) * 2 ^ 64 + 2 ^ 64 ≤ 2 ^ 192 := by
      rw [h128, h192]
      have h64_pos : 1 ≤ (2 : Nat) ^ 64 := by
        have : (0 : Nat) < 2 ^ 64 := Nat.two_pow_pos _
        omega
      have h1 : (2 ^ 64 - 1) * (2 ^ 64 * 2 ^ 64) = 2 ^ 64 * 2 ^ 64 * 2 ^ 64 - 2 ^ 64 * 2 ^ 64 := by
        rw [Nat.sub_mul]; ring_nf
      have h2 : (2 ^ 64 - 1) * 2 ^ 64 = 2 ^ 64 * 2 ^ 64 - 2 ^ 64 := by
        rw [Nat.sub_mul]; ring_nf
      have hn2_le_n3 : 2 ^ 64 * 2 ^ 64 ≤ 2 ^ 64 * 2 ^ 64 * 2 ^ 64 := by nlinarith
      have hn_le_n2 : (2 : Nat) ^ 64 ≤ 2 ^ 64 * 2 ^ 64 := by nlinarith
      omega
    omega
  rcases hCHi_cases with hCHi0 | hCHi192
  · -- No top carry.
    have : hi.toNat * 2 ^ 128 + mid.toNat * 2 ^ 64 + lo.toNat + x.toNat
              = hi'.toNat * 2 ^ 128 + mid'.toNat * 2 ^ 64 + lo'.toNat := by
      omega
    rw [← this]
    exact (Nat.mod_eq_of_lt (by omega)).symm
  · -- Top carry of 2^192.
    have hTotal' : hi.toNat * 2 ^ 128 + mid.toNat * 2 ^ 64 + lo.toNat + x.toNat
                    = (hi'.toNat * 2 ^ 128 + mid'.toNat * 2 ^ 64 + lo'.toNat) + 1 * 2 ^ 192 := by
      omega
    rw [hTotal', Nat.add_mul_mod_self_right]
    exact (Nat.mod_eq_of_lt hTriple_lt).symm

/-! ## Multiplication: 64 × 128 → 192-bit triple

`cmpScaledMixed_fast2` computes `R = b · (gHi · 2^64 + gLo)` via four
schoolbook UInt64 multiplications and a single carry-aware mid-row
addition.  When `b < 2^60` (the guard imposed at the top of the fast
path) the full product is `< 2^124`, well inside `2^192`, so the
triple value exactly equals the mathematical product.
-/

/-- The 192-bit triple `(r_hi, r_mid, r_lo)` assembled from
    `bU * gLo`, `mulHi64 bU gLo`, `bU * gHi`, `mulHi64 bU gHi`
    plus the mid-row carry equals the Nat product
    `bU.toNat * (gHi.toNat * 2^64 + gLo.toNat) mod 2^192`. -/
theorem mul192_b_g_toNat (bU gHi gLo : UInt64) :
    let rLo  := bU * gLo
    let rLoH := mulHi64 bU gLo
    let rHi  := bU * gHi
    let rHiH := mulHi64 bU gHi
    let midSum   : UInt64 := rHi + rLoH
    let midCarry : UInt64 := if midSum < rHi then 1 else 0
    let r_hi  : UInt64 := rHiH + midCarry
    let r_mid : UInt64 := midSum
    let r_lo  : UInt64 := rLo
    triple192Nat r_hi r_mid r_lo
      = (bU.toNat * (gHi.toNat * 2 ^ 64 + gLo.toNat)) % 2 ^ 192 := by
  -- Bounds.
  have hb : bU.toNat < 2 ^ 64 := bU.toNat_lt
  have hgH : gHi.toNat < 2 ^ 64 := gHi.toNat_lt
  have hgL : gLo.toNat < 2 ^ 64 := gLo.toNat_lt
  have h64 : (2 : Nat) ^ 64 > 0 := Nat.two_pow_pos _
  have h128 : (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 := pow2_128_split
  have h192 : (2 : Nat) ^ 192 = 2 ^ 64 * 2 ^ 64 * 2 ^ 64 := pow2_192_split
  -- Component values.
  set blo : Nat := bU.toNat * gLo.toNat
  have hblo_def : blo = bU.toNat * gLo.toNat := rfl
  set bhi : Nat := bU.toNat * gHi.toNat
  have hbhi_def : bhi = bU.toNat * gHi.toNat := rfl
  -- rLo.toNat = blo mod 2^64.  rLoH.toNat = blo / 2^64.
  have hrLo_toNat : (bU * gLo).toNat = blo % 2 ^ 64 := by
    rw [hblo_def]; exact UInt64.toNat_mul bU gLo
  have hrLoH_toNat : (mulHi64 bU gLo).toNat = blo / 2 ^ 64 := by
    rw [hblo_def]; exact mulHi64_toNat_eq bU gLo
  have hrHi_toNat : (bU * gHi).toNat = bhi % 2 ^ 64 := by
    rw [hbhi_def]; exact UInt64.toNat_mul bU gHi
  have hrHiH_toNat : (mulHi64 bU gHi).toNat = bhi / 2 ^ 64 := by
    rw [hbhi_def]; exact mulHi64_toNat_eq bU gHi
  -- Split lemmas.
  have hblo_split : blo = (blo / 2 ^ 64) * 2 ^ 64 + blo % 2 ^ 64 := by
    have := Nat.div_add_mod blo (2 ^ 64); omega
  have hbhi_split : bhi = (bhi / 2 ^ 64) * 2 ^ 64 + bhi % 2 ^ 64 := by
    have := Nat.div_add_mod bhi (2 ^ 64); omega
  -- Bound: blo, bhi < 2^128.
  have hblo_lt : blo < 2 ^ 128 := by
    rw [hblo_def, h128]
    exact Nat.mul_lt_mul_of_lt_of_lt hb hgL
  have hbhi_lt : bhi < 2 ^ 128 := by
    rw [hbhi_def, h128]
    exact Nat.mul_lt_mul_of_lt_of_lt hb hgH
  -- Hence blo/2^64, bhi/2^64 < 2^64.
  have hblo_hi_lt : blo / 2 ^ 64 < 2 ^ 64 := by
    apply Nat.div_lt_of_lt_mul; rw [← h128]; exact hblo_lt
  have hbhi_hi_lt : bhi / 2 ^ 64 < 2 ^ 64 := by
    apply Nat.div_lt_of_lt_mul; rw [← h128]; exact hbhi_lt
  have hblo_lo_lt : blo % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ h64
  have hbhi_lo_lt : bhi % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ h64
  -- midSum = rHi + rLoH (UInt64); carry from this add.
  set rLo_v  : UInt64 := bU * gLo with hrLo_def
  set rLoH_v : UInt64 := mulHi64 bU gLo with hrLoH_def
  set rHi_v  : UInt64 := bU * gHi with hrHi_def
  set rHiH_v : UInt64 := mulHi64 bU gHi with hrHiH_def
  set midSum_v : UInt64 := rHi_v + rLoH_v with hmid_def
  have hMidNat_eq : rHi_v.toNat + rLoH_v.toNat
                      = midSum_v.toNat + (if rHi_v.toNat + rLoH_v.toNat < 2 ^ 64 then 0 else 2 ^ 64) := by
    rw [hmid_def]; exact UInt64_add_toNat_eq rHi_v rLoH_v
  set midCarry_v : UInt64 := if midSum_v < rHi_v then 1 else 0 with hmidCarry_def
  have hMidCarry_toNat : midCarry_v.toNat
                          = (if rHi_v.toNat + rLoH_v.toNat < 2 ^ 64 then 0 else 1) := by
    rw [hmidCarry_def]
    by_cases hC : rHi_v.toNat + rLoH_v.toNat < 2 ^ 64
    · have hNotLt : ¬ midSum_v < rHi_v := by rw [hmid_def, add_carry_iff]; omega
      simp only [hNotLt, if_false, if_pos hC]
      decide
    · have hLt' : midSum_v < rHi_v := by rw [hmid_def, add_carry_iff]; omega
      simp only [hLt', if_true, if_neg hC]
      decide
  set rHi_top : UInt64 := rHiH_v + midCarry_v with hrHi_top_def
  -- rHiH.toNat + midCarry.toNat doesn't overflow 2^64 here?  bU < 2^64 doesn't suffice
  -- in general, but rHiH < 2^64 and midCarry ≤ 1, so the sum is ≤ 2^64; and we'll
  -- track this carefully below.
  -- Mass equation in Nat:
  --   bU · g  = bU · (gHi · 2^64 + gLo)
  --           = bhi · 2^64 + blo
  --           = (bhi/2^64) · 2^128 + (bhi % 2^64) · 2^64
  --             + (blo / 2^64) · 2^64 + (blo % 2^64)
  --           = bhi_hi · 2^128 + (bhi_lo + blo_hi) · 2^64 + blo_lo
  -- where the mid coefficient is at most 2(2^64-1) = 2^65 - 2.
  -- So mid = bhi_lo + blo_hi, may carry up to 1 into the high.
  set blo_lo : Nat := blo % 2 ^ 64
  set blo_hi : Nat := blo / 2 ^ 64
  set bhi_lo : Nat := bhi % 2 ^ 64
  set bhi_hi : Nat := bhi / 2 ^ 64
  have hbg_eq : bU.toNat * (gHi.toNat * 2 ^ 64 + gLo.toNat) = bhi * 2 ^ 64 + blo := by
    rw [hbhi_def, hblo_def]; ring
  have hbg_full :
      bU.toNat * (gHi.toNat * 2 ^ 64 + gLo.toNat)
        = bhi_hi * 2 ^ 128 + (bhi_lo + blo_hi) * 2 ^ 64 + blo_lo := by
    rw [hbg_eq]
    -- bhi · 2^64 + blo
    --   = (bhi_hi · 2^64 + bhi_lo) · 2^64 + (blo_hi · 2^64 + blo_lo)
    have hb1 : bhi = bhi_hi * 2 ^ 64 + bhi_lo := hbhi_split
    have hb2 : blo = blo_hi * 2 ^ 64 + blo_lo := hblo_split
    rw [hb1, hb2, h128]; ring
  -- midSum.toNat (the UInt64) = (bhi_lo + blo_hi) % 2^64
  --   and midCarry indicates whether bhi_lo + blo_hi ≥ 2^64.
  have hrHi_eq : rHi_v.toNat = bhi_lo := by rw [hrHi_def, hrHi_toNat]
  have hrLoH_eq : rLoH_v.toNat = blo_hi := by rw [hrLoH_def, hrLoH_toNat]
  have hrLo_eq : rLo_v.toNat = blo_lo := by rw [hrLo_def, hrLo_toNat]
  have hrHiH_eq : rHiH_v.toNat = bhi_hi := by rw [hrHiH_def, hrHiH_toNat]
  -- Recast hMidNat_eq.
  have hMidNat_eq' : bhi_lo + blo_hi
                       = midSum_v.toNat + (if bhi_lo + blo_hi < 2 ^ 64 then 0 else 2 ^ 64) := by
    rw [← hrHi_eq, ← hrLoH_eq]; exact hMidNat_eq
  have hMidCarry_eq' : midCarry_v.toNat
                          = (if bhi_lo + blo_hi < 2 ^ 64 then 0 else 1) := by
    rw [← hrHi_eq, ← hrLoH_eq]; exact hMidCarry_toNat
  -- Sum into high.  rHi_top = rHiH + midCarry; this doesn't overflow because
  -- both are < 2^64 and midCarry ∈ {0, 1} and we need to handle bhi_hi + 1 = 2^64
  -- as a wrap case — but that requires bhi_hi = 2^64 - 1 which means bhi ≥ ...
  -- big.  In general the formula is:
  --   r_hi.toNat = (bhi_hi + midCarry.toNat) % 2^64
  --   r_hi.toNat = (bhi_hi + midCarry.toNat) - top_carry · 2^64
  -- and the triple is (r_hi, r_mid, r_lo).toNat mod 2^192.
  have hHiSum_eq : bhi_hi + midCarry_v.toNat
                     = rHi_top.toNat + (if bhi_hi + midCarry_v.toNat < 2 ^ 64 then 0 else 2 ^ 64) := by
    have := UInt64_add_toNat_eq rHiH_v midCarry_v
    rw [hrHi_top_def, ← hrHiH_eq]; exact this
  -- Triple value as Nat.
  unfold triple192Nat
  -- triple192Nat r_hi r_mid r_lo = r_hi.toNat · 2^128 + r_mid.toNat · 2^64 + r_lo.toNat
  -- We want to show triple = (bhi · 2^64 + blo) % 2^192.
  -- The LHS variables (the let-defined ones above) are exactly rHi_top, midSum_v, rLo_v.
  show rHi_top.toNat * 2 ^ 128 + midSum_v.toNat * 2 ^ 64 + rLo_v.toNat
        = (bU.toNat * (gHi.toNat * 2 ^ 64 + gLo.toNat)) % 2 ^ 192
  rw [hbg_full, hrLo_eq]
  -- Goal: rHi_top.toNat · 2^128 + midSum_v.toNat · 2^64 + blo_lo
  --     = (bhi_hi · 2^128 + (bhi_lo + blo_hi) · 2^64 + blo_lo) % 2^192
  set cMid : Nat := if bhi_lo + blo_hi < 2 ^ 64 then 0 else 2 ^ 64 with hcMid_def
  set cHi : Nat := if bhi_hi + midCarry_v.toNat < 2 ^ 64 then 0 else 2 ^ 64 with hcHi_def
  have hMid_sub : midSum_v.toNat = bhi_lo + blo_hi - cMid := by
    rw [hcMid_def]; omega
  have hHi_sub : rHi_top.toNat = bhi_hi + midCarry_v.toNat - cHi := by
    rw [hcHi_def]; omega
  have hMidCarry_pow : midCarry_v.toNat * 2 ^ 64 = cMid := by
    rw [hMidCarry_eq', hcMid_def]
    split <;> simp
  have hcHi_le_pow : cHi ≤ 2 ^ 64 := by
    rw [hcHi_def]; split <;> omega
  -- Bound check on r_hi.toNat.
  have hHiBound : rHi_top.toNat < 2 ^ 64 := rHi_top.toNat_lt
  -- Bound check on midSum_v.toNat.
  have hMidBound : midSum_v.toNat < 2 ^ 64 := midSum_v.toNat_lt
  -- Big arithmetic: the LHS sums to bhi_hi · 2^128 + (bhi_lo + blo_hi) · 2^64 + blo_lo - cHi · 2^128
  -- Why? Because:
  --   rHi_top · 2^128 = (bhi_hi + midCarry - cHi/2^64) · 2^128
  --                   = bhi_hi · 2^128 + midCarry · 2^128 - cHi · 2^128
  --                   = bhi_hi · 2^128 + cMid · 2^64 - cHi · 2^128
  --   midSum · 2^64 = (bhi_lo + blo_hi - cMid) · 2^64 = (bhi_lo + blo_hi)·2^64 - cMid·2^64
  -- Hence rHi_top · 2^128 + midSum · 2^64 = bhi_hi · 2^128 + (bhi_lo + blo_hi)·2^64 - cHi · 2^128.
  have hLHS_eq :
      rHi_top.toNat * 2 ^ 128 + midSum_v.toNat * 2 ^ 64 + blo_lo + cHi * 2 ^ 128
        = bhi_hi * 2 ^ 128 + (bhi_lo + blo_hi) * 2 ^ 64 + blo_lo := by
    have hcMid_pow128 : cMid * 2 ^ 64 = midCarry_v.toNat * 2 ^ 128 := by
      rw [← hMidCarry_pow, h128]; ring
    -- Use the carry equations.
    have hHiSum_eq' : rHi_top.toNat + cHi = bhi_hi + midCarry_v.toNat := by
      rw [hcHi_def]; omega
    have hMidSum_eq' : midSum_v.toNat + cMid = bhi_lo + blo_hi := by
      rw [hcMid_def]; omega
    -- Multiply hHiSum_eq' by 2^128, hMidSum_eq' by 2^64, expand.
    have h_hi : rHi_top.toNat * 2 ^ 128 + cHi * 2 ^ 128
                  = bhi_hi * 2 ^ 128 + midCarry_v.toNat * 2 ^ 128 := by
      have := congrArg (· * 2 ^ 128) hHiSum_eq'
      simp at this; linarith
    have h_mid : midSum_v.toNat * 2 ^ 64 + cMid * 2 ^ 64
                   = bhi_lo * 2 ^ 64 + blo_hi * 2 ^ 64 := by
      have := congrArg (· * 2 ^ 64) hMidSum_eq'
      simp at this
      have : (midSum_v.toNat + cMid) * 2 ^ 64 = (bhi_lo + blo_hi) * 2 ^ 64 := by
        rw [hMidSum_eq']
      linarith [this]
    linarith [h_hi, h_mid, hcMid_pow128]
  -- Triple LHS bounded by 2^192.
  have hLHS_lt : rHi_top.toNat * 2 ^ 128 + midSum_v.toNat * 2 ^ 64 + blo_lo < 2 ^ 192 := by
    have hHi_bd : rHi_top.toNat * 2 ^ 128 ≤ (2 ^ 64 - 1) * 2 ^ 128 := by
      apply Nat.mul_le_mul_right; omega
    have hMid_bd : midSum_v.toNat * 2 ^ 64 ≤ (2 ^ 64 - 1) * 2 ^ 64 := by
      apply Nat.mul_le_mul_right; omega
    have hLo_bd : blo_lo < 2 ^ 64 := hblo_lo_lt
    have hKey : (2 ^ 64 - 1) * 2 ^ 128 + (2 ^ 64 - 1) * 2 ^ 64 + 2 ^ 64 ≤ 2 ^ 192 := by
      rw [h128, h192]
      have h64_pos : 1 ≤ (2 : Nat) ^ 64 := by
        have : (0 : Nat) < 2 ^ 64 := Nat.two_pow_pos _
        omega
      have h1 : (2 ^ 64 - 1) * (2 ^ 64 * 2 ^ 64) = 2 ^ 64 * 2 ^ 64 * 2 ^ 64 - 2 ^ 64 * 2 ^ 64 := by
        rw [Nat.sub_mul]; ring_nf
      have h2 : (2 ^ 64 - 1) * 2 ^ 64 = 2 ^ 64 * 2 ^ 64 - 2 ^ 64 := by
        rw [Nat.sub_mul]; ring_nf
      have hn2_le_n3 : 2 ^ 64 * 2 ^ 64 ≤ 2 ^ 64 * 2 ^ 64 * 2 ^ 64 := by nlinarith
      have hn_le_n2 : (2 : Nat) ^ 64 ≤ 2 ^ 64 * 2 ^ 64 := by nlinarith
      omega
    omega
  -- The cHi · 2^128 is either 0 or 2^192.
  have hCHi_cases : cHi * 2 ^ 128 = 0 ∨ cHi * 2 ^ 128 = 2 ^ 192 := by
    by_cases hCC : bhi_hi + midCarry_v.toNat < 2 ^ 64
    · left
      have : cHi = 0 := by rw [hcHi_def, if_pos hCC]
      rw [this]; ring
    · right
      have : cHi = 2 ^ 64 := by rw [hcHi_def, if_neg hCC]
      rw [this, h192]; ring
  rcases hCHi_cases with hCHi0 | hCHi192
  · -- No top carry: rHi_top.toNat · 2^128 + midSum_v · 2^64 + blo_lo = bhi_hi · 2^128 + (bhi_lo + blo_hi) · 2^64 + blo_lo
    -- The product is < 2^192, so the mod is trivial.
    have hEq : rHi_top.toNat * 2 ^ 128 + midSum_v.toNat * 2 ^ 64 + blo_lo
                = bhi_hi * 2 ^ 128 + (bhi_lo + blo_hi) * 2 ^ 64 + blo_lo := by
      have := hLHS_eq
      rw [hCHi0] at this; omega
    rw [hEq]
    exact (Nat.mod_eq_of_lt (by omega)).symm
  · -- Top carry of 2^192.  This means bhi_hi + midCarry ≥ 2^64.  But bhi_hi < 2^64 and
    -- midCarry ≤ 1, so this requires bhi_hi = 2^64 - 1 ∧ midCarry = 1.
    have hTotal' : bhi_hi * 2 ^ 128 + (bhi_lo + blo_hi) * 2 ^ 64 + blo_lo
                    = (rHi_top.toNat * 2 ^ 128 + midSum_v.toNat * 2 ^ 64 + blo_lo) + 1 * 2 ^ 192 := by
      have := hLHS_eq
      rw [hCHi192] at this
      omega
    rw [hTotal', Nat.add_mul_mod_self_right]
    exact (Nat.mod_eq_of_lt hLHS_lt).symm

/-! ## Bit-shift kernel: `L = a · 2^s` as a 192-bit triple

`cmpScaledMixed_fast2` computes `L = a · 2^{q+h}` directly as a triple
of UInt64s via case analysis on `s = q + h`.  The branches cover the
ranges `[64, 128)` and `[128, 192)`; the inputs Schubfach actually
produces always lie in those ranges (in fact `s ∈ [124, 134]` for
binary64 inputs).  This section proves the kernel computes the
correct triple under those assumptions.

The key Nat fact: when `a.toNat < 2^60`:
  - For `s ∈ [64, 128)`: writing `s64 = s - 64 ∈ [0, 64)`:
      `a · 2^s = a · 2^{s64} · 2^64`
              = `(a >>> (64 - s64)) · 2^128 + (a <<< s64) · 2^64`
      when `s64 > 0`, and `a · 2^64` when `s64 = 0`.
  - For `s ∈ [128, 192)`: writing `s64 = s - 128 ∈ [0, 64)`:
      `a · 2^s = a · 2^{s64} · 2^128`
              = `(a <<< s64) · 2^128`
      when `s64 < 4` (since `a < 2^60` forces no overflow at 64), and
      since the function uses this branch up to `s = 191`, requiring
      `a · 2^{s64} < 2^64` which means `s64 < 4`.

Schubfach's `s` is always `< 60 + (60 + 4)` here, but in practice for
binary64 the range `q + h ∈ [124, 134]` so `s64 - 128 ≤ 6`.  A
tighter bound is fine for our purposes.
-/

/-- Variant of `UInt64.toNat_shiftLeft` specialised to the shift amount
    being a small Nat (specifically `0 < s < 64`). -/
theorem UInt64_shl_toNat_lt (a : UInt64) (s : Nat)
    (hs : s < 64) :
    (a <<< (UInt64.ofNat s)).toNat = (a.toNat * 2 ^ s) % 2 ^ 64 := by
  rw [UInt64.toNat_shiftLeft]
  have h_size : UInt64.size = 2 ^ 64 := rfl
  have hofNat : (UInt64.ofNat s).toNat = s := by
    apply UInt64.toNat_ofNat_of_lt'
    rw [h_size]
    have h64lt : (64 : Nat) < 2 ^ 64 := by decide
    omega
  rw [hofNat]
  have hsMod : s % 64 = s := Nat.mod_eq_of_lt hs
  rw [hsMod]
  rw [Nat.shiftLeft_eq]

/-- Variant of `UInt64.toNat_shiftRight` specialised to a small Nat shift. -/
theorem UInt64_shr_toNat_lt (a : UInt64) (s : Nat)
    (hs : s < 64) :
    (a >>> (UInt64.ofNat s)).toNat = a.toNat / 2 ^ s := by
  rw [UInt64.toNat_shiftRight]
  have h_size : UInt64.size = 2 ^ 64 := rfl
  have hofNat : (UInt64.ofNat s).toNat = s := by
    apply UInt64.toNat_ofNat_of_lt'
    rw [h_size]
    have h64lt : (64 : Nat) < 2 ^ 64 := by decide
    omega
  rw [hofNat]
  have hsMod : s % 64 = s := Nat.mod_eq_of_lt hs
  rw [hsMod, Nat.shiftRight_eq_div_pow]

/-- For `s ∈ [64, 128)`, `s64 := s - 64`, and `a < 2^64`, the triple
    constructed by the `else` branch of the second `if` in
    `cmpScaledMixed_fast2`'s shift kernel computes `a · 2^s`.

    Statement chosen to match the actual Lean expression in the function.

    Case `s64 = 0` separately: triple is `(0, a, 0)`, value `a · 2^64 = a · 2^s`. -/
theorem shift_kernel_mid_eq (aU : UInt64) (s64 : Nat)
    (hLt : s64 < 64) :
    let triple : UInt64 × UInt64 × UInt64 :=
      if s64 = 0 then (0, aU, 0)
      else (aU >>> (UInt64.ofNat (64 - s64)), aU <<< (UInt64.ofNat s64), 0)
    triple192Nat triple.1 triple.2.1 triple.2.2
      = (aU.toNat * 2 ^ (s64 + 64)) % 2 ^ 192 := by
  have h2_64_pos : (0 : Nat) < 2 ^ 64 := Nat.two_pow_pos _
  have h2_128_pos : (0 : Nat) < 2 ^ 128 := Nat.two_pow_pos _
  have h2_192_pos : (0 : Nat) < 2 ^ 192 := Nat.two_pow_pos _
  have ha : aU.toNat < 2 ^ 64 := aU.toNat_lt
  have h128 : (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 := pow2_128_split
  have h192 : (2 : Nat) ^ 192 = 2 ^ 64 * 2 ^ 64 * 2 ^ 64 := pow2_192_split
  by_cases hs0 : s64 = 0
  · -- s64 = 0 branch.
    simp only [hs0, if_pos]
    unfold triple192Nat
    show (0 : UInt64).toNat * 2 ^ 128 + aU.toNat * 2 ^ 64 + (0 : UInt64).toNat
          = (aU.toNat * 2 ^ (0 + 64)) % 2 ^ 192
    simp only [UInt64.toNat_ofNat, Nat.zero_mod]
    -- Goal: 0 * 2^128 + a · 2^64 + 0 = (a · 2^64) % 2^192
    rw [Nat.zero_mul, Nat.add_zero, Nat.zero_add, Nat.zero_add]
    have hlt : aU.toNat * 2 ^ 64 < 2 ^ 192 := by
      have h1 : aU.toNat * 2 ^ 64 ≤ (2 ^ 64 - 1) * 2 ^ 64 := by
        apply Nat.mul_le_mul_right; omega
      have hKey : (2 ^ 64 - 1) * 2 ^ 64 < 2 ^ 192 := by
        rw [h192]
        have h2 : (2 ^ 64 - 1) * 2 ^ 64 = 2 ^ 64 * 2 ^ 64 - 2 ^ 64 := by
          rw [Nat.sub_mul]; ring_nf
        rw [h2]
        have h64_pos : (0 : Nat) < 2 ^ 64 := Nat.two_pow_pos _
        have hn2_le_n3 : 2 ^ 64 * 2 ^ 64 ≤ 2 ^ 64 * 2 ^ 64 * 2 ^ 64 := by nlinarith
        have h_step1 : 2 ^ 64 * 2 ^ 64 - 2 ^ 64 < 2 ^ 64 * 2 ^ 64 := by omega
        omega
      omega
    exact (Nat.mod_eq_of_lt hlt).symm
  · -- s64 ≠ 0; 0 < s64 < 64.
    have hs0Pos : 0 < s64 := Nat.pos_of_ne_zero hs0
    have hLt' : 64 - s64 < 64 := by omega
    have hLt2 : 64 - s64 > 0 := by omega
    simp only [hs0, if_false]
    unfold triple192Nat
    show (aU >>> (UInt64.ofNat (64 - s64))).toNat * 2 ^ 128
          + (aU <<< (UInt64.ofNat s64)).toNat * 2 ^ 64
          + (0 : UInt64).toNat
          = (aU.toNat * 2 ^ (s64 + 64)) % 2 ^ 192
    -- Reduce shifts.
    rw [UInt64_shr_toNat_lt aU (64 - s64) hLt']
    rw [UInt64_shl_toNat_lt aU s64 hLt]
    -- Goal: a/2^(64-s64) · 2^128 + (a · 2^s64 % 2^64) · 2^64 + 0
    --     = (a · 2^(s64+64)) % 2^192
    simp only [UInt64.toNat_ofNat, Nat.zero_mod]
    rw [Nat.add_zero]
    -- Goal: (a / 2^(64-s64)) · 2^128 + ((a · 2^s64) % 2^64) · 2^64
    --     = (a · 2^(s64+64)) % 2^192
    -- a · 2^(s64+64) = (a · 2^s64) · 2^64
    --                = (((a · 2^s64) / 2^64) · 2^64 + (a · 2^s64) % 2^64) · 2^64
    --                = ((a · 2^s64) / 2^64) · 2^128 + ((a · 2^s64) % 2^64) · 2^64
    -- And (a · 2^s64) / 2^64 = a / 2^(64-s64) (key identity).
    have hpow_split : 2 ^ 64 = 2 ^ (64 - s64) * 2 ^ s64 := by
      rw [← Nat.pow_add]
      have : (64 - s64) + s64 = 64 := by omega
      rw [this]
    have hkey : (aU.toNat * 2 ^ s64) / 2 ^ 64 = aU.toNat / 2 ^ (64 - s64) := by
      rw [hpow_split]
      rw [show 2 ^ (64 - s64) * 2 ^ s64 = 2 ^ s64 * 2 ^ (64 - s64) from by ring]
      rw [show aU.toNat * 2 ^ s64 = 2 ^ s64 * aU.toNat from by ring]
      rw [Nat.mul_div_mul_left _ _ (Nat.two_pow_pos s64)]
    have h_pow : 2 ^ (s64 + 64) = 2 ^ s64 * 2 ^ 64 := by
      rw [Nat.pow_add]
    have habs : aU.toNat * 2 ^ (s64 + 64)
                  = (aU.toNat * 2 ^ s64) * 2 ^ 64 := by
      rw [h_pow]; ring
    have h_div_mod : aU.toNat * 2 ^ s64 = ((aU.toNat * 2 ^ s64) / 2 ^ 64) * 2 ^ 64
                                          + (aU.toNat * 2 ^ s64) % 2 ^ 64 := by
      have := Nat.div_add_mod (aU.toNat * 2 ^ s64) (2 ^ 64); omega
    -- Rewrite RHS using these.
    have hRHS : aU.toNat * 2 ^ (s64 + 64)
                  = (aU.toNat / 2 ^ (64 - s64)) * 2 ^ 128
                    + ((aU.toNat * 2 ^ s64) % 2 ^ 64) * 2 ^ 64 := by
      rw [habs]
      have hG : aU.toNat * 2 ^ s64
                  = (aU.toNat / 2 ^ (64 - s64)) * 2 ^ 64
                    + (aU.toNat * 2 ^ s64) % 2 ^ 64 := by
        rw [show (aU.toNat / 2 ^ (64 - s64)) * 2 ^ 64
              = ((aU.toNat * 2 ^ s64) / 2 ^ 64) * 2 ^ 64 from by rw [hkey]]
        exact h_div_mod
      calc aU.toNat * 2 ^ s64 * 2 ^ 64
          = ((aU.toNat / 2 ^ (64 - s64)) * 2 ^ 64
            + (aU.toNat * 2 ^ s64) % 2 ^ 64) * 2 ^ 64 := by rw [← hG]
        _ = (aU.toNat / 2 ^ (64 - s64)) * 2 ^ 128
            + ((aU.toNat * 2 ^ s64) % 2 ^ 64) * 2 ^ 64 := by rw [h128]; ring
    rw [hRHS]
    -- Now show LHS < 2^192, then drop the mod.
    have hLHS_lt :
        (aU.toNat / 2 ^ (64 - s64)) * 2 ^ 128
          + ((aU.toNat * 2 ^ s64) % 2 ^ 64) * 2 ^ 64 < 2 ^ 192 := by
      have h1 : aU.toNat / 2 ^ (64 - s64) < 2 ^ 64 := by
        apply Nat.div_lt_of_lt_mul
        have hp : 2 ^ (64 - s64) ≥ 1 := Nat.one_le_two_pow
        nlinarith [ha, hp]
      have hMod : (aU.toNat * 2 ^ s64) % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ h2_64_pos
      have h_hi_bd : (aU.toNat / 2 ^ (64 - s64)) * 2 ^ 128 ≤ (2 ^ 64 - 1) * 2 ^ 128 := by
        apply Nat.mul_le_mul_right; omega
      have h_mid_bd : ((aU.toNat * 2 ^ s64) % 2 ^ 64) * 2 ^ 64 ≤ (2 ^ 64 - 1) * 2 ^ 64 := by
        apply Nat.mul_le_mul_right; omega
      have hKey : (2 ^ 64 - 1) * 2 ^ 128 + (2 ^ 64 - 1) * 2 ^ 64 < 2 ^ 192 := by
        rw [h128, h192]
        have h1 : (2 ^ 64 - 1) * (2 ^ 64 * 2 ^ 64) = 2 ^ 64 * 2 ^ 64 * 2 ^ 64 - 2 ^ 64 * 2 ^ 64 := by
          rw [Nat.sub_mul]; ring_nf
        have h2 : (2 ^ 64 - 1) * 2 ^ 64 = 2 ^ 64 * 2 ^ 64 - 2 ^ 64 := by
          rw [Nat.sub_mul]; ring_nf
        have h64_pos : 1 ≤ (2 : Nat) ^ 64 := by
          have : (0 : Nat) < 2 ^ 64 := Nat.two_pow_pos _
          omega
        have hn2_le_n3 : 2 ^ 64 * 2 ^ 64 ≤ 2 ^ 64 * 2 ^ 64 * 2 ^ 64 := by nlinarith
        have hn_le_n2 : (2 : Nat) ^ 64 ≤ 2 ^ 64 * 2 ^ 64 := by nlinarith
        omega
      omega
    exact (Nat.mod_eq_of_lt hLHS_lt).symm

/-- For `s ∈ [128, 192)`, `s64 := s - 128`, and `a < 2^(64-s64)`, the
    triple `(a <<< s64, 0, 0)` (or `(a, 0, 0)` for s64 = 0) represents
    `a · 2^s`.

    The precondition `a < 2^(64-s64)` ensures the shift doesn't lose
    information.  In the Schubfach use, `a < 2^60` and `s64 ≤ 6`, so
    `64 - s64 ≥ 58 > 60`, satisfying the bound. -/
theorem shift_kernel_hi_eq (aU : UInt64) (s64 : Nat)
    (hLt : s64 < 64)
    (hABd : aU.toNat < 2 ^ (64 - s64)) :
    let triple : UInt64 × UInt64 × UInt64 :=
      if s64 = 0 then (aU, 0, 0)
      else (aU <<< (UInt64.ofNat s64), 0, 0)
    triple192Nat triple.1 triple.2.1 triple.2.2
      = aU.toNat * 2 ^ (s64 + 128) := by
  have h2_64_pos : (0 : Nat) < 2 ^ 64 := Nat.two_pow_pos _
  have h128 : (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 := pow2_128_split
  by_cases hs0 : s64 = 0
  · subst hs0
    simp only [if_pos]
    unfold triple192Nat
    show aU.toNat * 2 ^ 128 + (0 : UInt64).toNat * 2 ^ 64 + (0 : UInt64).toNat
          = aU.toNat * 2 ^ (0 + 128)
    simp only [UInt64.toNat_ofNat, Nat.zero_mod, Nat.zero_mul, Nat.add_zero,
               Nat.zero_add]
  · simp only [hs0, if_false]
    have hs0Pos : 0 < s64 := Nat.pos_of_ne_zero hs0
    unfold triple192Nat
    show (aU <<< (UInt64.ofNat s64)).toNat * 2 ^ 128
          + (0 : UInt64).toNat * 2 ^ 64
          + (0 : UInt64).toNat
          = aU.toNat * 2 ^ (s64 + 128)
    rw [UInt64_shl_toNat_lt aU s64 hLt]
    simp only [UInt64.toNat_ofNat, Nat.zero_mod, Nat.zero_mul, Nat.add_zero]
    -- Goal: ((a · 2^s64) % 2^64) · 2^128 = a · 2^(s64 + 128)
    have hpow_split : 2 ^ 64 = 2 ^ (64 - s64) * 2 ^ s64 := by
      rw [← Nat.pow_add]
      have : (64 - s64) + s64 = 64 := by omega
      rw [this]
    have h_ash64_lt : aU.toNat * 2 ^ s64 < 2 ^ 64 := by
      calc aU.toNat * 2 ^ s64 < 2 ^ (64 - s64) * 2 ^ s64 :=
              (Nat.mul_lt_mul_right (Nat.two_pow_pos s64)).mpr hABd
        _ = 2 ^ 64 := hpow_split.symm
    have hmod_eq : (aU.toNat * 2 ^ s64) % 2 ^ 64 = aU.toNat * 2 ^ s64 :=
      Nat.mod_eq_of_lt h_ash64_lt
    rw [hmod_eq]
    -- Goal: (a · 2^s64) · 2^128 = a · 2^(s64+128)
    rw [Nat.pow_add]; ring

/-! ## UInt64 sub bridge: `s - 64` equals `UInt64.ofNat (s.toNat - 64)`. -/

/-- If a UInt64 `s` represents a Nat in the range `[lo, 2^64)`, the
    UInt64 subtraction `s - (UInt64.ofNat lo)` represents the Nat
    subtraction. -/
theorem UInt64_sub_toNat_of_ge (s : UInt64) (lo : Nat)
    (hLoLt : lo < 2 ^ 64)
    (hSGe : s.toNat ≥ lo) :
    (s - UInt64.ofNat lo).toNat = s.toNat - lo := by
  rw [UInt64.toNat_sub]
  have hLoUInt : (UInt64.ofNat lo).toNat = lo := by
    apply UInt64.toNat_ofNat_of_lt'
    show lo < UInt64.size
    have : UInt64.size = 2 ^ 64 := rfl
    rw [this]; exact hLoLt
  rw [hLoUInt]
  have hSLt : s.toNat < 2 ^ 64 := s.toNat_lt
  -- Goal: (2^64 - lo + s.toNat) % 2^64 = s.toNat - lo
  have h1 : 2 ^ 64 - lo + s.toNat = (s.toNat - lo) + 1 * 2 ^ 64 := by omega
  rw [h1, Nat.add_mul_mod_self_right]
  exact Nat.mod_eq_of_lt (by omega : s.toNat - lo < 2 ^ 64)

/-! ## Right-shift extraction from a 192-bit triple

`shiftedSig_fast2` extracts `⌊T / 2^s⌋ % 2^64` from its 192-bit
`(rHi, rMid, rLo)` triple via a UInt64-level dispatch on the shift
amount `s`.  These lemmas bridge the UInt64-level output to the Nat
result `T / 2^s`, which is exact (no `% 2^64` truncation) when
`T < 2^(s + 64)` (the shifted value fits in UInt64).

We focus on the kernel's actual range `s ∈ [124, 192)`.  For the case
`s ∈ [128, 192)`, extraction is `rHi >>> (s - 128)`.  For
`s ∈ [124, 128)`, extraction is `(rMid >>> (s - 64)) ||| (rHi <<< (64 - (s - 64)))`,
which represents the sum `(rHi · 2^(128 - s)) + ⌊rMid / 2^(s-64)⌋`
(no truncation when `rHi < 2^(s - 64)`). -/

/-- OR is addition when the lower operand has no bits at and above position
    `k` and the upper operand is shifted left by `k`. -/
private theorem nat_lor_shift_add (a b k : Nat) (ha : a < 2 ^ k) :
    a ||| (b * 2 ^ k) = a + b * 2 ^ k := by
  -- Prove equality via testBit at every position.
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, Nat.testBit_mul_two_pow]
  by_cases hik : i < k
  · -- Below shift point: `b * 2^k` contributes nothing; sum's bit i = a.testBit i.
    have hki_neg : ¬ (k ≤ i) := by omega
    rw [decide_eq_false hki_neg, Bool.false_and, Bool.or_false]
    -- (a + b * 2^k).testBit i = a.testBit i, since b * 2^k is a multiple of 2^(i+1).
    -- Write i = i, b * 2 ^ k = (b * 2^(k - i - 1)) * 2^(i+1).
    rcases Nat.exists_eq_add_of_lt hik with ⟨d, hd⟩
    -- d = k - i - 1, so k = i + d + 1.
    have hb2k_eq : b * 2 ^ k = (b * 2 ^ d) * 2 ^ (i + 1) := by
      rw [hd, show i + d + 1 = (i + 1) + d from by ring, Nat.pow_add]; ring
    rw [hb2k_eq]
    -- (a + c * 2^(i+1)).testBit i = a.testBit i.
    -- Use Nat.testBit_add and a < 2^k ≤ 2^(i+1)... wait, do we have a < 2^(i+1)?
    -- a < 2^k = 2^(i + d + 1) ≥ 2^(i + 1). So a < 2^k doesn't immediately give a < 2^(i+1).
    -- Hmm. Better: use (x + c · 2^(i+1)).testBit i = x.testBit i for any x.
    -- Lemma: Nat.testBit_add_mul_two_pow_of_lt.
    have hLt_succ : i < i + 1 := Nat.lt_succ_self i
    rw [show a + b * 2 ^ d * 2 ^ (i + 1) = a + 2 ^ (i + 1) * (b * 2 ^ d) from by ring]
    -- Use Nat.testBit_add_two_pow_mul_eq or similar — look up the right name.
    -- Try: (a + 2^(i+1) * c).testBit i
    -- We know (a + 2^(i+1) * c) / 2^i = a / 2^i + (2^(i+1) * c) / 2^i = a/2^i + 2 * c. So
    -- testBit i = ((a + 2^(i+1) * c) / 2^i).testBit 0 ... using Nat.testBit_eq_div_mod_two.
    have hkey : (a + 2 ^ (i + 1) * (b * 2 ^ d)) / 2 ^ i % 2 = a / 2 ^ i % 2 := by
      have h_div : (a + 2 ^ (i + 1) * (b * 2 ^ d)) / 2 ^ i
                    = a / 2 ^ i + 2 * (b * 2 ^ d) := by
        have hpow : 2 ^ (i + 1) = 2 * 2 ^ i := by rw [Nat.pow_succ]; ring
        rw [hpow]
        rw [show 2 * 2 ^ i * (b * 2 ^ d) = 2 * (b * 2 ^ d) * 2 ^ i from by ring]
        rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos i)]
      rw [h_div]
      omega
    -- testBit i = (n / 2^i) % 2 = 1.
    rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
    rw [hkey]
  · -- Above shift point: a.testBit i = false (a < 2^k ≤ 2^i).
    push_neg at hik
    have ha_lt_2_i : a < 2 ^ i := Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) hik)
    rw [Nat.testBit_lt_two_pow ha_lt_2_i, decide_eq_true hik, Bool.true_and, Bool.false_or]
    -- (a + b * 2^k).testBit i = b.testBit (i - k).
    -- Write i = k + (i - k); use Nat.testBit_add.
    have hi_eq : i = (i - k) + k := by omega
    have hLHS : (a + b * 2 ^ k).testBit i
                  = ((a + b * 2 ^ k) / 2 ^ k).testBit (i - k) := by
      conv_lhs => rw [hi_eq]
      exact Nat.testBit_add (a + b * 2 ^ k) (i - k) k
    rw [hLHS]
    have hadd_div : (a + b * 2 ^ k) / 2 ^ k = b := by
      rw [show a + b * 2 ^ k = a + 2 ^ k * b from by ring]
      rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos k)]
      rw [Nat.div_eq_of_lt ha]
      simp
    rw [hadd_div]

/-- Hi-branch right-shift: when `s.toNat ∈ [128, 192)`, the kernel
    extracts `rHi >>> (s - 128)`, which equals `T / 2^s.toNat` whenever
    `T = triple192Nat rHi rMid rLo`. -/
theorem shift_kernel_extract_hi (rHi rMid rLo : UInt64) (s : UInt64) (s64 : UInt64)
    (hs_toNat_ge : 128 ≤ s.toNat) (hs_toNat_lt : s.toNat < 192)
    (hs64_def : s64 = s - 128) :
    (rHi >>> s64).toNat = triple192Nat rHi rMid rLo / 2 ^ s.toNat := by
  have hs64_toNat : s64.toNat = s.toNat - 128 := by
    rw [hs64_def]; apply UInt64_sub_toNat_of_ge s 128 (by decide) hs_toNat_ge
  have hs64_lt_64 : s64.toNat < 64 := by omega
  -- Convert UInt64 shift to Nat division.
  have hs64_inj : s64 = UInt64.ofNat s64.toNat := by
    rw [← UInt64.toNat_inj]
    rw [show (UInt64.ofNat s64.toNat).toNat = s64.toNat by
      apply UInt64.toNat_ofNat_of_lt'
      show s64.toNat < UInt64.size
      have h264 : UInt64.size = 2 ^ 64 := rfl
      rw [h264]; omega]
  rw [hs64_inj]
  rw [UInt64_shr_toNat_lt rHi s64.toNat hs64_lt_64]
  -- Goal: rHi.toNat / 2^s64.toNat = triple192Nat rHi rMid rLo / 2^s.toNat
  unfold triple192Nat
  have hrMid_lt : rMid.toNat < 2 ^ 64 := rMid.toNat_lt
  have hrLo_lt : rLo.toNat < 2 ^ 64 := rLo.toNat_lt
  have hLower_lt : rMid.toNat * 2 ^ 64 + rLo.toNat < 2 ^ 128 := by
    have h128 : (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 := pow2_128_split
    rw [h128]
    have h1 : rMid.toNat * 2 ^ 64 ≤ (2 ^ 64 - 1) * 2 ^ 64 := by
      apply Nat.mul_le_mul_right; omega
    omega
  -- 2^s = 2^s64 · 2^128 (since s = s64 + 128).
  have hpow : 2 ^ s.toNat = 2 ^ s64.toNat * 2 ^ 128 := by
    have : s64.toNat + 128 = s.toNat := by omega
    rw [← this, Nat.pow_add]
  rw [hpow]
  -- Goal: rHi.toNat / 2^s64.toNat = (rHi · 2^128 + rMid · 2^64 + rLo) / (2^s64 · 2^128)
  -- Use Nat.div_div_eq_div_mul backwards (a / (b · c) = a / b / c).
  rw [show (2 ^ s64.toNat * 2 ^ 128 : Nat) = 2 ^ 128 * 2 ^ s64.toNat by ring]
  rw [← Nat.div_div_eq_div_mul]
  -- Goal: rHi.toNat / 2^s64.toNat = ((rHi · 2^128 + rMid · 2^64 + rLo) / 2^128) / 2^s64
  rw [show rHi.toNat * 2 ^ 128 + rMid.toNat * 2 ^ 64 + rLo.toNat
        = (rMid.toNat * 2 ^ 64 + rLo.toNat) + 2 ^ 128 * rHi.toNat by ring]
  rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos 128)]
  rw [Nat.div_eq_of_lt hLower_lt]
  simp

/-- Mid-branch right-shift: when `s.toNat ∈ [64, 128)`, `s64 = s - 64 ≠ 0`,
    and the upper `rHi < 2^s64.toNat`, the kernel's
    `(rMid >>> s64) ||| (rHi <<< (64 - s64))` represents `T / 2^s.toNat`. -/
theorem shift_kernel_extract_mid (rHi rMid rLo : UInt64) (s : UInt64) (s64 : UInt64)
    (hs_toNat_ge : 64 ≤ s.toNat) (hs_toNat_lt : s.toNat < 128)
    (hs64_def : s64 = s - 64) (hs64_nz : s64 ≠ 0)
    (hrHi_lt : rHi.toNat < 2 ^ s64.toNat) :
    ((rMid >>> s64) ||| (rHi <<< (64 - s64))).toNat
      = triple192Nat rHi rMid rLo / 2 ^ s.toNat := by
  have hs64_toNat : s64.toNat = s.toNat - 64 := by
    rw [hs64_def]; apply UInt64_sub_toNat_of_ge s 64 (by decide) hs_toNat_ge
  have hs64_lt_64 : s64.toNat < 64 := by omega
  have hs64_pos : 0 < s64.toNat := by
    have h_ne : s64.toNat ≠ 0 := by
      intro hz
      apply hs64_nz
      have hbk : s64 = UInt64.ofNat s64.toNat := by
        rw [← UInt64.toNat_inj]
        rw [show (UInt64.ofNat s64.toNat).toNat = s64.toNat by
          apply UInt64.toNat_ofNat_of_lt'
          show s64.toNat < UInt64.size
          have h264 : UInt64.size = 2 ^ 64 := rfl
          rw [h264]; omega]
      rw [hbk, hz]; rfl
    omega
  -- Convert UInt64 ops to Nat ops.
  have hs64_inj : s64 = UInt64.ofNat s64.toNat := by
    rw [← UInt64.toNat_inj]
    rw [show (UInt64.ofNat s64.toNat).toNat = s64.toNat by
      apply UInt64.toNat_ofNat_of_lt'
      show s64.toNat < UInt64.size
      have h264 : UInt64.size = 2 ^ 64 := rfl
      rw [h264]; omega]
  have h64_s64_toNat : (64 - s64 : UInt64).toNat = 64 - s64.toNat := by
    have h64_eq : (64 : UInt64) = UInt64.ofNat 64 := rfl
    conv_lhs => rw [h64_eq, hs64_inj]
    apply UInt64_sub_toNat_of_ge (UInt64.ofNat 64) s64.toNat (by omega)
    rw [show (UInt64.ofNat 64 : UInt64).toNat = 64 from by decide]
    omega
  have h_64_s64_ofNat : (64 - s64 : UInt64) = UInt64.ofNat (64 - s64.toNat) := by
    rw [← UInt64.toNat_inj]
    rw [show (UInt64.ofNat (64 - s64.toNat) : UInt64).toNat = 64 - s64.toNat by
      apply UInt64.toNat_ofNat_of_lt'
      show 64 - s64.toNat < UInt64.size
      have h264 : UInt64.size = 2 ^ 64 := rfl
      rw [h264]; omega]
    exact h64_s64_toNat
  rw [h_64_s64_ofNat, hs64_inj]
  rw [UInt64.toNat_or]
  rw [UInt64_shr_toNat_lt rMid s64.toNat hs64_lt_64]
  -- Normalize (UInt64.ofNat s64.toNat).toNat = s64.toNat.
  have hUInt_id : (UInt64.ofNat s64.toNat).toNat = s64.toNat := by
    apply UInt64.toNat_ofNat_of_lt'
    show s64.toNat < UInt64.size
    have h264 : UInt64.size = 2 ^ 64 := rfl
    rw [h264]; omega
  rw [hUInt_id]
  -- rHi <<< (64 - s64) = (rHi · 2^(64-s64)) mod 2^64; with rHi < 2^s64, mod is trivial.
  have h64_ms64_lt : 64 - s64.toNat < 64 := by omega
  rw [UInt64_shl_toNat_lt rHi (64 - s64.toNat) h64_ms64_lt]
  -- Simplify the shifted hi: rHi · 2^(64-s64) < 2^64.
  have hrHi_shl_lt : rHi.toNat * 2 ^ (64 - s64.toNat) < 2 ^ 64 := by
    have h1 : rHi.toNat * 2 ^ (64 - s64.toNat) < 2 ^ s64.toNat * 2 ^ (64 - s64.toNat) :=
      Nat.mul_lt_mul_of_pos_right hrHi_lt (Nat.two_pow_pos _)
    have h2 : 2 ^ s64.toNat * 2 ^ (64 - s64.toNat) = 2 ^ 64 := by
      rw [← Nat.pow_add]
      have : s64.toNat + (64 - s64.toNat) = 64 := by omega
      rw [this]
    rw [h2] at h1
    exact h1
  rw [Nat.mod_eq_of_lt hrHi_shl_lt]
  -- Now: rMid.toNat / 2^s64.toNat ||| rHi.toNat * 2^(64 - s64.toNat) = ?
  -- Apply nat_lor_shift_add: a = rMid/2^s64, b = rHi, k = 64 - s64; need a < 2^k.
  have hrMid_div_lt : rMid.toNat / 2 ^ s64.toNat < 2 ^ (64 - s64.toNat) := by
    apply Nat.div_lt_of_lt_mul
    rw [show (2 : Nat) ^ s64.toNat * 2 ^ (64 - s64.toNat) = 2 ^ 64 by
      rw [← Nat.pow_add]
      have : s64.toNat + (64 - s64.toNat) = 64 := by omega
      rw [this]]
    exact rMid.toNat_lt
  rw [nat_lor_shift_add (rMid.toNat / 2 ^ s64.toNat) rHi.toNat (64 - s64.toNat) hrMid_div_lt]
  -- Goal: rMid/2^s64 + rHi · 2^(64-s64) = T / 2^s
  -- T / 2^s = T / 2^(s64+64) = T / 2^64 / 2^s64 = (rHi · 2^64 + rMid) / 2^s64.
  unfold triple192Nat
  have hpow : 2 ^ s.toNat = 2 ^ s64.toNat * 2 ^ 64 := by
    have : s64.toNat + 64 = s.toNat := by omega
    rw [← this, Nat.pow_add]
  rw [hpow]
  have hrMid_lt : rMid.toNat < 2 ^ 64 := rMid.toNat_lt
  have hrLo_lt : rLo.toNat < 2 ^ 64 := rLo.toNat_lt
  have h128 : (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 := pow2_128_split
  -- Rewrite T / (2^s64 · 2^64) = T / 2^64 / 2^s64.
  rw [show (2 ^ s64.toNat * 2 ^ 64 : Nat) = 2 ^ 64 * 2 ^ s64.toNat by ring]
  rw [← Nat.div_div_eq_div_mul]
  -- T / 2^64 = rHi · 2^64 + rMid (since rLo < 2^64).
  have hT_div_64 : (rHi.toNat * 2 ^ 128 + rMid.toNat * 2 ^ 64 + rLo.toNat) / 2 ^ 64
                    = rHi.toNat * 2 ^ 64 + rMid.toNat := by
    rw [show rHi.toNat * 2 ^ 128 + rMid.toNat * 2 ^ 64 + rLo.toNat
          = rLo.toNat + 2 ^ 64 * (rHi.toNat * 2 ^ 64 + rMid.toNat) from by
            rw [h128]; ring]
    rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos 64)]
    rw [Nat.div_eq_of_lt hrLo_lt]; simp
  rw [hT_div_64]
  -- Goal: rMid/2^s64 + rHi · 2^(64-s64) = (rHi · 2^64 + rMid) / 2^s64.
  -- (rHi · 2^64 + rMid) / 2^s64 = rHi · 2^64 / 2^s64 + rMid / 2^s64
  -- since 2^s64 | rHi · 2^64 (as s64 ≤ 64).
  have h2_64_split : 2 ^ 64 = 2 ^ s64.toNat * 2 ^ (64 - s64.toNat) := by
    rw [← Nat.pow_add]
    have : s64.toNat + (64 - s64.toNat) = 64 := by omega
    rw [this]
  have hHi_div : rHi.toNat * 2 ^ 64 / 2 ^ s64.toNat = rHi.toNat * 2 ^ (64 - s64.toNat) := by
    rw [h2_64_split]
    rw [show rHi.toNat * (2 ^ s64.toNat * 2 ^ (64 - s64.toNat))
          = (rHi.toNat * 2 ^ (64 - s64.toNat)) * 2 ^ s64.toNat from by ring]
    rw [Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
  have hSplit : (rHi.toNat * 2 ^ 64 + rMid.toNat) / 2 ^ s64.toNat
                  = rHi.toNat * 2 ^ (64 - s64.toNat) + rMid.toNat / 2 ^ s64.toNat := by
    rw [show rHi.toNat * 2 ^ 64 + rMid.toNat
          = rMid.toNat + 2 ^ s64.toNat * (rHi.toNat * 2 ^ (64 - s64.toNat)) from by
            rw [h2_64_split]; ring]
    rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos s64.toNat)]
    omega
  rw [hSplit]
  omega

end Srtfp.Schubfach

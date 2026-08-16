/- Correctness of `shortestUnsigned` shorter-form selection (M3.8.6).

   The Schubfach printer's `shortestUnsigned m q` returns a pair
   `(sig, exp)` that is guaranteed to lie inside the rounding interval
   `R_v` for `v = m · 2^q`. The two early-return branches (the
   "shorter form" `(s/10, k+1)` or `(s/10 + 1, k+1)`) are correct
   tautologically — they are taken precisely when `inRoundingInterval`
   says they are valid. The fallback branch returns
   `(pickNearer s k m q, k)`, which by M3.8.5's `pickNearer_mem_rv` is
   correct provided that *at least one* of `(s, k)` and `(s+1, k)` is
   in `R_v`.

   The crucial obligation is therefore **Schubfach R11**:

       At least one of `s · 10^k` and `(s+1) · 10^k` lies in `R_v`,
       where `s = shiftedSig m q k` and `k = kOfMQ m q`.

   This file proves R11 and then bundles everything into
   `shortestUnsigned_mem_rv`.

   ## R11 proof sketch

   Let `P = twoPosPow q · tenNegPow k`, `Q = tenPosPow k · twoNegPow q`.
   In cleared-denominator form:
     * `V := 4m · P` represents `4 · v = 4 · m · 2^q`.
     * `U := 4s · Q` represents `4 · u = 4 · s · 10^k`.
     * `W := 4(s+1) · Q` represents `4 · w = 4 · (s+1) · 10^k`.
     * `VR := (4m+2) · P` represents `4 · vR = (4m+2) · 2^q`.
     * `VL := (4m - 1 or 4m - 2) · P` represents `4 · vL`.

   From `shiftedSig_correct` (×4): `U ≤ V < W`.

   From the structure of R_v: `VL < V < VR` (strict numerator order at
   shared scale).

   From `kOfMQ_correct` (the regular case): `10^k ≤ 2^q`, i.e. `Q ≤ P`,
   so `W - U = 4Q ≤ 4P = VR - VL`.

   From `kOfMQ_correct` (the irregular case): `4 · 10^k ≤ 3 · 2^q`,
   i.e. `4Q ≤ 3P = VR - VL`. So again `W - U = 4Q ≤ VR - VL`.

   For `u = s · 10^k` to be in `R_v`:
     * left: `VL < U  ∨  (VL = U ∧ m even)`,
     * right: `U < VR  ∨  (U = VR ∧ m even)`.

   We always have `U ≤ V < VR`, so the right side of `u` is strict;
   only the left side can fail.

   For `w = (s+1) · 10^k` to be in `R_v`:
     * left: `VL < W  ∨  (VL = W ∧ m even)`,
     * right: `W < VR  ∨  (W = VR ∧ m even)`.

   We always have `VL < V < W`, so the left side of `w` is strict;
   only the right side can fail.

   So u fails iff `U ≤ VL ∧ ¬(U = VL ∧ cEven)`, and w fails iff
   `W ≥ VR ∧ ¬(W = VR ∧ cEven)`. If *both* fail, then
   `U ≤ VL ∧ W ≥ VR`, so `W - U ≥ VR - VL`. Combined with the width
   inequality `W - U ≤ VR - VL`, we get equality. So `U = VL ∧
   W = VR ∧ ¬cEven` (otherwise one of the two would have passed via
   the cEven branch).

   Now equality `W - U = VR - VL` together with the width formulas
   `W - U = 4Q` and `VR - VL = 4P` (regular) or `3P` (irregular) gives:

     * Regular: `4Q = 4P` ⟹ `Q = P` ⟹ `10^k = 2^q` (after clearing).
       The only solution over `ℤ` is `k = q = 0`. But then `s = m`
       (`shiftedSig`'s exact form), so `U = 4s = 4m = V` and
       `VL = 4m - 2`; `U = VL` becomes `4m = 4m - 2`, contradiction.

     * Irregular: `4Q = 3P` ⟹ `4 · 10^k = 3 · 2^q` (after clearing).
       LHS has no factor of 3, RHS does, contradiction.

   So both u and w cannot simultaneously fail, completing R11.

   The only axioms used are `propext, Quot.sound, Classical.choice`. -/

import Srtfp.Proofs.Schubfach.PickNearer
import Srtfp.Proofs.Schubfach.ShiftedSig
import Srtfp.Proofs.Schubfach.K

namespace Srtfp.Schubfach

open Srtfp.Schubfach.RoundingInterval
open Srtfp.Schubfach.Midpoint

/-! ## `inRoundingInterval` reified as Int inequalities

The Boolean `inRoundingInterval s k m q irreg` is a conjunction of
two `cmpScaledMixed` clauses. We translate it once into integer
inequalities on the cleared-denominator forms so all subsequent
reasoning stays in `Int`. -/

/-- Cleared `4 · v`. -/
@[reducible] def fourV (m : Nat) (q k : Int) : Int :=
  cmpScaledMixed.lhs (4 * (m : Int)) q k

/-- Cleared `4 · u` for `u = s · 10^k`. -/
@[reducible] def fourU (s : Nat) (q k : Int) : Int :=
  cmpScaledMixed.rhs (4 * (s : Int)) q k

/-- Cleared `4 · w` where `w = (s+1) · 10^k`. -/
@[reducible] def fourW (s : Nat) (q k : Int) : Int :=
  cmpScaledMixed.rhs (4 * ((s : Int) + 1)) q k

/-- Cleared `4 · v_R = (4m + 2) · 2^q`. -/
@[reducible] def fourVR (m : Nat) (q k : Int) : Int :=
  cmpScaledMixed.lhs (4 * (m : Int) + 2) q k

/-- Cleared `4 · v_L` (regular: `(4m-2) · 2^q`; irregular: `(4m-1) · 2^q`). -/
@[reducible] def fourVL (m : Nat) (q k : Int) (irreg : Bool) : Int :=
  cmpScaledMixed.lhs (if irreg then 4 * (m : Int) - 1 else 4 * (m : Int) - 2) q k

/-! ## `inRoundingInterval` characterisation -/

/-- Reified form: `inRoundingInterval s k m q irreg` is true iff the
left-side check and the right-side check both pass, in cleared form. -/
theorem inRoundingInterval_iff (s : Nat) (k : Int) (m : Nat) (q : Int) (irreg : Bool) :
    inRoundingInterval s k m q irreg = true ↔
      (fourVL m q k irreg < fourU s q k ∨
        (fourVL m q k irreg = fourU s q k ∧ m % 2 = 0)) ∧
      (fourU s q k < fourVR m q k ∨
        (fourU s q k = fourVR m q k ∧ m % 2 = 0)) := by
  unfold inRoundingInterval
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
             Bool.and_eq_true, decide_eq_true_eq]
  -- Unfold the two cmp calls in lhs/rhs form.
  have hL := cmpScaledMixed_lt_iff
              (if irreg then 4 * (m : Int) - 1 else 4 * (m : Int) - 2) q (4 * (s : Int)) k
  have hL0 := cmpScaledMixed_eq_zero_iff
              (if irreg then 4 * (m : Int) - 1 else 4 * (m : Int) - 2) q (4 * (s : Int)) k
  have hR := cmpScaledMixed_gt_iff
              (4 * (m : Int) + 2) q (4 * (s : Int)) k
  have hR0 := cmpScaledMixed_eq_zero_iff
              (4 * (m : Int) + 2) q (4 * (s : Int)) k
  -- Push both cmp forms into their lhs/rhs forms.
  constructor
  · intro ⟨hleft, hright⟩
    refine ⟨?_, ?_⟩
    · rcases hleft with hlt | ⟨heq, heven⟩
      · left
        unfold fourVL fourU
        exact hL.mp hlt
      · right
        refine ⟨?_, heven⟩
        unfold fourVL fourU
        exact hL0.mp heq
    · rcases hright with hgt | ⟨heq, heven⟩
      · left
        unfold fourU fourVR
        have := hR.mp hgt
        omega
      · right
        refine ⟨?_, heven⟩
        unfold fourU fourVR
        have := hR0.mp heq
        omega
  · intro ⟨hleft, hright⟩
    refine ⟨?_, ?_⟩
    · rcases hleft with hlt | ⟨heq, heven⟩
      · left
        apply hL.mpr
        unfold fourVL fourU at hlt
        exact hlt
      · right
        refine ⟨?_, heven⟩
        apply hL0.mpr
        unfold fourVL fourU at heq
        exact heq
    · rcases hright with hgt | ⟨heq, heven⟩
      · left
        apply hR.mpr
        unfold fourU fourVR at hgt
        omega
      · right
        refine ⟨?_, heven⟩
        apply hR0.mpr
        unfold fourU fourVR at heq
        omega

/-! ## Basic relations between cleared forms

The `fourV`/`fourU`/`fourW`/`fourVL`/`fourVR` quantities are all
integers at a single common scale (`twoPosPow q · tenNegPow k` and
`twoNegPow q · tenPosPow k` cleared). They satisfy several structural
identities and inequalities. -/

/-- `fourV = (4m) · twoPosPow q · tenNegPow k`. -/
theorem fourV_eq (m : Nat) (q k : Int) :
    fourV m q k = (4 * (m : Int)) * (twoPosPow q : Int) * (tenNegPow k : Int) := by
  unfold fourV cmpScaledMixed.lhs twoPosPow tenNegPow
  rfl

/-- `fourU = (4s) · tenPosPow k · twoNegPow q`. -/
theorem fourU_eq (s : Nat) (q k : Int) :
    fourU s q k = (4 * (s : Int)) * (tenPosPow k : Int) * (twoNegPow q : Int) := by
  unfold fourU cmpScaledMixed.rhs tenPosPow twoNegPow
  rfl

/-- `fourW = 4(s+1) · tenPosPow k · twoNegPow q`. -/
theorem fourW_eq (s : Nat) (q k : Int) :
    fourW s q k = (4 * ((s : Int) + 1)) * (tenPosPow k : Int) * (twoNegPow q : Int) := by
  unfold fourW cmpScaledMixed.rhs tenPosPow twoNegPow
  rfl

/-- `fourVR = (4m+2) · twoPosPow q · tenNegPow k`. -/
theorem fourVR_eq (m : Nat) (q k : Int) :
    fourVR m q k = (4 * (m : Int) + 2) * (twoPosPow q : Int) * (tenNegPow k : Int) := by
  unfold fourVR cmpScaledMixed.lhs twoPosPow tenNegPow
  rfl

/-- `fourVL` in regular case: `(4m - 2) · twoPosPow q · tenNegPow k`. -/
theorem fourVL_eq_regular (m : Nat) (q k : Int) (h_reg : ¬ (isIrregular m q = true)) :
    fourVL m q k (isIrregular m q)
      = (4 * (m : Int) - 2) * (twoPosPow q : Int) * (tenNegPow k : Int) := by
  unfold fourVL cmpScaledMixed.lhs twoPosPow tenNegPow
  have hreg : isIrregular m q = false := Bool.eq_false_iff.mpr h_reg
  rw [hreg]
  simp

/-- `fourVL` in irregular case: `(4m - 1) · twoPosPow q · tenNegPow k`. -/
theorem fourVL_eq_irregular (m : Nat) (q k : Int) (h_irreg : isIrregular m q = true) :
    fourVL m q k (isIrregular m q)
      = (4 * (m : Int) - 1) * (twoPosPow q : Int) * (tenNegPow k : Int) := by
  unfold fourVL cmpScaledMixed.lhs twoPosPow tenNegPow
  rw [h_irreg]
  simp

/-- Positivity of `twoPosPow q * tenNegPow k` as an Int. -/
theorem twoPos_tenNeg_pos_Int (q k : Int) :
    (0 : Int) < (twoPosPow q : Int) * (tenNegPow k : Int) := by
  unfold twoPosPow tenNegPow
  apply Int.mul_pos
  · exact_mod_cast Nat.pow_pos (a := 2) (by decide)
  · exact_mod_cast Nat.pow_pos (a := 10) (by decide)

/-- Positivity of `tenPosPow k * twoNegPow q` as an Int. -/
theorem tenPos_twoNeg_pos_Int (q k : Int) :
    (0 : Int) < (tenPosPow k : Int) * (twoNegPow q : Int) := by
  unfold tenPosPow twoNegPow
  apply Int.mul_pos
  · exact_mod_cast Nat.pow_pos (a := 10) (by decide)
  · exact_mod_cast Nat.pow_pos (a := 2) (by decide)

/-- Helper: `a * c < b * c` given `a < b` and `0 < c`. -/
private theorem mul_lt_mul_right_of_pos {a b c : Int} (h : a < b) (hc : 0 < c) :
    a * c < b * c := Int.mul_lt_mul_of_pos_right h hc

/-- Helper: `(x*y)*z = x*(y*z)`. -/
private theorem mul_assoc3 (x y z : Int) :
    x * y * z = x * (y * z) := Int.mul_assoc x y z

/-- Structural: `fourVL < fourV`. -/
theorem fourVL_lt_fourV (m : Nat) (q k : Int) (irreg : Bool) :
    fourVL m q k irreg < fourV m q k := by
  rw [fourV_eq]
  have hpos := twoPos_tenNeg_pos_Int q k
  by_cases h : irreg
  · have hVL : fourVL m q k irreg
                  = (4 * (m : Int) - 1) * ((twoPosPow q : Int) * (tenNegPow k : Int)) := by
      unfold fourVL cmpScaledMixed.lhs twoPosPow tenNegPow
      simp [h, mul_assoc3]
    rw [hVL]
    have h1 : (4 * (m : Int) - 1) < 4 * (m : Int) := by omega
    have := mul_lt_mul_right_of_pos h1 hpos
    rw [mul_assoc3]
    exact this
  · have hVL : fourVL m q k irreg
                  = (4 * (m : Int) - 2) * ((twoPosPow q : Int) * (tenNegPow k : Int)) := by
      unfold fourVL cmpScaledMixed.lhs twoPosPow tenNegPow
      simp [h, mul_assoc3]
    rw [hVL]
    have h1 : (4 * (m : Int) - 2) < 4 * (m : Int) := by omega
    have := mul_lt_mul_right_of_pos h1 hpos
    rw [mul_assoc3]
    exact this

/-- Structural: `fourV < fourVR`. -/
theorem fourV_lt_fourVR (m : Nat) (q k : Int) :
    fourV m q k < fourVR m q k := by
  rw [fourV_eq, fourVR_eq]
  have hpos := twoPos_tenNeg_pos_Int q k
  have h1 : (4 * (m : Int)) < 4 * (m : Int) + 2 := by omega
  have := mul_lt_mul_right_of_pos h1 hpos
  rw [mul_assoc3 (4 * (m : Int)), mul_assoc3 (4 * (m : Int) + 2)]
  exact this

/-! ## Width identity used to convert `KCorrect` form to `fourW - fourU ≤ fourVR - fourVL`. -/

/-- Auxiliary: split a power into a known offset. `2^(n+2) = 2^n * 4` in Int. -/
private theorem pow_add2 (n : Nat) : (2 : Int) ^ (n + 2) = 2 ^ n * 4 := by
  rw [Int.pow_add]; rfl

/-- `4 · twoNegPow q · shiftFactor(q-2) = shiftFactor(-q+2) · twoPosPow q`.

This is the cross-multiplied form of `2^q = 4 · 2^(q-2)`, lifted across the
sign-split `twoPosPow / twoNegPow / shiftFactor` representations. -/
theorem shiftFactor_width_identity (q : Int) :
    (4 : Int) * (twoNegPow q : Int) * Midpoint.shiftFactor (q - 2)
      = Midpoint.shiftFactor (-q + 2) * (twoPosPow q : Int) := by
  unfold twoNegPow twoPosPow Midpoint.shiftFactor
  by_cases hq0 : q ≥ 0
  · -- q ≥ 0: twoPosPow ≠ 1, twoNegPow = 1.
    have hq_neg : ¬ (q < 0) := by omega
    rw [if_pos hq0, if_neg hq_neg]
    by_cases hq2 : q ≥ 2
    · -- q ≥ 2: (q-2).toNat = q.toNat - 2 ≥ 0; (-q+2).toNat = 0.
      have h1 : (q - 2).toNat = q.toNat - 2 := by omega
      have h2 : (-q + 2).toNat = 0 := by omega
      have hqN : q.toNat ≥ 2 := by omega
      rw [h1, h2]
      -- Goal: 4 * ↑(2^0) * 2^(q.toNat-2) = 2^0 * ↑(2^q.toNat)
      show (4 : Int) * ((2 ^ 0 : Nat) : Int) * (2 ^ (q.toNat - 2) : Int)
            = (2 : Int) ^ 0 * ((2 ^ q.toNat : Nat) : Int)
      have hcast : ((2 ^ q.toNat : Nat) : Int) = (2 : Int) ^ q.toNat := by
        push_cast; rfl
      have hcast2 : ((2 ^ 0 : Nat) : Int) = 1 := by decide
      rw [hcast, hcast2]
      -- Goal: 4 * 1 * 2^(q.toNat - 2) = 2^0 * 2^q.toNat
      have hpow : (2 : Int) ^ q.toNat = (2 : Int) ^ (q.toNat - 2) * 4 := by
        have heq : (q.toNat - 2) + 2 = q.toNat := by omega
        have := pow_add2 (q.toNat - 2)
        -- this : 2^(q.toNat - 2 + 2) = 2^(q.toNat - 2) * 4
        rw [heq] at this
        exact this
      rw [hpow]
      have hp0 : (2 : Int) ^ 0 = 1 := by decide
      rw [hp0, Int.one_mul, Int.mul_comm ((2 : Int) ^ (q.toNat - 2)) 4]
      show (4 : Int) * 1 * 2 ^ (q.toNat - 2) = 4 * 2 ^ (q.toNat - 2)
      rw [Int.mul_one]
    · -- 0 ≤ q < 2: (q-2).toNat = 0; (-q+2).toNat + q.toNat = 2.
      have hq_lt2 : q < 2 := by omega
      have h1 : (q - 2).toNat = 0 := by omega
      have hqN : q.toNat < 2 := by omega
      rw [h1]
      -- Goal: 4 * ↑(2^0) * 2^0 = 2^(-q+2).toNat * ↑(2^q.toNat)
      show (4 : Int) * ((2 ^ 0 : Nat) : Int) * (2 : Int) ^ 0
            = (2 : Int) ^ (-q + 2).toNat * ((2 ^ q.toNat : Nat) : Int)
      have hcast : ((2 ^ q.toNat : Nat) : Int) = (2 : Int) ^ q.toNat := by push_cast; rfl
      have hcast2 : ((2 ^ 0 : Nat) : Int) = 1 := by decide
      have hpow0 : (2 : Int) ^ 0 = 1 := by decide
      rw [hcast, hcast2, hpow0]
      -- Goal: 4 * 1 * 1 = 2^(-q+2).toNat * 2^q.toNat
      have hsum : (-q + 2).toNat + q.toNat = 2 := by omega
      have hprod : ((2 : Int) ^ (-q + 2).toNat) * ((2 : Int) ^ q.toNat) = (2 : Int) ^ 2 := by
        rw [← Int.pow_add, hsum]
      have hp22 : (2 : Int) ^ 2 = 4 := by decide
      rw [hprod, hp22]
      show (4 : Int) * 1 * 1 = 4
      omega
  · -- q < 0: twoPosPow = 1, twoNegPow = 2^(-q).toNat.
    have hq : q < 0 := by omega
    have hq_pos : ¬ (q ≥ 0) := by omega
    have h1 : (q - 2).toNat = 0 := by omega
    have h2 : (-q + 2).toNat = (-q).toNat + 2 := by omega
    rw [if_pos hq, if_neg hq_pos]
    rw [h1, h2]
    -- Goal: 4 * ↑(2^(-q).toNat) * 2^0 = 2^((-q).toNat+2) * ↑(2^0)
    show (4 : Int) * ((2 ^ (-q).toNat : Nat) : Int) * (2 : Int) ^ 0
          = (2 : Int) ^ ((-q).toNat + 2) * ((2 ^ 0 : Nat) : Int)
    have hcast : ((2 ^ (-q).toNat : Nat) : Int) = (2 : Int) ^ (-q).toNat := by push_cast; rfl
    have hcast2 : ((2 ^ 0 : Nat) : Int) = 1 := by decide
    have hpow0 : (2 : Int) ^ 0 = 1 := by decide
    rw [hcast, hcast2, hpow0]
    -- Goal: 4 * 2^(-q).toNat * 1 = 2^((-q).toNat+2) * 1
    have hpow : (2 : Int) ^ ((-q).toNat + 2) = (2 : Int) ^ (-q).toNat * 4 := pow_add2 _
    rw [hpow]
    rw [Int.mul_one, Int.mul_one, Int.mul_comm ((2 : Int) ^ (-q).toNat) 4]

/-- `4u ≤ 4v` in cleared form. -/
theorem fourU_le_fourV (s m : Nat) (q k : Int) (hs : s = shiftedSig m q k) :
    fourU s q k ≤ fourV m q k := by
  have h := shiftedSig_le m q k
  have hZ : ((shiftedSig m q k : Int) * ((twoNegPow q : Int) * (tenPosPow k : Int)))
              ≤ ((m : Int) * ((twoPosPow q : Int) * (tenNegPow k : Int))) := by
    exact_mod_cast h
  have h4 : (0 : Int) ≤ 4 := by decide
  have hZ4 : 4 * ((shiftedSig m q k : Int) * ((twoNegPow q : Int) * (tenPosPow k : Int)))
              ≤ 4 * ((m : Int) * ((twoPosPow q : Int) * (tenNegPow k : Int))) :=
    Int.mul_le_mul_of_nonneg_left hZ h4
  rw [fourU_eq, fourV_eq, hs]
  -- Goal: 4 * s * tenPos * twoNeg ≤ 4 * m * twoPos * tenNeg
  -- Reassociate both sides into `4 * (x * (y * z))` form.
  rw [Int.mul_assoc (4 * (shiftedSig m q k : Int)) (tenPosPow k : Int) (twoNegPow q : Int),
      Int.mul_assoc 4 (shiftedSig m q k : Int) ((tenPosPow k : Int) * (twoNegPow q : Int)),
      Int.mul_assoc (4 * (m : Int)) (twoPosPow q : Int) (tenNegPow k : Int),
      Int.mul_assoc 4 (m : Int) ((twoPosPow q : Int) * (tenNegPow k : Int)),
      Int.mul_comm (tenPosPow k : Int) (twoNegPow q : Int)]
  exact hZ4

/-- `4v < 4w` in cleared form. -/
theorem fourV_lt_fourW (s m : Nat) (q k : Int) (hs : s = shiftedSig m q k) :
    fourV m q k < fourW s q k := by
  have h := shiftedSig_lt_succ m q k
  have hZ : ((m : Int) * ((twoPosPow q : Int) * (tenNegPow k : Int)))
              < (((shiftedSig m q k : Int) + 1) * ((twoNegPow q : Int) * (tenPosPow k : Int))) := by
    exact_mod_cast h
  have h4 : (0 : Int) < 4 := by decide
  have hZ4 : 4 * ((m : Int) * ((twoPosPow q : Int) * (tenNegPow k : Int)))
              < 4 * (((shiftedSig m q k : Int) + 1) * ((twoNegPow q : Int) * (tenPosPow k : Int))) :=
    Int.mul_lt_mul_of_pos_left hZ h4
  rw [fourV_eq, fourW_eq, hs]
  rw [Int.mul_assoc (4 * (m : Int)) (twoPosPow q : Int) (tenNegPow k : Int),
      Int.mul_assoc 4 (m : Int) ((twoPosPow q : Int) * (tenNegPow k : Int)),
      Int.mul_assoc (4 * ((shiftedSig m q k : Int) + 1)) (tenPosPow k : Int) (twoNegPow q : Int),
      Int.mul_assoc 4 ((shiftedSig m q k : Int) + 1) ((tenPosPow k : Int) * (twoNegPow q : Int)),
      Int.mul_comm (tenPosPow k : Int) (twoNegPow q : Int)]
  exact hZ4

/-! ## From `kOfMQ_correct`: width inequality `4·(tenPos·twoNeg) ≤ wn·(twoPos·tenNeg)`. -/

/-- Casting helper: `p10Num K = tenPosPow K` (both are `10^max(K,0)`). -/
theorem p10Num_eq_tenPosPow (K : Int) :
    (p10Num K : Int) = (tenPosPow K : Int) := by
  unfold p10Num tenPosPow
  by_cases h : K ≥ 0
  · rw [if_pos h, if_pos h]
    have hK_toN : K.toNat = K.natAbs := by
      have := Int.natAbs_of_nonneg h
      omega
    rw [hK_toN]
  · rw [if_neg h, if_neg h]

/-- Casting helper: `p10Den K = tenNegPow K` (both are `10^max(-K,0)`). -/
theorem p10Den_eq_tenNegPow (K : Int) :
    (p10Den K : Int) = (tenNegPow K : Int) := by
  unfold p10Den tenNegPow
  by_cases h : K ≥ 0
  · rw [if_pos h]
    have hneg : ¬ K < 0 := by omega
    rw [if_neg hneg]
  · rw [if_neg h]
    have hneg : K < 0 := by omega
    rw [if_pos hneg]
    have hK_eq : (-K).toNat = K.natAbs := by
      have hpos : 0 ≤ -K := by omega
      have := Int.toNat_of_nonneg hpos
      have habs : (-K).natAbs = K.natAbs := by
        omega
      omega
    rw [hK_eq]

/-- The width inequality, cross-multiplied:
`4 · tenPosPow K · twoNegPow q ≤ width.num · twoPosPow q · tenNegPow K`.

Derived from `kOfMQ_correct`'s first half, multiplied by 4 and rearranged
using `shiftFactor_width_identity`.

Note: `width.num = 4` (regular) or `3` (irregular). -/
theorem width_inequality (m : Nat) (q : Int)
    (hm_pos : 1 ≤ m) (hm_le : m < 2 ^ 53) (hq_lo : -1074 ≤ q) (hq_hi : q ≤ 971) :
    let K := kOfMQ m q
    let wn := (if isIrregular m q then 3 else 4 : Int)
    4 * (tenPosPow K : Int) * (twoNegPow q : Int)
      ≤ wn * (twoPosPow q : Int) * (tenNegPow K : Int) := by
  intro K wn
  -- Get the cleared inequality from kOfMQ_correct.
  have h := kOfMQ_le_log_width m q hm_pos hm_le hq_lo hq_hi
  -- The `let` bindings inside the theorem statement need unfolding.
  simp only at h
  -- h : (p10Num K) * shiftFactor (w.denPow2) ≤ w.num * shiftFactor (-w.denPow2) * p10Den K
  -- where w = R.width, w.denPow2 = -q + 2, w.num = 4 (reg) or 3 (irreg).
  have hwd : (RoundingInterval.ofMQ m q hm_pos hm_le hq_lo hq_hi).width.denPow2 = -q + 2 :=
    ofMQ_width_denPow2 m q hm_pos hm_le hq_lo hq_hi
  rw [hwd] at h
  -- Now h : p10Num K * shiftFactor (-q + 2) ≤ w.num * shiftFactor (-(-q + 2)) * p10Den K
  -- Simplify -(-q + 2) = q - 2.
  have hneg : -(-q + 2 : Int) = q - 2 := by omega
  rw [hneg] at h
  -- Replace `w.num` with the concrete value.
  have hwn : (RoundingInterval.ofMQ m q hm_pos hm_le hq_lo hq_hi).width.num = wn := by
    show (RoundingInterval.ofMQ m q hm_pos hm_le hq_lo hq_hi).width.num =
          (if isIrregular m q then 3 else 4 : Int)
    by_cases hirr : isIrregular m q = true
    · rw [if_pos hirr]
      exact ofMQ_width_num_irregular m q hm_pos hm_le hq_lo hq_hi hirr
    · rw [if_neg hirr]
      exact ofMQ_width_num_regular m q hm_pos hm_le hq_lo hq_hi hirr
  rw [hwn] at h
  -- Now h : p10Num K * shiftFactor (-q + 2) ≤ wn * shiftFactor (q - 2) * p10Den K
  -- Multiply both sides by 4 · twoNegPow q (all positive).
  -- We want: 4 * p10Num K * shiftFactor (-q + 2) * twoNegPow q
  --        ≤ 4 * wn * shiftFactor (q - 2) * p10Den K * twoNegPow q
  -- Using identity: 4 * twoNegPow q * shiftFactor (q - 2) = shiftFactor (-q + 2) * twoPosPow q
  -- The RHS becomes: wn * shiftFactor (-q + 2) * twoPosPow q * p10Den K
  -- After dividing by shiftFactor (-q + 2) > 0:
  --   4 * p10Num K * twoNegPow q ≤ wn * twoPosPow q * p10Den K
  have h4 : (0 : Int) ≤ 4 := by decide
  have hmul4 : (4 : Int) * ((p10Num K : Int) * Midpoint.shiftFactor (-q + 2))
                ≤ 4 * (wn * Midpoint.shiftFactor (q - 2) * (p10Den K : Int)) :=
    Int.mul_le_mul_of_nonneg_left h h4
  have htn_nn : (0 : Int) ≤ (twoNegPow q : Int) := by
    have := twoPos_tenNeg_pos_Int q 0
    -- Actually we need a clean nonneg for twoNegPow q directly.
    unfold twoNegPow
    exact_mod_cast Nat.zero_le _
  have hmul4tn : 4 * ((p10Num K : Int) * Midpoint.shiftFactor (-q + 2)) * (twoNegPow q : Int)
                ≤ 4 * (wn * Midpoint.shiftFactor (q - 2) * (p10Den K : Int)) * (twoNegPow q : Int) :=
    Int.mul_le_mul_of_nonneg_right hmul4 htn_nn
  -- Rearrange RHS using the identity.
  have hid := shiftFactor_width_identity q
  -- hid : 4 * twoNegPow q * shiftFactor(q-2) = shiftFactor(-q+2) * twoPosPow q
  -- RHS = 4 * wn * shiftFactor(q-2) * p10Den * twoNegPow
  --     = wn * p10Den * (4 * twoNegPow * shiftFactor(q-2))
  --     = wn * p10Den * (shiftFactor(-q+2) * twoPosPow)
  --     = shiftFactor(-q+2) * (wn * twoPosPow * p10Den)
  -- We use a generic `mul_comm/assoc` reasoning packaged into a single equality lemma.
  -- All these `Int` products are commutative and associative; the kernel can't see this
  -- via `rfl` because the term structures differ, so we prove the equalities by
  -- a fixed normalization to `a*b*c*d*e` ordering and then comparing.
  --
  -- Strategy: introduce intermediate `mul_comm`/`mul_assoc` rewrites by name.
  -- Auxiliary: 4 * (W * A * B) * C = (4 * C * A) * (W * B), proven by raw assoc/comm.
  -- Then we'll use this with W = wn, A = sfQm, B = pD, C = tN. After this step,
  -- the leftmost factor `4 * tN * sfQm` (in `4 * C * A`) is exactly what `hid` rewrites.
  have rearr_rhs : ∀ (W A B C : Int),
      4 * (W * A * B) * C = (4 * C * A) * (W * B) := by
    intros W A B C
    -- Compute via several mul_comm/mul_assoc.
    -- 4 * (W * A * B) * C
    --  = 4 * (W * A * B * C)         [mul_assoc 4 (W*A*B) C]
    --  = 4 * (W * A * (B * C))        [mul_assoc W*A B C]
    --  = 4 * (W * (A * (B * C)))      [mul_assoc W A (B*C)]
    --  = 4 * (W * (A * B * C))        [mul_assoc A B C, reverse]
    --  = 4 * (W * (B * (A * C)))      [mul_assoc + comm]
    --  ...
    -- Better: just compute both sides into the same flat list-product.
    -- We prove via repeated `Int.mul_assoc` and `Int.mul_comm` until we hit a tag.
    -- Easier route: prove `LHS * 1 = RHS * 1` is implied by `LHS = RHS`, then use
    -- `decide`-like normalization via Int.mul_comm/_assoc rotation.
    --
    -- I'll just use a sequence of explicit rewrites.
    rw [Int.mul_assoc 4 (W * A * B) C]
    -- 4 * (W * A * B * C)
    rw [Int.mul_assoc (W * A) B C]
    -- 4 * (W * A * (B * C))
    rw [Int.mul_assoc W A (B * C)]
    -- 4 * (W * (A * (B * C)))
    rw [← Int.mul_assoc A B C]
    -- 4 * (W * (A * B * C))
    rw [Int.mul_comm A B]
    -- 4 * (W * (B * A * C))
    rw [Int.mul_assoc B A C]
    -- 4 * (W * (B * (A * C)))
    rw [← Int.mul_assoc W B (A * C)]
    -- 4 * (W * B * (A * C))
    rw [← Int.mul_assoc 4 (W * B) (A * C)]
    -- 4 * (W * B) * (A * C)
    rw [Int.mul_comm 4 (W * B)]
    -- W * B * 4 * (A * C)
    rw [Int.mul_assoc (W * B) 4 (A * C)]
    -- W * B * (4 * (A * C))
    rw [← Int.mul_assoc 4 A C]
    -- W * B * (4 * A * C)
    rw [Int.mul_comm (W * B) (4 * A * C)]
    -- 4 * A * C * (W * B)
    rw [Int.mul_assoc 4 A C, Int.mul_comm A C, ← Int.mul_assoc 4 C A]
  -- LHS rearrangement: 4 * (P * S) * T = S * (4 * P * T).
  have rearr_lhs : ∀ (P S T : Int),
      4 * (P * S) * T = S * (4 * P * T) := by
    intros P S T
    -- 4 * (P * S) * T
    rw [← Int.mul_assoc 4 P S]
    -- 4 * P * S * T
    rw [Int.mul_assoc (4 * P) S T]
    -- 4 * P * (S * T)
    rw [Int.mul_comm (4 * P) (S * T)]
    -- S * T * (4 * P)
    rw [Int.mul_assoc S T (4 * P)]
    -- S * (T * (4 * P))
    rw [Int.mul_comm T (4 * P)]
    -- S * (4 * P * T)
  have hrhs_eq :
      4 * (wn * Midpoint.shiftFactor (q - 2) * (p10Den K : Int)) * (twoNegPow q : Int)
        = Midpoint.shiftFactor (-q + 2) * (wn * (twoPosPow q : Int) * (p10Den K : Int)) := by
    rw [rearr_rhs wn (Midpoint.shiftFactor (q - 2)) (p10Den K : Int) (twoNegPow q : Int)]
    -- Goal: (4 * tN * sfQm) * (wn * pD) = sfMq * (wn * twoPos * pD)
    rw [hid]
    -- Goal: (sfMq * twoPos) * (wn * pD) = sfMq * (wn * twoPos * pD)
    rw [Int.mul_assoc (Midpoint.shiftFactor (-q + 2)) (twoPosPow q : Int)
              (wn * (p10Den K : Int))]
    -- sfMq * (twoPos * (wn * pD)) = sfMq * (wn * twoPos * pD)
    rw [← Int.mul_assoc (twoPosPow q : Int) wn (p10Den K : Int),
        Int.mul_comm (twoPosPow q : Int) wn]
  have hlhs_eq :
      4 * ((p10Num K : Int) * Midpoint.shiftFactor (-q + 2)) * (twoNegPow q : Int)
        = Midpoint.shiftFactor (-q + 2) *
            (4 * (p10Num K : Int) * (twoNegPow q : Int)) :=
    rearr_lhs (p10Num K : Int) (Midpoint.shiftFactor (-q + 2)) (twoNegPow q : Int)
  rw [hlhs_eq, hrhs_eq] at hmul4tn
  -- hmul4tn : shiftFactor(-q+2) * (4 * p10Num * twoNegPow) ≤ shiftFactor(-q+2) * (wn * twoPos * p10Den)
  -- shiftFactor(-q+2) > 0, so we can cancel it.
  have hsf_pos := Midpoint.shiftFactor_pos (-q + 2)
  have := Int.le_of_mul_le_mul_left hmul4tn hsf_pos
  -- Now: 4 * p10Num K * twoNegPow q ≤ wn * twoPos q * p10Den K
  -- Rewrite p10Num → tenPosPow and p10Den → tenNegPow.
  rw [p10Num_eq_tenPosPow, p10Den_eq_tenNegPow] at this
  exact this

/-! ## Width identity: `fourW - fourU = 4 · tenPos · twoNeg`. -/

/-- `fourW - fourU = 4 · tenPosPow k · twoNegPow q`. -/
theorem fourW_sub_fourU (s : Nat) (q k : Int) :
    fourW s q k - fourU s q k
      = 4 * (tenPosPow k : Int) * (twoNegPow q : Int) := by
  rw [fourU_eq, fourW_eq]
  -- 4(s+1)*tenP*twoN - 4s*tenP*twoN = 4*tenP*twoN
  generalize (tenPosPow k : Int) = a
  generalize (twoNegPow q : Int) = b
  rw [show (4 * ((s : Int) + 1) = 4 * (s : Int) + 4) from by omega]
  rw [Int.add_mul, Int.add_mul]
  omega

/-- `fourVR - fourVL = wn · twoPosPow q · tenNegPow k`, where `wn = 3` (irreg)
or `4` (reg). -/
theorem fourVR_sub_fourVL (m : Nat) (q k : Int) :
    fourVR m q k - fourVL m q k (isIrregular m q)
      = (if isIrregular m q then 3 else 4 : Int)
          * (twoPosPow q : Int) * (tenNegPow k : Int) := by
  by_cases h : isIrregular m q = true
  · rw [fourVR_eq, fourVL_eq_irregular m q k h]
    rw [if_pos h]
    rw [Int.mul_assoc (4 * (m : Int) + 2), Int.mul_assoc (4 * (m : Int) - 1),
        Int.mul_assoc 3]
    generalize ((twoPosPow q : Int) * (tenNegPow k : Int)) = c
    rw [Int.add_mul, Int.sub_mul, Int.one_mul]
    omega
  · rw [fourVR_eq, fourVL_eq_regular m q k h]
    rw [if_neg h]
    rw [Int.mul_assoc (4 * (m : Int) + 2), Int.mul_assoc (4 * (m : Int) - 2),
        Int.mul_assoc 4]
    generalize ((twoPosPow q : Int) * (tenNegPow k : Int)) = c
    rw [Int.add_mul, Int.sub_mul]
    omega

/-! ## Combining width inequality and the diff identities: `fourW - fourU ≤ fourVR - fourVL`. -/

/-- The "interval width" inequality: at `k = kOfMQ m q`, the cleared
candidate interval `[fourU, fourW]` is no wider than the cleared rounding
interval `[fourVL, fourVR]`. -/
theorem fourW_sub_fourU_le_fourVR_sub_fourVL (s m : Nat) (q : Int)
    (hm_pos : 1 ≤ m) (hm_le : m < 2 ^ 53) (hq_lo : -1074 ≤ q) (hq_hi : q ≤ 971) :
    let K := kOfMQ m q
    fourW s q K - fourU s q K ≤ fourVR m q K - fourVL m q K (isIrregular m q) := by
  intro K
  rw [fourW_sub_fourU, fourVR_sub_fourVL]
  exact width_inequality m q hm_pos hm_le hq_lo hq_hi

/-! ## R11: at least one of (s, k) or (s+1, k) lies in R_v.

We carry through the algebraic argument: if both fail, then equality
forces `4·tenPos·twoNeg = wn·twoPos·tenNeg`. In the regular case
(wn=4), this implies `q = k = 0`, and then `fourU = 4s = fourVL = 4m - 2`
is impossible (LHS divisible by 4, RHS isn't). In the irregular case
(wn=3), LHS has no factor 3 but RHS does, contradiction. -/

/-! ### Membership reformulation: "u in R_v" as Int inequalities. -/

/-- "u = s · 10^k in R_v" reified:
   `fourVL ≤ fourU`-side (with even-tie) AND `fourU ≤ fourVR`-side. -/
private def UIn (s : Nat) (k : Int) (m : Nat) (q : Int) : Prop :=
  (fourVL m q k (isIrregular m q) < fourU s q k ∨
    (fourVL m q k (isIrregular m q) = fourU s q k ∧ m % 2 = 0)) ∧
  (fourU s q k < fourVR m q k ∨
    (fourU s q k = fourVR m q k ∧ m % 2 = 0))

/-- "w = (s+1) · 10^k in R_v" reified. -/
private def WIn (s : Nat) (k : Int) (m : Nat) (q : Int) : Prop :=
  (fourVL m q k (isIrregular m q) < fourW s q k ∨
    (fourVL m q k (isIrregular m q) = fourW s q k ∧ m % 2 = 0)) ∧
  (fourW s q k < fourVR m q k ∨
    (fourW s q k = fourVR m q k ∧ m % 2 = 0))

/-! ### Forbidding the "both fail" case.

The technical heart of R11. We assume both `UIn` and `WIn` fail and
derive a contradiction. -/

/-- If `4 · tenPosPow K · twoNegPow q = 3 · twoPosPow q · tenNegPow K` (the
irregular-case equality), we get an impossible factor-of-3 condition.
LHS has no factor 3 (both 4 and 2^_ and 10^_'s factors are 2/5), but
wait — `10^? = 2^? · 5^?` has no factor 3, and `4 = 2^2`, `2^? = 2^?`. So
LHS = 2^? * 5^?. RHS = 3 * 2^? * 2^? * 5^? * 1 = 3 * 2^? * 5^? — has a
factor 3. Contradiction. -/
private theorem irreg_width_eq_impossible (q K : Int) :
    ¬ (4 * (tenPosPow K : Int) * (twoNegPow q : Int)
        = 3 * (twoPosPow q : Int) * (tenNegPow K : Int)) := by
  intro heq
  -- LHS positive (it equals RHS, both positive). Take mod 3.
  -- LHS mod 3: 4 * 10^a * 2^b mod 3. 4 ≡ 1, 10 ≡ 1, 2 ≡ 2 (mod 3).
  -- So LHS ≡ 1 * 1 * 2^b (mod 3). RHS ≡ 0 (mod 3).
  -- 2^b mod 3 ∈ {1, 2}, so LHS ≢ 0 (mod 3). Contradiction.
  -- We argue by considering both sides mod 3 in Int.
  -- Take the residue of both sides modulo 3.
  have hmod : (4 * (tenPosPow K : Int) * (twoNegPow q : Int)) % 3
              = (3 * (twoPosPow q : Int) * (tenNegPow K : Int)) % 3 := by
    rw [heq]
  -- RHS mod 3 = 0.
  have hRHS_mod : (3 * (twoPosPow q : Int) * (tenNegPow K : Int)) % 3 = 0 := by
    rw [Int.mul_assoc]
    exact Int.mul_emod_right 3 _
  rw [hRHS_mod] at hmod
  -- Show LHS mod 3 ≠ 0.
  -- 4 mod 3 = 1; tenPosPow K mod 3 ∈ {1}; twoNegPow q mod 3 ∈ {1, 2}.
  -- Hence LHS mod 3 ∈ {1, 2}. Contradiction with hmod.
  -- We'll do it pointwise: tenPosPow K is 10^a so 10^a mod 3 = 1^a = 1.
  -- twoNegPow q is 2^b so 2^b mod 3 ∈ {1, 2}.
  have hLHS_ne : (4 * (tenPosPow K : Int) * (twoNegPow q : Int)) % 3 ≠ 0 := by
    -- Show LHS mod 3 ≠ 0 by showing it ∈ {1, 2}.
    -- Use 10^a ≡ 1 (mod 3): we have 10 ≡ 1 (mod 3), hence 10^a ≡ 1 (mod 3).
    -- Hence (tenPosPow K : Int) % 3 = 1.
    have h10 : ∀ a : Nat, (10 ^ a : Int) % 3 = 1 := by
      intro a
      induction a with
      | zero => decide
      | succ n ih =>
        rw [Int.pow_succ]
        rw [Int.mul_emod, ih]
        decide
    -- (twoNegPow q : Int) % 3 ∈ {1, 2}
    have h2 : ∀ b : Nat, (2 ^ b : Int) % 3 = 1 ∨ (2 ^ b : Int) % 3 = 2 := by
      intro b
      induction b with
      | zero => left; decide
      | succ n ih =>
        rw [Int.pow_succ]
        rw [Int.mul_emod]
        rcases ih with h | h
        · rw [h]; right; decide
        · rw [h]; left; decide
    -- tenPosPow K is (10 : Int) ^ (some a as Nat).
    have htP : (tenPosPow K : Int)
                = (10 : Int) ^ (if K ≥ 0 then K.toNat else 0) := by
      unfold tenPosPow
      push_cast; rfl
    have htN : (twoNegPow q : Int)
                = (2 : Int) ^ (if q < 0 then (-q).toNat else 0) := by
      unfold twoNegPow
      push_cast; rfl
    rw [htP, htN]
    generalize (if K ≥ 0 then K.toNat else 0) = a
    generalize (if q < 0 then (-q).toNat else 0) = b
    -- Goal: (4 * 10^a * 2^b) % 3 ≠ 0
    have hLHS_mod_calc :
        (4 * ((10 : Int) ^ a) * ((2 : Int) ^ b)) % 3
          = (1 * 1 * ((2 : Int) ^ b % 3)) % 3 := by
      rw [Int.mul_emod, Int.mul_emod 4 ((10 : Int) ^ a), h10 a]
      rw [show (4 : Int) % 3 = 1 from by decide]
      omega
    rw [hLHS_mod_calc]
    rcases h2 b with h | h
    · rw [h]; decide
    · rw [h]; decide
  exact hLHS_ne hmod

/-! ### Decompose the regular-case equality

For the regular case: if `4 · tenPosPow K · twoNegPow q = 4 · twoPosPow q · tenNegPow K`,
i.e. `tenPosPow K · twoNegPow q = twoPosPow q · tenNegPow K`, the four
sign-split factors must satisfy `q ≥ 0 ∧ K ≤ 0 ∧ 2^q = 10^(-K)` or all
exponents zero. `twoPosPow q · tenNegPow K - tenPosPow K · twoNegPow q = 0`
happens only when each side is `1`, i.e. `q = 0 ∧ K = 0`. We split by sign
of `q` and `K`. -/

/-- `2^n mod 5 ∈ {1, 2, 4, 3}` — never 0. -/
private theorem two_pow_mod5_ne_zero (n : Nat) : (2 : Int) ^ n % 5 ≠ 0 := by
  have h2_mod : ∀ n : Nat,
      (2 : Int) ^ n % 5 = 1 ∨ (2 : Int) ^ n % 5 = 2
        ∨ (2 : Int) ^ n % 5 = 4 ∨ (2 : Int) ^ n % 5 = 3 := by
    intro n
    induction n with
    | zero => left; decide
    | succ k ih =>
      rw [Int.pow_succ, Int.mul_emod]
      rcases ih with h | h | h | h
      · rw [h]; right; left; decide
      · rw [h]; right; right; left; decide
      · rw [h]; right; right; right; decide
      · rw [h]; left; decide
  rcases h2_mod n with h | h | h | h <;> omega

/-- `10^n` is divisible by 5 for `n ≥ 1`. -/
private theorem ten_pow_mod5_zero {n : Nat} (h : n ≥ 1) : (10 : Int) ^ n % 5 = 0 := by
  have h1 : n = (n - 1) + 1 := by omega
  rw [h1, Int.pow_succ]
  rw [Int.mul_emod]
  rw [show (10 : Int) % 5 = 0 from by decide]
  simp

/-- For all `n : Nat`, `(2 : Int) ^ n ≥ 1`. -/
private theorem two_pow_ge_one (n : Nat) : (1 : Int) ≤ (2 : Int) ^ n := by
  induction n with
  | zero => decide
  | succ k ih =>
    rw [Int.pow_succ]
    have h2 : (0 : Int) < 2 := by decide
    have hk : (0 : Int) ≤ (2 : Int) ^ k := by
      have := ih
      omega
    have : (1 : Int) * 1 ≤ (2 : Int) ^ k * 2 := by
      apply Int.mul_le_mul ih (by decide) (by decide) hk
    simpa using this

/-- For all `n : Nat`, `(10 : Int) ^ n ≥ 1`. -/
private theorem ten_pow_ge_one (n : Nat) : (1 : Int) ≤ (10 : Int) ^ n := by
  induction n with
  | zero => decide
  | succ k ih =>
    rw [Int.pow_succ]
    have h10 : (0 : Int) < 10 := by decide
    have hk : (0 : Int) ≤ (10 : Int) ^ k := by
      have := ih; omega
    have : (1 : Int) * 1 ≤ (10 : Int) ^ k * 10 := by
      apply Int.mul_le_mul ih (by decide) (by decide) hk
    simpa using this

/-- `2^n ≥ 2` for `n ≥ 1`. -/
private theorem two_pow_ge_two {n : Nat} (h : n ≥ 1) : (2 : Int) ≤ (2 : Int) ^ n := by
  have h1 : n = (n - 1) + 1 := by omega
  rw [h1, Int.pow_succ]
  have hp : (1 : Int) ≤ (2 : Int) ^ (n - 1) := two_pow_ge_one _
  have hpos : (0 : Int) ≤ (2 : Int) ^ (n - 1) := by omega
  have : (1 : Int) * 2 ≤ (2 : Int) ^ (n - 1) * 2 :=
    Int.mul_le_mul_of_nonneg_right hp (by decide)
  simpa using this

/-- `10^n ≥ 10` for `n ≥ 1`. -/
private theorem ten_pow_ge_ten {n : Nat} (h : n ≥ 1) : (10 : Int) ≤ (10 : Int) ^ n := by
  have h1 : n = (n - 1) + 1 := by omega
  rw [h1, Int.pow_succ]
  have hp : (1 : Int) ≤ (10 : Int) ^ (n - 1) := ten_pow_ge_one _
  have hpos : (0 : Int) ≤ (10 : Int) ^ (n - 1) := by omega
  have : (1 : Int) * 10 ≤ (10 : Int) ^ (n - 1) * 10 :=
    Int.mul_le_mul_of_nonneg_right hp (by decide)
  simpa using this

/-- If `tenPosPow K · twoNegPow q = twoPosPow q · tenNegPow K`, then
`q = 0 ∧ K = 0`. The four sign cases split into trivial cases where the
exponents are zero on one side or the other. -/
private theorem reg_width_eq_forces_zero (q K : Int)
    (h : (tenPosPow K : Int) * (twoNegPow q : Int)
          = (twoPosPow q : Int) * (tenNegPow K : Int)) :
    q = 0 ∧ K = 0 := by
  -- Unfold all four factors as concrete pow expressions.
  unfold tenPosPow twoNegPow twoPosPow tenNegPow at h
  by_cases hq_nn : q ≥ 0
  all_goals by_cases hK_nn : K ≥ 0
  · -- q ≥ 0, K ≥ 0: twoNegPow = 2^0 = 1, tenNegPow = 10^0 = 1.
    have hq_neg : ¬ q < 0 := by omega
    have hK_neg : ¬ K < 0 := by omega
    simp only [if_pos hq_nn, if_pos hK_nn, if_neg hq_neg, if_neg hK_neg] at h
    push_cast at h
    -- h : (10 : Int)^K.toNat * 1 = (2 : Int)^q.toNat * 1
    rw [Int.mul_one, Int.mul_one] at h
    have hZ : (10 : Int) ^ K.toNat = (2 : Int) ^ q.toNat := h
    -- Factor 5 forces K.toNat = 0; then 2^q.toNat = 1 forces q.toNat = 0.
    have hK0 : K.toNat = 0 := by
      rcases Nat.eq_zero_or_pos K.toNat with hK0' | hK1
      · exact hK0'
      · exfalso
        have hLHS_mod : (10 : Int) ^ K.toNat % 5 = 0 := ten_pow_mod5_zero hK1
        have hRHS_ne : (2 : Int) ^ q.toNat % 5 ≠ 0 := two_pow_mod5_ne_zero _
        have h_eq_mod : (10 : Int) ^ K.toNat % 5 = (2 : Int) ^ q.toNat % 5 := by rw [hZ]
        rw [hLHS_mod] at h_eq_mod
        exact hRHS_ne h_eq_mod.symm
    rw [hK0, Int.pow_zero] at hZ
    have hq0 : q.toNat = 0 := by
      rcases Nat.eq_zero_or_pos q.toNat with hq0' | hq1
      · exact hq0'
      · exfalso
        have h2ge : (2 : Int) ≤ (2 : Int) ^ q.toNat := two_pow_ge_two hq1
        -- hZ : 1 = 2^q.toNat, h2ge : 2 ≤ 2^q.toNat ⟹ 1 ≥ 2, false.
        omega
    refine ⟨?_, ?_⟩
    · have hqz_eq : (q.toNat : Int) = 0 := by exact_mod_cast hq0
      omega
    · have hKz_eq : (K.toNat : Int) = 0 := by exact_mod_cast hK0
      omega
  · -- q ≥ 0, K < 0.
    have hq_neg : ¬ q < 0 := by omega
    have hK_pos : ¬ K ≥ 0 := hK_nn
    have hK_neg : K < 0 := by omega
    simp only [if_pos hq_nn, if_neg hK_nn, if_neg hq_neg, if_pos hK_neg] at h
    push_cast at h
    -- h : (10:Int)^0 * (2:Int)^0 = (2:Int)^q.toNat * (10:Int)^(-K).toNat — but after push_cast,
    -- the LHS pows of 0 are reduced to 1.
    -- h : 1 * 1 = (2:Int)^q.toNat * (10:Int)^(-K).toNat
    -- (or the form may be slightly different — handle both)
    have h_eq : (1 : Int) = (2 : Int) ^ q.toNat * (10 : Int) ^ (-K).toNat := by
      have : (1 : Int) * 1 = (2 : Int) ^ q.toNat * (10 : Int) ^ (-K).toNat := h
      have : (1 : Int) = (2 : Int) ^ q.toNat * (10 : Int) ^ (-K).toNat := by
        rw [Int.one_mul] at this; exact this
      exact this
    -- (-K).toNat ≥ 1 since K < 0.
    have hnK_pos : (-K).toNat ≥ 1 := by
      have hnegK : 0 < -K := by omega
      have : ((-K).toNat : Int) = -K := Int.toNat_of_nonneg (by omega)
      omega
    -- 10^(-K).toNat ≥ 10, 2^q.toNat ≥ 1.
    have h10_ge : (10 : Int) ≤ (10 : Int) ^ (-K).toNat := ten_pow_ge_ten hnK_pos
    have h2_ge : (1 : Int) ≤ (2 : Int) ^ q.toNat := two_pow_ge_one _
    have h10_pos : (0 : Int) < (10 : Int) ^ (-K).toNat := by omega
    have h2_pos : (0 : Int) < (2 : Int) ^ q.toNat := by omega
    have hprod : (1 : Int) * 10 ≤ (2 : Int) ^ q.toNat * (10 : Int) ^ (-K).toNat :=
      Int.mul_le_mul h2_ge h10_ge (by decide) (by omega)
    omega
  · -- q < 0, K ≥ 0.
    have hq_pos : ¬ q ≥ 0 := hq_nn
    have hq_neg : q < 0 := by omega
    have hK_neg : ¬ K < 0 := by omega
    simp only [if_neg hq_nn, if_pos hK_nn, if_pos hq_neg, if_neg hK_neg] at h
    push_cast at h
    -- h : (10:Int)^K.toNat * (2:Int)^(-q).toNat = (2:Int)^0 * (10:Int)^0 = 1*1
    have h_eq : (10 : Int) ^ K.toNat * (2 : Int) ^ (-q).toNat = 1 := by
      have h_clean : (10 : Int) ^ K.toNat * (2 : Int) ^ (-q).toNat = 1 * 1 := h
      rw [Int.mul_one] at h_clean
      exact h_clean
    have hnq_pos : (-q).toNat ≥ 1 := by
      have hnegq : 0 < -q := by omega
      have : ((-q).toNat : Int) = -q := Int.toNat_of_nonneg (by omega)
      omega
    have h2_ge : (2 : Int) ≤ (2 : Int) ^ (-q).toNat := two_pow_ge_two hnq_pos
    have h10_ge : (1 : Int) ≤ (10 : Int) ^ K.toNat := ten_pow_ge_one _
    have h10_pos : (0 : Int) < (10 : Int) ^ K.toNat := by omega
    have h2_pos : (0 : Int) < (2 : Int) ^ (-q).toNat := by omega
    have hprod : (1 : Int) * 2 ≤ (10 : Int) ^ K.toNat * (2 : Int) ^ (-q).toNat :=
      Int.mul_le_mul h10_ge h2_ge (by decide) (by omega)
    omega
  · -- q < 0, K < 0.
    have hq_pos : ¬ q ≥ 0 := hq_nn
    have hq_neg : q < 0 := by omega
    have hK_pos : ¬ K ≥ 0 := hK_nn
    have hK_neg : K < 0 := by omega
    simp only [if_neg hq_nn, if_neg hK_nn, if_pos hq_neg, if_pos hK_neg] at h
    push_cast at h
    -- h : (10:Int)^0 * (2:Int)^(-q).toNat = (2:Int)^0 * (10:Int)^(-K).toNat
    -- i.e. 1 * 2^(-q).toNat = 1 * 10^(-K).toNat
    have h_eq : (2 : Int) ^ (-q).toNat = (10 : Int) ^ (-K).toNat := by
      have h_clean : (1 : Int) * (2 : Int) ^ (-q).toNat
                       = 1 * (10 : Int) ^ (-K).toNat := h
      rw [Int.one_mul, Int.one_mul] at h_clean
      exact h_clean
    have hnK_pos : (-K).toNat ≥ 1 := by
      have : 0 < -K := by omega
      have : ((-K).toNat : Int) = -K := Int.toNat_of_nonneg (by omega)
      omega
    -- LHS mod 5 ≠ 0; RHS mod 5 = 0. Contradiction.
    have hLHS_mod : (2 : Int) ^ (-q).toNat % 5 ≠ 0 := two_pow_mod5_ne_zero _
    have hRHS_mod : (10 : Int) ^ (-K).toNat % 5 = 0 := ten_pow_mod5_zero hnK_pos
    have h_mod : (2 : Int) ^ (-q).toNat % 5 = (10 : Int) ^ (-K).toNat % 5 := by rw [h_eq]
    rw [hRHS_mod] at h_mod
    exact absurd h_mod hLHS_mod

/-- R11: at least one of `(s, k)` and `(s+1, k)` lies in `R_v`, where
`s = shiftedSig m q k` and `k = kOfMQ m q`. -/
theorem shiftedSig_or_succ_mem_rv (m : Nat) (q : Int)
    (hm_pos : 1 ≤ m) (hm_lt : m < 2^53)
    (hq_lo : -1074 ≤ q) (hq_hi : q ≤ 971) :
    let k := kOfMQ m q
    let s := shiftedSig m q k
    inRoundingInterval s k m q (isIrregular m q) = true ∨
    inRoundingInterval (s + 1) k m q (isIrregular m q) = true := by
  intro k s
  -- Use decidability of Bool equality to split into Or via Classical.em.
  rcases Decidable.em (inRoundingInterval s k m q (isIrregular m q) = true) with h_uIn | h_uIn
  · left; exact h_uIn
  rcases Decidable.em (inRoundingInterval (s + 1) k m q (isIrregular m q) = true) with h_wIn | h_wIn
  · right; exact h_wIn
  -- Both fail: derive contradiction.
  exfalso
  -- Translate to UIn / WIn negations.
  have hUIn_iff := inRoundingInterval_iff s k m q (isIrregular m q)
  have hWIn_iff := inRoundingInterval_iff (s + 1) k m q (isIrregular m q)
  have hU_not : ¬ ((fourVL m q k (isIrregular m q) < fourU s q k ∨
                     (fourVL m q k (isIrregular m q) = fourU s q k ∧ m % 2 = 0)) ∧
                   (fourU s q k < fourVR m q k ∨
                     (fourU s q k = fourVR m q k ∧ m % 2 = 0))) := by
    intro h
    exact h_uIn (hUIn_iff.mpr h)
  -- We need to express WIn(s) in terms of fourW (i.e., fourU (s+1) = fourW s).
  have hfourU_succ : fourU (s + 1) q k = fourW s q k := by
    unfold fourU fourW cmpScaledMixed.rhs
    have h_cast : (((s + 1) : Nat) : Int) = (s : Int) + 1 := by push_cast; rfl
    rw [h_cast]
  have hW_not : ¬ ((fourVL m q k (isIrregular m q) < fourW s q k ∨
                     (fourVL m q k (isIrregular m q) = fourW s q k ∧ m % 2 = 0)) ∧
                   (fourW s q k < fourVR m q k ∨
                     (fourW s q k = fourVR m q k ∧ m % 2 = 0))) := by
    intro h
    apply h_wIn
    apply hWIn_iff.mpr
    rw [hfourU_succ]
    exact h
  -- Now case-split. We have:
  --   * fourU ≤ fourV < fourVR  (u-right strict, w-left strict from shiftedSig + R_v structure)
  --   * fourVL < fourV < fourW
  -- So u's right side and w's left side are automatic.
  -- We need u's left to fail and w's right to fail.
  have hUV : fourU s q k ≤ fourV m q k := by
    have := fourU_le_fourV s m q k rfl
    exact this
  have hVW : fourV m q k < fourW s q k := by
    have := fourV_lt_fourW s m q k rfl
    exact this
  have hVL_lt_V : fourVL m q k (isIrregular m q) < fourV m q k :=
    fourVL_lt_fourV m q k (isIrregular m q)
  have hV_lt_VR : fourV m q k < fourVR m q k := fourV_lt_fourVR m q k
  -- u's right always holds (strict).
  have hU_lt_VR : fourU s q k < fourVR m q k := by omega
  -- w's left always holds (strict).
  have hVL_lt_W : fourVL m q k (isIrregular m q) < fourW s q k := by omega
  -- So failure of UIn must be on the left.
  have hU_left_fail : ¬ (fourVL m q k (isIrregular m q) < fourU s q k ∨
                          (fourVL m q k (isIrregular m q) = fourU s q k ∧ m % 2 = 0)) := by
    intro hL
    apply hU_not
    exact ⟨hL, Or.inl hU_lt_VR⟩
  -- And failure of WIn must be on the right.
  have hW_right_fail : ¬ (fourW s q k < fourVR m q k ∨
                          (fourW s q k = fourVR m q k ∧ m % 2 = 0)) := by
    intro hR
    apply hW_not
    exact ⟨Or.inl hVL_lt_W, hR⟩
  -- Manually unpack `¬ (P ∨ Q)` → `¬P ∧ ¬Q`.
  have hU_le_VL : ¬ fourVL m q k (isIrregular m q) < fourU s q k :=
    fun h => hU_left_fail (Or.inl h)
  have hU_eq_VL_or_odd : ¬ (fourVL m q k (isIrregular m q) = fourU s q k ∧ m % 2 = 0) :=
    fun h => hU_left_fail (Or.inr h)
  have hVR_le_W : ¬ fourW s q k < fourVR m q k :=
    fun h => hW_right_fail (Or.inl h)
  have hW_eq_VR_or_odd : ¬ (fourW s q k = fourVR m q k ∧ m % 2 = 0) :=
    fun h => hW_right_fail (Or.inr h)
  -- Promote the negated `<` to `≤` (Int).
  have hU_le_VL : fourU s q k ≤ fourVL m q k (isIrregular m q) := by omega
  have hVR_le_W : fourVR m q k ≤ fourW s q k := by omega
  -- So fourU ≤ fourVL ∧ fourW ≥ fourVR.
  -- Width: fourW - fourU ≥ fourVR - fourVL.
  -- And width ≤ via fourW_sub_fourU_le_fourVR_sub_fourVL.
  -- Hence equality.
  have hwidth_le : fourW s q k - fourU s q k
                    ≤ fourVR m q k - fourVL m q k (isIrregular m q) :=
    fourW_sub_fourU_le_fourVR_sub_fourVL s m q hm_pos hm_lt hq_lo hq_hi
  have hwidth_ge : fourW s q k - fourU s q k
                    ≥ fourVR m q k - fourVL m q k (isIrregular m q) := by omega
  have hwidth_eq : fourW s q k - fourU s q k
                    = fourVR m q k - fourVL m q k (isIrregular m q) := by omega
  -- Now: from hU_le_VL + hwidth_eq + hVR_le_W, we get fourU = fourVL ∧ fourW = fourVR.
  -- Specifically: fourW - fourU = fourVR - fourVL means fourVR - fourU ≥ fourW - fourU = fourVR - fourVL.
  -- Wait. We have fourU ≤ fourVL and fourW ≥ fourVR.
  --   fourW - fourU ≥ fourVR - fourVL (from those).
  -- We also know fourW - fourU ≤ fourVR - fourVL.
  -- So equality and individual equality:
  --   fourW - fourU = fourVR - fourVL.
  --   fourW = fourVR + (fourU - fourVL) ≤ fourVR + 0 = fourVR.
  -- Combined with hVR_le_W: fourW = fourVR ∧ fourU = fourVL.
  have hU_eq : fourU s q k = fourVL m q k (isIrregular m q) := by omega
  have hW_eq : fourW s q k = fourVR m q k := by omega
  -- Now the "even" sides of failure say `¬ (fourVL = fourU ∧ m % 2 = 0)`
  -- and `¬ (fourW = fourVR ∧ m % 2 = 0)`.
  -- Since fourU = fourVL and fourW = fourVR, both reduce to `¬ m % 2 = 0`, i.e. m is odd.
  have hm_odd : m % 2 ≠ 0 := by
    intro heven
    apply hU_eq_VL_or_odd
    refine ⟨hU_eq.symm, heven⟩
  -- Now use the width equality to derive a contradiction.
  have hwidth_concrete : 4 * (tenPosPow k : Int) * (twoNegPow q : Int)
                          = (if isIrregular m q then 3 else 4 : Int)
                              * (twoPosPow q : Int) * (tenNegPow k : Int) := by
    have h1 := fourW_sub_fourU s q k
    have h2 := fourVR_sub_fourVL m q k
    omega
  by_cases h_irreg : isIrregular m q = true
  · -- Irregular: 4 * 10^k * 2^-q = 3 * 2^q * 10^-k. Contradiction via mod 3.
    rw [if_pos h_irreg] at hwidth_concrete
    exact irreg_width_eq_impossible q k hwidth_concrete
  · -- Regular: 4 * 10^k * 2^-q = 4 * 2^q * 10^-k. So 10^k * 2^-q = 2^q * 10^-k.
    -- This forces q = 0 ∧ k = 0.
    rw [if_neg h_irreg] at hwidth_concrete
    -- Cancel the 4.
    have h_reg_eq : (tenPosPow k : Int) * (twoNegPow q : Int)
                      = (twoPosPow q : Int) * (tenNegPow k : Int) := by
      have h_re : 4 * ((tenPosPow k : Int) * (twoNegPow q : Int))
                  = 4 * ((twoPosPow q : Int) * (tenNegPow k : Int)) := by
        rw [← Int.mul_assoc, ← Int.mul_assoc]
        exact hwidth_concrete
      exact Int.eq_of_mul_eq_mul_left (by decide) h_re
    have ⟨hq0, hk0⟩ := reg_width_eq_forces_zero q k h_reg_eq
    -- Now q = 0 ∧ k = 0. Then fourU = 4s, fourVL = 4m - 2 (regular), fourW = 4(s+1), fourVR = 4m + 2.
    -- And hU_eq says 4s = 4m - 2, hW_eq says 4(s+1) = 4m + 2.
    -- Both give 4s = 4m - 2, impossible mod 4: LHS ≡ 0, RHS ≡ 2 (mod 4).
    subst hq0
    -- hk0 says kOfMQ m 0 = 0. We have k := kOfMQ m q := kOfMQ m 0.
    -- Now we need to actually use this. Let's directly compute fourU and fourVL at q=0, k=0.
    have hfourU_concrete : fourU s 0 0 = 4 * (s : Int) := by
      unfold fourU cmpScaledMixed.rhs
      simp
    have hfourVL_concrete_reg : fourVL m 0 0 (isIrregular m 0)
                                  = 4 * (m : Int) - 2 := by
      rw [fourVL_eq_regular m 0 0 h_irreg]
      simp
    have h_at_zero : k = 0 := hk0
    -- Substitute and conclude.
    rw [h_at_zero, hfourU_concrete, hfourVL_concrete_reg] at hU_eq
    -- hU_eq : 4 * s = 4 * m - 2 (in Int)
    -- 4 * s = 4 * m - 2 ↔ 4 (m - s) = 2 ↔ 2 (m - s) = 1, impossible (LHS even, RHS odd).
    omega

/-! ## Wrap-up: shortestUnsigned_mem_rv -/

/-- The main correctness theorem: `shortestUnsigned m q` returns a pair
`(sig, exp)` that lies inside the rounding interval `R_v`. -/
theorem shortestUnsigned_mem_rv (m : Nat) (q : Int)
    (hm_pos : 1 ≤ m) (hm_lt : m < 2^53)
    (hq_lo : -1074 ≤ q) (hq_hi : q ≤ 971) :
    let p := shortestUnsigned m q
    inRoundingInterval p.1 p.2 m q (isIrregular m q) = true := by
  intro p
  show inRoundingInterval (shortestUnsigned m q).1 (shortestUnsigned m q).2 m q
          (isIrregular m q) = true
  -- The R11 lemma for the fallback branches.
  have hR11 := shiftedSig_or_succ_mem_rv m q hm_pos hm_lt hq_lo hq_hi
  -- Unfold shortestUnsigned.
  unfold shortestUnsigned
  -- Case-split on `s ≥ 10`.
  by_cases h_s_big : shiftedSig m q (kOfMQ m q) ≥ 10
  · -- Shorter form attempted.
    simp only [h_s_big, if_true]
    -- Case-split on uIn (sHigh).
    by_cases h_uIn :
        inRoundingInterval (shiftedSig m q (kOfMQ m q) / 10) (kOfMQ m q + 1) m q
          (isIrregular m q) = true
    · simp only [h_uIn, if_true]
    · simp only [h_uIn]
      -- Case-split on wIn (sHigh + 1).
      by_cases h_wIn :
          inRoundingInterval (shiftedSig m q (kOfMQ m q) / 10 + 1) (kOfMQ m q + 1) m q
            (isIrregular m q) = true
      · simp only [h_wIn, if_true]
        exact h_wIn
      · simp only [h_wIn]
        -- Fallback: (pickNearer s k m q, k).
        exact pickNearer_mem_rv _ _ _ _ hR11
  · simp only [h_s_big, if_false]
    exact pickNearer_mem_rv _ _ _ _ hR11

end Srtfp.Schubfach

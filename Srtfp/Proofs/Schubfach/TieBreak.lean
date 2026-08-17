/- The tie-breaker clause of Schubfach correctness.

   `correctness_proof` (in `Srtfp/Proofs/Correctness.lean`)
   establishes that `Schubfach.toDecimal f` round-trips and is SHORTEST.
   This file supplies the machinery for the final clause: among canonical
   decimals that round-trip to `f` AND have the *same* digit length as
   the output `d`, the output is the rational closest to the exact value
   of `f`, breaking exact ties toward an even significand.

   The argument is laid out in the file in the stages described in the
   accompanying design note:

   * **(A) ℚ bridge.** `cmpScaledMixed a q b k` compares `a·2^q` with
     `b·10^k` as rationals. We lift the existing *integer* trichotomy
     (`cmpScaledMixed_lt_iff` etc., cleared-denominator form) to genuine
     ℚ inequalities `(a:ℚ)·2^q < (b:ℚ)·10^k`.

   * **(B) ℚ closeness.** For `v = m·2^q` and the two grid neighbours
     `u = s·10^k`, `w = (s+1)·10^k`, "closer to `u`" (`|v-u| < |v-w|`)
     is equivalent to `2v < u+w`, which the bridge connects to
     `CloserToLower`. Symmetrically for `CloserToUpper` / `Equidistant`. -/

import Srtfp.Proofs.CorrectnessSpec
import Srtfp.Proofs.Schubfach.PickNearer
import Srtfp.Proofs.Schubfach.Minimal
import Srtfp.Proofs.Clinger
import Srtfp.Tactics

open Srtfp.Compat

namespace Srtfp

-- `Decimal.toRat`, `Schubfach.magVal`, `Schubfach.floatVal` are the
-- spec-level rational-value definitions from
-- `Srtfp.Proofs.CorrectnessSpec` (imported above).

namespace Schubfach

/-! ## (A) ℚ bridge for `cmpScaledMixed`

We show that the integer cleared-denominator comparison
`cmpScaledMixed.lhs a q k  ⋚  cmpScaledMixed.rhs b q k` agrees with the
genuine rational comparison `(a:ℚ)·2^q ⋚ (b:ℚ)·10^k`.

The proof multiplies the rational goal by the common positive factor
`2^{max(-q,0)} · 10^{max(-k,0)}`, which clears both `zpow` denominators
and produces exactly `lhs` vs `rhs`. -/

/-- The common positive denominator-clearing factor for scale `(q,k)`:
`2^{max(-q,0)} · 10^{max(-k,0)}` as a rational. -/
private noncomputable def clearFactor (q k : Int) : ℚ :=
  (2 : ℚ) ^ (if q < 0 then (-q).toNat else 0)
    * (10 : ℚ) ^ (if k < 0 then (-k).toNat else 0)

private theorem clearFactor_pos (q k : Int) : 0 < clearFactor q k := by
  unfold clearFactor
  apply Rat.mul_pos <;> (apply Rat.pow_pos; decide)

/-- `b^q · b^{max(-q,0)} = b^{max(q,0)}` as rationals, for nonzero `b`. -/
private theorem zpow_split_gen (b : ℚ) (hb : b ≠ 0) (q : Int) :
    b ^ q * b ^ (if q < 0 then (-q).toNat else 0)
      = b ^ (if q ≥ 0 then q.toNat else 0) := by
  by_cases hq : q < 0
  · rw [if_pos hq, if_neg (by omega : ¬ q ≥ 0)]
    rw [← Rat.zpow_natCast b (-q).toNat, Int.toNat_of_nonneg (by omega : (0:Int) ≤ -q),
        ← Rat.zpow_add hb]
    rw [show q + -q = 0 from by omega, Rat.zpow_zero]
    exact (Rat.pow_zero b).symm
  · rw [if_neg hq, if_pos (by omega : q ≥ 0)]
    rw [← Rat.zpow_natCast b q.toNat, Int.toNat_of_nonneg (by omega : (0:Int) ≤ q)]
    simp

/-- `2^q · 2^{max(-q,0)} = 2^{max(q,0)}` as rationals. -/
private theorem zpow_two_split (q : Int) :
    (2 : ℚ) ^ q * (2 : ℚ) ^ (if q < 0 then (-q).toNat else 0)
      = (2 : ℚ) ^ (if q ≥ 0 then q.toNat else 0) :=
  zpow_split_gen 2 (by grind) q

/-- `10^k · 10^{max(-k,0)} = 10^{max(k,0)}` as rationals. -/
private theorem zpow_ten_split (k : Int) :
    (10 : ℚ) ^ k * (10 : ℚ) ^ (if k < 0 then (-k).toNat else 0)
      = (10 : ℚ) ^ (if k ≥ 0 then k.toNat else 0) :=
  zpow_split_gen 10 (by grind) k

/-- Multiplying `(a:ℚ)·2^q` by the clearing factor yields `(lhs : ℚ)`. -/
private theorem lhs_eq_clear (a : Int) (q k : Int) :
    (cmpScaledMixed.lhs a q k : ℚ)
      = ((a : ℚ) * (2 : ℚ) ^ q) * clearFactor q k := by
  unfold cmpScaledMixed.lhs clearFactor
  push_cast
  have h2 := zpow_two_split q
  calc (a : ℚ) * (2 : ℚ) ^ (if q ≥ 0 then q.toNat else 0)
          * (10 : ℚ) ^ (if k < 0 then (-k).toNat else 0)
      = (a : ℚ) * ((2 : ℚ) ^ q * (2 : ℚ) ^ (if q < 0 then (-q).toNat else 0))
          * (10 : ℚ) ^ (if k < 0 then (-k).toNat else 0) := by rw [h2]
    _ = (a : ℚ) * (2 : ℚ) ^ q
          * ((2 : ℚ) ^ (if q < 0 then (-q).toNat else 0)
             * (10 : ℚ) ^ (if k < 0 then (-k).toNat else 0)) := by grind

/-- Multiplying `(b:ℚ)·10^k` by the clearing factor yields `(rhs : ℚ)`. -/
private theorem rhs_eq_clear (b : Int) (q k : Int) :
    (cmpScaledMixed.rhs b q k : ℚ)
      = ((b : ℚ) * (10 : ℚ) ^ k) * clearFactor q k := by
  unfold cmpScaledMixed.rhs clearFactor
  push_cast
  have h10 := zpow_ten_split k
  calc (b : ℚ) * (10 : ℚ) ^ (if k ≥ 0 then k.toNat else 0)
          * (2 : ℚ) ^ (if q < 0 then (-q).toNat else 0)
      = (b : ℚ) * ((10 : ℚ) ^ k * (10 : ℚ) ^ (if k < 0 then (-k).toNat else 0))
          * (2 : ℚ) ^ (if q < 0 then (-q).toNat else 0) := by rw [h10]
    _ = (b : ℚ) * (10 : ℚ) ^ k
          * ((2 : ℚ) ^ (if q < 0 then (-q).toNat else 0)
             * (10 : ℚ) ^ (if k < 0 then (-k).toNat else 0)) := by grind

/-- **(A) ℚ bridge, `<` direction.** The integer cleared comparison equals
the rational comparison `(a:ℚ)·2^q < (b:ℚ)·10^k`. -/
theorem cmpScaledMixed_lhs_lt_rhs_iff_rat (a : Int) (q : Int) (b : Int) (k : Int) :
    cmpScaledMixed.lhs a q k < cmpScaledMixed.rhs b q k
      ↔ (a : ℚ) * (2 : ℚ) ^ q < (b : ℚ) * (10 : ℚ) ^ k := by
  rw [show (cmpScaledMixed.lhs a q k < cmpScaledMixed.rhs b q k)
        ↔ (cmpScaledMixed.lhs a q k : ℚ) < (cmpScaledMixed.rhs b q k : ℚ) from
        Int.cast_lt.symm]
  rw [lhs_eq_clear, rhs_eq_clear]
  exact mul_lt_mul_iff_of_pos_right (clearFactor_pos q k)

/-- **(A) ℚ bridge, `=` direction.** -/
theorem cmpScaledMixed_lhs_eq_rhs_iff_rat (a : Int) (q : Int) (b : Int) (k : Int) :
    cmpScaledMixed.lhs a q k = cmpScaledMixed.rhs b q k
      ↔ (a : ℚ) * (2 : ℚ) ^ q = (b : ℚ) * (10 : ℚ) ^ k := by
  rw [show (cmpScaledMixed.lhs a q k = cmpScaledMixed.rhs b q k)
        ↔ (cmpScaledMixed.lhs a q k : ℚ) = (cmpScaledMixed.rhs b q k : ℚ) from
        Int.cast_inj.symm]
  rw [lhs_eq_clear, rhs_eq_clear]
  exact mul_left_inj' (Rat.ne_of_gt (clearFactor_pos q k))

/-- **(A) ℚ bridge, `>` direction.** -/
theorem cmpScaledMixed_lhs_gt_rhs_iff_rat (a : Int) (q : Int) (b : Int) (k : Int) :
    cmpScaledMixed.lhs a q k > cmpScaledMixed.rhs b q k
      ↔ (a : ℚ) * (2 : ℚ) ^ q > (b : ℚ) * (10 : ℚ) ^ k := by
  rw [gt_iff_lt, gt_iff_lt]
  rw [show (cmpScaledMixed.rhs b q k < cmpScaledMixed.lhs a q k)
        ↔ (cmpScaledMixed.rhs b q k : ℚ) < (cmpScaledMixed.lhs a q k : ℚ) from
        Int.cast_lt.symm]
  rw [lhs_eq_clear, rhs_eq_clear]
  exact mul_lt_mul_iff_of_pos_right (clearFactor_pos q k)

/-! ## (B) ℚ closeness ↔ `cmp` predicates

For the value `v = magVal m q`, write the two adjacent decimal grid
neighbours at scale `k` as `gridVal s k = s · 10^k`. The relation
"`v` is strictly closer to `gridVal s k` than to `gridVal (s+1) k`" is
exactly `|v - u| < |v - w|`, and for `u < w` this reduces to
`2v < u + w`, i.e. `2m·2^q < (2s+1)·10^k`. We connect each such
"closeness" statement to the corresponding `CloserTo*` / `Equidistant`
predicate from `PickNearer.lean`. -/

/-- The rational value of the decimal grid point `s · 10^k`. -/
def gridVal (s : Nat) (k : Int) : ℚ := (s : ℚ) * (10 : ℚ) ^ k

theorem gridVal_lt_succ (s : Nat) (k : Int) : gridVal s k < gridVal (s + 1) k := by
  unfold gridVal
  have hpos : (0 : ℚ) < (10 : ℚ) ^ k := Rat.zpow_pos (by decide)
  push_cast
  have : (s : ℚ) < (s : ℚ) + 1 := by grind
  exact (mul_lt_mul_iff_of_pos_right hpos).mpr this

/-- **Scale-shift of a grid point.** Multiplying the significand by `10^j` and
lowering the scale by `j` leaves the value unchanged:
`gridVal (s · 10^j) k = gridVal s (k + j)`. -/
theorem gridVal_mul_pow10 (s : Nat) (j : Nat) (k : Int) :
    gridVal (s * 10 ^ j) k = gridVal s (k + (j : Int)) := by
  unfold gridVal
  push_cast
  rw [Rat.zpow_add (by grind : (10 : ℚ) ≠ 0) k (j : Int), Rat.zpow_natCast]
  grind

/-- Midpoint identity: `gridVal s k + gridVal (s+1) k = (2s+1)·10^k`. -/
private theorem gridVal_add_succ (s : Nat) (k : Int) :
    gridVal s k + gridVal (s + 1) k = ((2 * (s : Int) + 1 : Int) : ℚ) * (10 : ℚ) ^ k := by
  unfold gridVal; push_cast; grind

/-- `2·magVal = (2m)·2^q` as the bridge's left-hand side. -/
private theorem two_magVal_eq (m : Nat) (q : Int) :
    2 * magVal m q = ((2 * (m : Int) : Int) : ℚ) * (2 : ℚ) ^ q := by
  unfold magVal; push_cast; grind

/-- **Elementary closeness fact.** For `u < w`, `v` is strictly closer to
`u` than to `w` iff `v` is strictly below the midpoint, i.e. `2v < u + w`. -/
theorem abs_lt_abs_iff_two_lt (v u w : ℚ) (h : u < w) :
    |v - u| < |v - w| ↔ 2 * v < u + w := by
  rw [abs_lt_iff_mul_self_lt]
  have hkey : (v - w) * (v - w) - (v - u) * (v - u) = (w - u) * ((u + w) - 2 * v) := by
    grind
  have hwu : (0 : ℚ) < w - u := by grind
  constructor
  · intro hsq
    have hpos : 0 < (w - u) * ((u + w) - 2 * v) := by grind
    have := (Rat.mul_pos_iff_of_pos_left hwu).mp hpos
    grind
  · intro hmid
    have hX : (0 : ℚ) < (u + w) - 2 * v := by grind
    have := Rat.mul_pos hwu hX
    grind

/-- Symmetric: closer to `w` iff above the midpoint. -/
theorem abs_gt_abs_iff_two_gt (v u w : ℚ) (h : u < w) :
    |v - w| < |v - u| ↔ u + w < 2 * v := by
  rw [abs_lt_iff_mul_self_lt]
  have hkey : (v - u) * (v - u) - (v - w) * (v - w) = (w - u) * (2 * v - (u + w)) := by
    grind
  have hwu : (0 : ℚ) < w - u := by grind
  constructor
  · intro hsq
    have hpos : 0 < (w - u) * (2 * v - (u + w)) := by grind
    have := (Rat.mul_pos_iff_of_pos_left hwu).mp hpos
    grind
  · intro hmid
    have hX : (0 : ℚ) < 2 * v - (u + w) := by grind
    have := Rat.mul_pos hwu hX
    grind

/-- Equidistance iff exactly at the midpoint. -/
theorem abs_eq_abs_iff_two_eq (v u w : ℚ) (h : u < w) :
    |v - u| = |v - w| ↔ 2 * v = u + w := by
  rw [abs_eq_iff_mul_self_eq]
  have hwu : w - u ≠ 0 := by grind
  constructor
  · intro hsq
    have hfact : (2 * v - (u + w)) * (w - u) = 0 := by grind
    rcases Rat.mul_eq_zero.mp hfact with h1 | h1
    · grind
    · exact absurd h1 hwu
  · intro hmid; grind

/-- **(B) CloserToLower bridge.** `v = magVal m q` is strictly closer to
`gridVal s k` than to `gridVal (s+1) k` iff `CloserToLower s k m q`. -/
theorem closer_lower_iff_rat (s : Nat) (k : Int) (m : Nat) (q : Int) :
    |magVal m q - gridVal s k| < |magVal m q - gridVal (s + 1) k|
      ↔ CloserToLower s k m q := by
  rw [abs_lt_abs_iff_two_lt _ _ _ (gridVal_lt_succ s k), gridVal_add_succ,
      two_magVal_eq]
  unfold CloserToLower
  exact (cmpScaledMixed_lhs_lt_rhs_iff_rat _ q _ k).symm

/-- **(B) CloserToUpper bridge.** -/
theorem closer_upper_iff_rat (s : Nat) (k : Int) (m : Nat) (q : Int) :
    |magVal m q - gridVal (s + 1) k| < |magVal m q - gridVal s k|
      ↔ CloserToUpper s k m q := by
  rw [abs_gt_abs_iff_two_gt _ _ _ (gridVal_lt_succ s k), gridVal_add_succ,
      two_magVal_eq]
  unfold CloserToUpper
  rw [gt_iff_lt]
  exact (cmpScaledMixed_lhs_gt_rhs_iff_rat _ q _ k).symm

/-- **(B) Equidistant bridge.** -/
theorem equidistant_iff_rat (s : Nat) (k : Int) (m : Nat) (q : Int) :
    |magVal m q - gridVal s k| = |magVal m q - gridVal (s + 1) k|
      ↔ Equidistant s k m q := by
  rw [abs_eq_abs_iff_two_eq _ _ _ (gridVal_lt_succ s k), gridVal_add_succ,
      two_magVal_eq]
  unfold Equidistant
  exact (cmpScaledMixed_lhs_eq_rhs_iff_rat _ q _ k).symm

/-! ## (C) pickNearer distance lift

When both grid neighbours `s, s+1` lie in `R_v`, `pickNearer` returns the
one whose grid value is the rational nearer to `v = magVal m q`, breaking
exact ties toward the candidate with an *even* significand. We lift the
integer-comparison statement `pickNearer_closer_or_tie_even` into the
genuine ℚ distance statement, expressed against the *other* neighbour. -/

/-- **(C)** With both neighbours in `R_v`, the `pickNearer` output `pn`
satisfies, against the *other* neighbour `other ∈ {s, s+1} \ {pn}`:
either `pn`'s grid value is strictly closer to `v`, or it is an exact
tie and `pn` is even. -/
theorem pickNearer_grid_closer_or_tie_even (s : Nat) (k : Int) (m : Nat) (q : Int)
    (h_both : inRoundingInterval s k m q (isIrregular m q) = true ∧
              inRoundingInterval (s + 1) k m q (isIrregular m q) = true) :
    ∃ pn other : Nat,
      pickNearer s k m q = pn ∧
      (pn = s ∧ other = s + 1 ∨ pn = s + 1 ∧ other = s) ∧
      ( |magVal m q - gridVal pn k| < |magVal m q - gridVal other k|
        ∨ ( |magVal m q - gridVal pn k| = |magVal m q - gridVal other k|
            ∧ pn % 2 = 0 ) ) := by
  rcases pickNearer_closer_or_tie_even s k m q h_both with
    ⟨hcl, hpn⟩ | ⟨hcu, hpn⟩ | ⟨heq, hpar⟩
  · -- CloserToLower, pn = s.
    refine ⟨s, s + 1, hpn, Or.inl ⟨rfl, rfl⟩, Or.inl ?_⟩
    exact (closer_lower_iff_rat s k m q).mpr hcl
  · -- CloserToUpper, pn = s+1.
    refine ⟨s + 1, s, hpn, Or.inr ⟨rfl, rfl⟩, Or.inl ?_⟩
    exact (closer_upper_iff_rat s k m q).mpr hcu
  · -- Equidistant; pn is the even neighbour.
    have h_eqdist : |magVal m q - gridVal s k| = |magVal m q - gridVal (s + 1) k| :=
      (equidistant_iff_rat s k m q).mpr heq
    rcases hpar with ⟨hpn, hpar⟩ | ⟨hpn, hpar⟩
    · -- pn = s, s even.
      refine ⟨s, s + 1, hpn, Or.inl ⟨rfl, rfl⟩, Or.inr ⟨h_eqdist, hpar⟩⟩
    · -- pn = s+1, s odd ⇒ s+1 even.
      refine ⟨s + 1, s, hpn, Or.inr ⟨rfl, rfl⟩, Or.inr ⟨h_eqdist.symm, ?_⟩⟩
      omega

/-! ## (E) Nearest-grid: the floor neighbour `s = shiftedSig` brackets `v`

`s = shiftedSig m q k` is `⌊v / 10^k⌋`, so `v ∈ [s·10^k, (s+1)·10^k]`.
Therefore the two grid neighbours `s, s+1` are the two grid points
closest to `v`; any other grid point `sig' ∉ {s, s+1}` is *strictly*
farther from `v` than both of them (by at least one whole grid step). -/

/-- A `≤` form of the (A) bridge: `gridVal s k ≤ magVal m q` iff the
cleared integer comparison `fourU` ≤ `fourV`. -/
private theorem gridVal_le_magVal_iff (s : Nat) (k : Int) (m : Nat) (q : Int) :
    fourU s q k ≤ fourV m q k ↔ gridVal s k ≤ magVal m q := by
  unfold fourU fourV
  rw [← Int.not_lt]
  rw [cmpScaledMixed_lhs_lt_rhs_iff_rat (4 * (m : Int)) q (4 * (s : Int)) k]
  unfold gridVal magVal
  constructor
  · intro h
    -- ¬((4m)·2^q < (4s)·10^k) ⇒ (4s)·10^k ≤ (4m)·2^q ⇒ s·10^k ≤ m·2^q
    rw [not_lt] at h
    push_cast at h
    grind
  · intro h
    rw [not_lt]
    push_cast
    grind

/-- The value `v = magVal m q` is bracketed by its floor neighbour:
`gridVal s k ≤ v < gridVal (s+1) k` for `s = shiftedSig m q k`. -/
theorem magVal_bracket (m : Nat) (q : Int) (k : Int) (s : Nat)
    (hs : s = shiftedSig m q k) :
    gridVal s k ≤ magVal m q ∧ magVal m q < gridVal (s + 1) k := by
  refine ⟨?_, ?_⟩
  · exact (gridVal_le_magVal_iff s k m q).mp (fourU_le_fourV s m q k hs)
  · -- magVal m q < gridVal (s+1) k, from fourV < fourW = fourU (s+1).
    have h := fourV_lt_fourW s m q k hs
    -- fourV < fourW s = fourU (s+1).
    have hfw : fourW s q k = fourU (s + 1) q k := by
      rw [fourW_eq, fourU_eq]; push_cast; grind
    rw [hfw] at h
    -- fourV < fourU (s+1) ⇒ ¬ (fourU(s+1) ≤ fourV) ⇒ ¬ (gridVal(s+1) ≤ magVal) ⇒ magVal < gridVal(s+1).
    have h2 : ¬ (gridVal (s + 1) k ≤ magVal m q) := by
      rw [← gridVal_le_magVal_iff (s + 1) k m q]; omega
    exact lt_of_not_ge h2

/-- **(E) nearest-grid (strict-far direction).** With `s = shiftedSig m q k`,
a grid point `sig'` below the floor neighbour (`sig' ≤ s - 1`) is strictly
farther from `v` than the floor neighbour `s`; one above the ceiling
(`sig' ≥ s + 2`) is strictly farther than the ceiling neighbour `s+1`. -/
theorem grid_far_of_outside (m : Nat) (q : Int) (k : Int) (s sig' : Nat)
    (hs : s = shiftedSig m q k) :
    (sig' + 1 ≤ s → |magVal m q - gridVal s k| < |magVal m q - gridVal sig' k|)
      ∧ (s + 2 ≤ sig' → |magVal m q - gridVal (s + 1) k| < |magVal m q - gridVal sig' k|) := by
  obtain ⟨h_lo, h_hi⟩ := magVal_bracket m q k s hs
  have hstep_pos : (0 : ℚ) < (10 : ℚ) ^ k := Rat.zpow_pos (by decide)
  refine ⟨?_, ?_⟩
  · intro h_below
    -- sig' ≤ s - 1, so gridVal sig' k ≤ gridVal s k - 10^k.
    have h_sig_le : gridVal sig' k ≤ gridVal s k - (10 : ℚ) ^ k := by
      have h1 : gridVal s k - gridVal sig' k = ((s : ℚ) - (sig' : ℚ)) * (10:ℚ)^k := by
        unfold gridVal; grind
      have hsig : (1 : ℚ) ≤ (s : ℚ) - (sig' : ℚ) := by
        have : (sig' : ℚ) + 1 ≤ (s : ℚ) := by exact_mod_cast h_below
        grind
      have hmono : 1 * (10:ℚ)^k ≤ ((s : ℚ) - (sig' : ℚ)) * (10:ℚ)^k :=
        Rat.mul_le_mul_of_nonneg_right hsig (Rat.le_of_lt hstep_pos)
      grind
    have h_abs_sig : |magVal m q - gridVal sig' k| = magVal m q - gridVal sig' k :=
      abs_of_nonneg (by grind)
    have h_abs_s : |magVal m q - gridVal s k| = magVal m q - gridVal s k :=
      abs_of_nonneg (by grind)
    rw [h_abs_s, h_abs_sig]; grind
  · intro h_above
    -- sig' ≥ s + 2, so gridVal sig' k ≥ gridVal (s+1) k + 10^k.
    have h_sig_ge : gridVal (s + 1) k + (10 : ℚ) ^ k ≤ gridVal sig' k := by
      have h1 : gridVal sig' k - gridVal (s + 1) k
          = ((sig' : ℚ) - ((s : ℚ) + 1)) * (10:ℚ)^k := by
        unfold gridVal; push_cast; grind
      have hsig : (1 : ℚ) ≤ (sig' : ℚ) - ((s : ℚ) + 1) := by
        have : ((s : ℚ) + 1) + 1 ≤ (sig' : ℚ) := by exact_mod_cast h_above
        grind
      have hmono : 1 * (10:ℚ)^k ≤ ((sig' : ℚ) - ((s : ℚ) + 1)) * (10:ℚ)^k :=
        Rat.mul_le_mul_of_nonneg_right hsig (Rat.le_of_lt hstep_pos)
      grind
    have h_s1_val : gridVal (s + 1) k = gridVal s k + (10:ℚ)^k := by
      unfold gridVal; push_cast; grind
    have h_v_lt_sig : magVal m q < gridVal sig' k := by grind
    have h_v_lt_s1 : magVal m q < gridVal (s + 1) k := h_hi
    have h_abs_sig : |magVal m q - gridVal sig' k| = gridVal sig' k - magVal m q := by
      rw [abs_of_nonpos (by grind)]; grind
    have h_abs_s1 : |magVal m q - gridVal (s + 1) k| = gridVal (s + 1) k - magVal m q := by
      rw [abs_of_nonpos (by grind)]; grind
    rw [h_abs_s1, h_abs_sig]; grind

/-! ## (C+E) Scale-K tie-break: the unsigned clause (3)

Assembling (C) and (E): in the fallback branch (both neighbours `s, s+1`
of the floor value `s = shiftedSig m q k` in `R_v`, output `pn`), any
scale-`k` competitor `sig'` in `R_v` is either equal to `pn` (the
output), strictly farther from `v`, or an exact tie with `pn` even. -/

/-- **(C+E)** Unsigned clause (3) at the fallback scale `k`. For the floor
neighbour `s = shiftedSig m q k` with both `s, s+1 ∈ R_v`, the output
`pn = pickNearer s k m q` is, against *any* grid point `sig'`, either equal,
strictly closer to `v`, or an exact tie with `pn` even. (The geometry alone
suffices — `R_v` membership of `sig'` is not needed.) -/
theorem tieBreak_unsigned_fallback (m : Nat) (q : Int)
    (k : Int) (s : Nat) (hs : s = shiftedSig m q k)
    (h_s : inRoundingInterval s k m q (isIrregular m q) = true)
    (h_s1 : inRoundingInterval (s + 1) k m q (isIrregular m q) = true)
    (sig' : Nat) :
    let pn := pickNearer s k m q
    sig' = pn
      ∨ |magVal m q - gridVal pn k| < |magVal m q - gridVal sig' k|
      ∨ ( |magVal m q - gridVal pn k| = |magVal m q - gridVal sig' k|
          ∧ pn % 2 = 0 ) := by
  intro pn
  -- (C): pn is closer-or-tie-even vs the OTHER of {s, s+1}.
  obtain ⟨pn', other, h_pn_eq, h_pn_other, h_pn_dist⟩ :=
    pickNearer_grid_closer_or_tie_even s k m q ⟨h_s, h_s1⟩
  have h_pn'_eq : pn' = pn := by rw [← h_pn_eq]
  subst h_pn'_eq
  -- Case on where sig' sits relative to s.
  by_cases h_eq_pn : sig' = pn
  · exact Or.inl h_eq_pn
  · -- sig' ≠ pn. Determine if sig' = other (∈ {s,s+1}) or outside {s,s+1}.
    obtain ⟨h_below, h_above⟩ := grid_far_of_outside m q k s sig' hs
    rcases h_pn_other with ⟨h_pns, h_oth⟩ | ⟨h_pns1, h_oth⟩
    · -- pn = s, other = s+1. Normalise h_pn_dist to s vs s+1.
      rw [h_pns, h_oth] at h_pn_dist
      rw [h_pns]
      by_cases h_sig_other : sig' = s + 1
      · right; rw [h_sig_other]; exact h_pn_dist
      · -- sig' ∉ {s, s+1}: sig' ≤ s-1 or sig' ≥ s+2.
        have h_out : sig' + 1 ≤ s ∨ s + 2 ≤ sig' := by omega
        right; left
        rcases h_out with hb | ha
        · exact h_below hb
        · -- dist(s) ≤ dist(s+1) (from C) < dist(sig').
          have h_s_le_s1 : |magVal m q - gridVal s k| ≤ |magVal m q - gridVal (s + 1) k| := by
            rcases h_pn_dist with hlt | ⟨heq, _⟩
            · exact le_of_lt hlt
            · exact le_of_eq heq
          exact lt_of_le_of_lt h_s_le_s1 (h_above ha)
    · -- pn = s+1, other = s.
      rw [h_pns1, h_oth] at h_pn_dist
      rw [h_pns1]
      by_cases h_sig_other : sig' = s
      · right; rw [h_sig_other]; exact h_pn_dist
      · have h_out : sig' + 1 ≤ s ∨ s + 2 ≤ sig' := by omega
        right; left
        rcases h_out with hb | ha
        · -- dist(s+1) ≤ dist(s) (from C) < dist(sig').
          have h_s1_le_s : |magVal m q - gridVal (s + 1) k| ≤ |magVal m q - gridVal s k| := by
            rcases h_pn_dist with hlt | ⟨heq, _⟩
            · exact le_of_lt hlt
            · exact le_of_eq heq
          exact lt_of_le_of_lt h_s1_le_s (h_below hb)
        · exact h_above ha

/-- **Single-sided scale-`k` tie-break.** When exactly one of the floor
neighbours `s, s+1` (with `s = shiftedSig m q k`) lies in `R_v`, that one
(`out`) is the *unique* scale-`k` grid point in `R_v` among the two
candidates: any competitor `sig'` *confined to* `{s, s+1}` and in `R_v`
must equal `out`.

The "confined to {s, s+1}" hypothesis is supplied by the caller — at the
shorter-form scale `k+1` it comes from `Schubfach_K1_candidates`. We do
NOT attempt the (false in general at scale `k`) claim that membership
alone forces `sig' ∈ {s, s+1}`. -/
theorem tieBreak_unsigned_single_sided (m : Nat) (q : Int)
    (k : Int) (s : Nat) (out : Nat)
    (h_out : out = s ∨ out = s + 1)
    (h_other_not : (out = s → inRoundingInterval (s + 1) k m q (isIrregular m q) = false)
                 ∧ (out = s + 1 → inRoundingInterval s k m q (isIrregular m q) = false))
    (sig' : Nat)
    (h_sig'_cands : sig' = s ∨ sig' = s + 1)
    (h_sig'_mem : inRoundingInterval sig' k m q (isIrregular m q) = true) :
    sig' = out := by
  rcases h_out with h_os | h_os1
  · -- out = s; s+1 ∉ R_v, so sig' can't be s+1 ⇒ sig' = s = out.
    subst h_os
    have h_s1_not := h_other_not.1 rfl
    rcases h_sig'_cands with h | h
    · exact h
    · exfalso; rw [h] at h_sig'_mem; rw [h_s1_not] at h_sig'_mem; exact absurd h_sig'_mem (by decide)
  · -- out = s+1; s ∉ R_v, so sig' can't be s ⇒ sig' = s+1 = out.
    subst h_os1
    have h_s_not := h_other_not.2 rfl
    rcases h_sig'_cands with h | h
    · exfalso; rw [h] at h_sig'_mem; rw [h_s_not] at h_sig'_mem; exact absurd h_sig'_mem (by decide)
    · exact h

/-- **Scale-`k` tie-break against `R_v` competitors.** With `s = shiftedSig m q k`
and `out = pickNearer s k m q`, *any* competitor `sig'` that itself lies in
`R_v` (at scale `k`) is the output, strictly farther from `v`, or an exact
tie with `out` even. Unlike `tieBreak_unsigned_fallback`, this does NOT
require both `s, s+1 ∈ R_v` — when only one neighbour is in `R_v`, the
in-`R_v` competitor cannot be the excluded sibling, so it is either `out`
itself or strictly outside `{s, s+1}` (hence strictly farther by
`grid_far_of_outside_both`). -/
theorem tieBreak_unsigned_scaleK_pn (m : Nat) (q : Int)
    (k : Int) (s : Nat) (hs : s = shiftedSig m q k)
    (h_one : inRoundingInterval s k m q (isIrregular m q) = true ∨
             inRoundingInterval (s + 1) k m q (isIrregular m q) = true)
    (sig' : Nat)
    (h_sig'_mem : inRoundingInterval sig' k m q (isIrregular m q) = true) :
    let pn := pickNearer s k m q
    sig' = pn
      ∨ |magVal m q - gridVal pn k| < |magVal m q - gridVal sig' k|
      ∨ ( |magVal m q - gridVal pn k| = |magVal m q - gridVal sig' k|
          ∧ pn % 2 = 0 ) := by
  intro pn
  by_cases h_both : inRoundingInterval s k m q (isIrregular m q) = true ∧
                    inRoundingInterval (s + 1) k m q (isIrregular m q) = true
  · -- Both in R_v: the strong geometric tie-break covers all sig'.
    exact tieBreak_unsigned_fallback m q k s hs h_both.1 h_both.2 sig'
  · -- Single-sided: pn is the in-R_v neighbour; sig' ≠ excluded sibling, and
    -- by R_v connectedness sig' cannot lie *across* the excluded sibling either.
    obtain ⟨h_below, h_above⟩ := grid_far_of_outside m q k s sig' hs
    rcases h_one with h_s | h_s1
    · -- s ∈ R_v, s+1 ∉ R_v (since not both).
      have h_s1_not : inRoundingInterval (s + 1) k m q (isIrregular m q) = false := by
        rcases Bool.eq_false_or_eq_true (inRoundingInterval (s + 1) k m q (isIrregular m q)) with h | h
        · exact absurd ⟨h_s, h⟩ h_both
        · exact h
      have h_pn_s : pn = s := by
        show pickNearer s k m q = s
        simp [pickNearer, h_s, h_s1_not]
      rw [h_pn_s]
      by_cases h_eq : sig' = s
      · exact Or.inl h_eq
      · right; left
        -- sig' ≠ s+1 (∉ R_v); and sig' ≥ s+2 is impossible by connectedness
        -- (would force s+1 ∈ R_v between s and sig'). So sig' ≤ s-1.
        have h_sig_ne_s1 : sig' ≠ s + 1 := by
          intro h; rw [h] at h_sig'_mem; rw [h_s1_not] at h_sig'_mem; exact absurd h_sig'_mem (by decide)
        have h_not_above : ¬ s + 2 ≤ sig' := by
          intro ha
          have h_s1_in : inRoundingInterval (s + 1) k m q (isIrregular m q) = true :=
            inRoundingInterval_connected s (s + 1) sig' k m q (by omega) (by omega) h_s h_sig'_mem
          rw [h_s1_not] at h_s1_in; exact absurd h_s1_in (by decide)
        have hb : sig' + 1 ≤ s := by omega
        exact h_below hb
    · -- s+1 ∈ R_v, s ∉ R_v.
      have h_s_not : inRoundingInterval s k m q (isIrregular m q) = false := by
        rcases Bool.eq_false_or_eq_true (inRoundingInterval s k m q (isIrregular m q)) with h | h
        · exact absurd ⟨h, h_s1⟩ h_both
        · exact h
      have h_pn_s1 : pn = s + 1 := by
        show pickNearer s k m q = s + 1
        simp [pickNearer, h_s_not, h_s1]
      rw [h_pn_s1]
      by_cases h_eq : sig' = s + 1
      · exact Or.inl h_eq
      · right; left
        -- sig' ≠ s (∉ R_v); and sig' ≤ s-1 is impossible by connectedness
        -- (would force s ∈ R_v between sig' and s+1). So sig' ≥ s+2.
        have h_sig_ne_s : sig' ≠ s := by
          intro h; rw [h] at h_sig'_mem; rw [h_s_not] at h_sig'_mem; exact absurd h_sig'_mem (by decide)
        have h_not_below : ¬ sig' + 1 ≤ s := by
          intro hb
          have h_s_in : inRoundingInterval s k m q (isIrregular m q) = true :=
            inRoundingInterval_connected sig' s (s + 1) k m q (by omega) (by omega) h_sig'_mem h_s1
          rw [h_s_not] at h_s_in; exact absurd h_s_in (by decide)
        have ha : s + 2 ≤ sig' := by omega
        exact h_above ha

/-! ## Value of a Decimal as a signed grid point

`Decimal.toRat d` decomposes as `signFactor · gridVal d.significand d.exponent`,
and (crucially) is invariant under the trailing-zero stripping performed by
`Decimal.mk'`. -/

/-- `signFactor s = (-1)^s` as a rational. -/
def signFactor (s : Bool) : ℚ := if s then -1 else 1

theorem toRat_eq_signFactor_gridVal (d : Decimal) :
    d.toRat = signFactor d.sign * gridVal d.significand d.exponent := by
  unfold Decimal.toRat signFactor gridVal; grind

/-! ## (F) Sign handling

A canonical `d'` whose `ofDecimal` round-trips to a finite nonzero `f`
shares `f`'s sign. The proof runs through the Clinger bridge:
`decode (ofDecimal d') = decodedAbs d'.sign …`, whose `.sign` field is
`d'.sign` in every branch; combined with `decode (ofDecimal d') = decode f`
this gives `d'.sign = (decode f).sign`. -/

/-- `decodedAbs` preserves the sign field in every branch. -/
theorem decodedAbs_sign (sign : Bool) (sig : Nat) (exp : Int) :
    (Clinger.decodedAbs sign sig exp).sign = sign := by
  unfold Clinger.decodedAbs
  dsimp only
  split_ifs <;> rfl

/-- **(F)** A canonical `d'` with `IsFiniteAbs` flags whose `ofDecimal`
round-trips bitwise to `f` shares `(decode f).sign`. -/
theorem roundtrip_sign_eq (d' : Decimal) (w : UInt64)
    (h_fin : Clinger.IsFiniteAbs d'.sign d'.significand d'.exponent)
    (h_rt : Clinger.ofDecimalBits d' = w) :
    d'.sign = (Srtfp.Float.Word.decode w).sign := by
  have h_bridge : Srtfp.Float.Word.decode (Clinger.ofDecimalBits d')
      = Clinger.decodedAbs d'.sign d'.significand d'.exponent :=
    Clinger.decode_of_decimal_bridge_bits d' h_fin
  have h1 : (Srtfp.Float.Word.decode (Clinger.ofDecimalBits d')).sign = d'.sign := by
    rw [h_bridge, decodedAbs_sign]
  rw [← h1, h_rt]

/-! ## Signed-distance connector

The clause-(3) statement compares *signed* rational distances
`|Decimal.toRat d - floatVal f|`. When the decimal and the float share a
sign, the common `signFactor = ±1` factors out of the absolute value,
reducing the signed distance to the unsigned grid distance
`|magVal m q - gridVal sig exp|` for which `tieBreak_unsigned_fallback`
applies. -/

/-- `wordVal w = signFactor (Word.decode w).sign · magVal …`. -/
theorem wordVal_eq_signFactor_magVal (w : UInt64) :
    wordVal w = signFactor (Srtfp.Float.Word.decode w).sign
        * magVal (Srtfp.Float.Word.decode w).m (Srtfp.Float.Word.decode w).q := by
  unfold wordVal signFactor; rfl

/-- `|±1·a - ±1·b| = |a - b|`: the shared sign factors out of the distance. -/
theorem abs_signFactor_sub (sgn : Bool) (a b : ℚ) :
    |signFactor sgn * a - signFactor sgn * b| = |a - b| := by
  unfold signFactor
  cases sgn
  · simp
  · -- (-1)*a - (-1)*b = -(a-b); |-(a-b)| = |a-b|.
    rw [show ((if true then -1 else 1 : ℚ)) = -1 from rfl]
    rw [show (-1 : ℚ) * a - (-1) * b = -(a - b) from by grind, abs_neg]

/-- **Signed-distance reduction.** For a decimal `d'` whose sign matches
`(Srtfp.Float.Word.decode w).sign`, the signed clause-(3) distance reduces to the
unsigned grid distance against `v = magVal (Srtfp.Float.Word.decode w).m (Srtfp.Float.Word.decode
w).q`. -/
theorem toRat_dist_eq_grid_dist (d' : Decimal) (w : UInt64)
    (h_sign : d'.sign = (Srtfp.Float.Word.decode w).sign) :
    |Decimal.toRat d' - wordVal w|
      = |magVal (Srtfp.Float.Word.decode w).m (Srtfp.Float.Word.decode w).q
         - gridVal d'.significand d'.exponent| := by
  rw [toRat_eq_signFactor_gridVal, wordVal_eq_signFactor_magVal, h_sign]
  rw [show signFactor (Srtfp.Float.Word.decode w).sign
            * gridVal d'.significand d'.exponent
          - signFactor (Srtfp.Float.Word.decode w).sign
            * magVal (Srtfp.Float.Word.decode w).m (Srtfp.Float.Word.decode w).q
        = signFactor (Srtfp.Float.Word.decode w).sign
            * (gridVal d'.significand d'.exponent
               - magVal (Srtfp.Float.Word.decode w).m (Srtfp.Float.Word.decode w).q) from by
        grind]
  rw [show signFactor (Srtfp.Float.Word.decode w).sign
            * (gridVal d'.significand d'.exponent
               - magVal (Srtfp.Float.Word.decode w).m (Srtfp.Float.Word.decode w).q)
        = signFactor (Srtfp.Float.Word.decode w).sign * gridVal d'.significand d'.exponent
          - signFactor (Srtfp.Float.Word.decode w).sign
            * magVal (Srtfp.Float.Word.decode w).m (Srtfp.Float.Word.decode w).q from by grind]
  rw [abs_signFactor_sub, abs_sub_comm]

end Schubfach
end Srtfp

/- Correctness of `pickNearer` (M3.8.5).

   `pickNearer s k m q` picks one of `s · 10^k` or `(s+1) · 10^k`
   based on which is closer to `v = m · 2^q`, breaking exact ties
   by selecting the candidate with an *even* significand (banker's
   rounding, IEEE-754 roundTiesToEven).

   The definition (`Srtfp/Schubfach.lean`):

       let uIn := inRoundingInterval s k m q (isIrregular m q)
       let wIn := inRoundingInterval (s + 1) k m q (isIrregular m q)
       if uIn && !wIn then s
       else if !uIn && wIn then s + 1
       else
         let cmp := cmpScaledMixed (2m) q (2s+1) k
         if cmp < 0 then s
         else if cmp > 0 then s + 1
         else if s % 2 = 0 then s
         else s + 1

   The "closer to v" comparison is encoded directly by
   `cmpScaledMixed (2·m) q (2·s+1) k`, since the algebraic identity

       v - u  ≶  w - v   ↔   2·v  ≶  u + w
                           ↔   2·m · 2^q  ≶  (2·s + 1) · 10^k

   reduces "closer-to-which-side" to a single integer comparison after
   clearing the dyadic and decimal denominators.

   We formalise this via small `CloserToLower / CloserToUpper /
   Equidistant` predicates that capture the sign of the
   cleared-denominator difference. Downstream M3.8.6/M3.8.7 chain
   `pickNearer_mem_rv` and `pickNearer_both_in_spec` together with
   `kOfMQ_correct` and `shiftedSig_correct`.

   The only axioms used are `propext, Quot.sound, Classical.choice`. -/

import Srtfp.Proofs.Schubfach.RoundingInterval
import Srtfp.Proofs.Schubfach.K
import Srtfp.Proofs.Schubfach.ShiftedSig

namespace Srtfp.Schubfach

/-! ## `cmpScaledMixed` specification

`cmpScaledMixed a q b k` returns `-1`, `0`, or `1` according to whether
`a · 2^q` is less than, equal to, or greater than `b · 10^k` as
rationals. We extract this trichotomy in the cleared-denominator form
that all our downstream predicates use. -/

/-- The cleared-denominator left-hand side:
`a · 2^{max q 0} · 10^{max -k 0}`. -/
def cmpScaledMixed.lhs (a : Int) (q k : Int) : Int :=
  a * (2 ^ (if q ≥ 0 then q.toNat else 0) : Int)
    * (10 ^ (if k < 0 then (-k).toNat else 0) : Int)

/-- The cleared-denominator right-hand side:
`b · 10^{max k 0} · 2^{max -q 0}`. -/
def cmpScaledMixed.rhs (b : Int) (q k : Int) : Int :=
  b * (10 ^ (if k ≥ 0 then k.toNat else 0) : Int)
    * (2 ^ (if q < 0 then (-q).toNat else 0) : Int)

/-- Reify `cmpScaledMixed` as the integer comparison of `lhs` vs `rhs`. -/
theorem cmpScaledMixed_eq (a : Int) (q : Int) (b : Int) (k : Int) :
    cmpScaledMixed a q b k =
      (if cmpScaledMixed.lhs a q k < cmpScaledMixed.rhs b q k then -1
       else if cmpScaledMixed.lhs a q k = cmpScaledMixed.rhs b q k then 0
       else 1) := by
  rfl

/-- `cmpScaledMixed < 0 ↔ a · 2^q < b · 10^k` (in cleared form). -/
theorem cmpScaledMixed_lt_iff (a : Int) (q : Int) (b : Int) (k : Int) :
    cmpScaledMixed a q b k < 0 ↔
      cmpScaledMixed.lhs a q k < cmpScaledMixed.rhs b q k := by
  rw [cmpScaledMixed_eq]
  by_cases h1 : cmpScaledMixed.lhs a q k < cmpScaledMixed.rhs b q k
  · simp [h1]
  · simp [h1]
    by_cases h2 : cmpScaledMixed.lhs a q k = cmpScaledMixed.rhs b q k
    · simp [h2]
    · simp [h2]

/-- `cmpScaledMixed = 0 ↔ a · 2^q = b · 10^k` (in cleared form). -/
theorem cmpScaledMixed_eq_zero_iff (a : Int) (q : Int) (b : Int) (k : Int) :
    cmpScaledMixed a q b k = 0 ↔
      cmpScaledMixed.lhs a q k = cmpScaledMixed.rhs b q k := by
  rw [cmpScaledMixed_eq]
  by_cases h1 : cmpScaledMixed.lhs a q k < cmpScaledMixed.rhs b q k
  · simp [h1]; intro h2; omega
  · simp [h1]

/-- `cmpScaledMixed > 0 ↔ a · 2^q > b · 10^k` (in cleared form). -/
theorem cmpScaledMixed_gt_iff (a : Int) (q : Int) (b : Int) (k : Int) :
    cmpScaledMixed a q b k > 0 ↔
      cmpScaledMixed.lhs a q k > cmpScaledMixed.rhs b q k := by
  rw [cmpScaledMixed_eq]
  by_cases h1 : cmpScaledMixed.lhs a q k < cmpScaledMixed.rhs b q k
  · simp [h1]; omega
  · simp [h1]
    by_cases h2 : cmpScaledMixed.lhs a q k = cmpScaledMixed.rhs b q k
    · simp [h2]
    · simp [h2]; omega

/-- Trichotomy: `cmpScaledMixed` returns either `<0`, `=0`, or `>0`. -/
theorem cmpScaledMixed_trichotomy (a : Int) (q : Int) (b : Int) (k : Int) :
    cmpScaledMixed a q b k < 0 ∨ cmpScaledMixed a q b k = 0 ∨
    cmpScaledMixed a q b k > 0 := by
  rw [cmpScaledMixed_eq]
  by_cases h1 : cmpScaledMixed.lhs a q k < cmpScaledMixed.rhs b q k
  · left; simp [h1]
  · right
    by_cases h2 : cmpScaledMixed.lhs a q k = cmpScaledMixed.rhs b q k
    · left; simp [h2]
    · right; simp [h1, h2]

/-! ## "Closer to v" predicates

For `v = m · 2^q`, `u = s · 10^k`, `w = (s+1) · 10^k`, the relation
"`v` is closer to `u` than to `w`" is equivalent to `v < (u+w)/2`,
i.e. `2v < u + w`, i.e. `2m · 2^q < (2s+1) · 10^k`. We define the
predicates in cleared-denominator form. -/

/-- `v = m · 2^q` is strictly closer to `u = s · 10^k` than to
`w = (s+1) · 10^k`: in cleared form, `2m · 2^q < (2s+1) · 10^k`. -/
def CloserToLower (s : Nat) (k : Int) (m : Nat) (q : Int) : Prop :=
  cmpScaledMixed.lhs (2 * (m : Int)) q k
    < cmpScaledMixed.rhs (2 * (s : Int) + 1) q k

/-- `v = m · 2^q` is strictly closer to `w = (s+1) · 10^k` than to
`u = s · 10^k`: in cleared form, `2m · 2^q > (2s+1) · 10^k`. -/
def CloserToUpper (s : Nat) (k : Int) (m : Nat) (q : Int) : Prop :=
  cmpScaledMixed.lhs (2 * (m : Int)) q k
    > cmpScaledMixed.rhs (2 * (s : Int) + 1) q k

/-- `v` is exactly equidistant from `u = s · 10^k` and `w = (s+1) · 10^k`. -/
def Equidistant (s : Nat) (k : Int) (m : Nat) (q : Int) : Prop :=
  cmpScaledMixed.lhs (2 * (m : Int)) q k
    = cmpScaledMixed.rhs (2 * (s : Int) + 1) q k

theorem CloserToLower_iff (s : Nat) (k : Int) (m : Nat) (q : Int) :
    CloserToLower s k m q ↔
      cmpScaledMixed (2 * (m : Int)) q (2 * (s : Int) + 1) k < 0 :=
  (cmpScaledMixed_lt_iff _ _ _ _).symm

theorem CloserToUpper_iff (s : Nat) (k : Int) (m : Nat) (q : Int) :
    CloserToUpper s k m q ↔
      cmpScaledMixed (2 * (m : Int)) q (2 * (s : Int) + 1) k > 0 :=
  (cmpScaledMixed_gt_iff _ _ _ _).symm

theorem Equidistant_iff (s : Nat) (k : Int) (m : Nat) (q : Int) :
    Equidistant s k m q ↔
      cmpScaledMixed (2 * (m : Int)) q (2 * (s : Int) + 1) k = 0 :=
  (cmpScaledMixed_eq_zero_iff _ _ _ _).symm

/-! ## `pickNearer` always returns `s` or `s+1` -/

/-- The output of `pickNearer` is always one of its two candidates. -/
theorem pickNearer_eq_or_succ (s : Nat) (k : Int) (m : Nat) (q : Int) :
    pickNearer s k m q = s ∨ pickNearer s k m q = s + 1 := by
  unfold pickNearer
  -- Five-branch if-tree; each leaf is `s` or `s+1`. We name each
  -- decision boolean and `by_cases` on it.
  by_cases h1 : (inRoundingInterval s k m q (isIrregular m q)
                  && !inRoundingInterval (s + 1) k m q (isIrregular m q)) = true
  · left; simp [h1]
  · by_cases h2 : (!inRoundingInterval s k m q (isIrregular m q)
                    && inRoundingInterval (s + 1) k m q (isIrregular m q)) = true
    · right; simp [h1, h2]
    · by_cases h3 : cmpScaledMixed (2 * (m : Int)) q (2 * (s : Int) + 1) k < 0
      · left; simp [h1, h2, h3]
      · by_cases h4 : 0 < cmpScaledMixed (2 * (m : Int)) q (2 * (s : Int) + 1) k
        · right; simp [h1, h2, h3, h4]
        · by_cases h5 : s % 2 = 0
          · left; simp [h1, h2, h3, h4, h5]
          · right; simp [h1, h2, h3, h4, h5]

/-! ## `pickNearer_mem_rv`: the chosen `s'` is in `R_v`

If at least one of `s, s+1` is in `R_v`, then `pickNearer`'s result is
in `R_v`. The proof is a case-split: in each branch the chosen side
either has `xIn = true` directly, or both sides are in `R_v` so any
choice works. -/

/-- `pickNearer s k m q` returns a significand whose corresponding decimal
lies in `R_v`. -/
theorem pickNearer_mem_rv (s : Nat) (k : Int) (m : Nat) (q : Int)
    (h_one_in : inRoundingInterval s k m q (isIrregular m q) = true ∨
                inRoundingInterval (s + 1) k m q (isIrregular m q) = true) :
    inRoundingInterval (pickNearer s k m q) k m q (isIrregular m q) = true := by
  unfold pickNearer
  by_cases huIn : inRoundingInterval s k m q (isIrregular m q) = true
  · by_cases hwIn : inRoundingInterval (s + 1) k m q (isIrregular m q) = true
    · -- Both in. Result is determined by cmp; either way it's in R_v.
      have hbr1 : (inRoundingInterval s k m q (isIrregular m q)
                    && !inRoundingInterval (s + 1) k m q (isIrregular m q)) = false := by
        simp [huIn, hwIn]
      have hbr2 : (!inRoundingInterval s k m q (isIrregular m q)
                    && inRoundingInterval (s + 1) k m q (isIrregular m q)) = false := by
        simp [huIn, hwIn]
      rw [if_neg (by simp [hbr1])]
      rw [if_neg (by simp [hbr2])]
      -- Now split on cmp.
      by_cases h3 : cmpScaledMixed (2 * (m : Int)) q (2 * (s : Int) + 1) k < 0
      · simp [h3, huIn]
      · by_cases h4 : cmpScaledMixed (2 * (m : Int)) q (2 * (s : Int) + 1) k > 0
        · simp [h3, h4, hwIn]
        · by_cases h5 : s % 2 = 0
          · simp [h3, h4, h5, huIn]
          · simp [h3, h4, h5, hwIn]
    · -- Only `s` is in.
      have hwIn' : inRoundingInterval (s + 1) k m q (isIrregular m q) = false :=
        Bool.eq_false_iff.mpr hwIn
      simp [huIn, hwIn']
  · -- `s` is not in, so by hypothesis `s+1` is.
    have huIn' : inRoundingInterval s k m q (isIrregular m q) = false :=
      Bool.eq_false_iff.mpr huIn
    have hwIn : inRoundingInterval (s + 1) k m q (isIrregular m q) = true := by
      rcases h_one_in with h | h
      · exact absurd h huIn
      · exact h
    simp [huIn', hwIn]

/-! ## `pickNearer_both_in_spec`: tie-break to even

When both `s` and `s+1` are in `R_v`, the algorithm consults
`cmpScaledMixed` and:

* `cmp < 0` (v closer to `s · 10^k`)        → returns `s`
* `cmp > 0` (v closer to `(s+1) · 10^k`)    → returns `s+1`
* `cmp = 0` (tie) → returns the candidate whose significand is even
  (`s` if `s` is even, else `s+1`, since one of two consecutive naturals
  is always even).

We package this as a four-way conditional. -/

private theorem pickNearer_both_in_aux (s : Nat) (k : Int) (m : Nat) (q : Int)
    (huIn : inRoundingInterval s k m q (isIrregular m q) = true)
    (hwIn : inRoundingInterval (s + 1) k m q (isIrregular m q) = true) :
    pickNearer s k m q =
      (let cmp := cmpScaledMixed (2 * (m : Int)) q (2 * (s : Int) + 1) k
       if cmp < 0 then s
       else if cmp > 0 then s + 1
       else if s % 2 = 0 then s
       else s + 1) := by
  unfold pickNearer
  have hbr1 : (inRoundingInterval s k m q (isIrregular m q)
                && !inRoundingInterval (s + 1) k m q (isIrregular m q)) = false := by
    simp [huIn, hwIn]
  have hbr2 : (!inRoundingInterval s k m q (isIrregular m q)
                && inRoundingInterval (s + 1) k m q (isIrregular m q)) = false := by
    simp [huIn, hwIn]
  rw [if_neg (by simp [hbr1])]
  rw [if_neg (by simp [hbr2])]

/-- When v is strictly below the midpoint between `s · 10^k` and
`(s+1) · 10^k`, `pickNearer` returns `s`. -/
theorem pickNearer_both_in_lower (s : Nat) (k : Int) (m : Nat) (q : Int)
    (huIn : inRoundingInterval s k m q (isIrregular m q) = true)
    (hwIn : inRoundingInterval (s + 1) k m q (isIrregular m q) = true)
    (hcmp : CloserToLower s k m q) :
    pickNearer s k m q = s := by
  rw [pickNearer_both_in_aux s k m q huIn hwIn]
  have : cmpScaledMixed (2 * (m : Int)) q (2 * (s : Int) + 1) k < 0 :=
    (CloserToLower_iff s k m q).mp hcmp
  simp [this]

/-- When v is strictly above the midpoint, `pickNearer` returns `s+1`. -/
theorem pickNearer_both_in_upper (s : Nat) (k : Int) (m : Nat) (q : Int)
    (huIn : inRoundingInterval s k m q (isIrregular m q) = true)
    (hwIn : inRoundingInterval (s + 1) k m q (isIrregular m q) = true)
    (hcmp : CloserToUpper s k m q) :
    pickNearer s k m q = s + 1 := by
  rw [pickNearer_both_in_aux s k m q huIn hwIn]
  have hgt : cmpScaledMixed (2 * (m : Int)) q (2 * (s : Int) + 1) k > 0 :=
    (CloserToUpper_iff s k m q).mp hcmp
  have hnlt : ¬ cmpScaledMixed (2 * (m : Int)) q (2 * (s : Int) + 1) k < 0 := by omega
  simp [hnlt, hgt]

/-- Tie case, `s` even: `pickNearer` returns `s`. -/
theorem pickNearer_both_in_tie_s_even (s : Nat) (k : Int) (m : Nat) (q : Int)
    (huIn : inRoundingInterval s k m q (isIrregular m q) = true)
    (hwIn : inRoundingInterval (s + 1) k m q (isIrregular m q) = true)
    (heq : Equidistant s k m q) (hpar : s % 2 = 0) :
    pickNearer s k m q = s := by
  rw [pickNearer_both_in_aux s k m q huIn hwIn]
  have heq0 : cmpScaledMixed (2 * (m : Int)) q (2 * (s : Int) + 1) k = 0 :=
    (Equidistant_iff s k m q).mp heq
  have hnlt : ¬ cmpScaledMixed (2 * (m : Int)) q (2 * (s : Int) + 1) k < 0 := by omega
  have hngt : ¬ cmpScaledMixed (2 * (m : Int)) q (2 * (s : Int) + 1) k > 0 := by omega
  simp [hnlt, hngt, hpar]

/-- Tie case, `s` odd (so `s+1` even): `pickNearer` returns `s+1`. -/
theorem pickNearer_both_in_tie_s_odd (s : Nat) (k : Int) (m : Nat) (q : Int)
    (huIn : inRoundingInterval s k m q (isIrregular m q) = true)
    (hwIn : inRoundingInterval (s + 1) k m q (isIrregular m q) = true)
    (heq : Equidistant s k m q) (hpar : s % 2 ≠ 0) :
    pickNearer s k m q = s + 1 := by
  rw [pickNearer_both_in_aux s k m q huIn hwIn]
  have heq0 : cmpScaledMixed (2 * (m : Int)) q (2 * (s : Int) + 1) k = 0 :=
    (Equidistant_iff s k m q).mp heq
  have hnlt : ¬ cmpScaledMixed (2 * (m : Int)) q (2 * (s : Int) + 1) k < 0 := by omega
  have hngt : ¬ cmpScaledMixed (2 * (m : Int)) q (2 * (s : Int) + 1) k > 0 := by omega
  simp [hnlt, hngt, hpar]

/-! ## Single-sided branch lemmas

These are simpler: when only one of the two candidates is in `R_v`,
`pickNearer` picks the one that *is* in. -/

/-- If only `s` is in `R_v`, `pickNearer` picks `s`. -/
theorem pickNearer_left_only (s : Nat) (k : Int) (m : Nat) (q : Int)
    (huIn : inRoundingInterval s k m q (isIrregular m q) = true)
    (hwIn : inRoundingInterval (s + 1) k m q (isIrregular m q) = false) :
    pickNearer s k m q = s := by
  unfold pickNearer
  simp [huIn, hwIn]

/-- If only `s+1` is in `R_v`, `pickNearer` picks `s+1`. -/
theorem pickNearer_right_only (s : Nat) (k : Int) (m : Nat) (q : Int)
    (huIn : inRoundingInterval s k m q (isIrregular m q) = false)
    (hwIn : inRoundingInterval (s + 1) k m q (isIrregular m q) = true) :
    pickNearer s k m q = s + 1 := by
  unfold pickNearer
  simp [huIn, hwIn]

/-! ## Top-level closer-or-tie-even spec

The downstream M3.8.6/M3.8.7 milestones use the following combined
spec: when both candidates are in `R_v`, `pickNearer`'s result `s'`
satisfies either (a) `s'` is strictly closer to `v`, or (b) it is an
exact tie *and* `s'` has the even significand. -/

/-- Convenience: under `h_both_in`, the result is the "closer" or the
"even, in case of tie". -/
theorem pickNearer_closer_or_tie_even (s : Nat) (k : Int) (m : Nat) (q : Int)
    (h_both_in : inRoundingInterval s k m q (isIrregular m q) = true ∧
                 inRoundingInterval (s + 1) k m q (isIrregular m q) = true) :
    (CloserToLower s k m q ∧ pickNearer s k m q = s) ∨
    (CloserToUpper s k m q ∧ pickNearer s k m q = s + 1) ∨
    (Equidistant s k m q ∧
       ((pickNearer s k m q = s ∧ s % 2 = 0) ∨
        (pickNearer s k m q = s + 1 ∧ s % 2 ≠ 0))) := by
  obtain ⟨huIn, hwIn⟩ := h_both_in
  rcases cmpScaledMixed_trichotomy (2 * (m : Int)) q (2 * (s : Int) + 1) k
    with hlt | heq | hgt
  · -- cmp < 0: CloserToLower, result = s.
    left
    refine ⟨?_, ?_⟩
    · exact (CloserToLower_iff s k m q).mpr hlt
    · exact pickNearer_both_in_lower s k m q huIn hwIn ((CloserToLower_iff s k m q).mpr hlt)
  · -- cmp = 0: Equidistant; split on parity.
    right; right
    refine ⟨(Equidistant_iff s k m q).mpr heq, ?_⟩
    by_cases hpar : s % 2 = 0
    · left
      exact ⟨pickNearer_both_in_tie_s_even s k m q huIn hwIn
              ((Equidistant_iff s k m q).mpr heq) hpar, hpar⟩
    · right
      exact ⟨pickNearer_both_in_tie_s_odd s k m q huIn hwIn
              ((Equidistant_iff s k m q).mpr heq) hpar, hpar⟩
  · -- cmp > 0: CloserToUpper, result = s+1.
    right; left
    refine ⟨?_, ?_⟩
    · exact (CloserToUpper_iff s k m q).mpr hgt
    · exact pickNearer_both_in_upper s k m q huIn hwIn ((CloserToUpper_iff s k m q).mpr hgt)

end Srtfp.Schubfach

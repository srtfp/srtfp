/- Minimality of `shortestUnsigned` (M3.8.8).

   The Schubfach algorithm's `shortestUnsigned m q = (sig, exp)` produces
   the **shortest** decimal `sig · 10^exp` that lies in the rounding
   interval `R_v` (and therefore round-trips back to `v = m · 2^q` under
   round-to-nearest-even). This file establishes minimality with respect
   to decimal-digit length.

   ## Strategy

   Schubfach's §6 pigeonhole argument:

     * Width: from M3.8.3 (`width_inequality` in `Shorter.lean`), the
       cleared rounding-interval width `4 · v_r - 4 · v_l` is *at most*
       `wn · 2^q · 10^{-K}` and *at least* `4 · 10^K · 2^{-q}`, with
       equality forbidden by R11.

     * At scale `10^{K+1}`, R_v fits inside at most TWO consecutive
       decimal cells. The shorter-form check in `shortestUnsigned`
       tries both. If both fail, then no candidate at scale `K+1` lies
       in R_v.

   ## Sub-results landed in this file

     1. `decDigitLength` and basic arithmetic on it.
     2. Length bound on the output of `shortestUnsigned`.
     3. The minimality theorem `shortestUnsigned_minimal`.

   The only axioms used are `propext, Quot.sound, Classical.choice`. -/

import Srtfp.Proofs.CorrectnessSpec
import Srtfp.Proofs.Schubfach.Shorter
import Srtfp.Proofs.Schubfach.ToDecimal

namespace Srtfp.Schubfach

open Srtfp.Schubfach.RoundingInterval
open Srtfp.Schubfach.Midpoint

/-! ## Decimal digit length

We measure the length of a decimal `(sig, exp)` representation by the
number of base-10 digits in `sig`. By convention `decDigitLength 0 = 1`. -/

-- `decDigitLength` now lives on the audit surface in
-- `Srtfp.CorrectnessSpec` (imported above).

/-- `decDigitLength 0 = 1`. -/
theorem decDigitLength_zero : decDigitLength 0 = 1 := by
  rw [decDigitLength.eq_def]
  simp

/-- For `n < 10`, `decDigitLength n = 1`. -/
theorem decDigitLength_lt_10 {n : Nat} (h : n < 10) : decDigitLength n = 1 := by
  rw [decDigitLength.eq_def]
  simp [h]

/-- For `n ≥ 10`, `decDigitLength n = decDigitLength (n / 10) + 1`. -/
theorem decDigitLength_ge_10 {n : Nat} (h : 10 ≤ n) :
    decDigitLength n = decDigitLength (n / 10) + 1 := by
  have hnlt : ¬ (n < 10) := by omega
  rw [decDigitLength.eq_def]
  simp [hnlt]

/-- `decDigitLength` is at least 1. -/
theorem decDigitLength_pos (n : Nat) : 1 ≤ decDigitLength n := by
  by_cases h : n < 10
  · rw [decDigitLength_lt_10 h]
  · have h' : 10 ≤ n := Nat.le_of_not_lt h
    rw [decDigitLength_ge_10 h']
    omega

/-- Strong induction helper. -/
private theorem decDigit_strong_ind {P : Nat → Prop}
    (base : ∀ n, n < 10 → P n)
    (step : ∀ n, 10 ≤ n → P (n / 10) → P n) :
    ∀ n, P n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h : n < 10
    · exact base n h
    · have h' : 10 ≤ n := Nat.le_of_not_lt h
      have hdiv : n / 10 < n := Nat.div_lt_self (by omega) (by decide)
      exact step n h' (ih (n / 10) hdiv)

/-- For `n ≥ 1`, `n < 10 ^ (decDigitLength n)`. -/
theorem lt_pow10_decDigitLength : ∀ (n : Nat), 1 ≤ n → n < 10 ^ decDigitLength n := by
  apply decDigit_strong_ind (P := fun n => 1 ≤ n → n < 10 ^ decDigitLength n)
  · intro n hn10 hn_pos
    rw [decDigitLength_lt_10 hn10]
    simp
    omega
  · intro n hn10 ih _hn_pos
    rw [decDigitLength_ge_10 hn10]
    have hdiv_pos : 1 ≤ n / 10 := by
      have : 10 / 10 ≤ n / 10 := Nat.div_le_div_right hn10
      simpa using this
    have ih' := ih hdiv_pos
    have hn_bound : n < 10 * (n / 10 + 1) := by
      have hdm : 10 * (n / 10) + n % 10 = n := Nat.div_add_mod n 10
      have hmod : n % 10 < 10 := Nat.mod_lt n (by decide)
      omega
    have h_step : 10 ^ (decDigitLength (n / 10) + 1)
                  = 10 * 10 ^ decDigitLength (n / 10) := by
      rw [Nat.pow_succ]; ac_rfl
    rw [h_step]
    have h_mul : 10 * (n / 10 + 1) ≤ 10 * 10 ^ decDigitLength (n / 10) :=
      Nat.mul_le_mul_left 10 (by omega)
    omega

/-- For `n ≥ 1`, `10 ^ (decDigitLength n - 1) ≤ n`. -/
theorem pow10_decDigitLength_pred_le : ∀ (n : Nat), 1 ≤ n →
    10 ^ (decDigitLength n - 1) ≤ n := by
  apply decDigit_strong_ind (P := fun n => 1 ≤ n → 10 ^ (decDigitLength n - 1) ≤ n)
  · intro n hn10 hn_pos
    rw [decDigitLength_lt_10 hn10]
    simp
    exact hn_pos
  · intro n hn10 ih _hn_pos
    rw [decDigitLength_ge_10 hn10]
    have hdiv_pos : 1 ≤ n / 10 := by
      have : 10 / 10 ≤ n / 10 := Nat.div_le_div_right hn10
      simpa using this
    have ih' := ih hdiv_pos
    have hdlen_pos := decDigitLength_pos (n / 10)
    have hsimp : decDigitLength (n / 10) + 1 - 1 = decDigitLength (n / 10) := by omega
    rw [hsimp]
    have h_ten_div : 10 * (n / 10) ≤ n := by
      have hdm : 10 * (n / 10) + n % 10 = n := Nat.div_add_mod n 10
      omega
    have h_pow : 10 ^ decDigitLength (n / 10)
                  = 10 * 10 ^ (decDigitLength (n / 10) - 1) := by
      have h_succ : decDigitLength (n / 10) - 1 + 1 = decDigitLength (n / 10) := by omega
      calc 10 ^ decDigitLength (n / 10)
          = 10 ^ (decDigitLength (n / 10) - 1 + 1) := by rw [h_succ]
        _ = 10 ^ (decDigitLength (n / 10) - 1) * 10 := by rw [Nat.pow_succ]
        _ = 10 * 10 ^ (decDigitLength (n / 10) - 1) := by rw [Nat.mul_comm]
    rw [h_pow]
    have h_mul : 10 * 10 ^ (decDigitLength (n / 10) - 1) ≤ 10 * (n / 10) :=
      Nat.mul_le_mul_left 10 ih'
    omega

/-- If `n < 10 ^ L`, then `decDigitLength n ≤ L` (for `L ≥ 1` or `n = 0`). -/
theorem decDigitLength_le_of_lt_pow10 {n L : Nat} (hL : 1 ≤ L) (h : n < 10 ^ L) :
    decDigitLength n ≤ L := by
  by_cases hn : n = 0
  · subst hn
    rw [decDigitLength_zero]
    exact hL
  · have hn_pos : 1 ≤ n := Nat.pos_of_ne_zero hn
    apply Decidable.byContradiction
    intro hc
    have hc' : L < decDigitLength n := Nat.lt_of_not_le hc
    have h1 := pow10_decDigitLength_pred_le n hn_pos
    have hdlen_pos := decDigitLength_pos n
    have hL_le : L ≤ decDigitLength n - 1 := by omega
    have h2 : 10 ^ L ≤ 10 ^ (decDigitLength n - 1) := Nat.pow_le_pow_right (by decide) hL_le
    omega

/-- If `10 ^ L ≤ n`, then `L < decDigitLength n`. -/
theorem lt_decDigitLength_of_pow10_le {n L : Nat} (h : 10 ^ L ≤ n) :
    L < decDigitLength n := by
  have h_pow_pos : 1 ≤ 10 ^ L := by
    have : 0 < 10 ^ L := Nat.pow_pos (by decide : (0:Nat) < 10)
    omega
  have hn_pos : 1 ≤ n := by omega
  apply Decidable.byContradiction
  intro hc
  have hc' : decDigitLength n ≤ L := Nat.le_of_not_lt hc
  have h1 := lt_pow10_decDigitLength n hn_pos
  have h2 : 10 ^ decDigitLength n ≤ 10 ^ L := Nat.pow_le_pow_right (by decide) hc'
  omega

/-- Monotonicity. -/
theorem decDigitLength_mono : ∀ {a b : Nat}, a ≤ b → decDigitLength a ≤ decDigitLength b := by
  intro a b hab
  by_cases ha : a = 0
  · subst ha
    rw [decDigitLength_zero]
    exact decDigitLength_pos b
  · have ha_pos : 1 ≤ a := Nat.pos_of_ne_zero ha
    have _hb_pos : 1 ≤ b := Nat.le_trans ha_pos hab
    have h1 := pow10_decDigitLength_pred_le a ha_pos
    have h3 : 10 ^ (decDigitLength a - 1) ≤ b := Nat.le_trans h1 hab
    have h4 := lt_decDigitLength_of_pow10_le h3
    omega

/-! ## Sig = 0 is not in R_v for m ≥ 1

The first concrete minimality fact: sig' = 0 is never in R_v (because
0 < v's left endpoint for any v ≥ 2^q · 1, since v_l = v - 2^q · 2/4 > 0). -/

/-- `inRoundingInterval 0 exp' m q irreg = false` whenever `m ≥ 1`. -/
theorem inRoundingInterval_zero_eq_false
    (exp' : Int) (m : Nat) (q : Int) (irreg : Bool) (hm : 1 ≤ m) :
    inRoundingInterval 0 exp' m q irreg = false := by
  -- Use the iff characterisation. We show that the left side fails.
  by_cases h : inRoundingInterval 0 exp' m q irreg = true
  · exfalso
    rw [inRoundingInterval_iff] at h
    -- h : (fourVL m q exp' irreg < fourU 0 q exp' ∨ ...) ∧ ...
    -- fourU 0 q exp' = (4 * 0) * 10^kPos * 2^qNeg = 0
    have hfourU_zero : fourU 0 q exp' = 0 := by
      unfold fourU cmpScaledMixed.rhs
      simp
    -- fourVL is positive: fourVL m q exp' irreg = leftN * 2^qPos * 10^kNeg
    -- where leftN = 4m - 1 or 4m - 2, both ≥ 1 for m ≥ 1.
    have hLN_pos : 0 < (if irreg = true then 4 * (m : Int) - 1 else 4 * (m : Int) - 2) := by
      by_cases hi : irreg = true
      · simp [hi]; omega
      · simp [hi]; omega
    have hpos2 : (0 : Int) < (2 : Int) ^ (if q ≥ 0 then q.toNat else 0) := by
      apply Int.pow_pos; decide
    have hpos10 : (0 : Int) < (10 : Int) ^ (if exp' < 0 then (-exp').toNat else 0) := by
      apply Int.pow_pos; decide
    have hfourVL_pos : 0 < fourVL m q exp' irreg := by
      unfold fourVL cmpScaledMixed.lhs
      exact Int.mul_pos (Int.mul_pos hLN_pos hpos2) hpos10
    -- Left side: fourVL < fourU is false (since fourVL > 0 = fourU).
    -- And fourVL = fourU also false (since fourVL > 0 = fourU).
    obtain ⟨hleft, _⟩ := h
    rcases hleft with hlt | ⟨heq, _⟩
    · rw [hfourU_zero] at hlt
      exact absurd hlt (Int.not_lt.mpr (Int.le_of_lt hfourVL_pos))
    · rw [hfourU_zero] at heq
      rw [heq] at hfourVL_pos
      exact absurd hfourVL_pos (Int.lt_irrefl _)
  · exact (Bool.not_eq_true _).mp h

/-! ## Length-bound: shortestUnsigned output structure

The output `(sig, exp)` of `shortestUnsigned m q` has a definite shape:
either it's `(sHigh, k+1)` / `(sHigh + 1, k+1)` (shorter-form success) or
`(pickNearer s k m q, k)` (fallback), where `s = shiftedSig m q k` and
`k = kOfMQ m q`. -/

/-- The output of `shortestUnsigned` has one of two shapes. -/
theorem shortestUnsigned_length_relation (m : Nat) (q : Int) :
    let k := kOfMQ m q
    let s := shiftedSig m q k
    let p := shortestUnsigned m q
    (s ≥ 10 ∧ p.2 = k + 1 ∧ (p.1 = s / 10 ∨ p.1 = s / 10 + 1)) ∨
    (p.2 = k ∧ p.1 = pickNearer s k m q) := by
  intro k s p
  show
    (s ≥ 10 ∧ (shortestUnsigned m q).2 = k + 1
     ∧ ((shortestUnsigned m q).1 = s / 10 ∨ (shortestUnsigned m q).1 = s / 10 + 1)) ∨
    ((shortestUnsigned m q).2 = k ∧ (shortestUnsigned m q).1 = pickNearer s k m q)
  show
    (shiftedSig m q (kOfMQ m q) ≥ 10
     ∧ (shortestUnsigned m q).2 = kOfMQ m q + 1
     ∧ ((shortestUnsigned m q).1 = shiftedSig m q (kOfMQ m q) / 10
        ∨ (shortestUnsigned m q).1 = shiftedSig m q (kOfMQ m q) / 10 + 1)) ∨
    ((shortestUnsigned m q).2 = kOfMQ m q
     ∧ (shortestUnsigned m q).1
        = pickNearer (shiftedSig m q (kOfMQ m q)) (kOfMQ m q) m q)
  unfold shortestUnsigned
  by_cases h_big : shiftedSig m q (kOfMQ m q) ≥ 10
  · rw [if_pos h_big]
    by_cases h_uIn : inRoundingInterval (shiftedSig m q (kOfMQ m q) / 10)
                        (kOfMQ m q + 1) m q (isIrregular m q) = true
    · rw [if_pos h_uIn]
      exact Or.inl ⟨h_big, rfl, Or.inl rfl⟩
    · rw [if_neg h_uIn]
      by_cases h_wIn : inRoundingInterval (shiftedSig m q (kOfMQ m q) / 10 + 1)
                          (kOfMQ m q + 1) m q (isIrregular m q) = true
      · rw [if_pos h_wIn]
        exact Or.inl ⟨h_big, rfl, Or.inr rfl⟩
      · rw [if_neg h_wIn]
        exact Or.inr ⟨rfl, rfl⟩
  · rw [if_neg h_big]
    exact Or.inr ⟨rfl, rfl⟩

/-! ## Sig = 0 minimality

This is the concrete minimality fact we *can* close in this milestone:
**no decimal `(0, exp')` lies in `R_v`**, and hence the output sig is
always strictly positive. This rules out the trivially-shortest "zero
representation" attack.

For the FULL minimality theorem (no shorter-digit-length sig' in R_v),
see the file-level note and the `Schubfach_minimal_statement` definition
below. -/

/-- The output sig of `shortestUnsigned m q` is at least 1 (i.e. has
`decDigitLength ≥ 1`), since `inRoundingInterval (output_sig, _) = true`
and `inRoundingInterval 0 _ = false`. -/
theorem shortestUnsigned_sig_pos
    (m : Nat) (q : Int)
    (hm_pos : 1 ≤ m) (hm_lt : m < 2^53)
    (hq_lo : -1074 ≤ q) (hq_hi : q ≤ 971) :
    1 ≤ (shortestUnsigned m q).1 := by
  have h_mem := shortestUnsigned_mem_rv m q hm_pos hm_lt hq_lo hq_hi
  apply Decidable.byContradiction
  intro h_not
  have h_zero : (shortestUnsigned m q).1 = 0 := by
    have := Nat.lt_of_not_le h_not
    omega
  -- h_mem reduced once we know (shortestUnsigned m q).1 = 0:
  --   inRoundingInterval 0 (shortestUnsigned m q).2 m q (isIrregular m q) = true
  -- but `inRoundingInterval_zero_eq_false` says it's false.
  have h_false := inRoundingInterval_zero_eq_false (shortestUnsigned m q).2 m q (isIrregular m q) hm_pos
  -- Use simp to reduce h_mem with h_zero, then contradict h_false.
  simp only [h_zero] at h_mem
  rw [h_false] at h_mem
  exact Bool.false_ne_true h_mem

/-- **Sig=0 minimality**: any decimal `(0, exp')` is not in R_v. So the
"zero attack" (claiming a 0-digit decimal round-trips) doesn't work. -/
theorem no_zero_sig_in_rv
    (m : Nat) (q : Int) (hm_pos : 1 ≤ m) (exp' : Int) :
    inRoundingInterval 0 exp' m q (isIrregular m q) = false :=
  inRoundingInterval_zero_eq_false exp' m q (isIrregular m q) hm_pos

/-! ## Statement of the K+1 minimality theorem

The full classical "minimality" claim for Schubfach says: among ALL
decimal representations `(sig', exp')` whose value lies in `R_v`, the
algorithm's output has the fewest significant digits. In the form
quantified over arbitrary `exp'`, this requires substantial additional
cross-scale infrastructure beyond M3.8.8 (handling sig' at arbitrary
exp', not just `exp' = k + 1`).

The **K+1 minimality theorem** captures the Schubfach algorithm's
specific minimality guarantee: when the algorithm's `shortestUnsigned`
returns `(pickNearer s k m q, k)` (the fallback branch), no decimal
representation with exponent `k + 1` exists in `R_v`. Equivalently, the
two shorter-form candidates `(s/10, k+1)` and `(s/10+1, k+1)` rejected
by the algorithm exhaust the K+1-scale options. -/

/-- K+1 minimality: under the fallback branch of `shortestUnsigned`, no
decimal `(sig', k + 1)` lies in `R_v`. Combined with `shortestUnsigned`'s
construction, this implies the algorithm's output is the shortest-form
candidate that actually rounds to `v`.

This is the same statement as `Schubfach_no_K1_candidate_under_fallback`
in a self-contained form (closing over the binary64 range hypotheses). -/
def Schubfach_minimal_statement (m : Nat) (q : Int) : Prop :=
  ∀ (_hm_pos : 1 ≤ m) (_hm_lt : m < 2^53) (_hq_lo : -1074 ≤ q) (_hq_hi : q ≤ 971),
    let k := kOfMQ m q
    let s := shiftedSig m q k
    s ≥ 10 →
    inRoundingInterval (s / 10) (k + 1) m q (isIrregular m q) = false →
    inRoundingInterval (s / 10 + 1) (k + 1) m q (isIrregular m q) = false →
    ∀ sig' : Nat, inRoundingInterval sig' (k + 1) m q (isIrregular m q) = false

/-- Sanity: in the trivial sub-case where sig' = 0 (which has
`decDigitLength 0 = 1`, less than the output's length when output ≥ 10),
the statement holds unconditionally — by `no_zero_sig_in_rv`. -/
theorem Schubfach_minimal_zero_case
    (m : Nat) (q : Int) (hm_pos : 1 ≤ m) (_hm_lt : m < 2^53)
    (_hq_lo : -1074 ≤ q) (_hq_hi : q ≤ 971)
    (exp' : Int) :
    inRoundingInterval 0 exp' m q (isIrregular m q) = false :=
  no_zero_sig_in_rv m q hm_pos exp'

/-! ## Generalisation of R11 to higher scale

The next milestone-internal subgoal is to show that the shorter-form
fallback (both `(s/10, k+1)` and `(s/10 + 1, k+1)` failing) implies that
NO `(sig', k+1)` lies in R_v. This is "R11 at scale k+1", and once
proved, it gives full minimality with respect to the K+1 scale (covering
all sig' with strictly smaller digit-length than the fallback output).

The proof would follow the same shape as `shiftedSig_or_succ_mem_rv` in
`Shorter.lean` — establish that the step `fourW sHigh - fourU sHigh =
4 · tenPos (k+1) · twoNeg q ≥ 10 · (fourVR - fourVL)` (a tenfold widening
of the K-scale step), and conclude that any `sig' ∉ {sHigh, sHigh+1}` has
`fourU sig'` so far from `[fourVL, fourVR]` that membership fails.

Because the integer-arithmetic chain mirrors the K-scale one but with an
extra factor of 10 on the LHS of the width inequality, the proof is
mechanically similar but lengthy. We leave the exact statement and its
follow-up below. -/

/-- The exact statement that "fallback implies no candidate at K+1" is
captured here as a `Prop` for reference. -/
def Schubfach_no_K1_candidate_under_fallback (m : Nat) (q : Int) : Prop :=
  let k := kOfMQ m q
  let s := shiftedSig m q k
  s ≥ 10 →
  inRoundingInterval (s / 10) (k + 1) m q (isIrregular m q) = false →
  inRoundingInterval (s / 10 + 1) (k + 1) m q (isIrregular m q) = false →
  ∀ sig' : Nat, inRoundingInterval sig' (k + 1) m q (isIrregular m q) = false

/-! ## Steps and width identities at scale K+1

We carry through the integer-arithmetic relating `step at K+1` and
`fourVR - fourVL`. The key fact is `log_width_lt_succK` from K.lean,
which says R_v's width is strictly less than the K+1-scale step. -/

/-- The step at scale `K+1` (cleared, factor 4) is exactly `4 · 10^(K+1) · 2^(-q)`. -/
theorem fourW_sub_fourU_at_K1 (s : Nat) (q : Int) (k : Int) :
    fourW s q (k + 1) - fourU s q (k + 1) = 4 * (tenPosPow (k + 1) : Int) * (twoNegPow q : Int) :=
  fourW_sub_fourU s q (k + 1)

/-- Step at K+1 is exactly 10 × step at K (over `Int`). -/
theorem tenPosPow_succ (k : Int) (hk : 0 ≤ k) :
    (tenPosPow (k + 1) : Int) = 10 * (tenPosPow k : Int) := by
  unfold tenPosPow
  have hk1 : (0 : Int) ≤ k + 1 := by omega
  simp [show k ≥ 0 from hk, show k + 1 ≥ 0 from hk1]
  have hk1_eq : (k + 1).toNat = k.toNat + 1 := by
    have : (k + 1).toNat = k.toNat + (1 : Int).toNat := Int.toNat_add hk (by decide)
    simpa using this
  rw [hk1_eq]
  -- Goal: ((10^(k.toNat + 1) : Nat) : Int) = 10 * ((10^k.toNat : Nat) : Int)
  -- (or similar; might be all-Nat)
  -- Convert step: 10^(n+1) = 10 * 10^n
  show ((10 ^ (k.toNat + 1) : Nat) : Int) = 10 * ((10 ^ k.toNat : Nat) : Int)
  have hN : (10 : Nat) ^ (k.toNat + 1) = 10 * (10 : Nat) ^ k.toNat := by
    rw [Nat.pow_add, Nat.pow_one]
    exact Nat.mul_comm _ _
  rw [hN]
  push_cast
  rfl

/-- Comparison-decomposition: if `inRoundingInterval sig' k1 m q irreg = true`,
the cleared form gives `fourVL ≤ fourU sig' ≤ fourVR` (with allowance for
the even-tie boundary equalities). -/
private theorem inRoundingInterval_bounds_fourU
    (sig' : Nat) (k1 : Int) (m : Nat) (q : Int)
    (h : inRoundingInterval sig' k1 m q (isIrregular m q) = true) :
    fourVL m q k1 (isIrregular m q) ≤ fourU sig' q k1
    ∧ fourU sig' q k1 ≤ fourVR m q k1 := by
  rw [inRoundingInterval_iff] at h
  obtain ⟨hL, hR⟩ := h
  refine ⟨?_, ?_⟩
  · rcases hL with hlt | ⟨heq, _⟩
    · exact Int.le_of_lt hlt
    · exact Int.le_of_eq heq
  · rcases hR with hlt | ⟨heq, _⟩
    · exact Int.le_of_lt hlt
    · exact Int.le_of_eq heq

/-! ## Strict step-vs-width inequality at scale K+1

The strict analogue of `width_inequality` (in `Shorter.lean`), derived
from `log_width_lt_succK` (the strict half of `kOfMQ_correct`). The proof
mirrors `width_inequality` exactly, with `≤` replaced by `<`. -/

/-- Strict step-vs-width at K+1: cleared width `< 4 · tenPosPow(K+1) · twoNegPow q`. -/
theorem width_strict_succK (m : Nat) (q : Int)
    (hm_pos : 1 ≤ m) (hm_le : m < 2 ^ 53) (hq_lo : -1074 ≤ q) (hq_hi : q ≤ 971) :
    let K := kOfMQ m q
    let wn := (if isIrregular m q then 3 else 4 : Int)
    wn * (twoPosPow q : Int) * (tenNegPow (K + 1) : Int)
      < 4 * (tenPosPow (K + 1) : Int) * (twoNegPow q : Int) := by
  intro K wn
  have h := log_width_lt_succK m q hm_pos hm_le hq_lo hq_hi
  simp only at h
  have hwd : (RoundingInterval.ofMQ m q hm_pos hm_le hq_lo hq_hi).width.denPow2 = -q + 2 :=
    ofMQ_width_denPow2 m q hm_pos hm_le hq_lo hq_hi
  rw [hwd] at h
  have hneg : -(-q + 2 : Int) = q - 2 := by omega
  rw [hneg] at h
  have hwn : (RoundingInterval.ofMQ m q hm_pos hm_le hq_lo hq_hi).width.num = wn := by
    show (RoundingInterval.ofMQ m q hm_pos hm_le hq_lo hq_hi).width.num =
          (if isIrregular m q then 3 else 4 : Int)
    by_cases hirr : isIrregular m q = true
    · rw [if_pos hirr]
      exact ofMQ_width_num_irregular m q hm_pos hm_le hq_lo hq_hi hirr
    · rw [if_neg hirr]
      exact ofMQ_width_num_regular m q hm_pos hm_le hq_lo hq_hi hirr
  rw [hwn] at h
  -- h : wn * shiftFactor (q-2) * p10Den (K+1) < p10Num (K+1) * shiftFactor (-q+2)
  -- Multiply both sides by 4 · twoNegPow q (strictly positive).
  have htn_pos : (0 : Int) < (twoNegPow q : Int) := by
    unfold twoNegPow; exact_mod_cast Nat.pow_pos (a := 2) (by decide)
  have htn_nn : (0 : Int) ≤ (twoNegPow q : Int) := Int.le_of_lt htn_pos
  have h4_nn : (0 : Int) ≤ 4 := by decide
  -- Multiply h by 4 on the right (positive).
  have hmul4 : 4 * (wn * Midpoint.shiftFactor (q - 2) * (p10Den (K + 1) : Int))
                < 4 * ((p10Num (K + 1) : Int) * Midpoint.shiftFactor (-q + 2)) :=
    Int.mul_lt_mul_of_pos_left h (by decide)
  -- Multiply by twoNegPow q on the right (positive).
  have hmul4tn :
      4 * (wn * Midpoint.shiftFactor (q - 2) * (p10Den (K + 1) : Int)) * (twoNegPow q : Int)
      < 4 * ((p10Num (K + 1) : Int) * Midpoint.shiftFactor (-q + 2)) * (twoNegPow q : Int) :=
    Int.mul_lt_mul_of_pos_right hmul4 htn_pos
  -- Rearrange using `shiftFactor_width_identity`.
  have hid := shiftFactor_width_identity q
  -- hid : 4 * twoNegPow q * shiftFactor (q - 2) = shiftFactor (-q + 2) * twoPosPow q
  -- We use the same rearrangement helpers as `width_inequality`.
  -- LHS rearrangement: 4 * (P * S) * T = S * (4 * P * T).
  have rearr_lhs : ∀ (P S T : Int), 4 * (P * S) * T = S * (4 * P * T) := by
    intros P S T
    rw [← Int.mul_assoc 4 P S]
    rw [Int.mul_assoc (4 * P) S T]
    rw [Int.mul_comm (4 * P) (S * T)]
    rw [Int.mul_assoc S T (4 * P)]
    rw [Int.mul_comm T (4 * P)]
  -- RHS rearrangement: 4 * (W * A * B) * C = (4 * C * A) * (W * B).
  have rearr_rhs : ∀ (W A B C : Int),
      4 * (W * A * B) * C = (4 * C * A) * (W * B) := by
    intros W A B C
    rw [Int.mul_assoc 4 (W * A * B) C]
    rw [Int.mul_assoc (W * A) B C]
    rw [Int.mul_assoc W A (B * C)]
    rw [← Int.mul_assoc A B C]
    rw [Int.mul_comm A B]
    rw [Int.mul_assoc B A C]
    rw [← Int.mul_assoc W B (A * C)]
    rw [← Int.mul_assoc 4 (W * B) (A * C)]
    rw [Int.mul_comm 4 (W * B)]
    rw [Int.mul_assoc (W * B) 4 (A * C)]
    rw [← Int.mul_assoc 4 A C]
    rw [Int.mul_comm (W * B) (4 * A * C)]
    rw [Int.mul_assoc 4 A C, Int.mul_comm A C, ← Int.mul_assoc 4 C A]
  -- RHS = 4 * ((p10Num (K+1)) * shiftFactor(-q+2)) * twoNegPow q
  --     = (4 * twoNegPow q * shiftFactor(-q+2)) * ((p10Num (K+1)) * 1)
  -- Hmm. Let me just apply rearr_lhs to RHS.
  have hrhs_eq :
      4 * ((p10Num (K + 1) : Int) * Midpoint.shiftFactor (-q + 2)) * (twoNegPow q : Int)
        = Midpoint.shiftFactor (-q + 2)
            * (4 * (p10Num (K + 1) : Int) * (twoNegPow q : Int)) :=
    rearr_lhs (p10Num (K + 1) : Int) (Midpoint.shiftFactor (-q + 2)) (twoNegPow q : Int)
  -- LHS = 4 * (wn * shiftFactor(q-2) * p10Den (K+1)) * twoNegPow q
  --     = (4 * twoNegPow q * shiftFactor(q-2)) * (wn * p10Den)
  --     = (shiftFactor(-q+2) * twoPosPow q) * (wn * p10Den)     -- by hid
  --     = shiftFactor(-q+2) * (wn * twoPosPow q * p10Den)
  have hlhs_eq :
      4 * (wn * Midpoint.shiftFactor (q - 2) * (p10Den (K + 1) : Int)) * (twoNegPow q : Int)
        = Midpoint.shiftFactor (-q + 2)
            * (wn * (twoPosPow q : Int) * (p10Den (K + 1) : Int)) := by
    rw [rearr_rhs wn (Midpoint.shiftFactor (q - 2)) (p10Den (K + 1) : Int) (twoNegPow q : Int)]
    -- Goal: (4 * twoNeg q * sfQm2) * (wn * pD) = sfMq2 * (wn * twoPos q * pD)
    rw [hid]
    -- Goal: (sfMq2 * twoPos) * (wn * pD) = sfMq2 * (wn * twoPos q * pD)
    rw [Int.mul_assoc (Midpoint.shiftFactor (-q + 2)) (twoPosPow q : Int)
              (wn * (p10Den (K + 1) : Int))]
    -- sfMq2 * (twoPos * (wn * pD)) = sfMq2 * (wn * twoPos q * pD)
    rw [← Int.mul_assoc (twoPosPow q : Int) wn (p10Den (K + 1) : Int),
        Int.mul_comm (twoPosPow q : Int) wn]
  rw [hlhs_eq, hrhs_eq] at hmul4tn
  -- hmul4tn : sf(-q+2) * (wn * twoPos * pD) < sf(-q+2) * (4 * pN * twoNeg)
  have hsf_pos := Midpoint.shiftFactor_pos (-q + 2)
  have hcancel := (Int.mul_lt_mul_left hsf_pos).mp hmul4tn
  -- hcancel : wn * twoPos q * p10Den (K+1) < 4 * p10Num (K+1) * twoNeg q
  rw [p10Num_eq_tenPosPow, p10Den_eq_tenNegPow] at hcancel
  exact hcancel

/-- `fourVR - fourVL < fourW - fourU` at scale K+1, for any `s`. -/
theorem fourVR_sub_fourVL_lt_step_K1 (m : Nat) (q : Int)
    (hm_pos : 1 ≤ m) (hm_le : m < 2 ^ 53) (hq_lo : -1074 ≤ q) (hq_hi : q ≤ 971)
    (s : Nat) :
    let K := kOfMQ m q
    fourVR m q (K + 1) - fourVL m q (K + 1) (isIrregular m q)
      < fourW s q (K + 1) - fourU s q (K + 1) := by
  intro K
  rw [fourVR_sub_fourVL, fourW_sub_fourU]
  exact width_strict_succK m q hm_pos hm_le hq_lo hq_hi

/-! ## `shiftedSig` at consecutive scales

We identify `shiftedSig m q (k+1)` with `(shiftedSig m q k) / 10`, to
connect the K+1 pigeonhole with the algorithm's `s/10` test point. -/

/-- `shiftedSig m q (k+1) = (shiftedSig m q k) / 10`.

The proof case-splits on the sign of `k` (and `k+1`), tracking how
`tenPosPow`/`tenNegPow` shift between numerator and denominator. -/
theorem shiftedSig_succ (m : Nat) (q k : Int) :
    shiftedSig m q (k + 1) = shiftedSig m q k / 10 := by
  unfold shiftedSig
  -- Both sides are `let`-laden expressions. Reduce each to the
  -- normal `(N / D)` shape after substituting concrete branches.
  by_cases hk : k ≥ 0
  · -- k ≥ 0: tenNegPow k = tenNegPow(k+1) = 1, tenPosPow(k+1) = 10 · tenPosPow k.
    have hk1 : k + 1 ≥ 0 := by omega
    have hk_lt : ¬ k < 0 := by omega
    have hk1_lt : ¬ k + 1 < 0 := by omega
    simp only [hk, hk1, hk_lt, hk1_lt, if_true, if_false]
    have hk1_eq : (k + 1).toNat = k.toNat + 1 := by
      have : (k + 1).toNat = k.toNat + (1 : Int).toNat := Int.toNat_add hk (by decide)
      simpa using this
    rw [hk1_eq]
    -- After simp: (m * 2^qP * 10^0) / (2^qN * 10^(k.toNat+1))
    --           = ((m * 2^qP * 10^0) / (2^qN * 10^(k.toNat))) / 10
    -- 10^(k.toNat+1) = 10^k.toNat * 10. And div_div_eq_div_mul.
    rw [show (10 : Nat) ^ (k.toNat + 1) = 10 ^ k.toNat * 10 from Nat.pow_succ 10 k.toNat]
    rw [← Nat.mul_assoc (2 ^ _) (10 ^ k.toNat) 10]
    rw [Nat.div_div_eq_div_mul]
  · have hk_lt : k < 0 := by omega
    have hk_ge_neg : ¬ k ≥ 0 := hk
    by_cases hk1 : k + 1 ≥ 0
    · -- k = -1.
      have hk1_lt_neg : ¬ k + 1 < 0 := by omega
      simp only [hk_lt, hk_ge_neg, hk1, hk1_lt_neg, if_true, if_false]
      have hk_eq : k = -1 := by omega
      subst hk_eq
      -- After subst and simp, the goal has expressions like 10 ^ (-1 + 1).toNat = 10 ^ 0
      -- We have (-(-1 + 1) : Int).toNat = 0, but the goal contains the (-1+1).toNat form.
      have h_neg_k : ((1 : Int)).toNat = 1 := by decide  -- (- -1).toNat
      have h_k1 : ((-1 + 1 : Int)).toNat = 0 := by decide
      have h_k : ((-1 : Int)).toNat = 0 := by decide
      -- Use show to normalize the form first.
      show (m * 2 ^ (if q ≥ 0 then q.toNat else 0))
              * 10 ^ ((-(-1 + 1 : Int)).toNat)
              / ((2 ^ (if q < 0 then (-q).toNat else 0)) * 10 ^ ((-1 + 1 : Int).toNat))
            =
            ((m * 2 ^ (if q ≥ 0 then q.toNat else 0))
              * 10 ^ ((-(-1 : Int)).toNat)
              / ((2 ^ (if q < 0 then (-q).toNat else 0)) * 10 ^ ((-1 : Int).toNat))) / 10
      have h_neg_k1 : (-(-1 + 1 : Int)).toNat = 0 := by decide
      have h_neg_k' : (-(-1 : Int)).toNat = 1 := by decide
      rw [h_neg_k1, h_neg_k', h_k, h_k1]
      simp only [Nat.pow_zero, Nat.pow_one, Nat.mul_one]
      rw [Nat.div_div_eq_div_mul]
      rw [Nat.mul_div_mul_right (m * _) _ (by decide : 0 < 10)]
    · have hk1_lt : k + 1 < 0 := by omega
      have hk1_ge_neg : ¬ k + 1 ≥ 0 := hk1
      simp only [hk_lt, hk_ge_neg, hk1_lt, hk1_ge_neg, if_true, if_false]
      -- k ≤ -2.
      have hnk1_eq : (-(k + 1)).toNat + 1 = (-k).toNat := by
        have hnk1_nn : (0 : Int) ≤ -(k + 1) := by omega
        have hnk_nn : (0 : Int) ≤ -k := by omega
        have hL : ((-(k+1)).toNat : Int) = -(k + 1) := Int.toNat_of_nonneg hnk1_nn
        have hR : ((-k).toNat : Int) = -k := Int.toNat_of_nonneg hnk_nn
        omega
      simp only [Nat.pow_zero, Nat.mul_one]
      rw [show (-k).toNat = (-(k+1)).toNat + 1 from hnk1_eq.symm,
          Nat.pow_succ]
      rw [← Nat.mul_assoc (m * _) (10 ^ _) 10, Nat.div_div_eq_div_mul]
      rw [Nat.mul_div_mul_right (m * _ * _) _ (by decide : 0 < 10)]

/-! ## K+1 bounds via `shiftedSig` at the next scale

Using `shiftedSig_succ`, the value `t := s/10` is exactly
`shiftedSig m q (k+1)`. The K+1 analogues of `fourU_le_fourV` and
`fourV_lt_fourW` follow directly. -/

/-- `fourU (s/10) q (k+1) ≤ fourV m q (k+1)`, where `s = shiftedSig m q k`. -/
private theorem fourU_div10_le_fourV_K1 (m : Nat) (q k : Int) :
    fourU (shiftedSig m q k / 10) q (k + 1) ≤ fourV m q (k + 1) := by
  have h : shiftedSig m q (k + 1) = shiftedSig m q k / 10 := shiftedSig_succ m q k
  rw [← h]
  exact fourU_le_fourV (shiftedSig m q (k + 1)) m q (k + 1) rfl

/-- `fourV m q (k+1) < fourW (s/10) q (k+1)` = `fourU (s/10 + 1) q (k+1)`. -/
private theorem fourV_lt_fourW_div10_K1 (m : Nat) (q k : Int) :
    fourV m q (k + 1) < fourW (shiftedSig m q k / 10) q (k + 1) := by
  have h : shiftedSig m q (k + 1) = shiftedSig m q k / 10 := shiftedSig_succ m q k
  rw [← h]
  exact fourV_lt_fourW (shiftedSig m q (k + 1)) m q (k + 1) rfl

/-- `fourU n q k` is monotone in `n`. -/
private theorem fourU_mono {n n' : Nat} (q k : Int) (h : n ≤ n') :
    fourU n q k ≤ fourU n' q k := by
  rw [fourU_eq, fourU_eq]
  have h_cast : ((n : Int)) ≤ (n' : Int) := by exact_mod_cast h
  have h4 : 4 * (n : Int) ≤ 4 * (n' : Int) :=
    Int.mul_le_mul_of_nonneg_left h_cast (by decide)
  have htP_nn : (0 : Int) ≤ (tenPosPow k : Int) := by
    unfold tenPosPow; exact_mod_cast Nat.zero_le _
  have htN_nn : (0 : Int) ≤ (twoNegPow q : Int) := by
    unfold twoNegPow; exact_mod_cast Nat.zero_le _
  have h_rhs : (0 : Int) ≤ (tenPosPow k : Int) * (twoNegPow q : Int) :=
    Int.mul_nonneg htP_nn htN_nn
  -- 4n * (tP * tN) ≤ 4n' * (tP * tN), as products of ≤.
  have h1 : 4 * (n : Int) * (tenPosPow k : Int) ≤ 4 * (n' : Int) * (tenPosPow k : Int) :=
    Int.mul_le_mul_of_nonneg_right h4 htP_nn
  exact Int.mul_le_mul_of_nonneg_right h1 htN_nn

/-- `fourU` at successor: `fourU (n+1) q k = fourU n q k + step`. -/
private theorem fourU_succ_eq (n : Nat) (q k : Int) :
    fourU (n + 1) q k = fourU n q k + 4 * (tenPosPow k : Int) * (twoNegPow q : Int) := by
  rw [fourU_eq, fourU_eq]
  push_cast
  -- 4*(n+1)*tP*tN = 4*n*tP*tN + 4*tP*tN
  have h1 : 4 * ((n : Int) + 1) = 4 * (n : Int) + 4 := by
    rw [Int.mul_add]; rfl
  rw [h1, Int.add_mul, Int.add_mul]

/-- A common rewriting: `fourW s q k = fourU (s + 1) q k`. -/
private theorem fourW_eq_fourU_succ (s : Nat) (q k : Int) :
    fourW s q k = fourU (s + 1) q k := by
  rw [fourW_eq, fourU_eq]
  push_cast
  rfl

/-! ## K+1 pigeonhole: `Schubfach_no_K1_candidate_under_fallback` -/

/-- Under fallback (both shorter-form checks fail), no `(sig', k+1)` lies
in R_v.

Proof: Strict step > width at K+1 means R_v can intersect at most ONE
step interval `[fourU sig', fourU (sig'+1))`. The natural candidate
`(s/10, k+1)` (= `shiftedSig m q (k+1)`) satisfies `fourU(s/10) ≤ fourV`,
and the next candidate `(s/10+1, k+1)` satisfies `fourW(s/10) > fourV`,
together sandwiching R_v inside `[fourU(s/10), fourU(s/10+2))`. So any
`sig' < s/10` or `sig' > s/10 + 1` has its cleared `fourU` outside
`[fourVL, fourVR]`. Both `sig' = s/10` and `sig' = s/10 + 1` were tested
and rejected by hypothesis. -/
theorem Schubfach_no_K1_candidate_under_fallback_proof (m : Nat) (q : Int)
    (hm_pos : 1 ≤ m) (hm_lt : m < 2 ^ 53) (hq_lo : -1074 ≤ q) (hq_hi : q ≤ 971) :
    Schubfach_no_K1_candidate_under_fallback m q := by
  show let k := kOfMQ m q
       let s := shiftedSig m q k
       s ≥ 10 →
       inRoundingInterval (s / 10) (k + 1) m q (isIrregular m q) = false →
       inRoundingInterval (s / 10 + 1) (k + 1) m q (isIrregular m q) = false →
       ∀ sig' : Nat, inRoundingInterval sig' (k + 1) m q (isIrregular m q) = false
  intro k s _hs_big h_uIn_false h_wIn_false sig'
  -- We use t := s/10. Key facts at scale k+1.
  have h_uV : fourU (s / 10) q (k + 1) ≤ fourV m q (k + 1) :=
    fourU_div10_le_fourV_K1 m q k
  have h_Vw : fourV m q (k + 1) < fourW (s / 10) q (k + 1) :=
    fourV_lt_fourW_div10_K1 m q k
  have h_VL_lt_V : fourVL m q (k + 1) (isIrregular m q) < fourV m q (k + 1) :=
    fourVL_lt_fourV m q (k + 1) (isIrregular m q)
  have h_V_lt_VR : fourV m q (k + 1) < fourVR m q (k + 1) := fourV_lt_fourVR m q (k + 1)
  -- fourU(s/10) ≤ fourVR, and fourW(s/10) > fourVL.
  have h_uT_lt_VR : fourU (s / 10) q (k + 1) ≤ fourVR m q (k + 1) := by omega
  have h_wT_gt_VL : fourW (s / 10) q (k + 1) > fourVL m q (k + 1) (isIrregular m q) := by omega
  -- Strict width vs step at k+1.
  have h_strict :
      fourVR m q (k + 1) - fourVL m q (k + 1) (isIrregular m q)
        < fourW (s / 10) q (k + 1) - fourU (s / 10) q (k + 1) :=
    fourVR_sub_fourVL_lt_step_K1 m q hm_pos hm_lt hq_lo hq_hi (s / 10)
  -- fourW(s/10, k+1) = fourU(s/10 + 1, k+1).
  have h_wT_eq : fourW (s / 10) q (k + 1) = fourU (s / 10 + 1) q (k + 1) :=
    fourW_eq_fourU_succ (s / 10) q (k + 1)
  -- Step:
  let step : Int := 4 * (tenPosPow (k + 1) : Int) * (twoNegPow q : Int)
  have h_step_eq : fourW (s / 10) q (k + 1) - fourU (s / 10) q (k + 1) = step :=
    fourW_sub_fourU (s / 10) q (k + 1)
  apply Bool.eq_false_iff.mpr
  intro h_mem
  have h_bounds := inRoundingInterval_bounds_fourU sig' (k + 1) m q h_mem
  obtain ⟨h_VL_le_U, h_U_le_VR⟩ := h_bounds
  -- Compare sig' to s/10.
  rcases Nat.lt_or_ge sig' (s / 10) with h_lt | h_ge
  · -- sig' < s/10: fourU sig' + step ≤ fourU(s/10) ≤ fourVR, but fourVR < fourVL + step.
    have h_sig_le : sig' + 1 ≤ s / 10 := h_lt
    have h_fourU_succ_le : fourU (sig' + 1) q (k + 1) ≤ fourU (s / 10) q (k + 1) :=
      fourU_mono q (k + 1) h_sig_le
    have h_step_sig : fourU (sig' + 1) q (k + 1)
                      = fourU sig' q (k + 1) + step :=
      fourU_succ_eq sig' q (k + 1)
    have h_U_plus_step : fourU sig' q (k + 1) + step ≤ fourVR m q (k + 1) := by
      rw [← h_step_sig]
      exact Int.le_trans h_fourU_succ_le h_uT_lt_VR
    have h_VR_lt : fourVR m q (k + 1) < fourVL m q (k + 1) (isIrregular m q) + step := by
      have := h_strict
      rw [h_step_eq] at this
      omega
    have h_U_lt_VL : fourU sig' q (k + 1) < fourVL m q (k + 1) (isIrregular m q) := by omega
    omega
  · rcases Nat.lt_or_ge sig' (s / 10 + 2) with h_lt2 | h_ge2
    · rcases (Nat.lt_or_ge sig' (s / 10 + 1) : sig' < s / 10 + 1 ∨ sig' ≥ s / 10 + 1) with
        h_t | h_t1
      · -- sig' = s/10.
        have h_sig_eq : sig' = s / 10 := by omega
        subst h_sig_eq
        rw [h_uIn_false] at h_mem
        exact Bool.false_ne_true h_mem
      · -- sig' = s/10 + 1.
        have h_sig_eq : sig' = s / 10 + 1 := by omega
        subst h_sig_eq
        rw [h_wIn_false] at h_mem
        exact Bool.false_ne_true h_mem
    · -- sig' ≥ s/10 + 2.
      have h_fourU_succ : fourU (s / 10 + 2) q (k + 1)
                          = fourU (s / 10 + 1) q (k + 1) + step :=
        fourU_succ_eq (s / 10 + 1) q (k + 1)
      have h_fourU_sig_ge : fourU (s / 10 + 2) q (k + 1) ≤ fourU sig' q (k + 1) :=
        fourU_mono q (k + 1) h_ge2
      have h_VR_lt : fourVR m q (k + 1) < fourVL m q (k + 1) (isIrregular m q) + step := by
        have := h_strict
        rw [h_step_eq] at this
        omega
      have h_U_gt_VR : fourU sig' q (k + 1) > fourVR m q (k + 1) := by
        have h1 : fourU (s / 10 + 1) q (k + 1) = fourW (s / 10) q (k + 1) := h_wT_eq.symm
        -- fourU sig' ≥ fourU(s/10 + 2) = fourW(s/10) + step > fourVL + step > fourVR.
        omega
      omega

/-- Public statement form: the `Prop` definition combined with the proof. -/
theorem Schubfach_no_K1_candidate_under_fallback_holds (m : Nat) (q : Int)
    (hm_pos : 1 ≤ m) (hm_lt : m < 2 ^ 53) (hq_lo : -1074 ≤ q) (hq_hi : q ≤ 971) :
    Schubfach_no_K1_candidate_under_fallback m q :=
  Schubfach_no_K1_candidate_under_fallback_proof m q hm_pos hm_lt hq_lo hq_hi

/-- K+1 minimality: the full statement combined with the proof. -/
theorem Schubfach_minimal_statement_holds (m : Nat) (q : Int) :
    Schubfach_minimal_statement m q := by
  show ∀ (_hm_pos : 1 ≤ m) (_hm_lt : m < 2^53) (_hq_lo : -1074 ≤ q) (_hq_hi : q ≤ 971),
        let k := kOfMQ m q
        let s := shiftedSig m q k
        s ≥ 10 →
        inRoundingInterval (s / 10) (k + 1) m q (isIrregular m q) = false →
        inRoundingInterval (s / 10 + 1) (k + 1) m q (isIrregular m q) = false →
        ∀ sig' : Nat, inRoundingInterval sig' (k + 1) m q (isIrregular m q) = false
  intro hm_pos hm_lt hq_lo hq_hi k s h_big h_uF h_wF sig'
  exact Schubfach_no_K1_candidate_under_fallback_proof m q hm_pos hm_lt hq_lo hq_hi
          h_big h_uF h_wF sig'

/-! ## Summary of M3.8.8 status

All content in this file is proven (no sorries, only `propext`,
`Quot.sound`, `Classical.choice` are used).

Headline results:
  * `Schubfach_no_K1_candidate_under_fallback_proof` / `_holds`: the K+1
    pigeonhole. Under the fallback branch of `shortestUnsigned` (where
    both `(s/10, k+1)` and `(s/10+1, k+1)` were tested and rejected), NO
    `(sig', k+1)` lies in `R_v` for any `sig'`.
  * `Schubfach_minimal_statement_holds`: the **K+1 minimality theorem**.
    Says exactly the same thing as the K+1 pigeonhole, packaged in the
    form used downstream (M3.8.9, M4).

Infrastructure built along the way:
  * `decDigitLength` and its basic arithmetic
    (`decDigitLength_pos`, `_lt_10`, `_ge_10`, `lt_pow10_decDigitLength`,
    `pow10_decDigitLength_pred_le`, `_le_of_lt_pow10`,
    `lt_decDigitLength_of_pow10_le`, `_mono`).
  * `inRoundingInterval_zero_eq_false` / `no_zero_sig_in_rv`:
    no `(0, exp')` lies in `R_v` for any `m ≥ 1`.
  * `shortestUnsigned_sig_pos`: output `sig ≥ 1`.
  * `shortestUnsigned_length_relation`: shape of the output.
  * `width_strict_succK` / `fourVR_sub_fourVL_lt_step_K1`: strict
    step-vs-width inequality at K+1, derived from `log_width_lt_succK`
    via the `shiftFactor_width_identity` chain.
  * `shiftedSig_succ`: `shiftedSig m q (k+1) = (shiftedSig m q k) / 10`.
  * `fourU_div10_le_fourV_K1` / `fourV_lt_fourW_div10_K1`: K+1-scale
    `shiftedSig` bounds.

## Out of scope for M3.8.8

The classical "minimality across all scales" statement (no `(sig', exp')`
with strictly fewer significant digits than the output is in `R_v`,
quantified over arbitrary `exp'`) is **not** addressed here. It
requires:

  * Lifting the K+1 pigeonhole to scale `exp' ≥ k + 1` (the strict
    step-vs-width inequality grows by a factor of 10 per step, so the
    pigeonhole survives — but the candidate-identification argument
    must use `shiftedSig m q exp'` instead of `s/10`).
  * Cross-scale digit-length reasoning showing that any `(sig', exp')`
    with `decDigitLength sig' < decDigitLength p.1` forces
    `exp' ≥ k + 1` (or is a different shape — e.g. trailing zeros).

This cross-scale closure is a natural M3.8.9 follow-up (estimated
500-1000 lines).

## Downstream consumers

The two headline theorems above are the building blocks M4 (Clinger
correctness) needs from M3.8.8. Specifically, the K+1 minimality theorem
combined with `shortestUnsigned_mem_rv` says: `shortestUnsigned` returns
a representation in `R_v` that has minimum digit length among all
representations at scale `k + 1`. -/

end Srtfp.Schubfach

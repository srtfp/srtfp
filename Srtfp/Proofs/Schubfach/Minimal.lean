/- Classical minimality of `toDecimal` on canonical Decimals (M3.8.9 re-scoped).

   The original M3.8.9 statement — "no Decimal with fewer digits rounds to v" —
   is **false** for the raw `shortestUnsigned` output, because the raw output
   may carry trailing zeros (e.g., `(10^15, -13)` representing `v = 100`
   has 16-digit significand, but `(1, 2)` also represents `100` with 1 digit).

   M3.8.9 holds, however, when the competing decimal `(sig', exp')` is itself
   canonical (`sig' % 10 ≠ 0`).

   ## Headline result

   `toDecimal_minimal` at the end of this file (around line 1960) is the full
   cross-scale classical minimality theorem: for any canonical competitor at
   any scale, its digit length is at least that of the `toDecimal` output.
   It is the union of two pieces:
     * `toDecimal_minimal_high_scale` — `exp' ≥ k + 1` case, via the K+1
       pigeonhole + shift-invariance of `inRoundingInterval` (~lines 1389+).
     * `toDecimal_minimal_low_scale` — `exp' ≤ result.exponent` case, via the
       value-magnitude vs digit-length inequality (~lines 1655+).
   The combined theorem (~line 1962) is the user-facing one referenced from
   `Srtfp/Proofs/Correctness.lean`. -/

import Srtfp.Proofs.Schubfach.Shortest
import Srtfp.Proofs.Decimal
import Srtfp.Tactics

open Srtfp.Compat

namespace Srtfp.Schubfach

open Srtfp.Schubfach.RoundingInterval
open Srtfp.Float
open Srtfp

/-! ## Shift-invariance of `cmpScaledMixed`

The comparison `a · 2^q ⋚ b · 10^k` is preserved under value-preserving
replacements `(b, k) ↦ (10·b, k - 1)`.  Proof: depending on the sign of
`k`, the cleared `lhs`/`rhs` either both stay the same or both scale by
exactly `10`, so the comparison direction is unchanged. -/

/-- A `cmpScaledMixed` value is determined by the comparison `lhs vs rhs`
of its `cmpScaledMixed.lhs`/`.rhs`. If we replace `(lhs, rhs)` by
`(c · lhs, c · rhs)` for some positive `c`, the result is unchanged. -/
private theorem cmp_branch_eq_of_scale (L R L' R' c : Int) (hc : 0 < c)
    (hL : L' = c * L) (hR : R' = c * R) :
    (if L' < R' then (-1 : Int) else if L' = R' then (0 : Int) else 1) =
    (if L < R then (-1 : Int) else if L = R then (0 : Int) else 1) := by
  rw [hL, hR]
  by_cases h_lt : L < R
  · have h : c * L < c * R := Int.mul_lt_mul_of_pos_left h_lt hc
    simp [h_lt, h]
  · by_cases h_eq : L = R
    · simp [h_eq]
    · have h_gt : R < L := by omega
      have h1 : c * R < c * L := Int.mul_lt_mul_of_pos_left h_gt hc
      have h2 : ¬ (c * L < c * R) := by omega
      have h3 : ¬ (c * L = c * R) := by omega
      simp [h_lt, h_eq, h2, h3]

/-- Shift down by one decimal place: `a · 2^q ⋚ (10·b) · 10^(k-1)` is the
same comparison as `a · 2^q ⋚ b · 10^k`. -/
private theorem cmpScaledMixed_mul10_shift_down (a : Int) (q : Int) (b : Int) (k : Int) :
    cmpScaledMixed a q (10 * b) (k - 1) = cmpScaledMixed a q b k := by
  unfold cmpScaledMixed
  by_cases hk1_pos : k ≥ 1
  · -- k ≥ 1: scale by c = 1.
    have hk_nn : k ≥ 0 := by omega
    have hk_not_lt : ¬ k < 0 := by omega
    have hk1_nn : k - 1 ≥ 0 := by omega
    have hk1_not_lt : ¬ k - 1 < 0 := by omega
    simp only [hk_nn, hk_not_lt, hk1_nn, hk1_not_lt, if_true, if_false]
    have hk_eq : k.toNat = (k - 1).toNat + 1 := by
      have h1 : (k.toNat : Int) = k := Int.toNat_of_nonneg hk_nn
      have h2 : ((k - 1).toNat : Int) = k - 1 := Int.toNat_of_nonneg hk1_nn
      have h3 : (k.toNat : Int) = ((k - 1).toNat + 1 : Int) := by rw [h1, h2]; omega
      exact_mod_cast h3
    have hpow_eq : (10 : Int) ^ k.toNat = 10 ^ (k - 1).toNat * 10 := by
      rw [hk_eq, Int.pow_succ]
    apply cmp_branch_eq_of_scale _ _ _ _ 1 (by decide)
    · -- L' = 1 * L_k (both have factor 10^0 = 1).
      simp
    · -- 10 * b * 10^(k-1) * X = 1 * (b * 10^k * X), with 10^k = 10^(k-1) * 10.
      have : (10 : Int) * b * (10 : Int) ^ (k - 1).toNat
            = b * ((10 : Int) ^ (k - 1).toNat * 10) := by
        rw [Int.mul_comm 10 b, Int.mul_assoc b 10 (_ ^ _),
            Int.mul_comm 10 _]
      rw [Int.one_mul, hpow_eq]
      -- Goal: 10 * b * 10^(k-1).toNat * X = b * (10^(k-1).toNat * 10) * X
      rw [this]
  · -- k ≤ 0: scale by c = 10.
    have hk_le_0 : k ≤ 0 := by omega
    have hk1_neg : k - 1 < 0 := by omega
    have hk1_not_nn : ¬ k - 1 ≥ 0 := by omega
    apply cmp_branch_eq_of_scale _ _ _ _ 10 (by decide)
    · -- L' = 10 * L_k.
      by_cases hk_eq0 : k = 0
      · subst hk_eq0
        have h_zero_not_lt : ¬ ((0 : Int) < 0) := by decide
        have h_neg1_lt : ((0 - 1 : Int) < 0) := by decide
        have h_neg_neg1 : (-(0 - 1 : Int)).toNat = 1 := by decide
        simp only [h_zero_not_lt, if_false, h_neg1_lt, if_true, h_neg_neg1]
        -- LHS: a * 2^qPos * 10^1.  RHS = 10 * (a * 2^qPos * 10^0) = 10 * a * 2^qPos.
        show a * (2 ^ (if q ≥ 0 then q.toNat else 0) : Int) * (10 ^ 1 : Int)
              = 10 * (a * (2 ^ (if q ≥ 0 then q.toNat else 0) : Int) * (10 ^ 0 : Int))
        have h10pow1 : (10 : Int) ^ 1 = 10 := by decide
        have h10pow0 : (10 : Int) ^ 0 = 1 := by decide
        rw [h10pow1, h10pow0, Int.mul_one]
        -- a * 2^X * 10 = 10 * (a * 2^X).
        rw [Int.mul_comm (a * _) 10]
      · have hk_lt : k < 0 := by omega
        have h_neg_k_nn : (0 : Int) ≤ -k := by omega
        have h_neg_k1_nn : (0 : Int) ≤ -(k - 1) := by omega
        have hk_eq_succ : (-(k - 1)).toNat = (-k).toNat + 1 := by
          have h1 : ((-k).toNat : Int) = -k := Int.toNat_of_nonneg h_neg_k_nn
          have h2 : ((-(k - 1)).toNat : Int) = -(k - 1) := Int.toNat_of_nonneg h_neg_k1_nn
          have h3 : ((-(k - 1)).toNat : Int) = ((-k).toNat + 1 : Int) := by
            rw [h1, h2]; omega
          exact_mod_cast h3
        simp only [hk_lt, hk1_neg, if_true]
        rw [hk_eq_succ, Int.pow_succ]
        -- LHS: a * 2^qPos * (10^(-k).toNat * 10).  RHS: 10 * (a * 2^qPos * 10^(-k).toNat).
        show a * (2 ^ (if q ≥ 0 then q.toNat else 0) : Int) * ((10 : Int) ^ (-k).toNat * 10)
              = 10 * (a * (2 ^ (if q ≥ 0 then q.toNat else 0) : Int) * (10 : Int) ^ (-k).toNat)
        rw [← Int.mul_assoc (a * _) ((10 : Int) ^ _) 10,
            Int.mul_comm _ 10]
    · -- R' = 10 * R_k.
      by_cases hk_eq0 : k = 0
      · subst hk_eq0
        have h0_ge : (0 : Int) ≥ 0 := by decide
        have h1_not_ge : ¬ ((0 - 1 : Int) ≥ 0) := by decide
        simp only [h0_ge, if_true, h1_not_ge, if_false]
        show ((10 * b) : Int) * (10 ^ 0 : Int) * (2 ^ (if q < 0 then (-q).toNat else 0) : Int)
              = 10 * (b * (10 ^ (0 : Int).toNat : Int) * (2 ^ (if q < 0 then (-q).toNat else 0) : Int))
        have h0_toNat : ((0 : Int).toNat : Nat) = 0 := by decide
        rw [h0_toNat]
        -- Both 10^0 = 1 and 10^(0:Int).toNat = 1
        have h10pow0 : (10 : Int) ^ 0 = 1 := by decide
        rw [h10pow0]
        rw [Int.mul_one]
        -- 10 * b * X = 10 * (b * 1 * X)
        rw [Int.mul_one b]
        rw [Int.mul_assoc 10 b _]
      · have hk_lt : k < 0 := by omega
        have hk_not_nn : ¬ k ≥ 0 := by omega
        have hk1_not_nn' : ¬ k - 1 ≥ 0 := by omega
        simp only [hk_not_nn, hk1_not_nn', if_false]
        show ((10 * b) : Int) * (10 ^ 0 : Int) * (2 ^ (if q < 0 then (-q).toNat else 0) : Int)
              = 10 * (b * (10 ^ 0 : Int) * (2 ^ (if q < 0 then (-q).toNat else 0) : Int))
        have h10pow0 : (10 : Int) ^ 0 = 1 := by decide
        rw [h10pow0, Int.mul_one b, Int.mul_one (10 * b)]
        rw [Int.mul_assoc 10 b _]

/-! ## Shift-invariance of `inRoundingInterval` -/

/-- Shifting `(sig, exp)` down to `(10 · sig, exp - 1)` represents the same
rational and so preserves R_v membership. -/
theorem inRoundingInterval_mul10_shift_down
    (sig : Nat) (exp : Int) (m : Nat) (q : Int) (irreg : Bool) :
    inRoundingInterval (10 * sig) (exp - 1) m q irreg
      = inRoundingInterval sig exp m q irreg := by
  have heq : 4 * ((10 * sig : Nat) : Int) = 10 * (4 * (sig : Int)) := by
    push_cast
    show (4 : Int) * (10 * (sig : Int)) = 10 * (4 * (sig : Int))
    rw [← Int.mul_assoc 4 10 _, Int.mul_comm 4 10, Int.mul_assoc 10 4 _]
  have h_left :
      cmpScaledMixed (if irreg then 4 * (m : Int) - 1 else 4 * (m : Int) - 2) q
                     (4 * ((10 * sig : Nat) : Int)) (exp - 1)
      = cmpScaledMixed (if irreg then 4 * (m : Int) - 1 else 4 * (m : Int) - 2) q
                       (4 * (sig : Int)) exp := by
    rw [heq]
    exact cmpScaledMixed_mul10_shift_down _ _ _ _
  have h_right :
      cmpScaledMixed (4 * (m : Int) + 2) q (4 * ((10 * sig : Nat) : Int)) (exp - 1)
      = cmpScaledMixed (4 * (m : Int) + 2) q (4 * (sig : Int)) exp := by
    rw [heq]
    exact cmpScaledMixed_mul10_shift_down _ _ _ _
  -- Unfold inRoundingInterval and rewrite the two cmp calls.
  show
    (let leftN : Int := if irreg then 4 * (m : Int) - 1 else 4 * (m : Int) - 2
     let rightN : Int := 4 * (m : Int) + 2
     let cmpL := cmpScaledMixed leftN q (4 * ((10 * sig : Nat) : Int)) (exp - 1)
     let cmpR := cmpScaledMixed rightN q (4 * ((10 * sig : Nat) : Int)) (exp - 1)
     let cEven := m % 2 = 0
     let leftOK := decide (cmpL < 0) || decide (cmpL = 0) && decide cEven
     let rightOK := decide (cmpR > 0) || decide (cmpR = 0) && decide cEven
     leftOK && rightOK)
    =
    (let leftN : Int := if irreg then 4 * (m : Int) - 1 else 4 * (m : Int) - 2
     let rightN : Int := 4 * (m : Int) + 2
     let cmpL := cmpScaledMixed leftN q (4 * (sig : Int)) exp
     let cmpR := cmpScaledMixed rightN q (4 * (sig : Int)) exp
     let cEven := m % 2 = 0
     let leftOK := decide (cmpL < 0) || decide (cmpL = 0) && decide cEven
     let rightOK := decide (cmpR > 0) || decide (cmpR = 0) && decide cEven
     leftOK && rightOK)
  simp only [h_left, h_right]

/-- Iterate `mul10_shift_down`: `(sig · 10^j, exp - j)` represents the same
rational as `(sig, exp)`. -/
theorem inRoundingInterval_mul10pow_shift_down
    (sig : Nat) (j : Nat) (exp : Int) (m : Nat) (q : Int) (irreg : Bool) :
    inRoundingInterval (sig * 10 ^ j) (exp - (j : Int)) m q irreg
      = inRoundingInterval sig exp m q irreg := by
  induction j with
  | zero =>
    show inRoundingInterval (sig * 10 ^ 0) (exp - ((0 : Nat) : Int)) m q irreg
          = inRoundingInterval sig exp m q irreg
    simp
  | succ k ih =>
    have hpow : sig * 10 ^ (k + 1) = 10 * (sig * 10 ^ k) := by
      rw [Nat.pow_succ, Nat.mul_comm (10 ^ k) 10, ← Nat.mul_assoc,
          Nat.mul_comm sig 10, Nat.mul_assoc]
    have hexp : exp - ((k + 1 : Nat) : Int) = (exp - (k : Nat)) - 1 := by
      push_cast; omega
    rw [hpow, hexp, inRoundingInterval_mul10_shift_down, ih]

/-! ## Lifting the K+1 pigeonhole to higher scales

Under fallback, the K+1 pigeonhole forbids any `(sig', k+1)` from being
in R_v. We now lift this to any `(sig', exp')` with `exp' ≥ k+1`, since
such a candidate is value-equivalent to one at scale `k+1`. -/

/-- Under fallback, **no decimal at any scale `≥ k+1`** lies in R_v.

This is the K+1 pigeonhole lifted to all scales above K+1 by shift-invariance
of `inRoundingInterval`. The statement matches `Schubfach_no_K1_candidate_under_fallback`
in shape, but quantifies `exp' ≥ k+1` instead of `exp' = k+1`. -/
theorem Schubfach_no_high_scale_under_fallback_proof (m : Nat) (q : Int)
    (hm_pos : 1 ≤ m) (hm_lt : m < 2 ^ 53) (hq_lo : -1074 ≤ q) (hq_hi : q ≤ 971) :
    let k := kOfMQ m q
    let s := shiftedSig m q k
    s ≥ 10 →
    inRoundingInterval (s / 10) (k + 1) m q (isIrregular m q) = false →
    inRoundingInterval (s / 10 + 1) (k + 1) m q (isIrregular m q) = false →
    ∀ (sig' : Nat) (exp' : Int), exp' ≥ k + 1 →
      inRoundingInterval sig' exp' m q (isIrregular m q) = false := by
  intro k s hs_big h_uIn_false h_wIn_false sig' exp' h_exp_ge
  have h_diff_nn : 0 ≤ exp' - (k + 1) := by omega
  let j : Nat := (exp' - (k + 1)).toNat
  have h_j_eq : (j : Int) = exp' - (k + 1) := Int.toNat_of_nonneg h_diff_nn
  have h_exp_form : exp' - (j : Int) = k + 1 := by
    rw [h_j_eq]; omega
  have hshift :
      inRoundingInterval (sig' * 10 ^ j) (exp' - (j : Int)) m q (isIrregular m q)
        = inRoundingInterval sig' exp' m q (isIrregular m q) :=
    inRoundingInterval_mul10pow_shift_down sig' j exp' m q (isIrregular m q)
  rw [h_exp_form] at hshift
  have h_K1 := Schubfach_no_K1_candidate_under_fallback_proof m q hm_pos hm_lt hq_lo hq_hi
                  hs_big h_uIn_false h_wIn_false (sig' * 10 ^ j)
  rw [← hshift]
  exact h_K1

/-! ## Top-level classical-minimality theorem

The full toDecimal classical minimality statement. We phrase it on
finite, non-zero Floats only (NaN/Inf/zero are handled by the trivial
cases of `toDecimal`). The minimality covers competing decimals
`(sig', exp')` whose **value lies in R_v** and which have **strictly
fewer digits than the canonical Schubfach output**, restricted to
canonical competitors (`sig' % 10 ≠ 0`). The argument routes through
the K+1 pigeonhole, which provides what we need for any candidate at
scales `≥ k + 1`. -/

/-- Helper: the canonical-minimality bound under fallback.

For any `(sig', exp')` (canonical or otherwise) at scale `exp' ≥ k+1`,
where `k = kOfMQ m q`, when `shortestUnsigned` is in fallback,
`(sig', exp')` is not in R_v. -/
theorem toDecimal_no_higher_scale_under_fallback
    (w : UInt64)
    (h_fin : Word.isFinite w = true)
    (h_nonzero : (Word.decode w).m ≠ 0) :
    let d := Word.decode w
    let k := kOfMQ d.m d.q
    let s := shiftedSig d.m d.q k
    s ≥ 10 →
    inRoundingInterval (s / 10) (k + 1) d.m d.q (isIrregular d.m d.q) = false →
    inRoundingInterval (s / 10 + 1) (k + 1) d.m d.q (isIrregular d.m d.q) = false →
    ∀ (sig' : Nat) (exp' : Int), exp' ≥ k + 1 →
      inRoundingInterval sig' exp' d.m d.q (isIrregular d.m d.q) = false := by
  intro d k s hs_big h_u h_w sig' exp' h_exp
  have ⟨h_m_lt, h_q_lo, h_q_hi⟩ :=
    Srtfp.Schubfach.decode_invariants_bits w h_fin
  have h_m_pos : 1 ≤ d.m := Nat.one_le_iff_ne_zero.mpr h_nonzero
  exact Schubfach_no_high_scale_under_fallback_proof d.m d.q h_m_pos h_m_lt h_q_lo h_q_hi
          hs_big h_u h_w sig' exp' h_exp

/-! ## Connecting decDigitLength to exponent bounds

For canonical `(sig', exp')` (sig' ≠ 0, sig' % 10 ≠ 0) with the value
sitting in R_v (so the value is positive and bounded above by `v_r`),
and with `decDigitLength sig'` strictly less than the canonical
Schubfach output's digit length, the magnitude argument forces
`exp' ≥ k + 1` — which then routes into the fallback-higher-scale theorem.

The magnitude argument is non-trivial and relies on bounds on `v_r` in
terms of `m, q`. We skip this and provide a strictly weaker but
syntactically faithful classical statement: the canonical-and-higher-scale
form. -/

/-- **Classical minimality** of `toDecimal` on canonical Decimals.

Under fallback, no canonical decimal whose **scale `exp'` exceeds `k`**
lies in R_v. Equivalently: the canonical Schubfach output (which sits at
exponent `k` in the fallback case) is the lowest-exponent canonical
decimal in R_v — any canonical decimal **representing a value in R_v**
must have `exp' ≤ k`.

This is the K+1 pigeonhole expressed in canonical-only form. -/
theorem toDecimal_classically_minimal_canonical
    (w : UInt64)
    (h_fin : Word.isFinite w = true)
    (h_nonzero : (Word.decode w).m ≠ 0) :
    let d := Word.decode w
    let k := kOfMQ d.m d.q
    let s := shiftedSig d.m d.q k
    s ≥ 10 →
    inRoundingInterval (s / 10) (k + 1) d.m d.q (isIrregular d.m d.q) = false →
    inRoundingInterval (s / 10 + 1) (k + 1) d.m d.q (isIrregular d.m d.q) = false →
    ∀ (_sign' : Bool) (sig' : Nat) (exp' : Int),
      sig' ≠ 0 →
      sig' % 10 ≠ 0 →
      exp' ≥ k + 1 →
      ¬ inRoundingInterval sig' exp' d.m d.q (isIrregular d.m d.q) = true := by
  intro d k s hs_big h_u h_w sign' sig' exp' _hsig_ne _hcanon h_exp_ge h_mem
  have h_false :=
    toDecimal_no_higher_scale_under_fallback w h_fin h_nonzero hs_big h_u h_w sig' exp' h_exp_ge
  rw [h_false] at h_mem
  exact Bool.false_ne_true h_mem

/-! ## Universally-quantified form: classical minimality across the toDecimal output

The most general statement that the K+1 pigeonhole supports. Phrased as
`∃ d, toDecimalBits w = .ok d ∧ ∀ canonical competitor not in R_v at any
scale ≥ k + 1` — without the digit-length comparison. -/

/-- **Universally quantified classical minimality** for `toDecimal`.

`toDecimal f` succeeds on finite non-zero floats and produces a result
`d` such that **no canonical decimal `(sign', sig', exp')` with
`exp' ≥ k + 1`** has its rational value in R_v, where `k = kOfMQ
(Word.decode w).m (Word.decode w).q`. This is the cleanest classical-minimality
result that follows directly from the K+1 pigeonhole.

In the shorter-form output cases (`uIn = true` or `wIn = true` at
`k + 1`), the output exponent IS `k + 1`, and the K+1 pigeonhole's
fallback hypothesis is not satisfied; this theorem is vacuous in those
cases. Under fallback, it gives the canonical-classical-minimality
claim. -/
theorem toDecimal_classically_minimal
    (w : UInt64)
    (h_fin : Word.isFinite w = true)
    (h_nonzero : (Word.decode w).m ≠ 0) :
    ∃ result, toDecimalBits w = .ok result ∧
      let d := Word.decode w
      let k := kOfMQ d.m d.q
      let s := shiftedSig d.m d.q k
      s ≥ 10 →
      inRoundingInterval (s / 10) (k + 1) d.m d.q (isIrregular d.m d.q) = false →
      inRoundingInterval (s / 10 + 1) (k + 1) d.m d.q (isIrregular d.m d.q) = false →
      ∀ (_sign' : Bool) (sig' : Nat) (exp' : Int),
        sig' ≠ 0 →
        sig' % 10 ≠ 0 →
        exp' ≥ k + 1 →
        ¬ inRoundingInterval sig' exp' d.m d.q (isIrregular d.m d.q) = true := by
  obtain ⟨result, hresult, _⟩ := toDecimalBits_in_Rv w h_fin h_nonzero
  refine ⟨result, hresult, ?_⟩
  intro d k s hs_big h_u h_w sign' sig' exp' h_sig_ne h_canon h_exp_ge h_mem
  exact toDecimal_classically_minimal_canonical w h_fin h_nonzero
          hs_big h_u h_w sign' sig' exp' h_sig_ne h_canon h_exp_ge h_mem

/-! ## Cross-scale infrastructure

Tools for the cross-scale-shortest theorem.

### Phase A: Magnitude bounds connecting `inRoundingInterval` membership
to integer bounds on `sig' · 10^exp'`. -/

/-- Internal: cleared `fourVL ≤ fourU` bounds for an `inRoundingInterval` witness.
Re-derived locally from `inRoundingInterval_iff` since the canonical version
in `Shortest.lean` is private. -/
private theorem inRoundingInterval_bounds_fourU_local
    (sig' : Nat) (exp' : Int) (m : Nat) (q : Int)
    (h : inRoundingInterval sig' exp' m q (isIrregular m q) = true) :
    fourVL m q exp' (isIrregular m q) ≤ fourU sig' q exp'
    ∧ fourU sig' q exp' ≤ fourVR m q exp' := by
  rw [inRoundingInterval_iff] at h
  obtain ⟨hL, hR⟩ := h
  refine ⟨?_, ?_⟩
  · rcases hL with hlt | ⟨heq, _⟩
    · exact Int.le_of_lt hlt
    · exact Int.le_of_eq heq
  · rcases hR with hlt | ⟨heq, _⟩
    · exact Int.le_of_lt hlt
    · exact Int.le_of_eq heq

/-- If `(sig', exp')` is in R_v, the cleared lower bound: for `m ≥ 1`,
`(4m - 2) * twoPosPow q * tenNegPow exp' ≤ 4 * sig' * tenPosPow exp' * twoNegPow q`.
Holds in both regular and irregular cases (irregular uses `4m - 1`,
which is even tighter and implies the `4m - 2` form). -/
private theorem inRoundingInterval_cleared_lower
    (sig' : Nat) (exp' : Int) (m : Nat) (q : Int)
    (_hm_pos : 1 ≤ m)
    (h_mem : inRoundingInterval sig' exp' m q (isIrregular m q) = true) :
    (4 * (m : Int) - 2) * (twoPosPow q : Int) * (tenNegPow exp' : Int)
      ≤ 4 * (sig' : Int) * (tenPosPow exp' : Int) * (twoNegPow q : Int) := by
  have ⟨h_VL_le_U, _⟩ :=
    inRoundingInterval_bounds_fourU_local sig' exp' m q h_mem
  by_cases h_irr : isIrregular m q = true
  · rw [fourVL_eq_irregular m q exp' h_irr] at h_VL_le_U
    rw [fourU_eq] at h_VL_le_U
    -- (4m-1) * ... ≤ 4*sig' * ..., and we want (4m-2) * ... ≤ 4*sig' * ...
    have hpos : (0 : Int) < (twoPosPow q : Int) * (tenNegPow exp' : Int) :=
      twoPos_tenNeg_pos_Int q exp'
    have h_step : ((4 * (m : Int) - 2) : Int) ≤ (4 * (m : Int) - 1) := by omega
    have h_step' : (4 * (m : Int) - 2) * ((twoPosPow q : Int) * (tenNegPow exp' : Int))
                    ≤ (4 * (m : Int) - 1) * ((twoPosPow q : Int) * (tenNegPow exp' : Int)) :=
      Int.mul_le_mul_of_nonneg_right h_step (Int.le_of_lt hpos)
    have hassoc1 : (4 * (m : Int) - 2) * ((twoPosPow q : Int) * (tenNegPow exp' : Int))
                    = (4 * (m : Int) - 2) * (twoPosPow q : Int) * (tenNegPow exp' : Int) := by
      rw [Int.mul_assoc]
    have hassoc2 : (4 * (m : Int) - 1) * ((twoPosPow q : Int) * (tenNegPow exp' : Int))
                    = (4 * (m : Int) - 1) * (twoPosPow q : Int) * (tenNegPow exp' : Int) := by
      rw [Int.mul_assoc]
    rw [hassoc1, hassoc2] at h_step'
    exact Int.le_trans h_step' h_VL_le_U
  · rw [fourVL_eq_regular m q exp' h_irr] at h_VL_le_U
    rw [fourU_eq] at h_VL_le_U
    exact h_VL_le_U

/-- If `(sig', exp')` is in R_v, the cleared upper bound. -/
private theorem inRoundingInterval_cleared_upper
    (sig' : Nat) (exp' : Int) (m : Nat) (q : Int)
    (h_mem : inRoundingInterval sig' exp' m q (isIrregular m q) = true) :
    4 * (sig' : Int) * (tenPosPow exp' : Int) * (twoNegPow q : Int)
      ≤ (4 * (m : Int) + 2) * (twoPosPow q : Int) * (tenNegPow exp' : Int) := by
  have ⟨_, h_U_le_VR⟩ :=
    inRoundingInterval_bounds_fourU_local sig' exp' m q h_mem
  rw [fourU_eq, fourVR_eq] at h_U_le_VR
  exact h_U_le_VR

/-- If `(sig', exp')` is in R_v with `m ≥ 1`, then `sig' ≥ 1` (the value
is bounded below by `v_l > 0`). -/
private theorem inRoundingInterval_sig_pos
    (sig' : Nat) (exp' : Int) (m : Nat) (q : Int)
    (hm_pos : 1 ≤ m)
    (h_mem : inRoundingInterval sig' exp' m q (isIrregular m q) = true) :
    1 ≤ sig' := by
  by_contra h_not
  have h_zero : sig' = 0 := by omega
  subst h_zero
  have h_false := inRoundingInterval_zero_eq_false exp' m q (isIrregular m q) hm_pos
  rw [h_false] at h_mem
  exact Bool.false_ne_true h_mem

/-! ## Phase A: Digit count vs cleared magnitude

Connecting `decDigitLength sig'` to the cleared cross-mul form. -/

/-- **Lower-bound on decDigitLength**: if `sig' ≥ 1` is in R_v, then
`sig' ≥ 10^(L'-1)` so the cleared lower endpoint forces
`(4m - 2) * 2^q * 10^{-exp'} < 4 * 10^L' * 10^exp' * 2^{-q}`. -/
private theorem digit_lower_bound_from_Rv
    (sig' : Nat) (exp' : Int) (m : Nat) (q : Int)
    (hm_pos : 1 ≤ m)
    (h_mem : inRoundingInterval sig' exp' m q (isIrregular m q) = true) :
    (4 * (m : Int) - 2) * (twoPosPow q : Int) * (tenNegPow exp' : Int)
      < 4 * (10 : Int) ^ (decDigitLength sig')
          * (tenPosPow exp' : Int) * (twoNegPow q : Int) := by
  have hsig_pos := inRoundingInterval_sig_pos sig' exp' m q hm_pos h_mem
  have h_lo := inRoundingInterval_cleared_lower sig' exp' m q hm_pos h_mem
  -- h_lo : (4m-2)*twoPos*tenNeg ≤ 4*sig'*tenPos*twoNeg
  -- want: ... < 4*10^L' * tenPos * twoNeg
  have h_sig_lt : (sig' : Int) < (10 : Int) ^ (decDigitLength sig') := by
    have hlt := lt_pow10_decDigitLength sig' hsig_pos
    exact_mod_cast hlt
  have hpos : (0 : Int) < (tenPosPow exp' : Int) * (twoNegPow q : Int) :=
    tenPos_twoNeg_pos_Int q exp'
  have h4pos : (0 : Int) < 4 := by decide
  have h4tp_pos : (0 : Int) < 4 * ((tenPosPow exp' : Int) * (twoNegPow q : Int)) :=
    Int.mul_pos h4pos hpos
  have h_step : 4 * (sig' : Int) * (tenPosPow exp' : Int) * (twoNegPow q : Int)
                  < 4 * (10 : Int) ^ (decDigitLength sig')
                      * (tenPosPow exp' : Int) * (twoNegPow q : Int) := by
    have h4mul : 4 * (sig' : Int) < 4 * (10 : Int) ^ (decDigitLength sig') :=
      Int.mul_lt_mul_of_pos_left h_sig_lt h4pos
    have htP_nn : (0 : Int) ≤ (tenPosPow exp' : Int) := by
      unfold tenPosPow; exact_mod_cast Nat.zero_le _
    have htN_pos : (0 : Int) < (twoNegPow q : Int) := by
      unfold twoNegPow; exact_mod_cast Nat.pow_pos (a := 2) (by decide)
    have hmul2 : 4 * (sig' : Int) * (tenPosPow exp' : Int)
                  ≤ 4 * (10 : Int) ^ (decDigitLength sig') * (tenPosPow exp' : Int) :=
      Int.mul_le_mul_of_nonneg_right (Int.le_of_lt h4mul) htP_nn
    -- now multiply by twoNegPow q > 0 to get strict via the strict factor h4mul
    -- Actually we need strict; use strict on sig' and nn on others.
    by_cases hexp_pos : (tenPosPow exp' : Int) > 0
    · have hmul2_strict : 4 * (sig' : Int) * (tenPosPow exp' : Int)
                          < 4 * (10 : Int) ^ (decDigitLength sig') * (tenPosPow exp' : Int) :=
        Int.mul_lt_mul_of_pos_right h4mul hexp_pos
      exact Int.mul_lt_mul_of_pos_right hmul2_strict htN_pos
    · -- tenPosPow exp' > 0 always (it's a power of 10), so this branch is vacuous
      exfalso
      have h_tp_pos : (0 : Int) < (tenPosPow exp' : Int) := by
        unfold tenPosPow; exact_mod_cast Nat.pow_pos (a := 10) (by decide)
      exact hexp_pos h_tp_pos
  exact Int.lt_of_le_of_lt h_lo h_step

/-- **Upper-bound on decDigitLength**: if `sig'` is in R_v, then
`sig' < 10^L'` so the cleared upper endpoint forces
`4 * 10^(L'-1) * 10^exp' * 2^{-q} ≤ (4m + 2) * 2^q * 10^{-exp'}`. -/
private theorem digit_upper_bound_from_Rv
    (sig' : Nat) (exp' : Int) (m : Nat) (q : Int)
    (hm_pos : 1 ≤ m)
    (h_mem : inRoundingInterval sig' exp' m q (isIrregular m q) = true) :
    4 * (10 : Int) ^ (decDigitLength sig' - 1)
        * (tenPosPow exp' : Int) * (twoNegPow q : Int)
      ≤ (4 * (m : Int) + 2) * (twoPosPow q : Int) * (tenNegPow exp' : Int) := by
  have hsig_pos := inRoundingInterval_sig_pos sig' exp' m q hm_pos h_mem
  have h_up := inRoundingInterval_cleared_upper sig' exp' m q h_mem
  have h_sig_ge : (10 : Int) ^ (decDigitLength sig' - 1) ≤ (sig' : Int) := by
    have h := pow10_decDigitLength_pred_le sig' hsig_pos
    exact_mod_cast h
  have hpos : (0 : Int) < (tenPosPow exp' : Int) * (twoNegPow q : Int) :=
    tenPos_twoNeg_pos_Int q exp'
  have h4pos : (0 : Int) < 4 := by decide
  have h_step : 4 * (10 : Int) ^ (decDigitLength sig' - 1)
                    * (tenPosPow exp' : Int) * (twoNegPow q : Int)
                  ≤ 4 * (sig' : Int) * (tenPosPow exp' : Int) * (twoNegPow q : Int) := by
    have h4mul : 4 * (10 : Int) ^ (decDigitLength sig' - 1) ≤ 4 * (sig' : Int) :=
      Int.mul_le_mul_of_nonneg_left h_sig_ge (Int.le_of_lt h4pos)
    have htP_nn : (0 : Int) ≤ (tenPosPow exp' : Int) := by
      unfold tenPosPow; exact_mod_cast Nat.zero_le _
    have htN_nn : (0 : Int) ≤ (twoNegPow q : Int) := by
      unfold twoNegPow; exact_mod_cast Nat.zero_le _
    have hmul2 : 4 * (10 : Int) ^ (decDigitLength sig' - 1) * (tenPosPow exp' : Int)
                  ≤ 4 * (sig' : Int) * (tenPosPow exp' : Int) :=
      Int.mul_le_mul_of_nonneg_right h4mul htP_nn
    exact Int.mul_le_mul_of_nonneg_right hmul2 htN_nn
  exact Int.le_trans h_step h_up

/-! ## Phase A.5: shifted-sig magnitudes

A useful technical lemma: if `(sig', exp')` is in R_v and we shift it
down to a target scale `≤ exp'`, the membership is preserved (already
shown via `inRoundingInterval_mul10pow_shift_down`). -/

/-! ## Phase B: K+1 uniqueness without fallback

The K+1 pigeonhole's proof uses the strict step-vs-width bound. Without the
"both shorter-form checks fail" hypothesis, we can still conclude: any
`(sig', k+1)` in R_v must have `sig' ∈ {s/10, s/10 + 1}`. This is the
**unrestricted** form of the K+1 pigeonhole. -/

/-- At scale K+1, the only candidates for R_v membership are `s/10` and `s/10+1`.
This is the unrestricted form of the K+1 pigeonhole, holding without any
fallback hypothesis. -/
theorem Schubfach_K1_candidates (m : Nat) (q : Int)
    (hm_pos : 1 ≤ m) (hm_lt : m < 2 ^ 53) (hq_lo : -1074 ≤ q) (hq_hi : q ≤ 971) :
    let k := kOfMQ m q
    let s := shiftedSig m q k
    ∀ sig' : Nat,
      inRoundingInterval sig' (k + 1) m q (isIrregular m q) = true →
      sig' = s / 10 ∨ sig' = s / 10 + 1 := by
  intro k s sig' h_mem
  -- Use the K+1 pigeonhole structure: candidates ∉ {s/10, s/10+1} are excluded.
  -- The proof is structurally similar to `Schubfach_no_K1_candidate_under_fallback_proof`
  -- but reaches a different conclusion when `sig' ∈ {s/10, s/10+1}`.
  -- Key K+1-scale facts.
  have h_uV : fourU (s / 10) q (k + 1) ≤ fourV m q (k + 1) := by
    have h : shiftedSig m q (k + 1) = s / 10 := shiftedSig_succ m q k
    rw [← h]
    exact fourU_le_fourV (shiftedSig m q (k + 1)) m q (k + 1) rfl
  have h_Vw : fourV m q (k + 1) < fourW (s / 10) q (k + 1) := by
    have h : shiftedSig m q (k + 1) = s / 10 := shiftedSig_succ m q k
    rw [← h]
    exact fourV_lt_fourW (shiftedSig m q (k + 1)) m q (k + 1) rfl
  have h_VL_lt_V : fourVL m q (k + 1) (isIrregular m q) < fourV m q (k + 1) :=
    fourVL_lt_fourV m q (k + 1) (isIrregular m q)
  have h_V_lt_VR : fourV m q (k + 1) < fourVR m q (k + 1) := fourV_lt_fourVR m q (k + 1)
  have h_uT_lt_VR : fourU (s / 10) q (k + 1) ≤ fourVR m q (k + 1) := by omega
  have h_wT_gt_VL : fourW (s / 10) q (k + 1) > fourVL m q (k + 1) (isIrregular m q) := by omega
  have h_strict :
      fourVR m q (k + 1) - fourVL m q (k + 1) (isIrregular m q)
        < fourW (s / 10) q (k + 1) - fourU (s / 10) q (k + 1) :=
    fourVR_sub_fourVL_lt_step_K1 m q hm_pos hm_lt hq_lo hq_hi (s / 10)
  let step : Int := 4 * (tenPosPow (k + 1) : Int) * (twoNegPow q : Int)
  have h_step_eq : fourW (s / 10) q (k + 1) - fourU (s / 10) q (k + 1) = step :=
    fourW_sub_fourU (s / 10) q (k + 1)
  -- Use the bounds.
  have h_bounds := inRoundingInterval_bounds_fourU_local sig' (k + 1) m q h_mem
  obtain ⟨h_VL_le_U, h_U_le_VR⟩ := h_bounds
  -- Compare sig' to s/10.
  rcases Nat.lt_or_ge sig' (s / 10) with h_lt | h_ge
  · -- sig' < s/10: contradiction (this branch.
    exfalso
    have h_sig_le : sig' + 1 ≤ s / 10 := h_lt
    have h_fourU_succ_le : fourU (sig' + 1) q (k + 1) ≤ fourU (s / 10) q (k + 1) := by
      rw [fourU_eq, fourU_eq]
      have h_cast : ((sig' + 1 : Nat) : Int) ≤ ((s / 10 : Nat) : Int) := by exact_mod_cast h_sig_le
      have h4 : 4 * ((sig' + 1 : Nat) : Int) ≤ 4 * ((s / 10 : Nat) : Int) :=
        Int.mul_le_mul_of_nonneg_left h_cast (by decide)
      have htP_nn : (0 : Int) ≤ (tenPosPow (k + 1) : Int) := by
        unfold tenPosPow; exact_mod_cast Nat.zero_le _
      have htN_nn : (0 : Int) ≤ (twoNegPow q : Int) := by
        unfold twoNegPow; exact_mod_cast Nat.zero_le _
      have h1 : 4 * ((sig' + 1 : Nat) : Int) * (tenPosPow (k + 1) : Int)
                  ≤ 4 * ((s / 10 : Nat) : Int) * (tenPosPow (k + 1) : Int) :=
        Int.mul_le_mul_of_nonneg_right h4 htP_nn
      exact Int.mul_le_mul_of_nonneg_right h1 htN_nn
    have h_step_sig : fourU (sig' + 1) q (k + 1)
                      = fourU sig' q (k + 1) + step := by
      rw [fourU_eq, fourU_eq]
      push_cast
      show (4 * ((sig' : Int) + 1)) * (tenPosPow (k + 1) : Int) * (twoNegPow q : Int)
            = 4 * (sig' : Int) * (tenPosPow (k + 1) : Int) * (twoNegPow q : Int) + step
      show (4 * ((sig' : Int) + 1)) * (tenPosPow (k + 1) : Int) * (twoNegPow q : Int)
            = 4 * (sig' : Int) * (tenPosPow (k + 1) : Int) * (twoNegPow q : Int)
              + 4 * (tenPosPow (k + 1) : Int) * (twoNegPow q : Int)
      have : (4 * ((sig' : Int) + 1)) = 4 * (sig' : Int) + 4 := by grind
      rw [this]
      grind
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
    · -- sig' ∈ {s/10, s/10 + 1}.
      rcases Nat.lt_or_ge sig' (s / 10 + 1) with h_t | h_t1
      · -- sig' = s/10.
        left; omega
      · -- sig' = s/10 + 1.
        right; omega
    · -- sig' ≥ s/10 + 2: contradiction.
      exfalso
      have h_fourU_succ : fourU (s / 10 + 2) q (k + 1)
                          = fourU (s / 10 + 1) q (k + 1) + step := by
        rw [fourU_eq, fourU_eq]
        push_cast
        show (4 * ((s / 10 : Nat) : Int) + 8) * (tenPosPow (k + 1) : Int) * (twoNegPow q : Int)
              = (4 * ((s / 10 : Nat) : Int) + 4) * (tenPosPow (k + 1) : Int) * (twoNegPow q : Int) + step
        show (4 * ((s / 10 : Nat) : Int) + 8) * (tenPosPow (k + 1) : Int) * (twoNegPow q : Int)
              = (4 * ((s / 10 : Nat) : Int) + 4) * (tenPosPow (k + 1) : Int) * (twoNegPow q : Int)
                + 4 * (tenPosPow (k + 1) : Int) * (twoNegPow q : Int)
        grind
      have h_fourU_sig_ge : fourU (s / 10 + 2) q (k + 1) ≤ fourU sig' q (k + 1) := by
        rw [fourU_eq, fourU_eq]
        have h_cast : ((s / 10 + 2 : Nat) : Int) ≤ (sig' : Int) := by exact_mod_cast h_ge2
        have h4 : 4 * ((s / 10 + 2 : Nat) : Int) ≤ 4 * (sig' : Int) :=
          Int.mul_le_mul_of_nonneg_left h_cast (by decide)
        have htP_nn : (0 : Int) ≤ (tenPosPow (k + 1) : Int) := by
          unfold tenPosPow; exact_mod_cast Nat.zero_le _
        have htN_nn : (0 : Int) ≤ (twoNegPow q : Int) := by
          unfold twoNegPow; exact_mod_cast Nat.zero_le _
        have h1 : 4 * ((s / 10 + 2 : Nat) : Int) * (tenPosPow (k + 1) : Int)
                    ≤ 4 * (sig' : Int) * (tenPosPow (k + 1) : Int) :=
          Int.mul_le_mul_of_nonneg_right h4 htP_nn
        exact Int.mul_le_mul_of_nonneg_right h1 htN_nn
      have h_VR_lt : fourVR m q (k + 1) < fourVL m q (k + 1) (isIrregular m q) + step := by
        have := h_strict
        rw [h_step_eq] at this
        omega
      have h_wT_eq : fourW (s / 10) q (k + 1) = fourU (s / 10 + 1) q (k + 1) := by
        rw [fourW_eq, fourU_eq]
        push_cast
        rfl
      have h_U_gt_VR : fourU sig' q (k + 1) > fourVR m q (k + 1) := by
        -- fourU sig' ≥ fourU(s/10 + 2) = fourU(s/10+1) + step = fourW(s/10) + step > fourVL + step > fourVR.
        omega
      omega

/-! ## Phase C: digit count for high-scale competitors

For a competitor `(sig', exp')` at exp' ≥ k+1, the lifted K+1 candidates
theorem forces `sig' * 10^(exp'-k-1) ∈ {s/10, s/10+1}`. We use this to
bound `decDigitLength sig'`. -/

/-- For any positive Nat `sig'` and `j ≥ 0`, if `sig' * 10^j ≥ 1`, then
`decDigitLength (sig' * 10^j) = decDigitLength sig' + j` provided `sig' ≥ 1`. -/
theorem decDigitLength_mul_pow10 (sig' : Nat) (j : Nat) (h_pos : 1 ≤ sig') :
    decDigitLength (sig' * 10 ^ j) = decDigitLength sig' + j := by
  induction j with
  | zero => simp
  | succ k ih =>
    have h_pow : sig' * 10 ^ (k + 1) = (sig' * 10 ^ k) * 10 := by
      rw [Nat.pow_succ, ← Nat.mul_assoc]
    rw [h_pow]
    have hsk_pos : 1 ≤ sig' * 10 ^ k := by
      have h_pow_pos : 0 < 10 ^ k := Nat.pow_pos (a := 10) (by decide)
      have : 1 * 1 ≤ sig' * 10 ^ k := Nat.mul_le_mul h_pos h_pow_pos
      omega
    have h_ge10 : 10 ≤ sig' * 10 ^ k * 10 := by
      have : 1 * 10 ≤ sig' * 10 ^ k * 10 :=
        Nat.mul_le_mul_right 10 hsk_pos
      omega
    rw [decDigitLength_ge_10 h_ge10]
    have h_div : sig' * 10 ^ k * 10 / 10 = sig' * 10 ^ k :=
      Nat.mul_div_cancel _ (by decide : (0:Nat) < 10)
    rw [h_div, ih]
    omega

/-- Lifted form: at any scale `exp' ≥ k+1`, a sig' in R_v shifts to
either `s/10` or `s/10+1` at scale K+1. -/
theorem Schubfach_high_scale_candidates (m : Nat) (q : Int)
    (hm_pos : 1 ≤ m) (hm_lt : m < 2 ^ 53) (hq_lo : -1074 ≤ q) (hq_hi : q ≤ 971) :
    let k := kOfMQ m q
    let s := shiftedSig m q k
    ∀ (sig' : Nat) (exp' : Int),
      exp' ≥ k + 1 →
      inRoundingInterval sig' exp' m q (isIrregular m q) = true →
      let j : Nat := (exp' - (k + 1)).toNat
      sig' * 10 ^ j = s / 10 ∨ sig' * 10 ^ j = s / 10 + 1 := by
  intro k s sig' exp' h_exp_ge h_mem j
  have h_diff_nn : 0 ≤ exp' - (k + 1) := by omega
  have h_j_eq : (j : Int) = exp' - (k + 1) := Int.toNat_of_nonneg h_diff_nn
  have h_exp_form : exp' - (j : Int) = k + 1 := by
    rw [h_j_eq]; omega
  -- Lift via shift_down: (sig' * 10^j, k+1) is in R_v.
  have hshift :
      inRoundingInterval (sig' * 10 ^ j) (exp' - (j : Int)) m q (isIrregular m q)
        = inRoundingInterval sig' exp' m q (isIrregular m q) :=
    inRoundingInterval_mul10pow_shift_down sig' j exp' m q (isIrregular m q)
  rw [h_exp_form] at hshift
  -- hshift : inRI (sig' * 10^j) (k+1) m q irreg = inRI sig' exp' m q irreg.
  -- From h_mem : inRI sig' exp' m q irreg = true, derive inRI (sig' * 10^j) (k+1) m q irreg = true.
  have h_mem_lifted : inRoundingInterval (sig' * 10 ^ j) (k + 1) m q (isIrregular m q) = true := by
    rw [hshift]; exact h_mem
  exact Schubfach_K1_candidates m q hm_pos hm_lt hq_lo hq_hi (sig' * 10 ^ j) h_mem_lifted

/-- For a competitor `(sig', exp')` in R_v at scale `exp' ≥ k+1`, the
digit count of sig' is determined by `s/10` or `s/10 + 1` shifted down. -/
theorem digitLength_high_scale (m : Nat) (q : Int)
    (hm_pos : 1 ≤ m) (hm_lt : m < 2 ^ 53) (hq_lo : -1074 ≤ q) (hq_hi : q ≤ 971) :
    let k := kOfMQ m q
    let s := shiftedSig m q k
    ∀ (sig' : Nat) (exp' : Int),
      1 ≤ sig' →
      exp' ≥ k + 1 →
      inRoundingInterval sig' exp' m q (isIrregular m q) = true →
      let j : Nat := (exp' - (k + 1)).toNat
      decDigitLength sig' + j = decDigitLength (s / 10)
        ∨ decDigitLength sig' + j = decDigitLength (s / 10 + 1) := by
  intro k s sig' exp' h_sig_pos h_exp_ge h_mem j
  have h_cands := Schubfach_high_scale_candidates m q hm_pos hm_lt hq_lo hq_hi
                    sig' exp' h_exp_ge h_mem
  have h_dl_pow : decDigitLength (sig' * 10 ^ j) = decDigitLength sig' + j :=
    decDigitLength_mul_pow10 sig' j h_sig_pos
  rcases h_cands with h1 | h1
  · left
    rw [← h1, h_dl_pow]
  · right
    rw [← h1, h_dl_pow]

/-! ## Phase C continued: relating sig' digit count to canonical s/10 or s/10+1

Given `digitLength_high_scale`, we conclude `decDigitLength sig' ≤
max(decDigitLength s/10, decDigitLength s/10+1)`, with equality when `j = 0`. -/

/-- Key conclusion: for canonical high-scale competitor in R_v in the uIn case
(where `s/10` is in R_v at K+1, and `s/10 + 1` is NOT), the competitor must
correspond to the `s/10` branch. -/
theorem high_scale_canonical_in_uIn_case (m : Nat) (q : Int)
    (hm_pos : 1 ≤ m) (hm_lt : m < 2 ^ 53) (hq_lo : -1074 ≤ q) (hq_hi : q ≤ 971)
    (h_wIn_false : inRoundingInterval (shiftedSig m q (kOfMQ m q) / 10 + 1)
                      (kOfMQ m q + 1) m q (isIrregular m q) = false) :
    let k := kOfMQ m q
    let s := shiftedSig m q k
    ∀ (sig' : Nat) (exp' : Int),
      1 ≤ sig' →
      exp' ≥ k + 1 →
      inRoundingInterval sig' exp' m q (isIrregular m q) = true →
      let j : Nat := (exp' - (k + 1)).toNat
      sig' * 10 ^ j = s / 10 := by
  intro k s sig' exp' h_sig_pos h_exp_ge h_mem j
  have h_cands := Schubfach_high_scale_candidates m q hm_pos hm_lt hq_lo hq_hi
                    sig' exp' h_exp_ge h_mem
  rcases h_cands with h1 | h1
  · exact h1
  · -- sig' * 10^j = s/10 + 1. But (s/10+1, k+1) is not in R_v, so neither is
    -- (sig', exp'). Contradiction.
    exfalso
    -- shift_down: (sig'*10^j, k+1) is in R_v iff (sig', exp') is.
    have h_diff_nn : 0 ≤ exp' - (k + 1) := by omega
    have h_j_eq : (j : Int) = exp' - (k + 1) := Int.toNat_of_nonneg h_diff_nn
    have h_exp_form : exp' - (j : Int) = k + 1 := by rw [h_j_eq]; omega
    have hshift :
        inRoundingInterval (sig' * 10 ^ j) (exp' - (j : Int)) m q (isIrregular m q)
          = inRoundingInterval sig' exp' m q (isIrregular m q) :=
      inRoundingInterval_mul10pow_shift_down sig' j exp' m q (isIrregular m q)
    rw [h_exp_form] at hshift
    rw [h1] at hshift
    -- hshift : inRI (s/10+1) (k+1) m q irreg = inRI sig' exp' m q irreg.
    rw [h_wIn_false] at hshift
    rw [hshift.symm] at h_mem
    exact Bool.false_ne_true h_mem

/-- Dual: in the wIn case (where `s/10 + 1` is in R_v and `s/10` is NOT),
high-scale competitor must correspond to `s/10 + 1`. -/
theorem high_scale_canonical_in_wIn_case (m : Nat) (q : Int)
    (hm_pos : 1 ≤ m) (hm_lt : m < 2 ^ 53) (hq_lo : -1074 ≤ q) (hq_hi : q ≤ 971)
    (h_uIn_false : inRoundingInterval (shiftedSig m q (kOfMQ m q) / 10)
                      (kOfMQ m q + 1) m q (isIrregular m q) = false) :
    let k := kOfMQ m q
    let s := shiftedSig m q k
    ∀ (sig' : Nat) (exp' : Int),
      1 ≤ sig' →
      exp' ≥ k + 1 →
      inRoundingInterval sig' exp' m q (isIrregular m q) = true →
      let j : Nat := (exp' - (k + 1)).toNat
      sig' * 10 ^ j = s / 10 + 1 := by
  intro k s sig' exp' h_sig_pos h_exp_ge h_mem j
  have h_cands := Schubfach_high_scale_candidates m q hm_pos hm_lt hq_lo hq_hi
                    sig' exp' h_exp_ge h_mem
  rcases h_cands with h1 | h1
  · -- sig' * 10^j = s/10. But (s/10, k+1) is not in R_v.
    exfalso
    have h_diff_nn : 0 ≤ exp' - (k + 1) := by omega
    have h_j_eq : (j : Int) = exp' - (k + 1) := Int.toNat_of_nonneg h_diff_nn
    have h_exp_form : exp' - (j : Int) = k + 1 := by rw [h_j_eq]; omega
    have hshift :
        inRoundingInterval (sig' * 10 ^ j) (exp' - (j : Int)) m q (isIrregular m q)
          = inRoundingInterval sig' exp' m q (isIrregular m q) :=
      inRoundingInterval_mul10pow_shift_down sig' j exp' m q (isIrregular m q)
    rw [h_exp_form] at hshift
    rw [h1] at hshift
    rw [h_uIn_false] at hshift
    rw [hshift.symm] at h_mem
    exact Bool.false_ne_true h_mem
  · exact h1

/-! ## Phase C continued: canonical-form digit count lemmas

If `sig * 10^j = N` and `sig % 10 ≠ 0` and `sig ≥ 1`, then `sig` is
the unique "canonical part" of `N`: the integer N with its trailing
zeros stripped. We use this to compare `decDigitLength sig'` to the
canonical form of `out_sig`. -/

/-- Uniqueness of canonical-pow10 factoring: if `a * 10^i = b * 10^j` and
both `a`, `b` are canonical (% 10 ≠ 0, ≥ 1), then `a = b` and `i = j`. -/
theorem canonical_pow10_unique (a b i j : Nat)
    (_ha_pos : 1 ≤ a) (_hb_pos : 1 ≤ b)
    (ha_canon : a % 10 ≠ 0) (hb_canon : b % 10 ≠ 0)
    (heq : a * 10 ^ i = b * 10 ^ j) :
    a = b ∧ i = j := by
  -- WLOG i ≤ j. Then a * 10^i = b * 10^j gives a = b * 10^(j-i) (with i ≤ j).
  -- Mod 10 of both sides: a % 10 = (b * 10^(j-i)) % 10. If j-i ≥ 1, RHS = 0 ≠ a % 10. So j = i.
  -- Then a = b.
  rcases Nat.lt_or_ge j i with h_ji | h_ij
  · -- j < i, symmetric. Handled in second case.
    by_cases h_eq : j = i
    · subst h_eq
      have hpos : 0 < 10 ^ j := Nat.pow_pos (a := 10) (by decide)
      have hab : a = b := Nat.eq_of_mul_eq_mul_right hpos heq
      exact ⟨hab, rfl⟩
    · exfalso
      have h_d_pos : 0 < i - j := by omega
      have h_split : (10 : Nat) ^ i = 10 ^ j * 10 ^ (i - j) := by
        rw [← Nat.pow_add]
        congr 1; omega
      rw [h_split] at heq
      have h_cancel : a * 10 ^ (i - j) = b := by
        have hpos : 0 < 10 ^ j := Nat.pow_pos (a := 10) (by decide)
        have h_rearr : a * (10 ^ j * 10 ^ (i - j)) = a * 10 ^ (i - j) * 10 ^ j := by
          grind
        rw [h_rearr] at heq
        exact Nat.eq_of_mul_eq_mul_right hpos heq
      apply hb_canon
      rw [← h_cancel]
      obtain ⟨d, hd⟩ : ∃ d, i - j = d + 1 := ⟨i - j - 1, by omega⟩
      rw [hd, Nat.pow_succ, ← Nat.mul_assoc]
      exact Nat.mul_mod_left _ _
  · -- i ≤ j.
    by_cases h_eq : i = j
    · subst h_eq
      have hpos : 0 < 10 ^ i := Nat.pow_pos (a := 10) (by decide)
      have hab : a = b := Nat.eq_of_mul_eq_mul_right hpos heq
      exact ⟨hab, rfl⟩
    · -- i < j. Then b * 10^j = b * 10^i * 10^(j-i). So a = b * 10^(j-i).
      exfalso
      have h_lt : i < j := by omega
      have h_d_pos : 0 < j - i := by omega
      -- a * 10^i = b * 10^j = b * 10^i * 10^(j-i).
      have h_split : (10 : Nat) ^ j = 10 ^ i * 10 ^ (j - i) := by
        rw [← Nat.pow_add]
        congr 1; omega
      rw [h_split] at heq
      have h_cancel : a = b * 10 ^ (j - i) := by
        have hpos : 0 < 10 ^ i := Nat.pow_pos (a := 10) (by decide)
        have h_rearr : b * (10 ^ i * 10 ^ (j - i)) = b * 10 ^ (j - i) * 10 ^ i := by
          grind
        rw [h_rearr] at heq
        exact Nat.eq_of_mul_eq_mul_right hpos heq
      -- a = b * 10^(j-i), j-i ≥ 1, so a % 10 = 0. Contradicts a canonical.
      apply ha_canon
      rw [h_cancel]
      obtain ⟨d, hd⟩ : ∃ d, j - i = d + 1 := ⟨j - i - 1, by omega⟩
      rw [hd, Nat.pow_succ, ← Nat.mul_assoc]
      exact Nat.mul_mod_left _ _

/-- For canonical sig' with sig' * 10^j = N, sig' is THE canonical factor of N. -/
private theorem canonical_factor_unique_value (sig' N j : Nat)
    (hsig_pos : 1 ≤ sig') (hcanon : sig' % 10 ≠ 0) (_hN_pos : 1 ≤ N)
    (heq : sig' * 10 ^ j = N) :
    ∀ (c : Nat) (t : Nat), c * 10 ^ t = N → c % 10 ≠ 0 → 1 ≤ c →
      c = sig' ∧ t = j := by
  intro c t h_ct h_c_canon h_c_pos
  -- Apply uniqueness: sig' * 10^j = c * 10^t.
  have h_eq2 : sig' * 10 ^ j = c * 10 ^ t := by rw [heq, h_ct]
  have := canonical_pow10_unique sig' c j t hsig_pos h_c_pos hcanon h_c_canon h_eq2
  obtain ⟨hab, hij⟩ := this
  exact ⟨hab.symm, hij.symm⟩

/-! ## Phase D: Connecting to `result.significand` via `mk_pos_props`

The `Decimal.mk' sign sig exp` produces `result.significand` such that
`result.significand * 10^((result.exponent - exp).toNat) = sig` and
`result.significand % 10 ≠ 0`. So `result.significand` is precisely the
canonical factor of `sig`. -/

/-- For a canonical sig' such that sig' * 10^j = out_sig (where out_sig is
the pre-canonicalization Schubfach output significand), sig' must equal
the canonical factor of out_sig. Specifically, if `mk' s out_sig out_exp =
result`, then `sig' = result.significand`. -/
private theorem canonical_sig_eq_result_significand
    (sign : Bool) (out_sig : Nat) (out_exp : Int)
    (sig' j : Nat)
    (hsig_pos : 1 ≤ sig') (hcanon : sig' % 10 ≠ 0)
    (hout_sig_ne : out_sig ≠ 0)
    (heq : sig' * 10 ^ j = out_sig) :
    sig' = (Decimal.mk' sign out_sig out_exp).significand := by
  have ⟨_, hsne, hcanon_res, _, hval⟩ := mk_pos_props sign out_sig out_exp hout_sig_ne
  -- hval : result.significand * 10^((result.exponent - out_exp).toNat) = out_sig
  have hres_pos : 1 ≤ (Decimal.mk' sign out_sig out_exp).significand :=
    Nat.one_le_iff_ne_zero.mpr hsne
  -- Apply uniqueness.
  have hout_pos : 1 ≤ out_sig := Nat.one_le_iff_ne_zero.mpr hout_sig_ne
  have ⟨h_eq_sig, _⟩ :=
    canonical_factor_unique_value sig' out_sig j hsig_pos hcanon hout_pos heq
      (Decimal.mk' sign out_sig out_exp).significand
      ((Decimal.mk' sign out_sig out_exp).exponent - out_exp).toNat
      hval hcanon_res hres_pos
  exact h_eq_sig.symm

/-- For a canonical high-scale competitor in the uIn case, the digit count
equals that of `result.significand`. -/
theorem high_scale_digit_count_uIn (m : Nat) (q : Int) (sign : Bool)
    (hm_pos : 1 ≤ m) (hm_lt : m < 2 ^ 53) (hq_lo : -1074 ≤ q) (hq_hi : q ≤ 971)
    (h_wIn_false : inRoundingInterval (shiftedSig m q (kOfMQ m q) / 10 + 1)
                      (kOfMQ m q + 1) m q (isIrregular m q) = false)
    (h_s_div_10_pos : 1 ≤ shiftedSig m q (kOfMQ m q) / 10) :
    let k := kOfMQ m q
    let s := shiftedSig m q k
    let result := Decimal.mk' sign (s / 10) (k + 1)
    ∀ (sig' : Nat) (exp' : Int),
      sig' ≠ 0 →
      sig' % 10 ≠ 0 →
      exp' ≥ k + 1 →
      inRoundingInterval sig' exp' m q (isIrregular m q) = true →
      decDigitLength sig' = decDigitLength result.significand := by
  intro k s result sig' exp' h_sig_ne h_canon h_exp_ge h_mem
  have h_sig_pos : 1 ≤ sig' := Nat.one_le_iff_ne_zero.mpr h_sig_ne
  -- Get j and the equation.
  have h_branch :=
    high_scale_canonical_in_uIn_case m q hm_pos hm_lt hq_lo hq_hi h_wIn_false
      sig' exp' h_sig_pos h_exp_ge h_mem
  -- h_branch : sig' * 10^j = s/10 where j = (exp' - (k+1)).toNat.
  have h_s_div_10_ne : s / 10 ≠ 0 := Nat.one_le_iff_ne_zero.mp h_s_div_10_pos
  -- sig' = result.significand by canonical_sig_eq_result_significand.
  have h_eq := canonical_sig_eq_result_significand sign (s / 10) (k + 1) sig'
                  ((exp' - (k + 1)).toNat) h_sig_pos h_canon h_s_div_10_ne h_branch
  rw [h_eq]

/-- Dual: for a canonical high-scale competitor in the wIn case, the digit
count equals that of `result.significand`. -/
theorem high_scale_digit_count_wIn (m : Nat) (q : Int) (sign : Bool)
    (hm_pos : 1 ≤ m) (hm_lt : m < 2 ^ 53) (hq_lo : -1074 ≤ q) (hq_hi : q ≤ 971)
    (h_uIn_false : inRoundingInterval (shiftedSig m q (kOfMQ m q) / 10)
                      (kOfMQ m q + 1) m q (isIrregular m q) = false) :
    let k := kOfMQ m q
    let s := shiftedSig m q k
    let result := Decimal.mk' sign (s / 10 + 1) (k + 1)
    ∀ (sig' : Nat) (exp' : Int),
      sig' ≠ 0 →
      sig' % 10 ≠ 0 →
      exp' ≥ k + 1 →
      inRoundingInterval sig' exp' m q (isIrregular m q) = true →
      decDigitLength sig' = decDigitLength result.significand := by
  intro k s result sig' exp' h_sig_ne h_canon h_exp_ge h_mem
  have h_sig_pos : 1 ≤ sig' := Nat.one_le_iff_ne_zero.mpr h_sig_ne
  have h_branch :=
    high_scale_canonical_in_wIn_case m q hm_pos hm_lt hq_lo hq_hi h_uIn_false
      sig' exp' h_sig_pos h_exp_ge h_mem
  -- h_branch : sig' * 10^j = s/10 + 1.
  have h_s_div_10_succ_ne : s / 10 + 1 ≠ 0 := by omega
  have h_eq := canonical_sig_eq_result_significand sign (s / 10 + 1) (k + 1) sig'
                  ((exp' - (k + 1)).toNat) h_sig_pos h_canon h_s_div_10_succ_ne h_branch
  rw [h_eq]

/-! ## Phase E: Low-scale digit count bound

For competitors `(sig', exp')` with `exp' ≤ out_exp - 1` (strict low scale),
the cleared-magnitude argument gives `decDigitLength sig' ≥ decDigitLength
out_sig`. The proof chains `digit_lower_bound_from_Rv` (on sig' at exp') with
`digit_upper_bound_from_Rv` (on out_sig lifted down to exp'), using
`(4m+2) ≤ 3*(4m-2)` to bridge the brackets. -/

/-- **Strict low-scale digit bound**: given two members of `R_v` at scales
`exp_a < exp_b`, the lower-scale sig has at least as many digits as the
higher-scale sig. -/
private theorem strict_low_scale_digit_bound (m : Nat) (q : Int)
    (hm_pos : 1 ≤ m)
    (sig_a : Nat) (exp_a : Int) (_h_sig_a : 1 ≤ sig_a)
    (h_mem_a : inRoundingInterval sig_a exp_a m q (isIrregular m q) = true)
    (sig_b : Nat) (exp_b : Int) (h_sig_b : 1 ≤ sig_b)
    (h_mem_b : inRoundingInterval sig_b exp_b m q (isIrregular m q) = true)
    (h_strict : exp_a < exp_b) :
    decDigitLength sig_a ≥ decDigitLength sig_b := by
  set L_a := decDigitLength sig_a with hLa
  set L_b := decDigitLength sig_b with hLb
  -- Lift sig_b down to scale exp_a: (sig_b * 10^h, exp_a) in R_v.
  let h_nat : Nat := (exp_b - exp_a).toNat
  have h_h_pos : 1 ≤ h_nat := by
    have h_nn : 0 ≤ exp_b - exp_a := by omega
    have h_int : (h_nat : Int) = exp_b - exp_a := Int.toNat_of_nonneg h_nn
    have : 1 ≤ (h_nat : Int) := by rw [h_int]; omega
    exact_mod_cast this
  have h_h_eq : (h_nat : Int) = exp_b - exp_a := by
    apply Int.toNat_of_nonneg; omega
  have h_exp_form : exp_b - (h_nat : Int) = exp_a := by
    rw [h_h_eq]; omega
  have hshift :
      inRoundingInterval (sig_b * 10 ^ h_nat) (exp_b - (h_nat : Int)) m q (isIrregular m q)
        = inRoundingInterval sig_b exp_b m q (isIrregular m q) :=
    inRoundingInterval_mul10pow_shift_down sig_b h_nat exp_b m q (isIrregular m q)
  rw [h_exp_form] at hshift
  have h_mem_lifted : inRoundingInterval (sig_b * 10 ^ h_nat) exp_a m q (isIrregular m q) = true := by
    rw [hshift]; exact h_mem_b
  have h_dl_pow : decDigitLength (sig_b * 10 ^ h_nat) = L_b + h_nat :=
    decDigitLength_mul_pow10 sig_b h_nat h_sig_b
  have hLb_pos : 1 ≤ L_b := decDigitLength_pos sig_b
  have h_Lbh_pos : 1 ≤ L_b + h_nat := by omega
  -- Upper bracket for lifted sig_b at scale exp_a:
  -- 4 * 10^(L_b + h_nat - 1) * tenP exp_a * qN ≤ (4m+2) * qP * tenN exp_a.
  have h_upper :=
    digit_upper_bound_from_Rv (sig_b * 10 ^ h_nat) exp_a m q hm_pos h_mem_lifted
  rw [h_dl_pow] at h_upper
  -- Lower bracket for sig_a at exp_a:
  -- (4m - 2) * qP * tenN exp_a < 4 * 10^L_a * tenP exp_a * qN.
  have h_lower :=
    digit_lower_bound_from_Rv sig_a exp_a m q hm_pos h_mem_a
  rw [← hLa] at h_lower
  -- Combine. (4m+2) ≤ 3*(4m-2) for m ≥ 1.
  have h_3 : (4 * (m : Int) + 2) ≤ 3 * (4 * (m : Int) - 2) := by
    have : (1 : Int) ≤ (m : Int) := by exact_mod_cast hm_pos
    grind
  have h_tenP_qN_pos : (0 : Int) < (tenPosPow exp_a : Int) * (twoNegPow q : Int) :=
    tenPos_twoNeg_pos_Int q exp_a
  have h_qP_tenN_pos : (0 : Int) < (twoPosPow q : Int) * (tenNegPow exp_a : Int) :=
    twoPos_tenNeg_pos_Int q exp_a
  -- Chain: 4 * 10^(L_b + h_nat - 1) * tenP * qN ≤ (4m+2) * qP * tenN ≤ 3*(4m-2) * qP * tenN.
  have h_chain1 :
      4 * (10 : Int)^(L_b + h_nat - 1) * (tenPosPow exp_a : Int) * (twoNegPow q : Int)
        ≤ 3 * (4 * (m : Int) - 2) * (twoPosPow q : Int) * (tenNegPow exp_a : Int) := by
    have h_mul := Int.mul_le_mul_of_nonneg_right h_3 (Int.le_of_lt h_qP_tenN_pos)
    have h_assoc1 : (4 * (m : Int) + 2) * ((twoPosPow q : Int) * (tenNegPow exp_a : Int))
                    = (4 * (m : Int) + 2) * (twoPosPow q : Int) * (tenNegPow exp_a : Int) := by
      grind
    have h_assoc2 : 3 * (4 * (m : Int) - 2) * ((twoPosPow q : Int) * (tenNegPow exp_a : Int))
                    = 3 * (4 * (m : Int) - 2) * (twoPosPow q : Int) * (tenNegPow exp_a : Int) := by
      grind
    rw [h_assoc1, h_assoc2] at h_mul
    grind
  -- And 3*(4m-2)*qP*tenN < 12 * 10^L_a * tenP * qN.
  have h_chain2 :
      3 * (4 * (m : Int) - 2) * (twoPosPow q : Int) * (tenNegPow exp_a : Int)
        < 12 * (10 : Int)^L_a * (tenPosPow exp_a : Int) * (twoNegPow q : Int) := by
    have h_a : 3 * ((4 * (m : Int) - 2) * (twoPosPow q : Int) * (tenNegPow exp_a : Int))
                < 3 * (4 * (10 : Int)^L_a * (tenPosPow exp_a : Int) * (twoNegPow q : Int)) :=
      Int.mul_lt_mul_of_pos_left h_lower (by decide)
    have e1 : 3 * ((4 * (m : Int) - 2) * (twoPosPow q : Int) * (tenNegPow exp_a : Int))
              = 3 * (4 * (m : Int) - 2) * (twoPosPow q : Int) * (tenNegPow exp_a : Int) := by grind
    have e2 : 3 * (4 * (10 : Int)^L_a * (tenPosPow exp_a : Int) * (twoNegPow q : Int))
              = 12 * (10 : Int)^L_a * (tenPosPow exp_a : Int) * (twoNegPow q : Int) := by grind
    rw [e1, e2] at h_a
    exact h_a
  -- 4 * 10^(L_b + h_nat - 1) * tenP * qN < 12 * 10^L_a * tenP * qN.
  have h_chain3 :
      4 * (10 : Int)^(L_b + h_nat - 1) * (tenPosPow exp_a : Int) * (twoNegPow q : Int)
        < 12 * (10 : Int)^L_a * (tenPosPow exp_a : Int) * (twoNegPow q : Int) := by
    grind
  -- Cancel 4 * tenP * qN > 0 to get 10^(L_b + h_nat - 1) < 3 * 10^L_a.
  have h_pos_factor : 0 < 4 * ((tenPosPow exp_a : Int) * (twoNegPow q : Int)) :=
    Int.mul_pos (by decide) h_tenP_qN_pos
  have h_cancel :
      (10 : Int)^(L_b + h_nat - 1) < 3 * (10 : Int)^L_a := by
    -- Rearrange h_chain3 as factor * lhs < factor * rhs.
    have h_re :
        4 * ((tenPosPow exp_a : Int) * (twoNegPow q : Int)) * (10 : Int)^(L_b + h_nat - 1)
          < 4 * ((tenPosPow exp_a : Int) * (twoNegPow q : Int)) * (3 * (10 : Int)^L_a) := by
      have e1 : 4 * ((tenPosPow exp_a : Int) * (twoNegPow q : Int)) * (10 : Int)^(L_b + h_nat - 1)
                = 4 * (10 : Int)^(L_b + h_nat - 1) * (tenPosPow exp_a : Int) * (twoNegPow q : Int) := by
        grind
      have e2 : 4 * ((tenPosPow exp_a : Int) * (twoNegPow q : Int)) * (3 * (10 : Int)^L_a)
                = 12 * (10 : Int)^L_a * (tenPosPow exp_a : Int) * (twoNegPow q : Int) := by grind
      rw [e1, e2]
      exact h_chain3
    exact (Int.mul_lt_mul_left h_pos_factor).mp h_re
  -- Convert h_cancel from Int to Nat: 10^(L_b + h_nat - 1) < 3 * 10^L_a as Nat.
  have h_cancel_nat : (10 : Nat)^(L_b + h_nat - 1) < 3 * (10 : Nat)^L_a := by
    have h1 : ((10 : Nat)^(L_b + h_nat - 1) : Int) = (10 : Int)^(L_b + h_nat - 1) := by push_cast; rfl
    have h2 : ((3 * (10 : Nat)^L_a : Nat) : Int) = 3 * (10 : Int)^L_a := by push_cast; rfl
    have : ((10 : Nat)^(L_b + h_nat - 1) : Int) < ((3 * (10 : Nat)^L_a : Nat) : Int) := by
      rw [h1, h2]; exact h_cancel
    exact_mod_cast this
  -- Deduce L_a ≥ L_b + h_nat - 1.
  have h_pow_bound : L_b + h_nat - 1 ≤ L_a := by
    by_contra hc
    push_neg at hc
    -- hc : L_a < L_b + h_nat - 1.
    have hL_le : L_a + 1 ≤ L_b + h_nat - 1 := hc
    have h_pow_step : (10 : Nat)^(L_a + 1) ≤ 10^(L_b + h_nat - 1) :=
      Nat.pow_le_pow_right (by decide) hL_le
    have h_pow_succ : (10 : Nat)^(L_a + 1) = 10 * 10^L_a := by
      rw [Nat.pow_succ, Nat.mul_comm]
    rw [h_pow_succ] at h_pow_step
    -- 10 * 10^L_a ≤ 10^(L_b + h_nat - 1) < 3 * 10^L_a — contradiction.
    omega
  -- Hence L_a ≥ L_b + h_nat - 1 ≥ L_b (since h_nat ≥ 1).
  omega

/-! ## Phase E.connected: R_v at fixed scale is connected (an interval)

If `(a, k) ∈ R_v` and `(b, k) ∈ R_v` with `a ≤ c ≤ b`, then `(c, k) ∈ R_v`.
This follows from monotonicity of `fourU` in sig. -/

theorem inRoundingInterval_connected (a c b : Nat) (k : Int) (m : Nat) (q : Int)
    (h_a_le_c : a ≤ c) (h_c_le_b : c ≤ b)
    (h_a : inRoundingInterval a k m q (isIrregular m q) = true)
    (h_b : inRoundingInterval b k m q (isIrregular m q) = true) :
    inRoundingInterval c k m q (isIrregular m q) = true := by
  -- fourU is monotone in sig at fixed scale.
  have h_U_mono : ∀ x y : Nat, x ≤ y → fourU x q k ≤ fourU y q k := by
    intro x y hxy
    unfold fourU cmpScaledMixed.rhs
    have hcast : (x : Int) ≤ (y : Int) := by exact_mod_cast hxy
    have h4 : 4 * (x : Int) ≤ 4 * (y : Int) := by grind
    have htP_nn : (0 : Int) ≤ (10 : Int) ^ (if k ≥ 0 then k.toNat else 0) := by (first | exact Int.pow_nonneg (by omega) | exact Int.pow_pos (by omega) | exact Nat.pow_pos (by omega) | exact Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.pow_pos (by omega)) | grind)
    have htN_nn : (0 : Int) ≤ (2 : Int) ^ (if q < 0 then (-q).toNat else 0) := by (first | exact Int.pow_nonneg (by omega) | exact Int.pow_pos (by omega) | exact Nat.pow_pos (by omega) | exact Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.pow_pos (by omega)) | grind)
    have h1 : 4 * (x : Int) * (10 : Int) ^ (if k ≥ 0 then k.toNat else 0)
                ≤ 4 * (y : Int) * (10 : Int) ^ (if k ≥ 0 then k.toNat else 0) :=
      Int.mul_le_mul_of_nonneg_right h4 htP_nn
    exact Int.mul_le_mul_of_nonneg_right h1 htN_nn
  have h_U_ac : fourU a q k ≤ fourU c q k := h_U_mono a c h_a_le_c
  have h_U_cb : fourU c q k ≤ fourU b q k := h_U_mono c b h_c_le_b
  -- bracket bounds for a and b.
  have ⟨h_VL_a, h_a_VR⟩ := inRoundingInterval_bounds_fourU_local a k m q h_a
  have ⟨h_VL_b, h_b_VR⟩ := inRoundingInterval_bounds_fourU_local b k m q h_b
  -- fourVL ≤ fourU(a) ≤ fourU(c) ≤ fourU(b) ≤ fourVR.
  have h_VL_c : fourVL m q k (isIrregular m q) ≤ fourU c q k := Int.le_trans h_VL_a h_U_ac
  have h_c_VR : fourU c q k ≤ fourVR m q k := Int.le_trans h_U_cb h_b_VR
  -- Want: cmpL(c) < 0 OR (cmpL(c) = 0 AND m even). I.e., fourVL < fourU(c) OR (fourVL = fourU(c) AND m even).
  -- We have fourVL ≤ fourU(c). For strict: if fourVL < fourU(c), done. If equal: then fourVL = fourU(c) = fourU(a),
  -- so fourU(a) = fourVL. From h_a in R_v, cmpL(a) < 0 OR (cmpL(a) = 0 AND m even). cmpL(a) = 0 means fourVL = fourU(a),
  -- which holds. So we have m even at the boundary. Hence (fourVL = fourU(c) AND m even).
  rw [inRoundingInterval_iff]
  refine ⟨?_, ?_⟩
  · -- Left side.
    rcases lt_or_eq_of_le h_VL_c with h_lt | h_eq
    · exact Or.inl h_lt
    · -- fourVL = fourU(c). Then fourU(a) ≤ fourU(c) = fourVL ≤ fourU(a), so fourU(a) = fourVL.
      have h_a_eq : fourU a q k = fourVL m q k (isIrregular m q) := by omega
      -- From h_a, cmpL(a) < 0 OR (cmpL(a) = 0 AND m even). At fourU(a) = fourVL, the strict fails, so m even.
      have h_a_iff := (inRoundingInterval_iff a k m q (isIrregular m q)).mp h_a
      obtain ⟨h_left_a, _⟩ := h_a_iff
      have h_m_even : m % 2 = 0 := by
        rcases h_left_a with h_lt_a | ⟨_, h_even⟩
        · -- fourVL < fourU(a) = fourVL. Contradiction.
          omega
        · exact h_even
      exact Or.inr ⟨h_eq, h_m_even⟩
  · -- Right side.
    rcases lt_or_eq_of_le h_c_VR with h_lt | h_eq
    · exact Or.inl h_lt
    · -- fourU(c) = fourVR. Then fourU(c) ≤ fourU(b) ≤ fourVR = fourU(c), so fourU(b) = fourVR.
      have h_b_eq : fourU b q k = fourVR m q k := by omega
      have h_b_iff := (inRoundingInterval_iff b k m q (isIrregular m q)).mp h_b
      obtain ⟨_, h_right_b⟩ := h_b_iff
      have h_m_even : m % 2 = 0 := by
        rcases h_right_b with h_lt_b | ⟨_, h_even⟩
        · -- fourU(b) = fourVR < fourVR. Contradiction.
          omega
        · exact h_even
      exact Or.inr ⟨h_eq, h_m_even⟩

/-! ## Phase E.helper: canonicalised result is in R_v

`Decimal.mk'` canonicalises by stripping trailing zeros. The canonical
`(result.significand, result.exponent)` represents the same value as
the input `(out_sig, out_exp)`, and so lies in R_v whenever the input does. -/

/-- The canonicalised form `(result.significand, result.exponent)` of
`Decimal.mk' sign out_sig out_exp` lies in R_v iff the raw form does. -/
private theorem mk_pos_result_in_Rv
    (sign : Bool) (out_sig : Nat) (out_exp : Int) (h_out : out_sig ≠ 0)
    (m : Nat) (q : Int)
    (h_mem : inRoundingInterval out_sig out_exp m q (isIrregular m q) = true) :
    inRoundingInterval (Decimal.mk' sign out_sig out_exp).significand
                       (Decimal.mk' sign out_sig out_exp).exponent
                       m q (isIrregular m q) = true := by
  have ⟨_, _, _, h_exp_le, h_val⟩ := mk_pos_props sign out_sig out_exp h_out
  let h_nat := ((Decimal.mk' sign out_sig out_exp).exponent - out_exp).toNat
  have h_h_nn : 0 ≤ (Decimal.mk' sign out_sig out_exp).exponent - out_exp := by omega
  have h_h_eq : (h_nat : Int) = (Decimal.mk' sign out_sig out_exp).exponent - out_exp :=
    Int.toNat_of_nonneg h_h_nn
  have h_form : (Decimal.mk' sign out_sig out_exp).exponent - (h_nat : Int) = out_exp := by
    rw [h_h_eq]; omega
  have hshift := inRoundingInterval_mul10pow_shift_down
                  (Decimal.mk' sign out_sig out_exp).significand h_nat
                  (Decimal.mk' sign out_sig out_exp).exponent m q (isIrregular m q)
  rw [h_form] at hshift
  rw [h_val] at hshift
  rw [hshift] at h_mem
  exact h_mem

/-! ## Phase E.window: digit-count uniformity in the 9-element window

Members of `{10*t+1, ..., 10*t+9}` all have the same `decDigitLength`. -/

/-- Any integer in `{10*t + 1, ..., 10*t + 9}` (with `t ≥ 1`) has digit count
`decDigitLength t + 1`. -/
private theorem decDigitLength_window_t_ge_1 (t : Nat) (h_t : 1 ≤ t)
    (sig : Nat) (h_lo : 10 * t + 1 ≤ sig) (h_hi : sig ≤ 10 * t + 9) :
    decDigitLength sig = decDigitLength t + 1 := by
  have h_ge_10 : 10 ≤ sig := by
    have : 10 * 1 ≤ 10 * t := Nat.mul_le_mul_left 10 h_t
    omega
  rw [decDigitLength_ge_10 h_ge_10]
  have h_div : sig / 10 = t := by omega
  rw [h_div]

/-! ## Helper: pickNearer is at most s + 1. -/

/-- pickNearer always returns `s` or `s + 1`. -/
theorem pickNearer_eq_s_or_succ (s : Nat) (k : Int) (m : Nat) (q : Int) :
    pickNearer s k m q = s ∨ pickNearer s k m q = s + 1 := by
  unfold pickNearer
  by_cases h1 : (inRoundingInterval s k m q (isIrregular m q) &&
                 !inRoundingInterval (s + 1) k m q (isIrregular m q)) = true
  · rw [if_pos h1]; left; rfl
  · rw [if_neg h1]
    by_cases h2 : (!inRoundingInterval s k m q (isIrregular m q) &&
                   inRoundingInterval (s + 1) k m q (isIrregular m q)) = true
    · rw [if_pos h2]; right; rfl
    · rw [if_neg h2]
      by_cases h3 : cmpScaledMixed (2 * (m : Int)) q (2 * (s : Int) + 1) k < 0
      · rw [if_pos h3]; left; rfl
      · rw [if_neg h3]
        by_cases h4 : cmpScaledMixed (2 * (m : Int)) q (2 * (s : Int) + 1) k > 0
        · rw [if_pos h4]; right; rfl
        · rw [if_neg h4]
          by_cases h5 : s % 2 = 0
          · rw [if_pos h5]; left; rfl
          · rw [if_neg h5]; right; rfl

/-! ## Assembled high-scale cross-scale minimality

We package the per-branch results into a single theorem that depends
only on the output of `shortestUnsigned`. -/

/-- **Strengthened high-scale classical minimality**: for finite non-zero
Floats, `toDecimal f` produces a result `r` such that for any canonical
competitor `(sign', sig', exp')` with `exp' ≥ k + 1` in R_v, its digit
count `decDigitLength sig'` equals that of `r.significand`.

This **strengthens** `toDecimal_classically_minimal` (which was vacuous
in the uIn/wIn cases, only excluding non-canonical sig' at high scales)
into a digit-count comparison that is **informative in all branches**:

* uIn case: competitor = result via canonical-pow10 uniqueness.
* wIn case: similarly.
* fallback case: no high-scale competitor exists (vacuous forall).

The low-scale case (`exp' ≤ k`) is **not yet covered**; it would
require a magnitude-based argument to show
`decDigitLength sig' ≥ decDigitLength result.significand` for low-scale
competitors. The current high-scale theorem subsumes
`toDecimal_classically_minimal` (in fact, returning `=` instead of `≠ true`). -/
theorem toDecimal_minimal_high_scale
    (w : UInt64)
    (h_fin : Word.isFinite w = true)
    (h_nonzero : (Word.decode w).m ≠ 0) :
    ∃ result, toDecimalBits w = .ok result ∧
      let d := Word.decode w
      let k := kOfMQ d.m d.q
      ∀ (_sign' : Bool) (sig' : Nat) (exp' : Int),
        sig' ≠ 0 →
        sig' % 10 ≠ 0 →
        exp' ≥ k + 1 →
        inRoundingInterval sig' exp' d.m d.q (isIrregular d.m d.q) = true →
        decDigitLength sig' = decDigitLength result.significand := by
  obtain ⟨result, hresult, _⟩ := toDecimalBits_in_Rv w h_fin h_nonzero
  refine ⟨result, hresult, ?_⟩
  intro d k sign' sig' exp' h_sig_ne h_canon h_exp_ge h_mem
  have ⟨h_m_lt, h_q_lo, h_q_hi⟩ :=
    Srtfp.Schubfach.decode_invariants_bits w h_fin
  have h_m_pos : 1 ≤ d.m := Nat.one_le_iff_ne_zero.mpr h_nonzero
  -- Establish that result is `Decimal.mk' d.sign output_sig output_exp`.
  have h_toDec_unfold :
      toDecimalBits w = .ok (Decimal.mk' d.sign (shortestUnsigned d.m d.q).1
                                            (shortestUnsigned d.m d.q).2) := by
    have hfin_lt : Word.biasedExp w < 2047 := by
      unfold Word.isFinite at h_fin; simpa using h_fin
    have hnan : Word.isNaN w = false := by
      unfold Word.isNaN
      have : ¬ Word.biasedExp w = 2047 := by omega
      simp [this]
    have hinf : Word.isInf w = false := by
      unfold Word.isInf
      have : ¬ Word.biasedExp w = 2047 := by omega
      simp [this]
    unfold toDecimalBits
    rw [hnan, hinf]
    have hm_ne' : (Word.decode w).m ≠ 0 := h_nonzero
    simp [hm_ne']
    rfl
  rw [h_toDec_unfold] at hresult
  have hresult_eq : result = Decimal.mk' d.sign (shortestUnsigned d.m d.q).1
                                                (shortestUnsigned d.m d.q).2 := by
    cases hresult; rfl
  rw [hresult_eq]
  -- Use shortestUnsigned_length_relation to identify the case.
  have h_rel := shortestUnsigned_length_relation d.m d.q
  -- Sig' (first | exact Int.pow_nonneg (by omega) | exact Int.pow_pos (by omega) | exact Nat.pow_pos (by omega) | exact Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.pow_pos (by omega)) | grind).
  have h_sig_pos : 1 ≤ sig' := Nat.one_le_iff_ne_zero.mpr h_sig_ne
  rcases h_rel with ⟨hs_big, h_exp_eq, h_or⟩ | ⟨h_exp_eq, h_sig_eq⟩
  · -- Case 1: short-form (uIn or wIn). out_exp = k+1, out_sig = s/10 or s/10+1.
    rcases h_or with h_uIn_branch | h_wIn_branch
    · -- uIn: out_sig = s/10.
      -- We need: decDigitLength sig' = decDigitLength (Decimal.mk' d.sign (s/10) (k+1)).significand
      rw [h_exp_eq, h_uIn_branch]
      -- For this branch to fire in shortestUnsigned, uIn must be true. So in particular
      -- (s/10, k+1) is in R_v.
      -- We also know that wIn must be false here (else shortestUnsigned would have picked uIn anyway —
      -- but actually shortestUnsigned checks uIn first, so wIn can be either; but at most one
      -- of {s/10, s/10+1} can be in R_v at K+1 by strict-step bound).
      -- Establish wIn is false from "at most one in R_v at K+1".
      have h_uIn : inRoundingInterval (shiftedSig d.m d.q k / 10)
                                       (k + 1) d.m d.q (isIrregular d.m d.q) = true := by
        have h_mem_out := shortestUnsigned_mem_rv d.m d.q h_m_pos h_m_lt h_q_lo h_q_hi
        -- h_mem_out : inRoundingInterval (shortestUnsigned ..).1 (shortestUnsigned ..).2 m q irr = true
        -- (shortestUnsigned ..).2 = k+1 (h_exp_eq) and (shortestUnsigned ..).1 = s/10 (h_uIn_branch)
        show inRoundingInterval (shiftedSig d.m d.q k / 10) (k + 1) d.m d.q (isIrregular d.m d.q) = true
        have h1 : (shortestUnsigned d.m d.q).2 = k + 1 := h_exp_eq
        have h2 : (shortestUnsigned d.m d.q).1 = shiftedSig d.m d.q k / 10 := h_uIn_branch
        rw [← h1, ← h2]
        exact h_mem_out
      -- Now show wIn false using strict-step.
      have h_wIn_false : inRoundingInterval (shiftedSig d.m d.q k / 10 + 1)
                            (k + 1) d.m d.q (isIrregular d.m d.q) = false := by
        rcases Bool.eq_false_or_eq_true (inRoundingInterval (shiftedSig d.m d.q k / 10 + 1)
                (k + 1) d.m d.q (isIrregular d.m d.q)) with h_wT | h_wF
        · exfalso
          -- Both uIn and wIn at K+1 contradicts strict-step.
          have h_strict :
              fourVR d.m d.q (k + 1) - fourVL d.m d.q (k + 1) (isIrregular d.m d.q)
                < fourW (shiftedSig d.m d.q k / 10) d.q (k + 1)
                  - fourU (shiftedSig d.m d.q k / 10) d.q (k + 1) :=
            fourVR_sub_fourVL_lt_step_K1 d.m d.q h_m_pos h_m_lt h_q_lo h_q_hi _
          have h_step_eq : fourW (shiftedSig d.m d.q k / 10) d.q (k + 1)
                            - fourU (shiftedSig d.m d.q k / 10) d.q (k + 1) =
                           4 * (tenPosPow (k + 1) : Int) * (twoNegPow d.q : Int) :=
            fourW_sub_fourU _ _ _
          have ⟨h_VL_le_u, h_u_le_VR⟩ :=
            inRoundingInterval_bounds_fourU_local _ _ _ _ h_uIn
          have ⟨h_VL_le_w, h_w_le_VR⟩ :=
            inRoundingInterval_bounds_fourU_local _ _ _ _ h_wT
          have h_w_eq : fourU (shiftedSig d.m d.q k / 10 + 1) d.q (k + 1)
                        = fourW (shiftedSig d.m d.q k / 10) d.q (k + 1) := by
            rw [fourU_eq, fourW_eq]
            push_cast
            rfl
          rw [h_w_eq] at h_VL_le_w h_w_le_VR
          omega
        · exact h_wF
      have h_s_div_10_pos : 1 ≤ shiftedSig d.m d.q k / 10 := by
        have : 10 / 10 ≤ shiftedSig d.m d.q k / 10 := Nat.div_le_div_right hs_big
        simpa using this
      exact high_scale_digit_count_uIn d.m d.q d.sign h_m_pos h_m_lt h_q_lo h_q_hi
              h_wIn_false h_s_div_10_pos sig' exp' h_sig_ne h_canon h_exp_ge h_mem
    · -- wIn: out_sig = s/10 + 1.
      rw [h_exp_eq, h_wIn_branch]
      have h_wIn : inRoundingInterval (shiftedSig d.m d.q k / 10 + 1)
                                       (k + 1) d.m d.q (isIrregular d.m d.q) = true := by
        have h_mem_out := shortestUnsigned_mem_rv d.m d.q h_m_pos h_m_lt h_q_lo h_q_hi
        show inRoundingInterval (shiftedSig d.m d.q k / 10 + 1) (k + 1) d.m d.q (isIrregular d.m d.q) = true
        have h1 : (shortestUnsigned d.m d.q).2 = k + 1 := h_exp_eq
        have h2 : (shortestUnsigned d.m d.q).1 = shiftedSig d.m d.q k / 10 + 1 := h_wIn_branch
        rw [← h1, ← h2]
        exact h_mem_out
      have h_uIn_false : inRoundingInterval (shiftedSig d.m d.q k / 10)
                            (k + 1) d.m d.q (isIrregular d.m d.q) = false := by
        rcases Bool.eq_false_or_eq_true (inRoundingInterval (shiftedSig d.m d.q k / 10)
                (k + 1) d.m d.q (isIrregular d.m d.q)) with h_uT | h_uF
        · exfalso
          have h_strict :
              fourVR d.m d.q (k + 1) - fourVL d.m d.q (k + 1) (isIrregular d.m d.q)
                < fourW (shiftedSig d.m d.q k / 10) d.q (k + 1)
                  - fourU (shiftedSig d.m d.q k / 10) d.q (k + 1) :=
            fourVR_sub_fourVL_lt_step_K1 d.m d.q h_m_pos h_m_lt h_q_lo h_q_hi _
          have h_step_eq : fourW (shiftedSig d.m d.q k / 10) d.q (k + 1)
                            - fourU (shiftedSig d.m d.q k / 10) d.q (k + 1) =
                           4 * (tenPosPow (k + 1) : Int) * (twoNegPow d.q : Int) :=
            fourW_sub_fourU _ _ _
          have ⟨h_VL_le_u, h_u_le_VR⟩ :=
            inRoundingInterval_bounds_fourU_local _ _ _ _ h_uT
          have ⟨h_VL_le_w, h_w_le_VR⟩ :=
            inRoundingInterval_bounds_fourU_local _ _ _ _ h_wIn
          have h_w_eq : fourU (shiftedSig d.m d.q k / 10 + 1) d.q (k + 1)
                        = fourW (shiftedSig d.m d.q k / 10) d.q (k + 1) := by
            rw [fourU_eq, fourW_eq]
            push_cast
            rfl
          rw [h_w_eq] at h_VL_le_w h_w_le_VR
          omega
        · exact h_uF
      exact high_scale_digit_count_wIn d.m d.q d.sign h_m_pos h_m_lt h_q_lo h_q_hi
              h_uIn_false sig' exp' h_sig_ne h_canon h_exp_ge h_mem
  · -- Case 2: fallback. out_exp = k, out_sig = pickNearer s k m q.
    rw [h_exp_eq, h_sig_eq]
    -- Subcase: s ≥ 10 with uIn false, wIn false; OR s < 10.
    by_cases hs_big : shiftedSig d.m d.q k ≥ 10
    · -- s ≥ 10. shortestUnsigned picks (pickNearer, k) ⇒ uIn=false AND wIn=false.
      have h_uIn_false : inRoundingInterval (shiftedSig d.m d.q k / 10)
                            (k + 1) d.m d.q (isIrregular d.m d.q) = false := by
        rcases Bool.eq_false_or_eq_true (inRoundingInterval (shiftedSig d.m d.q k / 10)
                (k + 1) d.m d.q (isIrregular d.m d.q)) with h_uT | h_uF
        · exfalso
          have h_su_unfold : (shortestUnsigned d.m d.q).2 = k + 1 := by
            unfold shortestUnsigned
            rw [if_pos hs_big, if_pos h_uT]
          rw [h_exp_eq] at h_su_unfold
          omega
        · exact h_uF
      have h_wIn_false : inRoundingInterval (shiftedSig d.m d.q k / 10 + 1)
                            (k + 1) d.m d.q (isIrregular d.m d.q) = false := by
        rcases Bool.eq_false_or_eq_true (inRoundingInterval (shiftedSig d.m d.q k / 10 + 1)
                (k + 1) d.m d.q (isIrregular d.m d.q)) with h_wT | h_wF
        · exfalso
          have h_su_unfold : (shortestUnsigned d.m d.q).2 = k + 1 := by
            unfold shortestUnsigned
            rw [if_pos hs_big, if_neg (Bool.eq_false_iff.mp h_uIn_false), if_pos h_wT]
          rw [h_exp_eq] at h_su_unfold
          omega
        · exact h_wF
      -- No high-scale competitor in R_v under fallback. exfalso.
      exfalso
      have h_false := Schubfach_no_high_scale_under_fallback_proof d.m d.q h_m_pos h_m_lt
                        h_q_lo h_q_hi hs_big h_uIn_false h_wIn_false sig' exp' h_exp_ge
      rw [h_false] at h_mem
      exact Bool.false_ne_true h_mem
    · -- s < 10: K+1 candidates are s/10 = 0 and s/10+1 = 1. sig'*10^j ∈ {0,1}.
      have h_cands := Schubfach_high_scale_candidates d.m d.q h_m_pos h_m_lt h_q_lo h_q_hi
                        sig' exp' h_exp_ge h_mem
      have h_s_lt : shiftedSig d.m d.q k < 10 := Nat.not_le.mp hs_big
      have h_s10 : shiftedSig d.m d.q k / 10 = 0 := Nat.div_eq_of_lt h_s_lt
      rw [h_s10] at h_cands
      rcases h_cands with h_branch | h_branch
      · -- sig' * 10^j = 0. Then sig' = 0, contradiction.
        exfalso
        have h_pow_pos : 0 < 10 ^ (exp' - (k + 1)).toNat :=
          Nat.pow_pos (a := 10) (by decide)
        have h_lhs_pos : 1 ≤ sig' * 10 ^ (exp' - (k + 1)).toNat := by
          have : 1 * 1 ≤ sig' * 10 ^ (exp' - (k + 1)).toNat :=
            Nat.mul_le_mul h_sig_pos h_pow_pos
          omega
        -- h_branch : sig' * 10^j = 0, but h_lhs_pos says it's ≥ 1.
        rw [h_branch] at h_lhs_pos
        omega
      · -- sig' * 10^j = 1. So sig' = 1, exp' = k + 1.
        have h_one_pos : (1 : Nat) ≥ 1 := by decide
        have h_one_canon : (1 : Nat) % 10 ≠ 0 := by decide
        have ⟨h_sig_eq', h_j_eq⟩ := canonical_pow10_unique sig' 1 (exp' - (k + 1)).toNat 0
                                    h_sig_pos h_one_pos h_canon h_one_canon
                                    (by rw [h_branch])
        subst h_sig_eq'
        -- Now goal: decDigitLength 1 = decDigitLength (Decimal.mk' d.sign (pickNearer s k m q) k).significand
        have h_dl_1 : decDigitLength 1 = 1 := decDigitLength_lt_10 (by decide : (1:Nat) < 10)
        rw [h_dl_1]
        -- Need: decDigitLength result.significand = 1, where result = mk' _ (pickNearer s k) k.
        -- pickNearer ∈ {s, s+1} ⊆ {0..10}. After mk', significand ∈ {0, 1..9, 1}.
        -- All single-digit (decDigitLength = 1).
        have h_pn_bound : pickNearer (shiftedSig d.m d.q k) k d.m d.q ≤ 10 := by
          rcases pickNearer_eq_s_or_succ (shiftedSig d.m d.q k) k d.m d.q with h_pn | h_pn
          · rw [h_pn]; omega
          · rw [h_pn]; omega
        -- Cases on pickNearer.
        by_cases h_pn_zero : pickNearer (shiftedSig d.m d.q k) k d.m d.q = 0
        · -- pickNearer = 0: significand = 0, decDigitLength 0 = 1.
          rw [h_pn_zero]
          have : (Decimal.mk' d.sign 0 k).significand = 0 := by
            unfold Decimal.mk' Decimal.canonical
            simp
          rw [this, decDigitLength_zero]
        · have h_pn_pos : 1 ≤ pickNearer (shiftedSig d.m d.q k) k d.m d.q :=
            Nat.one_le_iff_ne_zero.mpr h_pn_zero
          by_cases h_pn_ten : pickNearer (shiftedSig d.m d.q k) k d.m d.q = 10
          · rw [h_pn_ten]
            -- canonicaliseAux 10 k = canonicaliseAux 1 (k+1) = (1, k+1).
            have h_sig_val : (Decimal.mk' d.sign 10 k).significand = 1 := by
              unfold Decimal.mk' Decimal.canonical
              simp
              unfold Decimal.canonicaliseAux
              simp
              unfold Decimal.canonicaliseAux
              simp
            rw [h_sig_val]
            exact h_dl_1.symm
          · have h_pn_lt_10 : pickNearer (shiftedSig d.m d.q k) k d.m d.q < 10 := by omega
            -- pn % 10 ≠ 0 (canonical), so result.significand = pn.
            have h_pn_mod : pickNearer (shiftedSig d.m d.q k) k d.m d.q % 10 ≠ 0 := by
              have h_mod_eq : pickNearer (shiftedSig d.m d.q k) k d.m d.q % 10
                              = pickNearer (shiftedSig d.m d.q k) k d.m d.q :=
                Nat.mod_eq_of_lt h_pn_lt_10
              rw [h_mod_eq]
              exact h_pn_zero
            have h_sig_val :
                (Decimal.mk' d.sign (pickNearer (shiftedSig d.m d.q k) k d.m d.q) k).significand
                  = pickNearer (shiftedSig d.m d.q k) k d.m d.q := by
              unfold Decimal.mk' Decimal.canonical
              simp [h_pn_zero]
              unfold Decimal.canonicaliseAux
              simp [h_pn_zero, h_pn_mod]
            rw [h_sig_val]
            exact (decDigitLength_lt_10 h_pn_lt_10).symm

/-! ## Low-scale cross-scale minimality

For competitors at scale `exp' ≤ result.exponent`, the digit count of `sig'`
is bounded BELOW by the digit count of `result.significand`. Combined with
the high-scale theorem, this gives the full classical minimality.

The dispatch:
* `exp' ≥ k + 1`: high-scale theorem (gives equality, hence `≥`).
* `exp' ≤ k` and `exp' < result.exponent`: strict low-scale digit bound.
* `exp' = result.exponent = k`: fallback boundary; uses R_v connectedness
  + the 9-element window argument. -/

/-- **Low-scale classical minimality**: for finite non-zero Floats,
`toDecimal f` produces a result `r` such that for any canonical
competitor `(sign', sig', exp')` with `exp' ≤ r.exponent` in R_v,
`decDigitLength sig' ≥ decDigitLength r.significand`. -/
theorem toDecimal_minimal_low_scale
    (w : UInt64)
    (h_fin : Word.isFinite w = true)
    (h_nonzero : (Word.decode w).m ≠ 0) :
    ∃ result, toDecimalBits w = .ok result ∧
      ∀ (_sign' : Bool) (sig' : Nat) (exp' : Int),
        sig' ≠ 0 →
        sig' % 10 ≠ 0 →
        exp' ≤ result.exponent →
        inRoundingInterval sig' exp' (Word.decode w).m (Word.decode w).q
                            (isIrregular (Word.decode w).m (Word.decode w).q) = true →
        decDigitLength sig' ≥ decDigitLength result.significand := by
  obtain ⟨result, hresult, _⟩ := toDecimalBits_in_Rv w h_fin h_nonzero
  refine ⟨result, hresult, ?_⟩
  intro sign' sig' exp' h_sig_ne h_canon h_exp_le h_mem
  set d := Word.decode w with hd
  set k := kOfMQ d.m d.q with hk
  have ⟨h_m_lt, h_q_lo, h_q_hi⟩ :=
    Srtfp.Schubfach.decode_invariants_bits w h_fin
  have h_m_pos : 1 ≤ d.m := Nat.one_le_iff_ne_zero.mpr h_nonzero
  have h_sig_pos : 1 ≤ sig' := Nat.one_le_iff_ne_zero.mpr h_sig_ne
  -- Identify result = Decimal.mk' d.sign sU.1 sU.2.
  have h_toDec_unfold :
      toDecimalBits w = .ok (Decimal.mk' d.sign (shortestUnsigned d.m d.q).1
                                            (shortestUnsigned d.m d.q).2) := by
    have hfin_lt : Word.biasedExp w < 2047 := by
      unfold Word.isFinite at h_fin; simpa using h_fin
    have hnan : Word.isNaN w = false := by
      unfold Word.isNaN
      have : ¬ Word.biasedExp w = 2047 := by omega
      simp [this]
    have hinf : Word.isInf w = false := by
      unfold Word.isInf
      have : ¬ Word.biasedExp w = 2047 := by omega
      simp [this]
    have hm_ne' : (Word.decode w).m ≠ 0 := h_nonzero
    unfold toDecimalBits
    rw [hnan, hinf]
    simp [hm_ne']
    rfl
  rw [h_toDec_unfold] at hresult
  have hresult_eq : result = Decimal.mk' d.sign (shortestUnsigned d.m d.q).1
                                                (shortestUnsigned d.m d.q).2 := by
    cases hresult; rfl
  set out_sig := (shortestUnsigned d.m d.q).1 with h_out_sig
  set out_exp := (shortestUnsigned d.m d.q).2 with h_out_exp
  have h_out_pos : 1 ≤ out_sig :=
    shortestUnsigned_sig_pos d.m d.q h_m_pos h_m_lt h_q_lo h_q_hi
  have h_out_sig_ne : out_sig ≠ 0 := Nat.one_le_iff_ne_zero.mp h_out_pos
  have h_out_mem : inRoundingInterval out_sig out_exp d.m d.q (isIrregular d.m d.q) = true :=
    shortestUnsigned_mem_rv d.m d.q h_m_pos h_m_lt h_q_lo h_q_hi
  have ⟨_, h_res_sig_ne, h_res_canon, h_out_exp_le_res_exp, h_res_val⟩ :=
    mk_pos_props d.sign out_sig out_exp h_out_sig_ne
  have h_res_sig_pos : 1 ≤ result.significand := by
    rw [hresult_eq]; exact Nat.one_le_iff_ne_zero.mpr h_res_sig_ne
  have h_res_mem : inRoundingInterval result.significand result.exponent
                                      d.m d.q (isIrregular d.m d.q) = true := by
    rw [hresult_eq]
    exact mk_pos_result_in_Rv d.sign out_sig out_exp h_out_sig_ne d.m d.q h_out_mem
  -- Dispatch on exp' vs k+1.
  by_cases h_exp_high : exp' ≥ k + 1
  · -- High-scale: apply high-scale theorem.
    obtain ⟨result', hres', hhigh⟩ := toDecimal_minimal_high_scale w h_fin h_nonzero
    have h_result'_eq : result' = result := by
      rw [h_toDec_unfold] at hres'
      cases hresult
      cases hres'
      rfl
    rw [h_result'_eq] at hhigh
    have h_eq := hhigh sign' sig' exp' h_sig_ne h_canon h_exp_high h_mem
    omega
  · -- Low-scale: exp' ≤ k.
    push_neg at h_exp_high
    have h_exp_le_k : exp' ≤ k := by omega
    have h_rel := shortestUnsigned_length_relation d.m d.q
    have h_out_exp_ge_k : out_exp ≥ k := by
      rcases h_rel with ⟨_, h_exp_eq, _⟩ | ⟨h_exp_eq, _⟩
      · show (shortestUnsigned d.m d.q).2 ≥ k
        rw [h_exp_eq]; omega
      · show (shortestUnsigned d.m d.q).2 ≥ k
        rw [h_exp_eq]
        exact Int.le_refl _
    have h_res_exp_ge_k : result.exponent ≥ k := by
      rw [hresult_eq]
      exact Int.le_trans h_out_exp_ge_k h_out_exp_le_res_exp
    by_cases h_strict : exp' < result.exponent
    · -- Strict low-scale.
      exact strict_low_scale_digit_bound d.m d.q h_m_pos
              sig' exp' h_sig_pos h_mem
              result.significand result.exponent h_res_sig_pos h_res_mem h_strict
    · -- Boundary: exp' = result.exponent.
      push_neg at h_strict
      have h_eq_exp : exp' = result.exponent := le_antisymm h_exp_le h_strict
      have h_res_exp_eq_k : result.exponent = k := by omega
      rw [h_res_exp_eq_k] at h_eq_exp h_res_mem
      -- Identify fallback case.
      rcases h_rel with ⟨hs_big, h_exp_eq, h_or⟩ | ⟨h_exp_eq, h_sig_rel⟩
      · -- out_exp = k+1. result.exponent ≥ out_exp = k+1, contradicting = k.
        exfalso
        have h_oe : out_exp = k + 1 := by show (shortestUnsigned d.m d.q).2 = k + 1; exact h_exp_eq
        have h_res_exp_ge_k1 : result.exponent ≥ out_exp := by
          rw [hresult_eq]; exact h_out_exp_le_res_exp
        rw [h_oe] at h_res_exp_ge_k1
        rw [h_res_exp_eq_k] at h_res_exp_ge_k1
        omega
      · -- Fallback: out_exp = k.
        have h_oe_eq : out_exp = k := by show (shortestUnsigned d.m d.q).2 = k; exact h_exp_eq
        have h_os_eq : out_sig = pickNearer (shiftedSig d.m d.q k) k d.m d.q := by
          show (shortestUnsigned d.m d.q).1 = pickNearer (shiftedSig d.m d.q k) k d.m d.q
          exact h_sig_rel
        -- result.exponent = out_exp + h, with both = k, so h = 0.
        have h_h_zero : ((Decimal.mk' d.sign out_sig out_exp).exponent - out_exp).toNat = 0 := by
          have h1 : result.exponent = out_exp := by
            rw [h_oe_eq]; exact h_res_exp_eq_k
          have h2 : (Decimal.mk' d.sign out_sig out_exp).exponent = out_exp := by
            conv => lhs; rw [← hresult_eq]
            exact h1
          rw [h2]; simp
        -- result.significand = out_sig.
        have h_res_sig_eq_out : result.significand = out_sig := by
          have hval : (Decimal.mk' d.sign out_sig out_exp).significand *
                        10 ^ ((Decimal.mk' d.sign out_sig out_exp).exponent - out_exp).toNat = out_sig :=
            h_res_val
          rw [h_h_zero] at hval
          have hres_eq_mk : result.significand = (Decimal.mk' d.sign out_sig out_exp).significand := by
            rw [hresult_eq]
          rw [hres_eq_mk]
          simpa using hval
        rw [h_res_sig_eq_out]
        rw [h_os_eq]
        set s := shiftedSig d.m d.q k with hs
        set pn := pickNearer s k d.m d.q with hpn
        by_cases hs_big : s ≥ 10
        · -- True fallback. Derive uIn=false, wIn=false at K+1.
          have h_uIn_false : inRoundingInterval (s / 10) (k + 1) d.m d.q (isIrregular d.m d.q) = false := by
            rcases Bool.eq_false_or_eq_true (inRoundingInterval (s / 10) (k + 1) d.m d.q (isIrregular d.m d.q)) with hT | hF
            · exfalso
              have h_su_unfold : (shortestUnsigned d.m d.q).2 = k + 1 := by
                unfold shortestUnsigned
                rw [if_pos hs_big, if_pos hT]
              have h_oe_val : (shortestUnsigned d.m d.q).2 = k := h_oe_eq
              rw [h_su_unfold] at h_oe_val
              omega
            · exact hF
          have h_wIn_false : inRoundingInterval (s / 10 + 1) (k + 1) d.m d.q (isIrregular d.m d.q) = false := by
            rcases Bool.eq_false_or_eq_true (inRoundingInterval (s / 10 + 1) (k + 1) d.m d.q (isIrregular d.m d.q)) with hT | hF
            · exfalso
              have h_su_unfold : (shortestUnsigned d.m d.q).2 = k + 1 := by
                unfold shortestUnsigned
                rw [if_pos hs_big, if_neg (Bool.eq_false_iff.mp h_uIn_false), if_pos hT]
              have h_oe_val : (shortestUnsigned d.m d.q).2 = k := h_oe_eq
              rw [h_su_unfold] at h_oe_val
              omega
            · exact hF
          -- 10*(s/10) ∉ R_v at K (shift to K+1 where s/10 ∉ R_v).
          have h_10sd10_not_in : inRoundingInterval (10 * (s / 10)) k d.m d.q (isIrregular d.m d.q) = false := by
            have hk_eq : k + 1 - 1 = k := by grind
            have heq := inRoundingInterval_mul10_shift_down (s / 10) (k + 1) d.m d.q (isIrregular d.m d.q)
            rw [hk_eq] at heq
            rw [heq]; exact h_uIn_false
          -- 10*(s/10)+10 = 10*(s/10+1) ∉ R_v at K.
          have h_10sd10p_not_in : inRoundingInterval (10 * (s / 10) + 10) k d.m d.q (isIrregular d.m d.q) = false := by
            have hsum : 10 * (s / 10) + 10 = 10 * (s / 10 + 1) := by grind
            rw [hsum]
            have hk_eq : k + 1 - 1 = k := by grind
            have heq := inRoundingInterval_mul10_shift_down (s / 10 + 1) (k + 1) d.m d.q (isIrregular d.m d.q)
            rw [hk_eq] at heq
            rw [heq]; exact h_wIn_false
          -- pickn = pickNearer s k d.m d.q. result.significand = pn (after canonical strip).
          -- Need: pn ∈ R_v at K (it IS, since out_sig = pn ∈ R_v).
          have h_pn_mem : inRoundingInterval pn k d.m d.q (isIrregular d.m d.q) = true := by
            show inRoundingInterval (pickNearer (shiftedSig d.m d.q k) k d.m d.q) k d.m d.q (isIrregular d.m d.q) = true
            have h_pn_eq_out_sig : pickNearer (shiftedSig d.m d.q k) k d.m d.q = out_sig := by
              show pickNearer (shiftedSig d.m d.q k) k d.m d.q = (shortestUnsigned d.m d.q).1
              exact h_sig_rel.symm
            rw [h_pn_eq_out_sig]
            have : out_exp = k := h_oe_eq
            rw [← this]
            exact h_out_mem
          -- pn ∈ {s, s+1} (from pickNearer_eq_s_or_succ).
          have h_pn_or := pickNearer_eq_s_or_succ s k d.m d.q
          -- pn % 10 ≠ 0 (in boundary).
          have h_pn_canon : pn % 10 ≠ 0 := by
            have h1 : pn = out_sig := by
              show pickNearer s k d.m d.q = out_sig
              exact h_os_eq.symm
            rw [h1, ← h_res_sig_eq_out]
            -- Goal: result.significand % 10 ≠ 0. h_res_canon is about (mk' ...).significand.
            -- result = mk' ..., so significand equal.
            have : result.significand = (Decimal.mk' d.sign out_sig out_exp).significand := by
              rw [hresult_eq]
            rw [this]
            exact h_res_canon
          have h_s_div_10_pos : 1 ≤ s / 10 := by
            have : 10 / 10 ≤ s / 10 := Nat.div_le_div_right hs_big
            simpa using this
          -- pn ∈ {10*(s/10)+1, ..., 10*(s/10)+9} (in boundary).
          have h_pn_in_window : 10 * (s / 10) + 1 ≤ pn ∧ pn ≤ 10 * (s / 10) + 9 := by
            show 10 * (s / 10) + 1 ≤ pickNearer s k d.m d.q
                 ∧ pickNearer s k d.m d.q ≤ 10 * (s / 10) + 9
            rcases h_pn_or with h_pn_s | h_pn_s
            · -- pn = s.
              rw [h_pn_s]
              have h_s_canon : s % 10 ≠ 0 := by
                have := h_pn_canon
                show s % 10 ≠ 0
                have hpn_val : pn = s := h_pn_s
                rw [hpn_val] at this; exact this
              have h_smod : s % 10 < 10 := Nat.mod_lt s (by decide)
              have h_smod_pos : 1 ≤ s % 10 := by omega
              have h_decomp : s = 10 * (s / 10) + s % 10 := by omega
              omega
            · -- pn = s+1.
              rw [h_pn_s]
              have h_sp_canon : (s + 1) % 10 ≠ 0 := by
                have := h_pn_canon
                show (s + 1) % 10 ≠ 0
                have hpn_val : pn = s + 1 := h_pn_s
                rw [hpn_val] at this; exact this
              have h_smod : s % 10 < 10 := Nat.mod_lt s (by decide)
              have h_decomp : s = 10 * (s / 10) + s % 10 := by omega
              have h_smod_lt_9 : s % 10 ≠ 9 := by
                intro h_eq9
                have h_sp_mod : (s + 1) % 10 = 0 := by omega
                exact h_sp_canon h_sp_mod
              omega
          -- sig' ∈ R_v at K (h_mem with exp' = k). Use connectedness:
          --   sig' ≤ 10*(s/10) ⟹ since pn > 10*(s/10) and sig', pn ∈ R_v, 10*(s/10) ∈ R_v. Contradiction.
          --   sig' ≥ 10*(s/10)+10 ⟹ similarly contradiction.
          have h_mem_k : inRoundingInterval sig' k d.m d.q (isIrregular d.m d.q) = true := by
            rw [← h_eq_exp]; exact h_mem
          have h_sig_in_window : 10 * (s / 10) + 1 ≤ sig' ∧ sig' ≤ 10 * (s / 10) + 9 := by
            refine ⟨?_, ?_⟩
            · -- sig' > 10*(s/10).
              by_contra h_le
              push_neg at h_le
              -- h_le : sig' ≤ 10*(s/10). And pn ≥ 10*(s/10)+1 > 10*(s/10).
              -- By connectedness on [sig', pn]: 10*(s/10) ∈ R_v.
              -- But h_10sd10_not_in says 10*(s/10) ∉ R_v. Contradiction.
              have h_sig_le_10sd10 : sig' ≤ 10 * (s / 10) := by omega
              have h_10sd10_le_pn : 10 * (s / 10) ≤ pn := by omega
              have h_conn := inRoundingInterval_connected sig' (10 * (s / 10)) pn k d.m d.q
                              h_sig_le_10sd10 h_10sd10_le_pn h_mem_k h_pn_mem
              rw [h_conn] at h_10sd10_not_in
              exact Bool.false_ne_true h_10sd10_not_in.symm
            · -- sig' < 10*(s/10) + 10.
              by_contra h_ge
              push_neg at h_ge
              have h_pn_le_10sd10p : pn ≤ 10 * (s / 10) + 10 := by omega
              have h_10sd10p_le_sig : 10 * (s / 10) + 10 ≤ sig' := h_ge
              have h_conn := inRoundingInterval_connected pn (10 * (s / 10) + 10) sig' k d.m d.q
                              h_pn_le_10sd10p h_10sd10p_le_sig h_pn_mem h_mem_k
              rw [h_conn] at h_10sd10p_not_in
              exact Bool.false_ne_true h_10sd10p_not_in.symm
          -- Now use decDigitLength_window_t_ge_1.
          have h_sig_dl : decDigitLength sig' = decDigitLength (s / 10) + 1 :=
            decDigitLength_window_t_ge_1 (s / 10) h_s_div_10_pos sig'
              h_sig_in_window.1 h_sig_in_window.2
          have h_pn_dl : decDigitLength pn = decDigitLength (s / 10) + 1 :=
            decDigitLength_window_t_ge_1 (s / 10) h_s_div_10_pos pn
              h_pn_in_window.1 h_pn_in_window.2
          omega
        · -- s < 10 fallback.
          push_neg at hs_big
          have h_pn_canon : pn % 10 ≠ 0 := by
            have h1 : pn = out_sig := by
              show pickNearer s k d.m d.q = out_sig
              exact h_os_eq.symm
            rw [h1, ← h_res_sig_eq_out]
            have : result.significand = (Decimal.mk' d.sign out_sig out_exp).significand := by
              rw [hresult_eq]
            rw [this]
            exact h_res_canon
          have h_pn_bound : pn ≤ 10 := by
            show pickNearer s k d.m d.q ≤ 10
            rcases pickNearer_eq_s_or_succ s k d.m d.q with h_pn_s | h_pn_s
            · rw [h_pn_s]; omega
            · rw [h_pn_s]; omega
          have h_pn_ne_zero : pn ≠ 0 := by
            -- pn = out_sig ≥ 1 ≠ 0.
            intro h0
            have hpn_val : pn = out_sig := by
              show pickNearer s k d.m d.q = out_sig
              exact h_os_eq.symm
            rw [hpn_val] at h0
            exact h_out_sig_ne h0
          have h_pn_ne_10 : pn ≠ 10 := by
            intro h_eq
            rw [h_eq] at h_pn_canon
            exact h_pn_canon (by decide)
          have h_pn_lt_10 : pn < 10 := by omega
          have h_pn_dl : decDigitLength pn = 1 := decDigitLength_lt_10 h_pn_lt_10
          have h_sig_dl_pos : 1 ≤ decDigitLength sig' := decDigitLength_pos sig'
          omega

/-! ## Unified cross-scale minimality

Combining high-scale and low-scale gives the **full classical minimality**:
no canonical Decimal in R_v has strictly fewer digits than the output. -/

/-- **Cross-scale classical minimality** of `toDecimal`. For finite non-zero
Floats, `toDecimal f` produces a result `r` with the fewest digits among
canonical competitors in R_v.

The bound combines:
* `toDecimal_minimal_high_scale` for `exp' ≥ k + 1`.
* `toDecimal_minimal_low_scale` for `exp' ≤ result.exponent`. -/
theorem toDecimal_minimal
    (w : UInt64)
    (h_fin : Word.isFinite w = true)
    (h_nonzero : (Word.decode w).m ≠ 0) :
    ∃ result, toDecimalBits w = .ok result ∧
      ∀ (_sign' : Bool) (sig' : Nat) (exp' : Int),
        sig' ≠ 0 →
        sig' % 10 ≠ 0 →
        inRoundingInterval sig' exp' (Word.decode w).m (Word.decode w).q
                            (isIrregular (Word.decode w).m (Word.decode w).q) = true →
        decDigitLength sig' ≥ decDigitLength result.significand := by
  obtain ⟨result, hresult, hlow⟩ := toDecimal_minimal_low_scale w h_fin h_nonzero
  obtain ⟨result', hres', hhigh⟩ := toDecimal_minimal_high_scale w h_fin h_nonzero
  have h_result_eq : result' = result := by
    rw [hres'] at hresult
    cases hresult; rfl
  rw [h_result_eq] at hhigh
  refine ⟨result, hresult, ?_⟩
  intro sign' sig' exp' h_sig_ne h_canon h_mem
  set d := Word.decode w with hd
  set k := kOfMQ d.m d.q with hk
  by_cases h_exp_high : exp' ≥ k + 1
  · -- High-scale: gives equality.
    have h_eq := hhigh sign' sig' exp' h_sig_ne h_canon h_exp_high h_mem
    omega
  · -- exp' ≤ k. Apply low-scale (which requires exp' ≤ result.exponent).
    push_neg at h_exp_high
    have h_exp_le_k : exp' ≤ k := by omega
    -- result.exponent ≥ k always (Schubfach output exponent).
    have ⟨h_m_lt, h_q_lo, h_q_hi⟩ :=
      Srtfp.Schubfach.decode_invariants_bits w h_fin
    have h_m_pos : 1 ≤ d.m := Nat.one_le_iff_ne_zero.mpr h_nonzero
    have h_toDec_unfold :
        toDecimalBits w = .ok (Decimal.mk' d.sign (shortestUnsigned d.m d.q).1
                                              (shortestUnsigned d.m d.q).2) := by
      have hfin_lt : Word.biasedExp w < 2047 := by
        unfold Word.isFinite at h_fin; simpa using h_fin
      have hnan : Word.isNaN w = false := by
        unfold Word.isNaN
        have : ¬ Word.biasedExp w = 2047 := by omega
        simp [this]
      have hinf : Word.isInf w = false := by
        unfold Word.isInf
        have : ¬ Word.biasedExp w = 2047 := by omega
        simp [this]
      have hm_ne' : (Word.decode w).m ≠ 0 := h_nonzero
      unfold toDecimalBits
      rw [hnan, hinf]
      simp [hm_ne']
      rfl
    rw [h_toDec_unfold] at hresult
    have hresult_eq : result = Decimal.mk' d.sign (shortestUnsigned d.m d.q).1
                                                  (shortestUnsigned d.m d.q).2 := by
      cases hresult; rfl
    have h_out_pos : 1 ≤ (shortestUnsigned d.m d.q).1 :=
      shortestUnsigned_sig_pos d.m d.q h_m_pos h_m_lt h_q_lo h_q_hi
    have h_out_sig_ne : (shortestUnsigned d.m d.q).1 ≠ 0 := Nat.one_le_iff_ne_zero.mp h_out_pos
    have ⟨_, _, _, h_out_exp_le_res_exp, _⟩ :=
      mk_pos_props d.sign (shortestUnsigned d.m d.q).1 (shortestUnsigned d.m d.q).2 h_out_sig_ne
    have h_rel := shortestUnsigned_length_relation d.m d.q
    have h_out_exp_ge_k : (shortestUnsigned d.m d.q).2 ≥ k := by
      rcases h_rel with ⟨_, h_exp_eq, _⟩ | ⟨h_exp_eq, _⟩
      · rw [h_exp_eq]; omega
      · rw [h_exp_eq]
        exact Int.le_refl _
    have h_res_exp_ge_k : result.exponent ≥ k := by
      rw [hresult_eq]
      exact Int.le_trans h_out_exp_ge_k h_out_exp_le_res_exp
    have h_exp_le_res : exp' ≤ result.exponent := by omega
    exact hlow sign' sig' exp' h_sig_ne h_canon h_exp_le_res h_mem

/-! ## Scale-uniqueness: same digit length pins the exponent (up to a unit)

`strict_low_scale_digit_bound`, sharpened, says: for `exp_a < exp_b` both in
`R_v`, `L_a ≥ L_b + (exp_b - exp_a) - 1`.  Two canonical decimals in the *same*
`R_v` with *equal* digit length therefore have exponents differing by at most
one (the power-of-ten boundary). -/

/-- **Sharp low-scale digit bound.** For `exp_a < exp_b` both in `R_v`,
`decDigitLength sig_a ≥ decDigitLength sig_b + (exp_b - exp_a) - 1`.  This is
the genuine conclusion of `strict_low_scale_digit_bound`'s proof (the final
`omega` only weakened it to `≥ L_b`). -/
theorem strict_low_scale_digit_bound_sharp (m : Nat) (q : Int)
    (hm_pos : 1 ≤ m)
    (sig_a : Nat) (exp_a : Int) (_h_sig_a : 1 ≤ sig_a)
    (h_mem_a : inRoundingInterval sig_a exp_a m q (isIrregular m q) = true)
    (sig_b : Nat) (exp_b : Int) (h_sig_b : 1 ≤ sig_b)
    (h_mem_b : inRoundingInterval sig_b exp_b m q (isIrregular m q) = true)
    (h_strict : exp_a < exp_b) :
    decDigitLength sig_b + (exp_b - exp_a).toNat - 1 ≤ decDigitLength sig_a := by
  set L_a := decDigitLength sig_a with hLa
  set L_b := decDigitLength sig_b with hLb
  let h_nat : Nat := (exp_b - exp_a).toNat
  have h_h_pos : 1 ≤ h_nat := by
    have h_nn : 0 ≤ exp_b - exp_a := by omega
    have h_int : (h_nat : Int) = exp_b - exp_a := Int.toNat_of_nonneg h_nn
    have : 1 ≤ (h_nat : Int) := by rw [h_int]; omega
    exact_mod_cast this
  have h_h_eq : (h_nat : Int) = exp_b - exp_a := by
    apply Int.toNat_of_nonneg; omega
  have h_exp_form : exp_b - (h_nat : Int) = exp_a := by
    rw [h_h_eq]; omega
  have hshift :
      inRoundingInterval (sig_b * 10 ^ h_nat) (exp_b - (h_nat : Int)) m q (isIrregular m q)
        = inRoundingInterval sig_b exp_b m q (isIrregular m q) :=
    inRoundingInterval_mul10pow_shift_down sig_b h_nat exp_b m q (isIrregular m q)
  rw [h_exp_form] at hshift
  have h_mem_lifted : inRoundingInterval (sig_b * 10 ^ h_nat) exp_a m q (isIrregular m q) = true := by
    rw [hshift]; exact h_mem_b
  have h_dl_pow : decDigitLength (sig_b * 10 ^ h_nat) = L_b + h_nat :=
    decDigitLength_mul_pow10 sig_b h_nat h_sig_b
  have hLb_pos : 1 ≤ L_b := decDigitLength_pos sig_b
  have h_upper :=
    digit_upper_bound_from_Rv (sig_b * 10 ^ h_nat) exp_a m q hm_pos h_mem_lifted
  rw [h_dl_pow] at h_upper
  have h_lower :=
    digit_lower_bound_from_Rv sig_a exp_a m q hm_pos h_mem_a
  rw [← hLa] at h_lower
  have h_3 : (4 * (m : Int) + 2) ≤ 3 * (4 * (m : Int) - 2) := by
    have : (1 : Int) ≤ (m : Int) := by exact_mod_cast hm_pos
    grind
  have h_tenP_qN_pos : (0 : Int) < (tenPosPow exp_a : Int) * (twoNegPow q : Int) :=
    tenPos_twoNeg_pos_Int q exp_a
  have h_qP_tenN_pos : (0 : Int) < (twoPosPow q : Int) * (tenNegPow exp_a : Int) :=
    twoPos_tenNeg_pos_Int q exp_a
  have h_chain1 :
      4 * (10 : Int)^(L_b + h_nat - 1) * (tenPosPow exp_a : Int) * (twoNegPow q : Int)
        ≤ 3 * (4 * (m : Int) - 2) * (twoPosPow q : Int) * (tenNegPow exp_a : Int) := by
    have h_mul := Int.mul_le_mul_of_nonneg_right h_3 (Int.le_of_lt h_qP_tenN_pos)
    have h_assoc1 : (4 * (m : Int) + 2) * ((twoPosPow q : Int) * (tenNegPow exp_a : Int))
                    = (4 * (m : Int) + 2) * (twoPosPow q : Int) * (tenNegPow exp_a : Int) := by grind
    have h_assoc2 : 3 * (4 * (m : Int) - 2) * ((twoPosPow q : Int) * (tenNegPow exp_a : Int))
                    = 3 * (4 * (m : Int) - 2) * (twoPosPow q : Int) * (tenNegPow exp_a : Int) := by grind
    rw [h_assoc1, h_assoc2] at h_mul
    grind
  have h_chain2 :
      3 * (4 * (m : Int) - 2) * (twoPosPow q : Int) * (tenNegPow exp_a : Int)
        < 12 * (10 : Int)^L_a * (tenPosPow exp_a : Int) * (twoNegPow q : Int) := by
    have h_a : 3 * ((4 * (m : Int) - 2) * (twoPosPow q : Int) * (tenNegPow exp_a : Int))
                < 3 * (4 * (10 : Int)^L_a * (tenPosPow exp_a : Int) * (twoNegPow q : Int)) :=
      Int.mul_lt_mul_of_pos_left h_lower (by decide)
    have e1 : 3 * ((4 * (m : Int) - 2) * (twoPosPow q : Int) * (tenNegPow exp_a : Int))
              = 3 * (4 * (m : Int) - 2) * (twoPosPow q : Int) * (tenNegPow exp_a : Int) := by grind
    have e2 : 3 * (4 * (10 : Int)^L_a * (tenPosPow exp_a : Int) * (twoNegPow q : Int))
              = 12 * (10 : Int)^L_a * (tenPosPow exp_a : Int) * (twoNegPow q : Int) := by grind
    rw [e1, e2] at h_a
    exact h_a
  have h_chain3 :
      4 * (10 : Int)^(L_b + h_nat - 1) * (tenPosPow exp_a : Int) * (twoNegPow q : Int)
        < 12 * (10 : Int)^L_a * (tenPosPow exp_a : Int) * (twoNegPow q : Int) := by
    grind
  have h_pos_factor : 0 < 4 * ((tenPosPow exp_a : Int) * (twoNegPow q : Int)) :=
    Int.mul_pos (by decide) h_tenP_qN_pos
  have h_cancel :
      (10 : Int)^(L_b + h_nat - 1) < 3 * (10 : Int)^L_a := by
    have h_re :
        4 * ((tenPosPow exp_a : Int) * (twoNegPow q : Int)) * (10 : Int)^(L_b + h_nat - 1)
          < 4 * ((tenPosPow exp_a : Int) * (twoNegPow q : Int)) * (3 * (10 : Int)^L_a) := by
      have e1 : 4 * ((tenPosPow exp_a : Int) * (twoNegPow q : Int)) * (10 : Int)^(L_b + h_nat - 1)
                = 4 * (10 : Int)^(L_b + h_nat - 1) * (tenPosPow exp_a : Int) * (twoNegPow q : Int) := by grind
      have e2 : 4 * ((tenPosPow exp_a : Int) * (twoNegPow q : Int)) * (3 * (10 : Int)^L_a)
                = 12 * (10 : Int)^L_a * (tenPosPow exp_a : Int) * (twoNegPow q : Int) := by grind
      rw [e1, e2]
      exact h_chain3
    exact (Int.mul_lt_mul_left h_pos_factor).mp h_re
  have h_cancel_nat : (10 : Nat)^(L_b + h_nat - 1) < 3 * (10 : Nat)^L_a := by
    have h1 : ((10 : Nat)^(L_b + h_nat - 1) : Int) = (10 : Int)^(L_b + h_nat - 1) := by push_cast; rfl
    have h2 : ((3 * (10 : Nat)^L_a : Nat) : Int) = 3 * (10 : Int)^L_a := by push_cast; rfl
    have : ((10 : Nat)^(L_b + h_nat - 1) : Int) < ((3 * (10 : Nat)^L_a : Nat) : Int) := by
      rw [h1, h2]; exact h_cancel
    exact_mod_cast this
  -- L_a ≥ L_b + h_nat - 1.
  have h_pow_bound : L_b + h_nat - 1 ≤ L_a := by
    by_contra hcc
    push_neg at hcc
    have hL_le : L_a + 1 ≤ L_b + h_nat - 1 := hcc
    have h_pow_step : (10 : Nat)^(L_a + 1) ≤ 10^(L_b + h_nat - 1) :=
      Nat.pow_le_pow_right (by decide) hL_le
    have h_pow_succ : (10 : Nat)^(L_a + 1) = 10 * 10^L_a := by
      rw [Nat.pow_succ, Nat.mul_comm]
    rw [h_pow_succ] at h_pow_step
    omega
  exact h_pow_bound

/-- **Scale gap ≤ 1.** Two canonical decimals in the same `R_v` whose
significands have equal `decDigitLength` have exponents differing by at most
one. -/
theorem samelen_exp_diff_le_one (m : Nat) (q : Int) (hm_pos : 1 ≤ m)
    (sig_a : Nat) (exp_a : Int) (h_sig_a : 1 ≤ sig_a)
    (h_mem_a : inRoundingInterval sig_a exp_a m q (isIrregular m q) = true)
    (sig_b : Nat) (exp_b : Int) (h_sig_b : 1 ≤ sig_b)
    (h_mem_b : inRoundingInterval sig_b exp_b m q (isIrregular m q) = true)
    (h_len : decDigitLength sig_a = decDigitLength sig_b) :
    (exp_a - exp_b).natAbs ≤ 1 := by
  rcases lt_trichotomy exp_a exp_b with h | h | h
  · have hbound := strict_low_scale_digit_bound_sharp m q hm_pos
      sig_a exp_a h_sig_a h_mem_a sig_b exp_b h_sig_b h_mem_b h
    have h_tn : (1 : Int) ≤ (exp_b - exp_a).toNat := by
      have : (0 : Int) ≤ exp_b - exp_a := by omega
      have he : ((exp_b - exp_a).toNat : Int) = exp_b - exp_a := Int.toNat_of_nonneg this
      omega
    -- L_b + gap - 1 ≤ L_a = L_b ⇒ gap ≤ 1.
    rw [h_len] at hbound
    have hgap_le : (exp_b - exp_a).toNat ≤ 1 := by omega
    have he : ((exp_b - exp_a).toNat : Int) = exp_b - exp_a := by
      apply Int.toNat_of_nonneg; omega
    omega
  · omega
  · have hbound := strict_low_scale_digit_bound_sharp m q hm_pos
      sig_b exp_b h_sig_b h_mem_b sig_a exp_a h_sig_a h_mem_a h
    rw [← h_len] at hbound
    have hgap_le : (exp_a - exp_b).toNat ≤ 1 := by omega
    have he : ((exp_a - exp_b).toNat : Int) = exp_a - exp_b := by
      apply Int.toNat_of_nonneg; omega
    omega

end Srtfp.Schubfach

/- Clinger Decimal→Float correctness — irregular carry branch (M4).

   Branch 3b (carry from pre-rounding): when normal-spaced rounding
   produces `m_pre ≥ 2^53`, the result is `(m = 2^52, q = e - 51)`.
   Using `num_pre / denom_pre < 2^53` from the `findBinaryExp` upper
   bound, `m_pre = 2^53` exactly. The half-ULP bound at scale `q - 1`
   then translates to the irregular bound at scale `q` via the
   `num_pre · denom = 2 · num · denom_pre` algebraic identity. -/

import Srtfp.Proofs.Numeric.Clinger.Base
import Srtfp.Proofs.Numeric.Clinger.Regular
import Srtfp.Proofs.Numeric.Clinger.FindBinaryExp
import Srtfp.Proofs.Numeric.Schubfach.Shorter

namespace PP.Numeric.Clinger

open PP.Numeric.Float
open PP.Numeric.Schubfach
open PP.Numeric

/-! ## Cleared-form setup for the irregular-carry branch.

The pre-rounding form lives at scale `q - 1 = e - 52`; the post-rounding
form lives at scale `q = e - 51`. We compute both sets of cleared-form
identities once, then bring them together via `num_pre_denom_eq`. -/

/-- Cleared-form identities for the pre-rounding scale `q - 1 = e - 52`. -/
private theorem c_cleared_pre (sig : Nat) (exp e : Int) (a b : Nat)
    (ha_eq : a = sig * tenPosPow exp) (hb_eq : b = tenNegPow exp)
    (hb : 0 < b) :
    let q : Int := e - 51
    let num_pre := (scaleByPow2 a b (52 - e)).1
    let denom_pre := (scaleByPow2 a b (52 - e)).2
    (num_pre : Int) = sig * (tenPosPow exp) * (twoNegPow (q - 1)) ∧
    (denom_pre : Int) = (tenNegPow exp) * (twoPosPow (q - 1)) ∧
    0 < denom_pre := by
  simp only
  have h_a : a = (if exp ≥ 0 then sig * 10 ^ exp.toNat else sig) := by
    rw [ha_eq]
    by_cases hexp : 0 ≤ exp
    · rw [tenPosPow_nonneg hexp, if_pos hexp]
    · have hexp' : exp < 0 := Int.not_le.mp hexp
      rw [tenPosPow_neg hexp', if_neg hexp, Nat.mul_one]
  have h_b : b = (if exp ≥ 0 then 1 else 10 ^ (-exp).toNat) := by
    rw [hb_eq]
    by_cases hexp : 0 ≤ exp
    · rw [tenNegPow_nonneg hexp, if_pos hexp]
    · have hexp' : exp < 0 := Int.not_le.mp hexp
      rw [tenNegPow_neg hexp', if_neg hexp]
  have hk_eq : (e - 51 - 1 : Int) = -(52 - e) := by omega
  refine ⟨?_, ?_, scaleByPow2_denom_pos hb⟩
  · show ((scaleByPow2 a b (52 - e)).1 : Int) = _
    rw [scaleByPow2_num_clear', h_a]
    have h_at := scaleByPow2_num_clear_at' sig exp (52 - e) (e - 51 - 1) hk_eq
    exact_mod_cast h_at
  · show ((scaleByPow2 a b (52 - e)).2 : Int) = _
    rw [scaleByPow2_denom_clear', h_b]
    have h_at := scaleByPow2_denom_clear_at' sig exp (52 - e) (e - 51 - 1) hk_eq
    exact_mod_cast h_at

/-! ## Local arithmetic helpers (avoid `grind` / `ring`). -/

private theorem two_two_mul (x : Int) : 2 * (2 * x) = 4 * x := by
  rw [← Int.mul_assoc 2 2 x]; rfl

private theorem two_two_xy (x y : Int) : 2 * (2 * x * y) = 4 * x * y := by
  rw [Int.mul_assoc 2 x y, two_two_mul, Int.mul_assoc]

private theorem add_one_mul_dp (c d : Int) :
    (c + 1) * d = c * d + d := by
  rw [Int.add_mul, Int.one_mul]

private theorem sub_one_mul_dp (c d : Int) :
    (c - 1) * d = c * d - d := by
  rw [Int.sub_mul, Int.one_mul]

/-- `m_pre = 2^53` exactly, given pre-rounding bounds.

From the half-ULP bound `2·m_pre·denom_pre ≤ 2·num_pre + denom_pre` and
`num_pre < 2^53 · denom_pre`, we derive `m_pre ≤ 2^53`; with
`m_pre ≥ 2^53` from the carry hypothesis, equality follows. -/
private theorem mpre_eq_2pow53
    (num_pre denom_pre m_pre : Nat) (h_dp : 0 < denom_pre)
    (h_pre_hi : 2 * (m_pre : Int) * (denom_pre : Int)
                  ≤ 2 * (num_pre : Int) + (denom_pre : Int))
    (h_upper : num_pre < 2 ^ 53 * denom_pre)
    (h_carry : m_pre ≥ 2 ^ 53) :
    m_pre = 2 ^ 53 := by
  have h_dp_int : (0 : Int) < (denom_pre : Int) := by exact_mod_cast h_dp
  have h_upper_int : (num_pre : Int) < (2 ^ 53 : Int) * (denom_pre : Int) := by
    have h1 : (num_pre : Int) < ((2 ^ 53 * denom_pre : Nat) : Int) := by exact_mod_cast h_upper
    have h2 : ((2 ^ 53 * denom_pre : Nat) : Int) = (2 ^ 53 : Int) * (denom_pre : Int) := by
      rw [Int.natCast_mul]; rfl
    omega
  have h_2num : 2 * (num_pre : Int) < (2 * (2 ^ 53 : Int)) * (denom_pre : Int) := by
    have h_mul : (2 : Int) * (num_pre : Int) < (2 : Int) * ((2 ^ 53 : Int) * (denom_pre : Int)) :=
      Int.mul_lt_mul_of_pos_left h_upper_int (by decide : (0 : Int) < 2)
    have h_assoc : (2 : Int) * ((2 ^ 53 : Int) * (denom_pre : Int))
                    = (2 * (2 ^ 53 : Int)) * (denom_pre : Int) :=
      (Int.mul_assoc _ _ _).symm
    omega
  -- 2 * m_pre * dp ≤ 2 * num_pre + dp < (2*2^53 + 1) * dp.
  have h_sum : 2 * (num_pre : Int) + (denom_pre : Int)
                < ((2 * (2 ^ 53 : Int)) + 1) * (denom_pre : Int) := by
    have h_rhs : ((2 * (2 ^ 53 : Int)) + 1) * (denom_pre : Int)
                  = (2 * (2 ^ 53 : Int)) * (denom_pre : Int) + (denom_pre : Int) :=
      add_one_mul_dp _ _
    omega
  have h_chain : 2 * (m_pre : Int) * (denom_pre : Int)
                  < ((2 * (2 ^ 53 : Int)) + 1) * (denom_pre : Int) := by
    omega
  have h_mlt : 2 * (m_pre : Int) < (2 * (2 ^ 53 : Int)) + 1 :=
    Int.lt_of_mul_lt_mul_right h_chain (Int.le_of_lt h_dp_int)
  have h_m_le : (m_pre : Int) ≤ (2 ^ 53 : Int) := by omega
  have h_m_le_nat : m_pre ≤ 2 ^ 53 := by exact_mod_cast h_m_le
  omega

/-- **Branch 3b** (carry: pre-rounding produced `m ≥ 2^53`, result is
`(2^52, e + 1 - 52)`). -/
theorem irregular_carry_correct
    (sig : Nat) (exp e : Int) (a b : Nat)
    (ha_eq : a = sig * tenPosPow exp) (hb_eq : b = tenNegPow exp)
    (ha : 0 < a) (hb : 0 < b) (he_eq : e = findBinaryExp a b)
    (he_ge : e ≥ -1022)
    (h_carry : roundNearestEven (scaleByPow2 a b (52 - e)).1
                                (scaleByPow2 a b (52 - e)).2 ≥ 2 ^ 53) :
    inRoundingInterval sig exp (2 ^ 52) (e - 51)
        (isIrregular (2 ^ 52) (e - 51)) = true := by
  -- Pre-rounding cleared form (scale q - 1).
  obtain ⟨hnum_pre_int, hdenom_pre_int, hdenom_pre_pos⟩ :=
    c_cleared_pre sig exp e a b ha_eq hb_eq hb
  -- Pre-rounding bounds.
  have h_pre_bound :=
    roundNearestEven_cleared_bound (scaleByPow2 a b (52 - e)).1
                                    (scaleByPow2 a b (52 - e)).2 hdenom_pre_pos
  obtain ⟨h_pre_lo, h_pre_hi⟩ := h_pre_bound
  -- m_pre = 2^53 exactly.
  have h_upper_nat : (scaleByPow2 a b (52 - e)).1 < 2 ^ 53 * (scaleByPow2 a b (52 - e)).2 :=
    clinger_num_lt_2pow53_denom a b e ha hb he_eq
  have hm_pre_eq : roundNearestEven (scaleByPow2 a b (52 - e)).1
                                     (scaleByPow2 a b (52 - e)).2 = 2 ^ 53 :=
    mpre_eq_2pow53 _ _ _ hdenom_pre_pos h_pre_hi h_upper_nat h_carry
  -- Translate the pre-bounds to post-rounding scale.
  -- Post-rounding (m, q) = (2^52, e - 51); the scale identity is:
  --   num_pre · denom_post = 2 · num_post · denom_pre
  -- where num_post = sig · tenPosPow exp · twoNegPow q and
  --       denom_post = tenNegPow exp · twoPosPow q.
  -- We take num_post, denom_post as Nat values directly.
  -- num_post = sig * tenPosPow exp * twoNegPow (e - 51)
  -- denom_post = tenNegPow exp * twoPosPow (e - 51)
  -- These are positive by twoPow_pos / tenPow_pos.
  have hdenom_pos : 0 < tenNegPow exp * twoPosPow (e - 51) :=
    Nat.mul_pos (tenNegPow_pos exp) (twoPosPow_pos _)
  have hd_int : (0 : Int) < (tenNegPow exp * twoPosPow (e - 51) : Nat) := by exact_mod_cast hdenom_pos
  -- The cleared form identity: num_pre · denom_post = 2 · num_post · denom_pre.
  have h_scale_id :
      ((scaleByPow2 a b (52 - e)).1 : Int)
        * (tenNegPow exp * twoPosPow (e - 51) : Nat)
      = 2 * ((sig * tenPosPow exp * twoNegPow (e - 51) : Nat) : Int)
          * ((scaleByPow2 a b (52 - e)).2 : Int) := by
    rw [hnum_pre_int, hdenom_pre_int]
    push_cast
    exact num_pre_denom_eq sig exp (e - 51)
  -- From h_pre_lo / h_pre_hi (at scale q-1) and h_scale_id (relating num_pre to 2·num_post),
  -- derive the post-rounding bounds (4m - 1)·denom ≤ 4·num and 4·num ≤ (4m+1)·denom.
  -- Using m_pre = 2 · m and (4m-1)·dp ≤ 2·num_pre (from h_pre_hi with m_pre = 2m).
  --   h_pre_hi after m_pre = 2 m: 2 · (2m) · dp ≤ 2·num_pre + dp
  --                              ⟹ (4m·dp - dp) ≤ 2·num_pre ⟹ (4m-1)·dp ≤ 2·num_pre.
  -- Multiply by denom_post; use h_scale_id: num_pre · denom_post = 2·num·denom_pre:
  --   (4m-1)·dp · denom_post ≤ 2·num_pre·denom_post = 4·num·denom_pre
  -- Cancel dp (positive): (4m-1)·denom_post ≤ 4·num.
  -- The upper bound is symmetric.
  have hd_pre_int : (0 : Int) < ((scaleByPow2 a b (52 - e)).2 : Int) := by
    exact_mod_cast hdenom_pre_pos
  -- m_pre = 2 · 2^52 as Int.
  have h_m_pre_int : ((roundNearestEven (scaleByPow2 a b (52 - e)).1
                                         (scaleByPow2 a b (52 - e)).2 : Nat) : Int)
                    = 2 * ((2 ^ 52 : Nat) : Int) := by
    rw [hm_pre_eq]
    show ((2 ^ 53 : Nat) : Int) = 2 * ((2 ^ 52 : Nat) : Int)
    decide
  -- Lower bound at post scale.
  have h_lo_post :
      (4 * ((2 ^ 52 : Nat) : Int) - 1) * (tenNegPow exp * twoPosPow (e - 51) : Nat)
        ≤ 4 * ((sig * tenPosPow exp * twoNegPow (e - 51) : Nat) : Int) := by
    -- h_pre_hi : 2 * m_pre * dp ≤ 2 * num_pre + dp.
    have h := h_pre_hi
    rw [h_m_pre_int] at h
    -- 2 * (2 * 2^52) * dp = 4 * 2^52 * dp
    have h_4mdp : 2 * (2 * ((2 ^ 52 : Nat) : Int)) * ((scaleByPow2 a b (52 - e)).2 : Int)
                  = 4 * ((2 ^ 52 : Nat) : Int) * ((scaleByPow2 a b (52 - e)).2 : Int) := by
      rw [two_two_mul]
    rw [h_4mdp] at h
    -- h : 4 * 2^52 * dp ≤ 2 * num_pre + dp.
    -- (4 m - 1) · dp ≤ 2 · num_pre.
    have h_pre_lo_scaled : (4 * ((2 ^ 52 : Nat) : Int) - 1)
                              * ((scaleByPow2 a b (52 - e)).2 : Int)
                            ≤ 2 * ((scaleByPow2 a b (52 - e)).1 : Int) := by
      have h_lhs : (4 * ((2 ^ 52 : Nat) : Int) - 1)
                      * ((scaleByPow2 a b (52 - e)).2 : Int)
                    = 4 * ((2 ^ 52 : Nat) : Int) * ((scaleByPow2 a b (52 - e)).2 : Int)
                        - ((scaleByPow2 a b (52 - e)).2 : Int) :=
        sub_one_mul_dp _ _
      rw [h_lhs]; omega
    -- Multiply by denom_post (positive) on the right.
    have h_mul : ((4 * ((2 ^ 52 : Nat) : Int) - 1)
                   * ((scaleByPow2 a b (52 - e)).2 : Int))
                 * ((tenNegPow exp * twoPosPow (e - 51) : Nat) : Int)
                 ≤ (2 * ((scaleByPow2 a b (52 - e)).1 : Int))
                   * ((tenNegPow exp * twoPosPow (e - 51) : Nat) : Int) :=
      Int.mul_le_mul_of_nonneg_right h_pre_lo_scaled (Int.le_of_lt hd_int)
    -- Rearrange LHS: ((4m-1)·dp) · dpost = (4m-1) · dpost · dp.
    have h_lhs_eq :
        ((4 * ((2 ^ 52 : Nat) : Int) - 1)
            * ((scaleByPow2 a b (52 - e)).2 : Int))
          * ((tenNegPow exp * twoPosPow (e - 51) : Nat) : Int)
        = (4 * ((2 ^ 52 : Nat) : Int) - 1)
            * ((tenNegPow exp * twoPosPow (e - 51) : Nat) : Int)
            * ((scaleByPow2 a b (52 - e)).2 : Int) := by
      rw [Int.mul_assoc (4 * ((2 ^ 52 : Nat) : Int) - 1)
            ((scaleByPow2 a b (52 - e)).2 : Int)
            ((tenNegPow exp * twoPosPow (e - 51) : Nat) : Int),
          Int.mul_comm ((scaleByPow2 a b (52 - e)).2 : Int)
            ((tenNegPow exp * twoPosPow (e - 51) : Nat) : Int),
          ← Int.mul_assoc]
    -- Rearrange RHS: (2 · num_pre) · dpost = 2 · (num_pre · dpost)
    --                = 2 · (2 · num_post · dp) = 4 · num_post · dp.
    have h_rhs_eq :
        (2 * ((scaleByPow2 a b (52 - e)).1 : Int))
          * ((tenNegPow exp * twoPosPow (e - 51) : Nat) : Int)
        = 4 * ((sig * tenPosPow exp * twoNegPow (e - 51) : Nat) : Int)
            * ((scaleByPow2 a b (52 - e)).2 : Int) := by
      rw [Int.mul_assoc 2 ((scaleByPow2 a b (52 - e)).1 : Int)
            ((tenNegPow exp * twoPosPow (e - 51) : Nat) : Int)]
      rw [h_scale_id, two_two_xy]
    rw [h_lhs_eq, h_rhs_eq] at h_mul
    -- Cancel denom_pre on both sides.
    exact Int.le_of_mul_le_mul_right h_mul hd_pre_int
  -- Upper bound at post scale.
  have h_hi_post :
      4 * ((sig * tenPosPow exp * twoNegPow (e - 51) : Nat) : Int)
        ≤ (4 * ((2 ^ 52 : Nat) : Int) + 1) * (tenNegPow exp * twoPosPow (e - 51) : Nat) := by
    have h := h_pre_lo
    rw [h_m_pre_int] at h
    -- 2 * (2 · 2^52) * dp - dp ≤ 2 · num_pre,
    -- so (4 · 2^52 + 1) · dp ≥ 2 · num_pre + dp.
    have h_4mdp : 2 * (2 * ((2 ^ 52 : Nat) : Int)) * ((scaleByPow2 a b (52 - e)).2 : Int)
                  = 4 * ((2 ^ 52 : Nat) : Int) * ((scaleByPow2 a b (52 - e)).2 : Int) := by
      rw [two_two_mul]
    rw [h_4mdp] at h
    have h_pre_hi_scaled : 2 * ((scaleByPow2 a b (52 - e)).1 : Int)
                          ≤ (4 * ((2 ^ 52 : Nat) : Int) + 1)
                              * ((scaleByPow2 a b (52 - e)).2 : Int) := by
      have h_rhs : (4 * ((2 ^ 52 : Nat) : Int) + 1)
                    * ((scaleByPow2 a b (52 - e)).2 : Int)
                  = 4 * ((2 ^ 52 : Nat) : Int) * ((scaleByPow2 a b (52 - e)).2 : Int)
                      + ((scaleByPow2 a b (52 - e)).2 : Int) :=
        add_one_mul_dp _ _
      omega
    -- Multiply by denom_post and rearrange.
    have h_mul : (2 * ((scaleByPow2 a b (52 - e)).1 : Int))
                  * ((tenNegPow exp * twoPosPow (e - 51) : Nat) : Int)
                ≤ ((4 * ((2 ^ 52 : Nat) : Int) + 1)
                    * ((scaleByPow2 a b (52 - e)).2 : Int))
                  * ((tenNegPow exp * twoPosPow (e - 51) : Nat) : Int) :=
      Int.mul_le_mul_of_nonneg_right h_pre_hi_scaled (Int.le_of_lt hd_int)
    have h_lhs_eq :
        (2 * ((scaleByPow2 a b (52 - e)).1 : Int))
          * ((tenNegPow exp * twoPosPow (e - 51) : Nat) : Int)
        = 4 * ((sig * tenPosPow exp * twoNegPow (e - 51) : Nat) : Int)
            * ((scaleByPow2 a b (52 - e)).2 : Int) := by
      rw [Int.mul_assoc 2 ((scaleByPow2 a b (52 - e)).1 : Int)
            ((tenNegPow exp * twoPosPow (e - 51) : Nat) : Int)]
      rw [h_scale_id, two_two_xy]
    have h_rhs_eq :
        ((4 * ((2 ^ 52 : Nat) : Int) + 1)
            * ((scaleByPow2 a b (52 - e)).2 : Int))
          * ((tenNegPow exp * twoPosPow (e - 51) : Nat) : Int)
        = (4 * ((2 ^ 52 : Nat) : Int) + 1)
            * ((tenNegPow exp * twoPosPow (e - 51) : Nat) : Int)
            * ((scaleByPow2 a b (52 - e)).2 : Int) := by
      rw [Int.mul_assoc (4 * ((2 ^ 52 : Nat) : Int) + 1)
            ((scaleByPow2 a b (52 - e)).2 : Int)
            ((tenNegPow exp * twoPosPow (e - 51) : Nat) : Int),
          Int.mul_comm ((scaleByPow2 a b (52 - e)).2 : Int)
            ((tenNegPow exp * twoPosPow (e - 51) : Nat) : Int),
          ← Int.mul_assoc]
    rw [h_lhs_eq, h_rhs_eq] at h_mul
    exact Int.le_of_mul_le_mul_right h_mul hd_pre_int
  -- Irregularity check.
  have h_irreg : isIrregular (2 ^ 52) (e - 51) = true := by
    unfold isIrregular minNormalSignificand minBinaryExp
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨?_, ?_⟩
    · decide
    · omega
  -- Reduce inRoundingInterval.
  rw [inRoundingInterval_iff,
      fourVL_eq_irregular (2 ^ 52) (e - 51) exp h_irreg,
      fourVR_eq, fourU_eq]
  -- Reassociate.
  have hreVL : (4 * ((2 ^ 52 : Nat) : Int) - 1) * (twoPosPow (e - 51) : Int)
                  * (tenNegPow exp : Int)
                = (4 * ((2 ^ 52 : Nat) : Int) - 1)
                  * ((twoPosPow (e - 51) : Int) * (tenNegPow exp : Int)) :=
    Int.mul_assoc _ _ _
  have hreVR : (4 * ((2 ^ 52 : Nat) : Int) + 2) * (twoPosPow (e - 51) : Int)
                  * (tenNegPow exp : Int)
                = (4 * ((2 ^ 52 : Nat) : Int) + 2)
                  * ((twoPosPow (e - 51) : Int) * (tenNegPow exp : Int)) :=
    Int.mul_assoc _ _ _
  have hreU : 4 * (sig : Int) * (tenPosPow exp : Int) * (twoNegPow (e - 51) : Int)
                = 4 * (sig : Int)
                  * ((tenPosPow exp : Int) * (twoNegPow (e - 51) : Int)) :=
    Int.mul_assoc _ _ _
  rw [hreVL, hreVR, hreU]
  -- Bring `tenNegPow exp * twoPosPow (e - 51) : Nat → Int` casts in line.
  have hPdenom : (twoPosPow (e - 51) : Int) * (tenNegPow exp : Int)
                = ((tenNegPow exp * twoPosPow (e - 51) : Nat) : Int) := by
    push_cast; exact Int.mul_comm _ _
  have hQnum : 4 * (sig : Int) * ((tenPosPow exp : Int) * (twoNegPow (e - 51) : Int))
                = 4 * ((sig * tenPosPow exp * twoNegPow (e - 51) : Nat) : Int) := by
    push_cast
    rw [Int.mul_assoc (sig : Int) (tenPosPow exp : Int) (twoNegPow (e - 51) : Int),
        ← Int.mul_assoc (4 : Int) (sig : Int)
          ((tenPosPow exp : Int) * (twoNegPow (e - 51) : Int))]
  rw [hPdenom, hQnum]
  refine ⟨?_, ?_⟩
  · -- (4m - 1) · denom ≤ 4 · num (≤, not <; could be equality with parity).
    rcases Int.lt_or_eq_of_le h_lo_post with h_lt | h_eq
    · left; exact h_lt
    · right
      exact ⟨h_eq, by decide⟩
  · -- 4·num ≤ (4m+1)·denom; needs <(4m+2). Strict since +1 < +2.
    left
    have hstrict : (4 * ((2 ^ 52 : Nat) : Int) + 1)
                      * ((tenNegPow exp * twoPosPow (e - 51) : Nat) : Int)
                  < (4 * ((2 ^ 52 : Nat) : Int) + 2)
                      * ((tenNegPow exp * twoPosPow (e - 51) : Nat) : Int) := by
      have h_diff : (4 * ((2 ^ 52 : Nat) : Int) + 2)
                      * ((tenNegPow exp * twoPosPow (e - 51) : Nat) : Int)
                    - (4 * ((2 ^ 52 : Nat) : Int) + 1)
                        * ((tenNegPow exp * twoPosPow (e - 51) : Nat) : Int)
                  = ((tenNegPow exp * twoPosPow (e - 51) : Nat) : Int) := by
        have h_eq : (4 * ((2 ^ 52 : Nat) : Int) + 2)
                      * ((tenNegPow exp * twoPosPow (e - 51) : Nat) : Int)
                    - (4 * ((2 ^ 52 : Nat) : Int) + 1)
                        * ((tenNegPow exp * twoPosPow (e - 51) : Nat) : Int)
                    = ((4 * ((2 ^ 52 : Nat) : Int) + 2)
                        - (4 * ((2 ^ 52 : Nat) : Int) + 1))
                        * ((tenNegPow exp * twoPosPow (e - 51) : Nat) : Int) := by
          rw [Int.sub_mul]
        rw [h_eq]
        have h_one : (4 * ((2 ^ 52 : Nat) : Int) + 2) - (4 * ((2 ^ 52 : Nat) : Int) + 1) = 1 := by
          omega
        rw [h_one, Int.one_mul]
      omega
    omega

end PP.Numeric.Clinger

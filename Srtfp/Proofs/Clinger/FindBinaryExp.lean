/- Clinger Decimal→Float correctness — `findBinaryExp` correctness (M4).

   The algorithm's `e := findBinaryExp a b` picks `e0 := log2 a − log2 b`
   if `leBy2e a b e0` holds, else `e0 − 1`. We prove that the chosen `e`
   satisfies `b · 2^e ≤ a < b · 2^{e+1}` (in the appropriate sign-split
   cleared form) whenever `a, b ≥ 1`.

   The bounds on the cleared `(num, denom) := scaleByPow2 a b (52 - e)`
   form (`2^52 · denom ≤ num` and `num < 2^53 · denom`) follow from
   those — they justify the no-carry irregular lower bound and the
   carry pre-rounding `m_pre = 2^53` analysis, respectively.

   The algebraic identity `num_pre · denom = 2 · num · denom_pre` ties
   the cleared forms at `q-1` and `q`. -/

import Srtfp.Proofs.Clinger.Base
import Srtfp.Proofs.Schubfach.Shorter

namespace Srtfp.Clinger

open Srtfp.Float
open Srtfp.Schubfach
open Srtfp

/-! ## `findBinaryExp` correctness -/

/-- Lower bound on `findBinaryExp`: `leBy2e a b (findBinaryExp a b) = true`. -/
theorem findBinaryExp_le (a b : Nat) (ha : 0 < a) (_hb : 0 < b) :
    leBy2e a b (findBinaryExp a b) = true := by
  unfold findBinaryExp
  by_cases h : leBy2e a b ((Nat.log2 a : Int) - Nat.log2 b) = true
  · simp [h]
  · have h_eq : (if leBy2e a b ((Nat.log2 a : Int) - Nat.log2 b) = true
                  then ((Nat.log2 a : Int) - Nat.log2 b)
                  else ((Nat.log2 a : Int) - Nat.log2 b) - 1)
              = ((Nat.log2 a : Int) - Nat.log2 b) - 1 := by
      rw [if_neg h]
    rw [h_eq, leBy2e_eq_true_iff]
    have ha_log : 2 ^ a.log2 ≤ a := Nat.log2_self_le (by omega)
    have hb_log' : b < 2 ^ (b.log2 + 1) := Nat.lt_log2_self
    have h_false : ¬ leBy2e a b ((Nat.log2 a : Int) - Nat.log2 b) = true := h
    rw [leBy2e_eq_true_iff] at h_false
    by_cases h1 : ((Nat.log2 a : Int) - Nat.log2 b - 1) ≥ 0
    · rw [if_pos h1]
      have he0 : ((Nat.log2 a : Int) - Nat.log2 b) ≥ 1 := by omega
      have he0_pos : ((Nat.log2 a : Int) - Nat.log2 b) ≥ 0 := by omega
      rw [if_pos he0_pos] at h_false
      have hb_le1 : b.log2 + 1 ≤ a.log2 := by
        have : 1 ≤ (a.log2 : Int) - b.log2 := he0; omega
      have he1_nat : ((Nat.log2 a : Int) - Nat.log2 b - 1).toNat = a.log2 - b.log2 - 1 := by
        have hh : ((Nat.log2 a : Int) - Nat.log2 b - 1) = ((a.log2 - b.log2 - 1 : Nat) : Int) := by
          omega
        rw [hh]; exact Int.toNat_natCast _
      have he0_nat : ((Nat.log2 a : Int) - Nat.log2 b).toNat = a.log2 - b.log2 := by
        have hh : ((Nat.log2 a : Int) - Nat.log2 b) = ((a.log2 - b.log2 : Nat) : Int) := by
          omega
        rw [hh]; exact Int.toNat_natCast _
      rw [he0_nat] at h_false
      rw [he1_nat]
      have h_false' : a < b * 2 ^ (a.log2 - b.log2) := by omega
      have hsplit : 2 ^ a.log2 = 2 ^ (b.log2 + 1) * 2 ^ (a.log2 - b.log2 - 1) := by
        rw [← Nat.pow_add]; congr 1; omega
      have key : b * 2 ^ (a.log2 - b.log2 - 1) < 2 ^ a.log2 := by
        rw [hsplit]
        exact (Nat.mul_lt_mul_right (Nat.pow_pos (by omega : 0 < (2 : Nat)))).mpr hb_log'
      omega
    · rw [if_neg h1]
      have he0 : ((Nat.log2 a : Int) - Nat.log2 b) ≤ 0 := by omega
      have h_a_le_b1 : a.log2 ≤ b.log2 + 1 := by
        have : (a.log2 : Int) ≤ b.log2 + 1 := by omega
        omega
      have hne : -((Nat.log2 a : Int) - Nat.log2 b - 1)
                  = ((b.log2 + 1 - a.log2 : Nat) : Int) := by
        omega
      have hne_toNat : (-((Nat.log2 a : Int) - Nat.log2 b - 1)).toNat
                          = b.log2 + 1 - a.log2 := by
        rw [hne]; exact Int.toNat_natCast _
      rw [hne_toNat]
      have hsplit : 2 ^ (b.log2 + 1) = 2 ^ a.log2 * 2 ^ (b.log2 + 1 - a.log2) := by
        rw [← Nat.pow_add]; congr 1; omega
      have key : 2 ^ (b.log2 + 1) ≤ a * 2 ^ (b.log2 + 1 - a.log2) := by
        rw [hsplit]
        exact Nat.mul_le_mul_right _ ha_log
      omega

/-- Upper bound on `findBinaryExp`: `a < b · 2^{e+1}` in the sign-split
cleared form. -/
theorem findBinaryExp_lt (a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    let e := findBinaryExp a b
    if e + 1 ≥ 0 then a < b * 2 ^ (e + 1).toNat
    else a * 2 ^ (-(e + 1)).toNat < b := by
  simp only
  have h_or : findBinaryExp a b = ((Nat.log2 a : Int) - Nat.log2 b) ∨
              findBinaryExp a b = ((Nat.log2 a : Int) - Nat.log2 b) - 1 :=
    findBinaryExp_eq_or a b
  have ha_log : 2 ^ a.log2 ≤ a := Nat.log2_self_le (by omega)
  have ha_log' : a < 2 ^ (a.log2 + 1) := Nat.lt_log2_self
  have hb_log : 2 ^ b.log2 ≤ b := Nat.log2_self_le (by omega)
  rcases h_or with h_e0 | h_e0
  · rw [h_e0]
    by_cases hsign : ((Nat.log2 a : Int) - Nat.log2 b + 1) ≥ 0
    · rw [if_pos hsign]
      have h_ab : a.log2 + 1 ≥ b.log2 := by
        have : (a.log2 : Int) + 1 ≥ b.log2 := by omega
        omega
      have h_pow : ((Nat.log2 a : Int) - Nat.log2 b + 1).toNat = a.log2 + 1 - b.log2 := by
        have : ((Nat.log2 a : Int) - Nat.log2 b + 1) = ((a.log2 + 1 - b.log2 : Nat) : Int) := by
          omega
        rw [this]; exact Int.toNat_natCast _
      rw [h_pow]
      have hsplit : 2 ^ (a.log2 + 1) = 2 ^ b.log2 * 2 ^ (a.log2 + 1 - b.log2) := by
        rw [← Nat.pow_add]; congr 1; omega
      have h1 : a < 2 ^ b.log2 * 2 ^ (a.log2 + 1 - b.log2) := by rw [← hsplit]; exact ha_log'
      have h2 : 2 ^ b.log2 * 2 ^ (a.log2 + 1 - b.log2) ≤ b * 2 ^ (a.log2 + 1 - b.log2) :=
        Nat.mul_le_mul_right _ hb_log
      omega
    · rw [if_neg hsign]
      have h_ba : b.log2 ≥ a.log2 + 2 := by
        have : (b.log2 : Int) ≥ a.log2 + 2 := by omega
        omega
      have h_pow : (-((Nat.log2 a : Int) - Nat.log2 b + 1)).toNat = b.log2 - a.log2 - 1 := by
        have : -((Nat.log2 a : Int) - Nat.log2 b + 1)
                  = ((b.log2 - a.log2 - 1 : Nat) : Int) := by
          omega
        rw [this]; exact Int.toNat_natCast _
      rw [h_pow]
      have hsplit : 2 ^ b.log2 = 2 ^ (a.log2 + 1) * 2 ^ (b.log2 - a.log2 - 1) := by
        rw [← Nat.pow_add]; congr 1; omega
      have h1 : a * 2 ^ (b.log2 - a.log2 - 1)
                  < 2 ^ (a.log2 + 1) * 2 ^ (b.log2 - a.log2 - 1) :=
        (Nat.mul_lt_mul_right (Nat.pow_pos (by omega : 0 < (2 : Nat)))).mpr ha_log'
      have h2 : 2 ^ (a.log2 + 1) * 2 ^ (b.log2 - a.log2 - 1) = 2 ^ b.log2 := hsplit.symm
      omega
  · rw [h_e0]
    have h_false : leBy2e a b ((Nat.log2 a : Int) - Nat.log2 b) = false := by
      cases h_val : leBy2e a b ((Nat.log2 a : Int) - Nat.log2 b) with
      | false => rfl
      | true =>
        exfalso
        unfold findBinaryExp at h_e0
        rw [if_pos h_val] at h_e0
        omega
    rw [show ((Nat.log2 a : Int) - Nat.log2 b - 1 + 1)
            = ((Nat.log2 a : Int) - Nat.log2 b) from by omega]
    have h_false' : ¬ (leBy2e a b ((Nat.log2 a : Int) - Nat.log2 b) = true) := by
      rw [h_false]; decide
    rw [leBy2e_eq_true_iff] at h_false'
    by_cases he0 : ((Nat.log2 a : Int) - Nat.log2 b) ≥ 0
    · rw [if_pos he0]
      rw [if_pos he0] at h_false'
      omega
    · rw [if_neg he0]
      rw [if_neg he0] at h_false'
      omega

/-! ## Scaled cleared-form bounds (no-carry case) -/

/-- In the no-carry case, `2^52 · denom ≤ num`. -/
theorem clinger_num_ge_2pow52_denom (a b : Nat) (e : Int)
    (_ha : 0 < a) (_hb : 0 < b) (he : leBy2e a b e = true) :
    let (num, denom) := scaleByPow2 a b (52 - e)
    2 ^ 52 * denom ≤ num := by
  simp only
  rw [scaleByPow2_num_eq, scaleByPow2_denom_eq]
  rw [leBy2e_eq_true_iff] at he
  by_cases hk : 52 - e ≥ 0
  · rw [if_pos hk, if_pos hk]
    by_cases he_nn : e ≥ 0
    · rw [if_pos he_nn] at he
      have he_le_52 : e ≤ 52 := by omega
      have he_sum : e.toNat + (52 - e).toNat = 52 := by
        have h1 : e.toNat = e := Int.toNat_of_nonneg he_nn
        have h2 : (52 - e).toNat = 52 - e := by rw [Int.toNat_of_nonneg hk]
        rw [← h1] at he_le_52; omega
      have hsplit : (2 : Nat) ^ 52 = 2 ^ e.toNat * 2 ^ (52 - e).toNat := by
        rw [← Nat.pow_add, he_sum]
      rw [hsplit]
      have heq : (2 : Nat) ^ e.toNat * 2 ^ (52 - e).toNat * b
                  = b * 2 ^ e.toNat * 2 ^ (52 - e).toNat := by grind
      rw [heq]
      exact Nat.mul_le_mul_right _ he
    · rw [if_neg he_nn] at he
      have he_neg : e < 0 := by omega
      have h_52e : (52 - e).toNat = 52 + (-e).toNat := by
        have h1 : ((52 - e).toNat : Int) = 52 - e := Int.toNat_of_nonneg hk
        have h2 : ((-e).toNat : Int) = -e := Int.toNat_of_nonneg (by omega)
        have : ((52 - e).toNat : Int) = ((52 + (-e).toNat : Nat) : Int) := by
          push_cast [h2]; omega
        exact_mod_cast this
      rw [h_52e, Nat.pow_add]
      have h_le_mul : (2 : Nat) ^ 52 * b ≤ 2 ^ 52 * (a * 2 ^ (-e).toNat) :=
        Nat.mul_le_mul_left _ he
      rw [show a * (2 ^ 52 * 2 ^ (-e).toNat) = 2 ^ 52 * (a * 2 ^ (-e).toNat) by grind]
      exact h_le_mul
  · rw [if_neg hk, if_neg hk]
    have he_gt_52 : e > 52 := by omega
    have he_ge_0 : e ≥ 0 := by omega
    rw [if_pos he_ge_0] at he
    have h_e52 : (-(52 - e)).toNat + 52 = e.toNat := by
      have h1 : ((-(52 - e)).toNat : Int) = -(52 - e) := Int.toNat_of_nonneg (by omega)
      have h2 : (e.toNat : Int) = e := Int.toNat_of_nonneg he_ge_0
      have : ((-(52 - e)).toNat + 52 : Nat) = e.toNat := by
        have hcast : (((-(52 - e)).toNat + 52 : Nat) : Int) = (e.toNat : Int) := by
          push_cast [h1, h2]; omega
        exact_mod_cast hcast
      exact this
    rw [show (2 ^ 52) * (b * 2 ^ (-(52 - e)).toNat) = b * 2 ^ ((-(52 - e)).toNat + 52) by
      rw [Nat.pow_add, Nat.mul_left_comm, Nat.mul_comm (2 ^ 52)]]
    rw [h_e52]; exact he

/-- In the carry case, `num < 2^53 · denom`. -/
theorem clinger_num_lt_2pow53_denom (a b : Nat) (e : Int)
    (ha : 0 < a) (hb : 0 < b) (he_eq : e = findBinaryExp a b) :
    let (num, denom) := scaleByPow2 a b (52 - e)
    num < 2 ^ 53 * denom := by
  simp only
  rw [scaleByPow2_num_eq, scaleByPow2_denom_eq]
  have hupper := findBinaryExp_lt a b ha hb
  simp only at hupper
  rw [← he_eq] at hupper
  by_cases hk : 52 - e ≥ 0
  · rw [if_pos hk, if_pos hk]
    by_cases he1 : e + 1 ≥ 0
    · rw [if_pos he1] at hupper
      have h1 : a < b * 2 ^ (e + 1).toNat := hupper
      have h_sum : (e + 1).toNat + (52 - e).toNat = 53 := by
        have h2 : ((e + 1).toNat : Int) = e + 1 := Int.toNat_of_nonneg he1
        have h3 : ((52 - e).toNat : Int) = 52 - e := Int.toNat_of_nonneg hk
        have hcast : (((e + 1).toNat + (52 - e).toNat : Nat) : Int) = ((53 : Nat) : Int) := by
          push_cast; omega
        exact_mod_cast hcast
      have hsplit : (2 : Nat) ^ 53 = 2 ^ (e + 1).toNat * 2 ^ (52 - e).toNat := by
        rw [← Nat.pow_add, h_sum]
      have h2 : a * 2 ^ (52 - e).toNat < b * 2 ^ (e + 1).toNat * 2 ^ (52 - e).toNat :=
        (Nat.mul_lt_mul_right (Nat.pow_pos (by omega : 0 < (2 : Nat)))).mpr h1
      have h3 : b * 2 ^ (e + 1).toNat * 2 ^ (52 - e).toNat = 2 ^ 53 * b := by
        rw [Nat.mul_assoc, ← hsplit]
        exact Nat.mul_comm _ _
      omega
    · rw [if_neg he1] at hupper
      have h1 : a * 2 ^ (-(e + 1)).toNat < b := hupper
      have h_neg_pos : -(e + 1) ≥ 0 := by omega
      have h_sum : (-(e + 1)).toNat + 53 = (52 - e).toNat := by
        have h2 : ((-(e + 1)).toNat : Int) = -(e + 1) := Int.toNat_of_nonneg h_neg_pos
        have h3 : ((52 - e).toNat : Int) = 52 - e := Int.toNat_of_nonneg hk
        have hcast : (((-(e + 1)).toNat + 53 : Nat) : Int) = (((52 - e).toNat : Nat) : Int) := by
          push_cast; omega
        exact_mod_cast hcast
      have hsplit : (2 : Nat) ^ (52 - e).toNat = 2 ^ (-(e + 1)).toNat * 2 ^ 53 := by
        rw [← Nat.pow_add, h_sum]
      rw [hsplit]
      rw [show a * (2 ^ (-(e + 1)).toNat * 2 ^ 53)
            = (a * 2 ^ (-(e + 1)).toNat) * 2 ^ 53 by grind]
      have h2 : (a * 2 ^ (-(e + 1)).toNat) * 2 ^ 53 < b * 2 ^ 53 :=
        (Nat.mul_lt_mul_right (Nat.pow_pos (by omega : 0 < (2 : Nat)))).mpr h1
      omega
  · rw [if_neg hk, if_neg hk]
    have he_ge_53 : e ≥ 53 := by omega
    have he1 : e + 1 ≥ 0 := by omega
    rw [if_pos he1] at hupper
    have h1 : a < b * 2 ^ (e + 1).toNat := hupper
    have h_neg_pos : -(52 - e) ≥ 0 := by omega
    have h_sum : 53 + (-(52 - e)).toNat = (e + 1).toNat := by
      have h2 : ((-(52 - e)).toNat : Int) = -(52 - e) := Int.toNat_of_nonneg h_neg_pos
      have h3 : ((e + 1).toNat : Int) = e + 1 := Int.toNat_of_nonneg (by omega : (0 : Int) ≤ e + 1)
      have hcast : ((53 + (-(52 - e)).toNat : Nat) : Int) = (((e + 1).toNat : Nat) : Int) := by
        push_cast; omega
      exact_mod_cast hcast
    have hsplit : (2 : Nat) ^ (e + 1).toNat = 2 ^ 53 * 2 ^ (-(52 - e)).toNat := by
      rw [← Nat.pow_add, h_sum]
    have h2 : a < b * (2 ^ 53 * 2 ^ (-(52 - e)).toNat) := by rw [← hsplit]; exact h1
    have h3 : b * (2 ^ 53 * 2 ^ (-(52 - e)).toNat) = 2 ^ 53 * (b * 2 ^ (-(52 - e)).toNat) := by
      rw [Nat.mul_left_comm]
    omega

/-! ## Algebraic identity for scale-shifting (carry case) -/

/-- `twoNegPow (q-1) · twoPosPow q = 2 · twoNegPow q · twoPosPow (q-1)`. -/
private theorem twoNegPow_pred_mul_twoPosPow (q : Int) :
    twoNegPow (q - 1) * twoPosPow q = 2 * twoNegPow q * twoPosPow (q - 1) := by
  unfold twoNegPow twoPosPow
  by_cases hq : q ≥ 1
  · have h1 : ¬ (q - 1 < 0) := by omega
    have h2 : ¬ (q < 0) := by omega
    have h3 : q ≥ 0 := by omega
    have h4 : q - 1 ≥ 0 := by omega
    rw [if_neg h1, if_neg h2, if_pos h3, if_pos h4]
    have hq_succ : q.toNat = (q - 1).toNat + 1 := by
      have h2 : ((q - 1).toNat : Int) = q - 1 := Int.toNat_of_nonneg h4
      have h3' : (q.toNat : Int) = q := Int.toNat_of_nonneg h3
      have hcast : (q.toNat : Int) = (((q - 1).toNat + 1 : Nat) : Int) := by
        push_cast; omega
      exact_mod_cast hcast
    rw [hq_succ, Nat.pow_succ]
    show 1 * (2 ^ ((q - 1).toNat) * 2) = 2 * 1 * 2 ^ (q - 1).toNat
    omega
  · by_cases hq0 : q = 0
    · subst hq0; decide
    · have hq_lt : q < 1 := by omega
      have hqn : q < 0 := by omega
      have hq1n : q - 1 < 0 := by omega
      have hqn' : ¬ (q ≥ 0) := by omega
      have hq1n' : ¬ (q - 1 ≥ 0) := by omega
      rw [if_pos hqn, if_pos hq1n, if_neg hqn', if_neg hq1n']
      have h_neg_q_pos : (-q) ≥ 0 := by omega
      have h_neg_q1_pos : -(q - 1) ≥ 0 := by omega
      have hq_succ : (-(q - 1)).toNat = (-q).toNat + 1 := by
        have h2 : ((-q).toNat : Int) = -q := Int.toNat_of_nonneg h_neg_q_pos
        have h3' : ((-(q - 1)).toNat : Int) = -(q - 1) := Int.toNat_of_nonneg h_neg_q1_pos
        have hcast : ((-(q - 1)).toNat : Int) = (((-q).toNat + 1 : Nat) : Int) := by
          push_cast; omega
        exact_mod_cast hcast
      rw [hq_succ, Nat.pow_succ]
      show 2 ^ ((-q).toNat) * 2 * 1 = 2 * 2 ^ (-q).toNat * 1
      omega

/-- `num_pre · denom = 2 · num · denom_pre` where the *_pre forms are at
scale `q - 1` and the others at scale `q`. -/
theorem num_pre_denom_eq (sig : Nat) (exp q : Int) :
    (sig * tenPosPow exp * twoNegPow (q - 1) : Int) * (tenNegPow exp * twoPosPow q)
      = 2 * (sig * tenPosPow exp * twoNegPow q : Int)
            * (tenNegPow exp * twoPosPow (q - 1)) := by
  have h_id : (twoNegPow (q - 1) : Int) * (twoPosPow q : Int)
            = 2 * (twoNegPow q : Int) * (twoPosPow (q - 1) : Int) := by
    exact_mod_cast twoNegPow_pred_mul_twoPosPow q
  calc (sig * tenPosPow exp * twoNegPow (q - 1) : Int) * (tenNegPow exp * twoPosPow q)
      = (sig : Int) * tenPosPow exp * tenNegPow exp
          * ((twoNegPow (q - 1) : Int) * twoPosPow q) := by grind
    _ = (sig : Int) * tenPosPow exp * tenNegPow exp
          * (2 * twoNegPow q * twoPosPow (q - 1)) := by rw [h_id]
    _ = 2 * (sig * tenPosPow exp * twoNegPow q : Int)
            * (tenNegPow exp * twoPosPow (q - 1)) := by grind

end Srtfp.Clinger

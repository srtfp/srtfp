/- Bridge theorems: `shortestUnsigned_u64_opt m q = some v → shortestUnsigned_packed m q = v`.

   This file lifts the cmpScaledMixed-level bridge
   (`cmpScaledMixed_packed_eq_u64_branch`) through
   `inRoundingInterval`, `pickNearer`, and finally `shortestUnsigned`,
   yielding `shortestUnsigned_v2 = shortestUnsigned_packed`.

   Once that holds we can re-target the `@[csimp]` registration
   from `shortestUnsigned_packed` to `shortestUnsigned_v2`, giving
   the runtime path the ~2× speedup measured at the v2 level. -/
import Srtfp.Numeric.Schubfach
import Srtfp.Numeric.Schubfach.Perf.Orchestration
import Srtfp.Numeric.Schubfach.Perf.Uint64Kernel

namespace PP.Numeric.Schubfach

/-! ## UInt64 arithmetic identities under size bounds

For inputs `m, s` arising from a binary64 `Float`, we have
`m ≤ 2^53` and `s < 10^17 < 2^57`.  The kernel does `mU <<< 2`,
`sU <<< 2`, `mU <<< 1`, `(sU <<< 1) + 1`, and subtractions/additions
of small constants.  All of these are overflow-free under those bounds. -/

/-- `x <<< 2 = 4 * x` as UInt64 (always — wraparound matches both sides). -/
lemma uint64_shiftLeft_2 (x : UInt64) : x <<< 2 = 4 * x := by
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_shiftLeft, UInt64.toNat_mul]
  have h2 : ((2 : UInt64).toNat % 64) = 2 := by decide
  have h4 : ((4 : UInt64).toNat) = 4 := by decide
  rw [h2, h4]
  simp [Nat.shiftLeft_eq, Nat.mul_comm]

/-- `x <<< 1 = 2 * x` as UInt64. -/
lemma uint64_shiftLeft_1 (x : UInt64) : x <<< 1 = 2 * x := by
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_shiftLeft, UInt64.toNat_mul]
  have h1 : ((1 : UInt64).toNat % 64) = 1 := by decide
  have h2 : ((2 : UInt64).toNat) = 2 := by decide
  rw [h1, h2]
  simp [Nat.shiftLeft_eq, Nat.mul_comm]

/-- For `m < 2^64`, `(UInt64.ofNat m).toNat = m`. -/
lemma toNat_ofNat_of_lt {m : Nat} (h : m < (1 <<< 64 : Nat)) :
    (UInt64.ofNat m).toNat = m := by
  rw [UInt64.toNat_ofNat']
  apply Nat.mod_eq_of_lt
  show m < 2 ^ 64
  have : (1 <<< 64 : Nat) = 2 ^ 64 := by decide
  omega

/-- `UInt64.ofNat (4 * m) = UInt64.ofNat m <<< 2` (unconditionally). -/
private lemma ofNat_4_mul_eq_shiftLeft_2 (m : Nat) :
    UInt64.ofNat (4 * m) = (UInt64.ofNat m) <<< 2 := by
  rw [uint64_shiftLeft_2, UInt64.ofNat_mul]
  rfl

/-- `UInt64.ofNat (2 * m) = UInt64.ofNat m <<< 1` (unconditionally). -/
private lemma ofNat_2_mul_eq_shiftLeft_1 (m : Nat) :
    UInt64.ofNat (2 * m) = (UInt64.ofNat m) <<< 1 := by
  rw [uint64_shiftLeft_1, UInt64.ofNat_mul]
  rfl

/-- For `m ≥ 1`, `(4·m - 2 : Int).toNat = 4*m - 2`. -/
lemma toNat_4m_sub_2_eq {m : Nat} (hm_pos : m ≥ 1) :
    (4 * (m : Int) - 2).toNat = 4 * m - 2 := by
  omega

/-- For `m ≥ 1`, `(4·m - 1 : Int).toNat = 4*m - 1`. -/
lemma toNat_4m_sub_1_eq {m : Nat} (hm_pos : m ≥ 1) :
    (4 * (m : Int) - 1).toNat = 4 * m - 1 := by
  omega

/-- `(4·m + 2 : Int).toNat = 4*m + 2`. -/
lemma toNat_4m_add_2_eq (m : Nat) : (4 * (m : Int) + 2).toNat = 4 * m + 2 := by
  omega

/-- `(4·s : Int).toNat = 4*s`. -/
lemma toNat_4s_eq (s : Nat) : (4 * (s : Int)).toNat = 4 * s := by omega

/-- `(2·m : Int).toNat = 2*m`. -/
lemma toNat_2m_eq (m : Nat) : (2 * (m : Int)).toNat = 2 * m := by omega

/-- `(2·s + 1 : Int).toNat = 2*s + 1`. -/
lemma toNat_2s_add_1_eq (s : Nat) : (2 * (s : Int) + 1).toNat = 2 * s + 1 := by omega

/-! ## UInt64-Int correspondence lemmas

These show that the `Int → UInt64` boundary conversions used by
`cmpScaledMixed_packed_eq_u64_branch` reduce to the shift/multiply
expressions used by `inRoundingInterval_u64_opt` and friends. -/

/-- `UInt64.ofNat (4m - 2) = (UInt64.ofNat m) <<< 2 - 2` when `m ≥ 1`. -/
lemma ofNat_4m_sub_2 {m : Nat} (hm_pos : m ≥ 1) :
    UInt64.ofNat (4 * m - 2) = (UInt64.ofNat m) <<< 2 - 2 := by
  rw [uint64_shiftLeft_2]
  have h1 : 4 * m = (4 * m - 2) + 2 := by omega
  have h2 : UInt64.ofNat (4 * m) = UInt64.ofNat (4 * m - 2) + UInt64.ofNat 2 := by
    conv_lhs => rw [h1]
    rw [UInt64.ofNat_add]
  rw [UInt64.ofNat_mul] at h2
  have h3 : (UInt64.ofNat 4 : UInt64) = 4 := rfl
  have h4 : (UInt64.ofNat 2 : UInt64) = 2 := rfl
  rw [h3, h4] at h2
  -- h2 : 4 * UInt64.ofNat m = UInt64.ofNat (4 * m - 2) + 2
  -- Goal: UInt64.ofNat (4 * m - 2) = 4 * UInt64.ofNat m - 2
  rw [h2]
  -- Goal: UInt64.ofNat (4 * m - 2) = UInt64.ofNat (4 * m - 2) + 2 - 2
  -- Use BitVec underlying ring structure: (x + 2) - 2 = x.
  apply UInt64.toBitVec_inj.mp
  simp []

/-- `UInt64.ofNat (4m - 1) = (UInt64.ofNat m) <<< 2 - 1` when `m ≥ 1`. -/
lemma ofNat_4m_sub_1 {m : Nat} (hm_pos : m ≥ 1) :
    UInt64.ofNat (4 * m - 1) = (UInt64.ofNat m) <<< 2 - 1 := by
  rw [uint64_shiftLeft_2]
  have h1 : 4 * m = (4 * m - 1) + 1 := by omega
  have h2 : UInt64.ofNat (4 * m) = UInt64.ofNat (4 * m - 1) + UInt64.ofNat 1 := by
    conv_lhs => rw [h1]
    rw [UInt64.ofNat_add]
  rw [UInt64.ofNat_mul] at h2
  have h3 : (UInt64.ofNat 4 : UInt64) = 4 := rfl
  have h4 : (UInt64.ofNat 1 : UInt64) = 1 := rfl
  rw [h3, h4] at h2
  rw [h2]
  apply UInt64.toBitVec_inj.mp
  simp []

/-- `UInt64.ofNat (4m + 2) = (UInt64.ofNat m) <<< 2 + 2`. -/
lemma ofNat_4m_add_2 (m : Nat) :
    UInt64.ofNat (4 * m + 2) = (UInt64.ofNat m) <<< 2 + 2 := by
  rw [uint64_shiftLeft_2]
  rw [UInt64.ofNat_add, UInt64.ofNat_mul]
  rfl

/-- `UInt64.ofNat (4s) = (UInt64.ofNat s) <<< 2`. -/
lemma ofNat_4s (s : Nat) :
    UInt64.ofNat (4 * s) = (UInt64.ofNat s) <<< 2 := by
  rw [uint64_shiftLeft_2, UInt64.ofNat_mul]
  rfl

/-- `UInt64.ofNat (2m) = (UInt64.ofNat m) <<< 1`. -/
lemma ofNat_2m (m : Nat) :
    UInt64.ofNat (2 * m) = (UInt64.ofNat m) <<< 1 := by
  rw [uint64_shiftLeft_1, UInt64.ofNat_mul]
  rfl

/-- `UInt64.ofNat (2s + 1) = (UInt64.ofNat s) <<< 1 + 1`. -/
lemma ofNat_2s_add_1 (s : Nat) :
    UInt64.ofNat (2 * s + 1) = (UInt64.ofNat s) <<< 1 + 1 := by
  rw [uint64_shiftLeft_1, UInt64.ofNat_add, UInt64.ofNat_mul]
  rfl

/-! ## cmpScaledMixed strict-verdict corollary

When the UInt64 kernel produces a strict (nonzero) verdict, the packed
spec kernel agrees with it.  This is the direct consequence of
`cmpScaledMixed_packed_eq_u64_branch`. -/

/-- Strict-verdict version: when the UInt64 kernel returns a nonzero value,
    `cmpScaledMixed_packed` agrees with it.  Stated under the same
    preconditions as `cmpScaledMixed_packed_eq_u64_branch`. -/
theorem cmpScaledMixed_packed_eq_u64_of_strict
    (q k : Int) (gHi gLo : UInt64) (qPlusH : Int)
    (a b : Int)
    (ha_nn : 0 ≤ a) (hb_nn : 0 ≤ b)
    (hb_pos : b ≠ 0)
    (ha_lt : a < (1 <<< 60 : Int)) (hb_lt : b < (1 <<< 60 : Int))
    (hk_lo : pow10Table128_kMin ≤ k) (hk_hi : k ≤ pow10Table128_kMax)
    (hqh_lo : 64 ≤ qPlusH) (hqh_hi : qPlusH ≤ 132)
    (hstrict : cmpScaledMixed_u64 gHi gLo (UInt64.ofNat qPlusH.toNat)
                  (UInt64.ofNat a.toNat) (UInt64.ofNat b.toNat) ≠ 0) :
    cmpScaledMixed_packed q k gHi gLo qPlusH a b =
      cmpScaledMixed_u64 gHi gLo (UInt64.ofNat qPlusH.toNat)
        (UInt64.ofNat a.toNat) (UInt64.ofNat b.toNat) := by
  rw [cmpScaledMixed_packed_eq_u64_branch _ _ _ _ _ _ _ ha_nn hb_nn hb_pos
        ha_lt hb_lt hk_lo hk_hi hqh_lo hqh_hi]
  simp only [if_neg hstrict]

/-! ## inRoundingInterval bridge

When `inRoundingInterval_u64_opt` returns `some v`, both inner cmps gave
strict verdicts, so `inRoundingInterval_packed` returns the same `v`. -/

/-- The fast-path correctness for `inRoundingInterval`.  Preconditions:
    `s, m < 2^58` (so `4m + 2`, `4s` fit in UInt64 without overflow), and
    `m ≥ 1`, `s ≥ 1` (so `4m - 2 ≥ 0` and `4s ≠ 0`), and the usual
    `cmpScaledMixed_packed` preconditions (`qPlusH ∈ [64, 132]`,
    `k ∈ pow10Table128 range`). -/
theorem inRoundingInterval_u64_opt_some_eq_packed
    (q k : Int) (gHi gLo : UInt64) (qPlusH : Int)
    (s m : Nat) (irregular : Bool) (v : Bool)
    (hm_pos : m ≥ 1) (hs_pos : s ≥ 1)
    (hm_lt : m < (1 <<< 58 : Nat))
    (hs_lt : s < (1 <<< 58 : Nat))
    (hk_lo : pow10Table128_kMin ≤ k) (hk_hi : k ≤ pow10Table128_kMax)
    (hqh_lo : 64 ≤ qPlusH) (hqh_hi : qPlusH ≤ 132)
    (hopt : inRoundingInterval_u64_opt gHi gLo
              (UInt64.ofNat qPlusH.toNat) (UInt64.ofNat s) (UInt64.ofNat m) irregular
            = some v) :
    inRoundingInterval_packed q k gHi gLo qPlusH s m irregular = v := by
  -- Unfold _u64_opt to extract the cmp values and the fact that they're strict.
  unfold inRoundingInterval_u64_opt at hopt
  -- The leftU and rightU constructions in _u64_opt use shifts:
  --   m4 = mU <<< 2;  leftU = m4 - 2 (or m4 - 1);  rightU = m4 + 2;  s4U = sU <<< 2.
  -- For the packed side, leftN, rightN, s4 are Int versions:
  --   leftN = 4m - 2 (or 4m - 1);  rightN = 4m + 2;  s4 = 4s.
  set mU : UInt64 := UInt64.ofNat m with hmU_def
  set sU : UInt64 := UInt64.ofNat s with hsU_def
  set qPlusH8 : UInt64 := UInt64.ofNat qPlusH.toNat with hqPlusH8_def
  -- Establish the UInt64-vs-Int-leftU/rightU/s4U correspondences.
  -- We need: UInt64.ofNat (leftN.toNat) = leftU; same for rightN, s4.
  have hleftU_corr_reg : UInt64.ofNat ((4 * (m : Int) - 2).toNat) = mU <<< 2 - 2 := by
    rw [toNat_4m_sub_2_eq hm_pos]
    exact ofNat_4m_sub_2 hm_pos
  have hleftU_corr_irr : UInt64.ofNat ((4 * (m : Int) - 1).toNat) = mU <<< 2 - 1 := by
    rw [toNat_4m_sub_1_eq hm_pos]
    exact ofNat_4m_sub_1 hm_pos
  have hrightU_corr : UInt64.ofNat ((4 * (m : Int) + 2).toNat) = mU <<< 2 + 2 := by
    rw [toNat_4m_add_2_eq m]
    exact ofNat_4m_add_2 m
  have hs4U_corr : UInt64.ofNat ((4 * (s : Int)).toNat) = sU <<< 2 := by
    rw [toNat_4s_eq s]
    exact ofNat_4s s
  -- Size bounds for cmpScaledMixed_packed preconditions:
  -- 4m - 2 ≥ 0 (since m ≥ 1), 4m + 2 < 2^60, 4s < 2^60, 4s ≠ 0.
  have hm_lt60 : 4 * m + 2 < (1 <<< 60 : Nat) := by
    have : 4 * m < 4 * (1 <<< 58) := by omega
    have : 4 * (1 <<< 58) = (1 <<< 60 : Nat) := by decide
    omega
  have hs_lt60 : 4 * s < (1 <<< 60 : Nat) := by
    have : 4 * s < 4 * (1 <<< 58) := by omega
    have : 4 * (1 <<< 58) = (1 <<< 60 : Nat) := by decide
    omega
  -- Packed leftN/rightN/s4 facts.
  have hleftN_nn_reg : (0 : Int) ≤ 4 * (m : Int) - 2 := by
    have : (1 : Int) ≤ (m : Int) := by exact_mod_cast hm_pos
    linarith
  have hleftN_nn_irr : (0 : Int) ≤ 4 * (m : Int) - 1 := by
    have : (1 : Int) ≤ (m : Int) := by exact_mod_cast hm_pos
    linarith
  have hrightN_nn : (0 : Int) ≤ 4 * (m : Int) + 2 := by positivity
  have hs4_nn : (0 : Int) ≤ 4 * (s : Int) := by positivity
  have hs4_pos : 4 * (s : Int) ≠ 0 := by
    have : (1 : Int) ≤ (s : Int) := by exact_mod_cast hs_pos
    omega
  -- Bound 4m and 4s against 2^60 using the explicit Nat→Int coercion.
  have hm_lt' : (m : Int) < 288230376151711744 := by
    have : (m : Int) < ((1 <<< 58 : Nat) : Int) := by exact_mod_cast hm_lt
    have heq : ((1 <<< 58 : Nat) : Int) = 288230376151711744 := by decide
    omega
  have hs_lt' : (s : Int) < 288230376151711744 := by
    have : (s : Int) < ((1 <<< 58 : Nat) : Int) := by exact_mod_cast hs_lt
    have heq : ((1 <<< 58 : Nat) : Int) = 288230376151711744 := by decide
    omega
  have h60_lit : (1 <<< 60 : Int) = 1152921504606846976 := by decide
  have hleftN_lt_reg : 4 * (m : Int) - 2 < (1 <<< 60 : Int) := by rw [h60_lit]; omega
  have hleftN_lt_irr : 4 * (m : Int) - 1 < (1 <<< 60 : Int) := by rw [h60_lit]; omega
  have hrightN_lt : 4 * (m : Int) + 2 < (1 <<< 60 : Int) := by rw [h60_lit]; omega
  have hs4_lt : 4 * (s : Int) < (1 <<< 60 : Int) := by rw [h60_lit]; omega
  -- Split on irregular up front to avoid `if` headache.
  unfold inRoundingInterval_packed
  by_cases hirr : irregular = true
  · -- Irregular case: leftN = 4m - 1, leftU = mU <<< 2 - 1.
    simp only [hirr, if_true] at hopt
    -- Now extract the two strict cmps from hopt.
    by_cases hcmpL_zero : cmpScaledMixed_u64 gHi gLo qPlusH8 (mU <<< 2 - 1) (sU <<< 2) = 0
    · simp [hcmpL_zero] at hopt
    by_cases hcmpR_zero : cmpScaledMixed_u64 gHi gLo qPlusH8 (mU <<< 2 + 2) (sU <<< 2) = 0
    · simp [hcmpL_zero, hcmpR_zero] at hopt
    have hL_ne : cmpScaledMixed_u64 gHi gLo qPlusH8 (mU <<< 2 - 1) (sU <<< 2) ≠ 0 := hcmpL_zero
    have hR_ne : cmpScaledMixed_u64 gHi gLo qPlusH8 (mU <<< 2 + 2) (sU <<< 2) ≠ 0 := hcmpR_zero
    -- hopt now: some ((cmpL < 0) && (0 < cmpR)) = some v
    have hopt' : v = (decide (cmpScaledMixed_u64 gHi gLo qPlusH8 (mU <<< 2 - 1) (sU <<< 2) < 0) &&
        decide (0 < cmpScaledMixed_u64 gHi gLo qPlusH8 (mU <<< 2 + 2) (sU <<< 2))) := by
      simp [hcmpL_zero, hcmpR_zero] at hopt
      exact hopt.symm
    -- Bridge the two packed cmps to the u64 cmps.
    have hcmpL_eq : cmpScaledMixed_packed q k gHi gLo qPlusH (4 * (m : Int) - 1) (4 * (s : Int))
                  = cmpScaledMixed_u64 gHi gLo qPlusH8 (mU <<< 2 - 1) (sU <<< 2) := by
      have hu64_eq : UInt64.ofNat (4 * (m : Int) - 1).toNat = mU <<< 2 - 1 := hleftU_corr_irr
      have hu64s_eq : UInt64.ofNat (4 * (s : Int)).toNat = sU <<< 2 := hs4U_corr
      have hstrict : cmpScaledMixed_u64 gHi gLo (UInt64.ofNat qPlusH.toNat)
          (UInt64.ofNat (4 * (m : Int) - 1).toNat)
          (UInt64.ofNat (4 * (s : Int)).toNat) ≠ 0 := by
        rw [hu64_eq, hu64s_eq]; exact hL_ne
      have := cmpScaledMixed_packed_eq_u64_of_strict q k gHi gLo qPlusH
        (4 * (m : Int) - 1) (4 * (s : Int))
        hleftN_nn_irr hs4_nn hs4_pos hleftN_lt_irr hs4_lt
        hk_lo hk_hi hqh_lo hqh_hi hstrict
      rw [this, hu64_eq, hu64s_eq]
    have hcmpR_eq : cmpScaledMixed_packed q k gHi gLo qPlusH (4 * (m : Int) + 2) (4 * (s : Int))
                  = cmpScaledMixed_u64 gHi gLo qPlusH8 (mU <<< 2 + 2) (sU <<< 2) := by
      have hu64_eq : UInt64.ofNat (4 * (m : Int) + 2).toNat = mU <<< 2 + 2 := hrightU_corr
      have hu64s_eq : UInt64.ofNat (4 * (s : Int)).toNat = sU <<< 2 := hs4U_corr
      have hstrict : cmpScaledMixed_u64 gHi gLo (UInt64.ofNat qPlusH.toNat)
          (UInt64.ofNat (4 * (m : Int) + 2).toNat)
          (UInt64.ofNat (4 * (s : Int)).toNat) ≠ 0 := by
        rw [hu64_eq, hu64s_eq]; exact hR_ne
      have := cmpScaledMixed_packed_eq_u64_of_strict q k gHi gLo qPlusH
        (4 * (m : Int) + 2) (4 * (s : Int))
        hrightN_nn hs4_nn hs4_pos hrightN_lt hs4_lt
        hk_lo hk_hi hqh_lo hqh_hi hstrict
      rw [this, hu64_eq, hu64s_eq]
    -- Now reduce the packed body.  irregular = true, leftN = 4m - 1.
    simp only [hirr, if_true]
    rw [hcmpL_eq, hcmpR_eq, hopt']
    simp [hL_ne, hR_ne]
  · -- Regular case: leftN = 4m - 2, leftU = mU <<< 2 - 2.
    have hirr' : irregular = false := by
      cases irregular <;> simp_all
    simp only [hirr'] at hopt
    by_cases hcmpL_zero : cmpScaledMixed_u64 gHi gLo qPlusH8 (mU <<< 2 - 2) (sU <<< 2) = 0
    · simp [hcmpL_zero] at hopt
    by_cases hcmpR_zero : cmpScaledMixed_u64 gHi gLo qPlusH8 (mU <<< 2 + 2) (sU <<< 2) = 0
    · simp [hcmpL_zero, hcmpR_zero] at hopt
    have hL_ne : cmpScaledMixed_u64 gHi gLo qPlusH8 (mU <<< 2 - 2) (sU <<< 2) ≠ 0 := hcmpL_zero
    have hR_ne : cmpScaledMixed_u64 gHi gLo qPlusH8 (mU <<< 2 + 2) (sU <<< 2) ≠ 0 := hcmpR_zero
    have hopt' : v = (decide (cmpScaledMixed_u64 gHi gLo qPlusH8 (mU <<< 2 - 2) (sU <<< 2) < 0) &&
        decide (0 < cmpScaledMixed_u64 gHi gLo qPlusH8 (mU <<< 2 + 2) (sU <<< 2))) := by
      simp [hcmpL_zero, hcmpR_zero] at hopt
      exact hopt.symm
    have hcmpL_eq : cmpScaledMixed_packed q k gHi gLo qPlusH (4 * (m : Int) - 2) (4 * (s : Int))
                  = cmpScaledMixed_u64 gHi gLo qPlusH8 (mU <<< 2 - 2) (sU <<< 2) := by
      have hu64_eq : UInt64.ofNat (4 * (m : Int) - 2).toNat = mU <<< 2 - 2 := hleftU_corr_reg
      have hu64s_eq : UInt64.ofNat (4 * (s : Int)).toNat = sU <<< 2 := hs4U_corr
      have hstrict : cmpScaledMixed_u64 gHi gLo (UInt64.ofNat qPlusH.toNat)
          (UInt64.ofNat (4 * (m : Int) - 2).toNat)
          (UInt64.ofNat (4 * (s : Int)).toNat) ≠ 0 := by
        rw [hu64_eq, hu64s_eq]; exact hL_ne
      have := cmpScaledMixed_packed_eq_u64_of_strict q k gHi gLo qPlusH
        (4 * (m : Int) - 2) (4 * (s : Int))
        hleftN_nn_reg hs4_nn hs4_pos hleftN_lt_reg hs4_lt
        hk_lo hk_hi hqh_lo hqh_hi hstrict
      rw [this, hu64_eq, hu64s_eq]
    have hcmpR_eq : cmpScaledMixed_packed q k gHi gLo qPlusH (4 * (m : Int) + 2) (4 * (s : Int))
                  = cmpScaledMixed_u64 gHi gLo qPlusH8 (mU <<< 2 + 2) (sU <<< 2) := by
      have hu64_eq : UInt64.ofNat (4 * (m : Int) + 2).toNat = mU <<< 2 + 2 := hrightU_corr
      have hu64s_eq : UInt64.ofNat (4 * (s : Int)).toNat = sU <<< 2 := hs4U_corr
      have hstrict : cmpScaledMixed_u64 gHi gLo (UInt64.ofNat qPlusH.toNat)
          (UInt64.ofNat (4 * (m : Int) + 2).toNat)
          (UInt64.ofNat (4 * (s : Int)).toNat) ≠ 0 := by
        rw [hu64_eq, hu64s_eq]; exact hR_ne
      have := cmpScaledMixed_packed_eq_u64_of_strict q k gHi gLo qPlusH
        (4 * (m : Int) + 2) (4 * (s : Int))
        hrightN_nn hs4_nn hs4_pos hrightN_lt hs4_lt
        hk_lo hk_hi hqh_lo hqh_hi hstrict
      rw [this, hu64_eq, hu64s_eq]
    simp only [hirr', Bool.false_eq_true, if_false]
    rw [hcmpL_eq, hcmpR_eq, hopt']
    simp [hL_ne, hR_ne]

/-! ## pickNearer bridge -/

/-- Helper: `UInt64.ofNat (s + 1) = UInt64.ofNat s + 1`. -/
lemma ofNat_succ (s : Nat) :
    UInt64.ofNat (s + 1) = UInt64.ofNat s + 1 := by
  rw [UInt64.ofNat_add]; rfl

/-- For `s < 2^58`, `(UInt64.ofNat s + 1).toNat = s + 1`. -/
lemma toNat_sU_add_1 {s : Nat} (hs_lt : s < (1 <<< 58 : Nat)) :
    (UInt64.ofNat s + 1).toNat = s + 1 := by
  rw [← ofNat_succ, UInt64.toNat_ofNat']
  apply Nat.mod_eq_of_lt
  have h64 : (1 <<< 58 : Nat) + 1 < (2 ^ 64 : Nat) := by decide
  omega

/-- `(UInt64.ofNat s).toNat = s` when `s < 2^64`. -/
lemma toNat_sU_eq {s : Nat} (hs_lt : s < (1 <<< 58 : Nat)) :
    (UInt64.ofNat s).toNat = s := by
  rw [UInt64.toNat_ofNat']
  apply Nat.mod_eq_of_lt
  have h64 : (1 <<< 58 : Nat) < (2 ^ 64 : Nat) := by decide
  omega

/-- pickNearer fast-path correctness.  Note `hs_lt` is one bit tighter than
    for `inRoundingInterval` because we evaluate `s + 1` inside. -/
theorem pickNearer_u64_opt_some_eq_packed
    (q k : Int) (gHi gLo : UInt64) (qPlusH : Int)
    (s m : Nat) (irregular : Bool) (chosen : UInt64)
    (hm_pos : m ≥ 1) (hs_pos : s ≥ 1)
    (hm_lt : m < (1 <<< 58 : Nat))
    (hs_lt : s < (1 <<< 57 : Nat))
    (hk_lo : pow10Table128_kMin ≤ k) (hk_hi : k ≤ pow10Table128_kMax)
    (hqh_lo : 64 ≤ qPlusH) (hqh_hi : qPlusH ≤ 132)
    (hirr_eq : irregular = isIrregular m q)
    (hopt : pickNearer_u64_opt gHi gLo
              (UInt64.ofNat qPlusH.toNat) (UInt64.ofNat s) (UInt64.ofNat m) irregular
            = some chosen) :
    pickNearer_packed q k gHi gLo qPlusH s m = chosen.toNat := by
  have hs_lt58 : s < (1 <<< 58 : Nat) := by
    have : (1 <<< 57 : Nat) ≤ (1 <<< 58 : Nat) := by decide
    omega
  -- Unfold pickNearer_u64_opt
  unfold pickNearer_u64_opt at hopt
  unfold pickNearer_packed
  rw [← hirr_eq]  -- align the `irregular` symbol
  -- Two inRoundingInterval_u64_packed_u8 calls (now u8 variant for perf).
  set qPlusH8 : UInt64 := UInt64.ofNat qPlusH.toNat with hqPlusH8_def
  set sU : UInt64 := UInt64.ofNat s with hsU_def
  set mU : UInt64 := UInt64.ofNat m with hmU_def
  -- Translate packed_u8 dispatch back to match-on-Option-Bool form.
  rw [inRoundingInterval_u64_packed_u8_eq, inRoundingInterval_u64_packed_u8_eq] at hopt
  -- Now we can match on inRoundingInterval_u64_opt as before.
  match h1 : inRoundingInterval_u64_opt gHi gLo qPlusH8 sU mU irregular with
  | none => simp [h1, inRoundingInterval_u8_AMBIG] at hopt
  | some uIn =>
    rw [h1] at hopt
    -- Match on the second
    -- For the second call, b = sU + 1.  Its UInt64 representation is UInt64.ofNat (s + 1).
    have hs1_eq : sU + 1 = UInt64.ofNat (s + 1) := by
      rw [hsU_def, ← ofNat_succ]
    -- Convert s+1 to UInt64.ofNat (s+1) in hopt.
    match h2 : inRoundingInterval_u64_opt gHi gLo qPlusH8 (sU + 1) mU irregular with
    | none => simp [h2] at hopt
    | some wIn =>
      rw [h2] at hopt
      -- Bridge the two inRoundingInterval calls.
      have h_uIn_pkd : inRoundingInterval_packed q k gHi gLo qPlusH s m irregular = uIn := by
        apply inRoundingInterval_u64_opt_some_eq_packed q k gHi gLo qPlusH s m irregular uIn
          hm_pos hs_pos hm_lt hs_lt58 hk_lo hk_hi hqh_lo hqh_hi
        rw [hsU_def, hmU_def, hqPlusH8_def] at h1
        exact h1
      have hs_plus_1_pos : s + 1 ≥ 1 := by omega
      have hs_plus_1_lt : s + 1 < (1 <<< 58 : Nat) := by
        have h57_58 : (1 <<< 57 : Nat) + 1 ≤ (1 <<< 58 : Nat) := by decide
        omega
      have h_wIn_pkd : inRoundingInterval_packed q k gHi gLo qPlusH (s + 1) m irregular = wIn := by
        apply inRoundingInterval_u64_opt_some_eq_packed q k gHi gLo qPlusH (s + 1) m irregular wIn
          hm_pos hs_plus_1_pos hm_lt hs_plus_1_lt hk_lo hk_hi hqh_lo hqh_hi
        rw [hs1_eq, hmU_def, hqPlusH8_def] at h2
        exact h2
      simp only [h_uIn_pkd, h_wIn_pkd]
      -- The cmp-branch needs cmpScaledMixed bridge.  Set it up once.
      have hcmp_pkd_eq : cmpScaledMixed_packed q k gHi gLo qPlusH (2 * (m : Int)) (2 * (s : Int) + 1)
                = cmpScaledMixed_u64 gHi gLo qPlusH8 (mU <<< 1) ((sU <<< 1) + 1)
                ∨ cmpScaledMixed_u64 gHi gLo qPlusH8 (mU <<< 1) ((sU <<< 1) + 1) = 0 := by
        by_cases hcmp_zero : cmpScaledMixed_u64 gHi gLo qPlusH8 (mU <<< 1) ((sU <<< 1) + 1) = 0
        · right; exact hcmp_zero
        left
        have h2m_corr : UInt64.ofNat (2 * (m : Int)).toNat = mU <<< 1 := by
          rw [toNat_2m_eq m]; exact ofNat_2m m
        have h2s1_corr : UInt64.ofNat (2 * (s : Int) + 1).toNat = (sU <<< 1) + 1 := by
          rw [toNat_2s_add_1_eq s]
          show UInt64.ofNat (2 * s + 1) = sU <<< 1 + 1
          rw [hsU_def, uint64_shiftLeft_1, UInt64.ofNat_add, UInt64.ofNat_mul]
          rfl
        have h2m_nn : (0 : Int) ≤ 2 * (m : Int) := by positivity
        have h2s1_nn : (0 : Int) ≤ 2 * (s : Int) + 1 := by
          have : (0 : Int) ≤ (s : Int) := Int.natCast_nonneg _
          linarith
        have h2s1_ne : 2 * (s : Int) + 1 ≠ 0 := by
          have : (0 : Int) ≤ (s : Int) := Int.natCast_nonneg _
          omega
        have h2m_lt : 2 * (m : Int) < (1 <<< 60 : Int) := by
          have hm_lt' : (m : Int) < ((1 <<< 58 : Nat) : Int) := by exact_mod_cast hm_lt
          have heq : ((1 <<< 58 : Nat) : Int) = 288230376151711744 := by decide
          have h60_lit : (1 <<< 60 : Int) = 1152921504606846976 := by decide
          omega
        have h2s1_lt : 2 * (s : Int) + 1 < (1 <<< 60 : Int) := by
          have hs_lt' : (s : Int) < ((1 <<< 57 : Nat) : Int) := by exact_mod_cast hs_lt
          have heq : ((1 <<< 57 : Nat) : Int) = 144115188075855872 := by decide
          have h60_lit : (1 <<< 60 : Int) = 1152921504606846976 := by decide
          omega
        have hstrict : cmpScaledMixed_u64 gHi gLo qPlusH8
            (UInt64.ofNat (2 * (m : Int)).toNat) (UInt64.ofNat (2 * (s : Int) + 1).toNat) ≠ 0 := by
          rw [h2m_corr, h2s1_corr]; exact hcmp_zero
        have hbridge := cmpScaledMixed_packed_eq_u64_of_strict q k gHi gLo qPlusH
          (2 * (m : Int)) (2 * (s : Int) + 1) h2m_nn h2s1_nn h2s1_ne h2m_lt h2s1_lt
          hk_lo hk_hi hqh_lo hqh_hi hstrict
        rw [hbridge, h2m_corr, h2s1_corr]
      -- The cmp dispatch (reused in two cases).
      have cmpDispatch : ∀ (h_cmp_branch :
            (if cmpScaledMixed_u64 gHi gLo qPlusH8 (mU <<< 1) (sU <<< 1 + 1) = 0 then (none : Option UInt64)
             else
              if cmpScaledMixed_u64 gHi gLo qPlusH8 (mU <<< 1) (sU <<< 1 + 1) < 0 then some sU
              else
                if 0 < cmpScaledMixed_u64 gHi gLo qPlusH8 (mU <<< 1) (sU <<< 1 + 1) then some (sU + 1)
                else if mU &&& 1 = 0 then some sU else some (sU + 1)) = some chosen),
            (if cmpScaledMixed_packed q k gHi gLo qPlusH (2 * (m : Int)) (2 * (s : Int) + 1) < 0 then s
             else if cmpScaledMixed_packed q k gHi gLo qPlusH (2 * (m : Int)) (2 * (s : Int) + 1) > 0 then s + 1
             else if s % 2 = 0 then s else s + 1) = chosen.toNat := by
        intro h_cmp_branch
        rcases hcmp_pkd_eq with hbridge | hzero
        · rw [hbridge]
          by_cases hcmp_neg : cmpScaledMixed_u64 gHi gLo qPlusH8 (mU <<< 1) ((sU <<< 1) + 1) < 0
          · have hcmp_zero : cmpScaledMixed_u64 gHi gLo qPlusH8 (mU <<< 1) ((sU <<< 1) + 1) ≠ 0 := by omega
            simp [hcmp_zero, hcmp_neg] at h_cmp_branch
            have hchosen : chosen = sU := h_cmp_branch.symm
            have hnot_pos : ¬ cmpScaledMixed_u64 gHi gLo qPlusH8 (mU <<< 1) ((sU <<< 1) + 1) > 0 := by omega
            simp [hcmp_neg]
            rw [hchosen, hsU_def, toNat_sU_eq hs_lt58]
          · push_neg at hcmp_neg
            by_cases hcmp_zero : cmpScaledMixed_u64 gHi gLo qPlusH8 (mU <<< 1) ((sU <<< 1) + 1) = 0
            · simp [hcmp_zero] at h_cmp_branch
            have hcmp_pos : cmpScaledMixed_u64 gHi gLo qPlusH8 (mU <<< 1) ((sU <<< 1) + 1) > 0 := by omega
            have hnot_neg : ¬ cmpScaledMixed_u64 gHi gLo qPlusH8 (mU <<< 1) ((sU <<< 1) + 1) < 0 := by omega
            simp [hcmp_zero, hnot_neg, hcmp_pos] at h_cmp_branch
            have hchosen : chosen = sU + 1 := h_cmp_branch.symm
            simp [hnot_neg, hcmp_pos]
            rw [hchosen, hsU_def, toNat_sU_add_1 hs_lt58]
        · simp [hzero] at h_cmp_branch
      -- Case-split on uIn, wIn (4 cases).
      cases huIn : uIn <;> cases hwIn : wIn <;>
        simp only [huIn, hwIn, Bool.not_true, Bool.not_false, Bool.and_true,
          Bool.and_false, Bool.false_eq_true,
          if_true, if_false] at hopt ⊢
      -- (false, false): cmp branch in u64 and in packed.
      · exact cmpDispatch hopt
      -- (false, true): w case (sU + 1).
      · have hchosen : chosen = sU + 1 := Option.some.inj hopt.symm
        rw [hchosen, hsU_def, toNat_sU_add_1 hs_lt58]
      -- (true, false): u case (sU).
      · have hchosen : chosen = sU := Option.some.inj hopt.symm
        rw [hchosen, hsU_def, toNat_sU_eq hs_lt58]
      -- (true, true): cmp branch.
      · exact cmpDispatch hopt

/-! ## shortestUnsigned bridge helpers

The full `shortestUnsigned_u64_opt → packed` bridge composes the
`inRoundingInterval` and `pickNearer` bridges above with case analysis
on the `s ≥ 10` dispatch.  These helper lemmas factor out the
recurring UInt64 arithmetic needed by the top-level proof. -/

/-- `shiftedSig 0 q k = 0`. -/
lemma shiftedSig_zero (q k : Int) : shiftedSig 0 q k = 0 := by
  unfold shiftedSig
  simp

/-- `UInt64.ofNat (s/10) = UInt64.ofNat s / 10` when `s < 2^57`. -/
lemma uint64_div_10 {s : Nat} (hs : s < (1 <<< 57 : Nat)) :
    UInt64.ofNat s / 10 = UInt64.ofNat (s / 10) := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_div]
  simp only [UInt64.toNat_ofNat']
  have h10 : ((10 : UInt64).toNat) = 10 := by decide
  rw [h10]
  have hs64 : s < 2^64 := by
    have : (1 <<< 57 : Nat) < 2^64 := by decide
    omega
  rw [Nat.mod_eq_of_lt hs64]
  have h10_lt : s / 10 < 2^64 := by
    have : s / 10 ≤ s := Nat.div_le_self _ _
    omega
  rw [Nat.mod_eq_of_lt h10_lt]

/-- For `n < 2^64`, `(UInt64.ofNat n).toNat = n`. -/
lemma toNat_ofNat_bounded {n : Nat} (h : n < 2^64) :
    (UInt64.ofNat n).toNat = n := by
  rw [UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt h

/-- shortestUnsigned fast-path correctness.  When `shortestUnsigned_u64_opt`
    returns `some v`, `shortestUnsigned_packed` returns the same `v`. -/
theorem shortestUnsigned_u64_opt_some_eq_packed
    (m : Nat) (q : Int) (v : Nat × Int)
    (hopt : shortestUnsigned_u64_opt m q = some v) :
    shortestUnsigned_packed m q = v := by
  rw [shortestUnsigned_packed_eq]
  show shortestUnsigned m q = v
  unfold shortestUnsigned_u64_opt at hopt
  -- Normalise the inner `kOfMQ_fast` and `shiftedSig_v3` to their specs.
  simp only [kOfMQ_fast_eq, shiftedSig_v3_eq] at hopt
  -- Normalise the `inRoundingInterval_u64_packed_u8` if-chain to a
  -- `match inRoundingInterval_u64_opt with` form so the existing
  -- bridge structure continues to apply.
  simp only [packed_u8_dispatch_eq_opt_match] at hopt
  by_cases hm_ge : m ≥ (1 <<< 53 : Nat)
  · rw [dif_pos hm_ge] at hopt; cases hopt
  rw [dif_neg hm_ge] at hopt
  push_neg at hm_ge
  by_cases hq_lo : q < (-1074 : Int)
  · rw [dif_pos hq_lo] at hopt; cases hopt
  rw [dif_neg hq_lo] at hopt
  by_cases hq_hi : q > 971
  · rw [dif_pos hq_hi] at hopt; cases hopt
  rw [dif_neg hq_hi] at hopt
  push_neg at hq_lo hq_hi
  by_cases hk_lo : kOfMQ m q < pow10Table128_kMin
  · rw [dif_pos hk_lo] at hopt; cases hopt
  rw [dif_neg hk_lo] at hopt
  by_cases hk_hi1 : kOfMQ m q + 1 > pow10Table128_kMax
  · rw [dif_pos hk_hi1] at hopt; cases hopt
  rw [dif_neg hk_hi1] at hopt
  push_neg at hk_lo hk_hi1
  by_cases hs_ge : shiftedSig m q (kOfMQ m q) ≥ (1 <<< 57 : Nat)
  · rw [dif_pos hs_ge] at hopt; cases hopt
  rw [dif_neg hs_ge] at hopt
  push_neg at hs_ge
  have hk_hi : kOfMQ m q ≤ pow10Table128_kMax := by omega
  have hm_lt : m < (1 <<< 58 : Nat) := by
    have : (1 <<< 53 : Nat) < (1 <<< 58 : Nat) := by decide
    omega
  have hm_pos : m ≥ 1 := by
    by_contra hcontra
    push_neg at hcontra
    have hm_zero : m = 0 := by omega
    rw [hm_zero, shiftedSig_zero] at hopt
    simp at hopt
  unfold shortestUnsigned
  by_cases hs10 : shiftedSig m q (kOfMQ m q) ≥ 10
  · rw [if_pos hs10]
    simp only [hs10, if_true] at hopt
    by_cases hqh_lo : q + (pow10Lookup128 (kOfMQ m q + 1)).2.2 < 64
    · rw [dif_pos hqh_lo] at hopt; cases hopt
    rw [dif_neg hqh_lo] at hopt
    by_cases hqh_hi : q + (pow10Lookup128 (kOfMQ m q + 1)).2.2 > 132
    · rw [dif_pos hqh_hi] at hopt; cases hopt
    rw [dif_neg hqh_hi] at hopt
    push_neg at hqh_lo hqh_hi
    have hsHigh_lt57 : shiftedSig m q (kOfMQ m q) / 10 < (1 <<< 57 : Nat) := by
      have : shiftedSig m q (kOfMQ m q) / 10 ≤ shiftedSig m q (kOfMQ m q) := Nat.div_le_self _ _
      omega
    have hsHigh_lt58 : shiftedSig m q (kOfMQ m q) / 10 < (1 <<< 58 : Nat) := by
      have : (1 <<< 57 : Nat) ≤ (1 <<< 58 : Nat) := by decide
      omega
    have hsHigh_pos : shiftedSig m q (kOfMQ m q) / 10 ≥ 1 := by
      show shiftedSig m q (kOfMQ m q) / 10 ≥ 1; omega
    have hdiv10 : UInt64.ofNat (shiftedSig m q (kOfMQ m q)) / 10 =
        UInt64.ofNat (shiftedSig m q (kOfMQ m q) / 10) := uint64_div_10 hs_ge
    rw [hdiv10] at hopt
    match h1 : inRoundingInterval_u64_opt (pow10Lookup128 (kOfMQ m q + 1)).1
                  (pow10Lookup128 (kOfMQ m q + 1)).2.1
                  (UInt64.ofNat (q + (pow10Lookup128 (kOfMQ m q + 1)).2.2).toNat)
                  (UInt64.ofNat (shiftedSig m q (kOfMQ m q) / 10))
                  (UInt64.ofNat m) (isIrregular m q) with
    | none => rw [h1] at hopt; cases hopt
    | some uIn =>
      rw [h1] at hopt
      have h_uIn_pkd : inRoundingInterval (shiftedSig m q (kOfMQ m q) / 10) (kOfMQ m q + 1) m q
          (isIrregular m q) = uIn := by
        rw [← inRoundingInterval_packed_eq]
        exact inRoundingInterval_u64_opt_some_eq_packed q (kOfMQ m q + 1)
          (pow10Lookup128 (kOfMQ m q + 1)).1 (pow10Lookup128 (kOfMQ m q + 1)).2.1
          (q + (pow10Lookup128 (kOfMQ m q + 1)).2.2)
          (shiftedSig m q (kOfMQ m q) / 10) m (isIrregular m q) uIn
          hm_pos hsHigh_pos hm_lt hsHigh_lt58
          (by omega) (by omega) hqh_lo hqh_hi h1
      by_cases huIn : uIn = true
      · -- uIn = true case
        simp only [h_uIn_pkd, huIn, if_true]
        simp only [huIn] at hopt
        have hsHigh_eq : (UInt64.ofNat (shiftedSig m q (kOfMQ m q) / 10)).toNat =
            shiftedSig m q (kOfMQ m q) / 10 := by
          apply toNat_ofNat_bounded
          have : (1 <<< 58 : Nat) < 2^64 := by decide
          omega
        cases hopt
        simp [hsHigh_eq]
      · -- uIn = false case
        have huIn_false : uIn = false := by cases uIn <;> simp_all
        simp only [h_uIn_pkd, huIn_false, Bool.false_eq_true, if_false]
        simp only [huIn_false] at hopt
        have hsHigh1_eq : UInt64.ofNat (shiftedSig m q (kOfMQ m q) / 10) + 1 =
            UInt64.ofNat (shiftedSig m q (kOfMQ m q) / 10 + 1) := (ofNat_succ _).symm
        have hsHigh1_lt58 : shiftedSig m q (kOfMQ m q) / 10 + 1 < (1 <<< 58 : Nat) := by
          have h57_58 : (1 <<< 57 : Nat) + 1 ≤ (1 <<< 58 : Nat) := by decide
          omega
        rw [hsHigh1_eq] at hopt
        match h2 : inRoundingInterval_u64_opt (pow10Lookup128 (kOfMQ m q + 1)).1
                      (pow10Lookup128 (kOfMQ m q + 1)).2.1
                      (UInt64.ofNat (q + (pow10Lookup128 (kOfMQ m q + 1)).2.2).toNat)
                      (UInt64.ofNat (shiftedSig m q (kOfMQ m q) / 10 + 1))
                      (UInt64.ofNat m) (isIrregular m q) with
        | none => rw [h2] at hopt; cases hopt
        | some wIn =>
          rw [h2] at hopt
          have h_wIn_pkd : inRoundingInterval (shiftedSig m q (kOfMQ m q) / 10 + 1) (kOfMQ m q + 1) m q
              (isIrregular m q) = wIn := by
            rw [← inRoundingInterval_packed_eq]
            exact inRoundingInterval_u64_opt_some_eq_packed q (kOfMQ m q + 1)
              (pow10Lookup128 (kOfMQ m q + 1)).1 (pow10Lookup128 (kOfMQ m q + 1)).2.1
              (q + (pow10Lookup128 (kOfMQ m q + 1)).2.2)
              (shiftedSig m q (kOfMQ m q) / 10 + 1) m (isIrregular m q) wIn
              hm_pos (by omega) hm_lt hsHigh1_lt58
              (by omega) (by omega) hqh_lo hqh_hi h2
          by_cases hwIn : wIn = true
          · -- wIn = true case
            simp only [h_wIn_pkd, hwIn, if_true]
            simp only [hwIn] at hopt
            have hwIn_eq : (UInt64.ofNat (shiftedSig m q (kOfMQ m q) / 10 + 1)).toNat =
                shiftedSig m q (kOfMQ m q) / 10 + 1 := by
              apply toNat_ofNat_bounded
              have : (1 <<< 58 : Nat) < 2^64 := by decide
              omega
            cases hopt
            congr 1
            exact hwIn_eq.symm
          · -- wIn = false case
            have hwIn_false : wIn = false := by cases wIn <;> simp_all
            simp only [h_wIn_pkd, hwIn_false, Bool.false_eq_true, if_false]
            simp only [hwIn_false] at hopt
            by_cases hqh2_lo : q + (pow10Lookup128 (kOfMQ m q)).2.2 < 64
            · rw [dif_pos hqh2_lo] at hopt; cases hopt
            rw [dif_neg hqh2_lo] at hopt
            by_cases hqh2_hi : q + (pow10Lookup128 (kOfMQ m q)).2.2 > 132
            · rw [dif_pos hqh2_hi] at hopt; cases hopt
            rw [dif_neg hqh2_hi] at hopt
            push_neg at hqh2_lo hqh2_hi
            match hp : pickNearer_u64_opt (pow10Lookup128 (kOfMQ m q)).1
                          (pow10Lookup128 (kOfMQ m q)).2.1
                          (UInt64.ofNat (q + (pow10Lookup128 (kOfMQ m q)).2.2).toNat)
                          (UInt64.ofNat (shiftedSig m q (kOfMQ m q)))
                          (UInt64.ofNat m) (isIrregular m q) with
            | none => rw [hp] at hopt; cases hopt
            | some chosen =>
              rw [hp] at hopt
              have hpkd : pickNearer (shiftedSig m q (kOfMQ m q)) (kOfMQ m q) m q = chosen.toNat := by
                rw [← pickNearer_packed_eq]
                exact pickNearer_u64_opt_some_eq_packed q (kOfMQ m q)
                  (pow10Lookup128 (kOfMQ m q)).1 (pow10Lookup128 (kOfMQ m q)).2.1
                  (q + (pow10Lookup128 (kOfMQ m q)).2.2)
                  (shiftedSig m q (kOfMQ m q)) m (isIrregular m q) chosen
                  hm_pos (by omega) hm_lt hs_ge (by omega) hk_hi hqh2_lo hqh2_hi rfl hp
              rw [hpkd]
              cases hopt
              rfl
  · rw [if_neg hs10]
    push_neg at hs10
    simp only [show (shiftedSig m q (kOfMQ m q) ≥ 10) = False from by simp [hs10],
      if_false] at hopt
    by_cases hs_zero : shiftedSig m q (kOfMQ m q) = 0
    · rw [dif_pos hs_zero] at hopt; cases hopt
    rw [dif_neg hs_zero] at hopt
    by_cases hqh2_lo : q + (pow10Lookup128 (kOfMQ m q)).2.2 < 64
    · rw [dif_pos hqh2_lo] at hopt; cases hopt
    rw [dif_neg hqh2_lo] at hopt
    by_cases hqh2_hi : q + (pow10Lookup128 (kOfMQ m q)).2.2 > 132
    · rw [dif_pos hqh2_hi] at hopt; cases hopt
    rw [dif_neg hqh2_hi] at hopt
    push_neg at hqh2_lo hqh2_hi
    match hp : pickNearer_u64_opt (pow10Lookup128 (kOfMQ m q)).1
                  (pow10Lookup128 (kOfMQ m q)).2.1
                  (UInt64.ofNat (q + (pow10Lookup128 (kOfMQ m q)).2.2).toNat)
                  (UInt64.ofNat (shiftedSig m q (kOfMQ m q)))
                  (UInt64.ofNat m) (isIrregular m q) with
    | none => rw [hp] at hopt; cases hopt
    | some chosen =>
      rw [hp] at hopt
      have hpkd : pickNearer (shiftedSig m q (kOfMQ m q)) (kOfMQ m q) m q = chosen.toNat := by
        rw [← pickNearer_packed_eq]
        exact pickNearer_u64_opt_some_eq_packed q (kOfMQ m q)
          (pow10Lookup128 (kOfMQ m q)).1 (pow10Lookup128 (kOfMQ m q)).2.1
          (q + (pow10Lookup128 (kOfMQ m q)).2.2)
          (shiftedSig m q (kOfMQ m q)) m (isIrregular m q) chosen
          hm_pos (by omega) hm_lt hs_ge (by omega) hk_hi hqh2_lo hqh2_hi rfl hp
      rw [hpkd]
      cases hopt
      rfl

/-- `shortestUnsigned_v2 = shortestUnsigned_packed` everywhere. -/
theorem shortestUnsigned_v2_eq_packed (m : Nat) (q : Int) :
    shortestUnsigned_v2 m q = shortestUnsigned_packed m q := by
  unfold shortestUnsigned_v2
  match h : shortestUnsigned_u64_opt m q with
  | none => rfl
  | some v =>
    exact (shortestUnsigned_u64_opt_some_eq_packed m q v h).symm

/-- `shortestUnsigned_v2 = shortestUnsigned` (via the packed chain). -/
theorem shortestUnsigned_v2_eq (m : Nat) (q : Int) :
    shortestUnsigned_v2 m q = shortestUnsigned m q := by
  rw [shortestUnsigned_v2_eq_packed, shortestUnsigned_packed_eq]

/-- `shortestUnsigned_packed = shortestUnsigned_v2`. -/
theorem shortestUnsigned_packed_eq_v2 :
    @shortestUnsigned_packed = @shortestUnsigned_v2 := by
  funext m q
  exact (shortestUnsigned_v2_eq_packed m q).symm

/-- `shortestUnsigned = shortestUnsigned_v2`. -/
theorem shortestUnsigned_eq_v2 :
    @shortestUnsigned = @shortestUnsigned_v2 := by
  funext m q
  exact (shortestUnsigned_v2_eq m q).symm

/-! ## Fused `toDecimal` with v2 inlined

The existing `toDecimal_packed` in `Orchestration.lean` was compiled
before our v2 csimp was registered, so its compiled body still calls
`shortestUnsigned_packed` directly.  This new `toDecimal_v2` is a
syntactic copy of `toDecimal` compiled AFTER the v2 csimp is in scope,
so the inner `shortestUnsigned` call inlines to `shortestUnsigned_v2`. -/

open PP.Numeric.Float in
/-- Fused `Float → Decimal` using the v2 path directly. -/
def toDecimal_v2 (f : _root_.Float) : Except String _root_.PP.Numeric.Decimal :=
  if isNaNBits f then
    .error "NaN"
  else if isInfBits f then
    .error (if signBit f then "-Infinity" else "Infinity")
  else
    let d := decode f
    if d.m = 0 then .ok ⟨d.sign, 0, 0⟩
    else
      let (sig, exp) := shortestUnsigned_v2 d.m d.q
      .ok (PP.Numeric.Decimal.mk' d.sign sig exp)

theorem toDecimal_v2_eq (f : _root_.Float) :
    toDecimal_v2 f = toDecimal f := by
  unfold toDecimal_v2 toDecimal
  by_cases h1 : PP.Numeric.Float.isNaNBits f = true
  · simp [h1]
  by_cases h2 : PP.Numeric.Float.isInfBits f = true
  · simp [h1, h2]
  simp only [h1, h2, if_false, Bool.false_eq_true]
  by_cases h3 : (PP.Numeric.Float.decode f).m = 0
  · simp [h3]
  simp only [h3, if_false]
  rw [shortestUnsigned_v2_eq]

/-- `toDecimal = toDecimal_v2`. -/
theorem toDecimal_eq_v2 : @toDecimal = @toDecimal_v2 := by
  funext f
  exact (toDecimal_v2_eq f).symm

/-! ## Bridge for `shortestUnsigned_u64_opt_v2` (UInt64-significand path).

Same shape as `shortestUnsigned_u64_opt_some_eq_packed`, but the
significand `s` is held as `UInt64` throughout, avoiding the
`Nat ↔ UInt64` round-trip.  The `sU.toNat` appears only at the
boundary.  -/

/-- UInt64 / Nat comparison: `sU ≥ 10 ↔ sU.toNat ≥ 10`. -/
lemma uint64_ge_10 (sU : UInt64) :
    sU ≥ (10 : UInt64) ↔ sU.toNat ≥ 10 := by
  constructor <;> (intro h; simpa [GE.ge] using h)

/-- UInt64 / Nat equality: `sU = 0 ↔ sU.toNat = 0`. -/
lemma uint64_eq_0 (sU : UInt64) :
    sU = 0 ↔ sU.toNat = 0 := by
  constructor
  · intro h; rw [h]; rfl
  · intro h
    rw [← UInt64.toNat_inj, h]; rfl

/-- `UInt64.ofNat n = UInt64.ofNat m → n.toNat = m.toNat` when both fit.
    Specialised for our needs: `(UInt64.ofNat s).toNat = s` when `s < 2^64`. -/
lemma uint64_ofNat_toNat_self {s : Nat} (h : s < 2^64) :
    (UInt64.ofNat s).toNat = s := by
  rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt h

/-- Round-trip the other way: `UInt64.ofNat sU.toNat = sU`. -/
lemma uint64_ofNat_toNat (sU : UInt64) :
    UInt64.ofNat sU.toNat = sU := UInt64.ofNat_toNat

/-- Helper: when both inRoundingInterval-paths agree, the s≥10 branches
    return identical results modulo `.toNat`.  Stated as: for any leaves
    `f g : UInt64 × Int`, the v1/v2 inRoundingInterval-then-pickNearer
    chain matches `f.toNat = g.toNat ∧ f.snd = g.snd`. -/
private theorem v1_v2_inner_eq_at_high (_m : Nat) (q : Int) (k : Int)
    (sU : UInt64) (mU : UInt64) (irregular : Bool) :
    (let cmpTupleH := pow10Lookup128 (k + 1)
     let cmpHGHi := cmpTupleH.1
     let cmpHGLo := cmpTupleH.2.1
     let cmpHH := cmpTupleH.2.2
     let cmpHQPlusH : Int := q + cmpHH
     if _h_qh_lo : cmpHQPlusH < 64 then (none : Option (Nat × Int))
     else if _h_qh_hi : cmpHQPlusH > 132 then none
     else
       let cmpHQPlusH8 : UInt64 := UInt64.ofNat cmpHQPlusH.toNat
       let sHighU : UInt64 := sU / 10
       let uV := inRoundingInterval_u64_packed_u8 cmpHGHi cmpHGLo cmpHQPlusH8
                   sHighU mU irregular
       if uV = inRoundingInterval_u8_AMBIG then none
       else if uV = inRoundingInterval_u8_TRUE then some (sHighU.toNat, k + 1)
       else
         let wV := inRoundingInterval_u64_packed_u8 cmpHGHi cmpHGLo cmpHQPlusH8
                     (sHighU + 1) mU irregular
         if wV = inRoundingInterval_u8_AMBIG then none
         else if wV = inRoundingInterval_u8_TRUE then some ((sHighU + 1).toNat, k + 1)
         else
           let cmpTuple := pow10Lookup128 k
           let cmpGHi := cmpTuple.1
           let cmpGLo := cmpTuple.2.1
           let cmpH := cmpTuple.2.2
           let cmpQPlusH : Int := q + cmpH
           if _h_qh2_lo : cmpQPlusH < 64 then none
           else if _h_qh2_hi : cmpQPlusH > 132 then none
           else
             let cmpQPlusH8 : UInt64 := UInt64.ofNat cmpQPlusH.toNat
             match pickNearer_u64_opt cmpGHi cmpGLo cmpQPlusH8 sU mU irregular with
             | none => none
             | some chosen => some (chosen.toNat, k)) =
    (let cmpTupleH := pow10Lookup128 (k + 1)
     let cmpHGHi := cmpTupleH.1
     let cmpHGLo := cmpTupleH.2.1
     let cmpHH := cmpTupleH.2.2
     let cmpHQPlusH : Int := q + cmpHH
     if _h_qh_lo : cmpHQPlusH < 64 then (none : Option (UInt64 × Int))
     else if _h_qh_hi : cmpHQPlusH > 132 then none
     else
       let cmpHQPlusH8 : UInt64 := UInt64.ofNat cmpHQPlusH.toNat
       let sHighU : UInt64 := sU / 10
       let uV := inRoundingInterval_u64_packed_u8 cmpHGHi cmpHGLo cmpHQPlusH8
                   sHighU mU irregular
       if uV = inRoundingInterval_u8_AMBIG then none
       else if uV = inRoundingInterval_u8_TRUE then some (sHighU, k + 1)
       else
         let wV := inRoundingInterval_u64_packed_u8 cmpHGHi cmpHGLo cmpHQPlusH8
                     (sHighU + 1) mU irregular
         if wV = inRoundingInterval_u8_AMBIG then none
         else if wV = inRoundingInterval_u8_TRUE then some (sHighU + 1, k + 1)
         else
           let cmpTuple := pow10Lookup128 k
           let cmpGHi := cmpTuple.1
           let cmpGLo := cmpTuple.2.1
           let cmpH := cmpTuple.2.2
           let cmpQPlusH : Int := q + cmpH
           if _h_qh2_lo : cmpQPlusH < 64 then none
           else if _h_qh2_hi : cmpQPlusH > 132 then none
           else
             let cmpQPlusH8 : UInt64 := UInt64.ofNat cmpQPlusH.toNat
             match pickNearer_u64_opt cmpGHi cmpGLo cmpQPlusH8 sU mU irregular with
             | none => none
             | some chosen => some (chosen, k)).map (fun p => (p.1.toNat, p.2)) := by
  simp only []
  split_ifs <;> simp only [Option.map] ;
    first
    | rfl
    | (cases pickNearer_u64_opt _ _ _ _ _ _ <;> rfl)

/-- Helper: same for the s<10 (pickNearer-only) path. -/
private theorem v1_v2_inner_eq_at_low (_m : Nat) (q : Int) (k : Int)
    (sU : UInt64) (mU : UInt64) (irregular : Bool) :
    (let cmpTuple := pow10Lookup128 k
     let cmpGHi := cmpTuple.1
     let cmpGLo := cmpTuple.2.1
     let cmpH := cmpTuple.2.2
     let cmpQPlusH : Int := q + cmpH
     if _h_qh2_lo : cmpQPlusH < 64 then (none : Option (Nat × Int))
     else if _h_qh2_hi : cmpQPlusH > 132 then none
     else
       let cmpQPlusH8 : UInt64 := UInt64.ofNat cmpQPlusH.toNat
       match pickNearer_u64_opt cmpGHi cmpGLo cmpQPlusH8 sU mU irregular with
       | none => none
       | some chosen => some (chosen.toNat, k)) =
    (let cmpTuple := pow10Lookup128 k
     let cmpGHi := cmpTuple.1
     let cmpGLo := cmpTuple.2.1
     let cmpH := cmpTuple.2.2
     let cmpQPlusH : Int := q + cmpH
     if _h_qh2_lo : cmpQPlusH < 64 then (none : Option (UInt64 × Int))
     else if _h_qh2_hi : cmpQPlusH > 132 then none
     else
       let cmpQPlusH8 : UInt64 := UInt64.ofNat cmpQPlusH.toNat
       match pickNearer_u64_opt cmpGHi cmpGLo cmpQPlusH8 sU mU irregular with
       | none => none
       | some chosen => some (chosen, k)).map (fun p => (p.1.toNat, p.2)) := by
  simp only []
  split_ifs <;> simp only [Option.map] ;
    first
    | rfl
    | (cases pickNearer_u64_opt _ _ _ _ _ _ <;> rfl)

/-- Structural correspondence: v1 = v2 (modulo `.toNat`). -/
theorem shortestUnsigned_u64_opt_eq_v2_map (m : Nat) (q : Int) :
    shortestUnsigned_u64_opt m q =
      (shortestUnsigned_u64_opt_v2 m q).map (fun p => (p.1.toNat, p.2)) := by
  unfold shortestUnsigned_u64_opt shortestUnsigned_u64_opt_v2
  by_cases hm_ge : m ≥ (1 <<< 53 : Nat)
  · simp only [dif_pos hm_ge, Option.map_none]
  simp only [dif_neg hm_ge]
  by_cases hq_lo : q < (-1074 : Int)
  · simp only [dif_pos hq_lo, Option.map_none]
  simp only [dif_neg hq_lo]
  by_cases hq_hi : q > 971
  · simp only [dif_pos hq_hi, Option.map_none]
  simp only [dif_neg hq_hi]
  by_cases hk_lo : kOfMQ_fast m q < pow10Table128_kMin
  · simp only [dif_pos hk_lo, Option.map_none]
  simp only [dif_neg hk_lo]
  by_cases hk_hi : kOfMQ_fast m q + 1 > pow10Table128_kMax
  · simp only [dif_pos hk_hi, Option.map_none]
  simp only [dif_neg hk_hi]
  set s : Nat := shiftedSig_v3 m q (kOfMQ_fast m q) with hs_def
  by_cases hs_ge : s ≥ (1 <<< 57 : Nat)
  · simp only [dif_pos hs_ge, Option.map_none]
  simp only [dif_neg hs_ge]
  push_neg at hs_ge
  have hs_lt_64 : s < 2^64 := by
    have : (1 <<< 57 : Nat) < 2^64 := by decide
    omega
  set sU : UInt64 := UInt64.ofNat s with hsU_def
  have h_sU_toNat : sU.toNat = s := uint64_ofNat_toNat_self hs_lt_64
  have h_ge_10 : (s ≥ 10) ↔ (sU ≥ (10 : UInt64)) := by
    rw [uint64_ge_10, h_sU_toNat]
  have h_eq_0 : (s = 0) ↔ (sU = 0) := by
    rw [uint64_eq_0, h_sU_toNat]
  by_cases hs10 : s ≥ 10
  · have hs10' : sU ≥ (10 : UInt64) := h_ge_10.mp hs10
    simp only [if_pos hs10, if_pos hs10']
    exact v1_v2_inner_eq_at_high m q (kOfMQ_fast m q) sU (UInt64.ofNat m) (isIrregular m q)
  · have hs10' : ¬ sU ≥ (10 : UInt64) := fun h => hs10 (h_ge_10.mpr h)
    simp only [if_neg hs10, if_neg hs10']
    by_cases hs0 : s = 0
    · have hs0' : sU = 0 := h_eq_0.mp hs0
      simp only [dif_pos hs0, dif_pos hs0', Option.map_none]
    have hs0' : sU ≠ 0 := fun h => hs0 (h_eq_0.mpr h)
    simp only [dif_neg hs0, dif_neg hs0']
    exact v1_v2_inner_eq_at_low m q (kOfMQ_fast m q) sU (UInt64.ofNat m) (isIrregular m q)

/-- `shortestUnsigned_v3 = shortestUnsigned_v2`. -/
theorem shortestUnsigned_v3_eq_v2 (m : Nat) (q : Int) :
    shortestUnsigned_v3 m q = shortestUnsigned_v2 m q := by
  unfold shortestUnsigned_v3 shortestUnsigned_v2
  rw [shortestUnsigned_u64_opt_eq_v2_map]
  cases shortestUnsigned_u64_opt_v2 m q
  · rfl
  · rfl

/-- `shortestUnsigned_v3 = shortestUnsigned_packed`. -/
theorem shortestUnsigned_v3_eq_packed (m : Nat) (q : Int) :
    shortestUnsigned_v3 m q = shortestUnsigned_packed m q := by
  rw [shortestUnsigned_v3_eq_v2, shortestUnsigned_v2_eq_packed]

/-- `shortestUnsigned_v3 = shortestUnsigned`. -/
theorem shortestUnsigned_v3_eq (m : Nat) (q : Int) :
    shortestUnsigned_v3 m q = shortestUnsigned m q := by
  rw [shortestUnsigned_v3_eq_packed, shortestUnsigned_packed_eq]

/-! ## Wire `shortestUnsigned_v3` into the runtime.

`@[csimp]` doesn't chain, so we need a direct csimp from each entry
point (`shortestUnsigned`, `shortestUnsigned_packed`, `shortestUnsigned_v2`)
to `shortestUnsigned_v3`.  Note that the prior v2 csimps remain in
scope; csimps registered later override earlier ones for the same
source declaration. -/

@[csimp]
theorem shortestUnsigned_packed_eq_v3_csimp :
    @shortestUnsigned_packed = @shortestUnsigned_v3 := by
  funext m q
  exact (shortestUnsigned_v3_eq_packed m q).symm

@[csimp]
theorem shortestUnsigned_eq_v3_csimp :
    @shortestUnsigned = @shortestUnsigned_v3 := by
  funext m q
  exact (shortestUnsigned_v3_eq m q).symm

@[csimp]
theorem shortestUnsigned_v2_eq_v3_csimp :
    @shortestUnsigned_v2 = @shortestUnsigned_v3 := by
  funext m q
  rw [shortestUnsigned_v2_eq_packed, ← shortestUnsigned_v3_eq_packed]

/-! ## Fused `toDecimal_v3` — direct v3 path, no v2 detour.

Compiled AFTER all v3 csimps so the inner `shortestUnsigned_packed`
call inlines to `shortestUnsigned_v3`. -/

open PP.Numeric.Float in
/-- Fused `Float → Decimal` using the v3 path directly. -/
def toDecimal_v3 (f : _root_.Float) : Except String _root_.PP.Numeric.Decimal :=
  if isNaNBits f then
    .error "NaN"
  else if isInfBits f then
    .error (if signBit f then "-Infinity" else "Infinity")
  else
    let d := decode f
    if d.m = 0 then .ok ⟨d.sign, 0, 0⟩
    else
      let (sig, exp) := shortestUnsigned_v3 d.m d.q
      .ok (PP.Numeric.Decimal.mk' d.sign sig exp)

theorem toDecimal_v3_eq (f : _root_.Float) :
    toDecimal_v3 f = toDecimal f := by
  unfold toDecimal_v3 toDecimal
  by_cases h1 : PP.Numeric.Float.isNaNBits f = true
  · simp [h1]
  by_cases h2 : PP.Numeric.Float.isInfBits f = true
  · simp [h1, h2]
  simp only [h1, h2, if_false, Bool.false_eq_true]
  by_cases h3 : (PP.Numeric.Float.decode f).m = 0
  · simp [h3]
  simp only [h3, if_false]
  rw [shortestUnsigned_v3_eq]

-- Superseded registration: `toDecimal_eq_v7_csimp` (KernelV6.lean) is the live @[csimp].
theorem toDecimal_eq_v3_csimp : @toDecimal = @toDecimal_v3 := by
  funext f
  exact (toDecimal_v3_eq f).symm

end PP.Numeric.Schubfach

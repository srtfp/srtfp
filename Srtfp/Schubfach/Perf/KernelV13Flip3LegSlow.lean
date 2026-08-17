/- flip3 spec-proof, slow-digit leg (`shiftedSig < 10`). Split per-module for bounded peak RAM. -/

import Srtfp.Schubfach.Perf.KernelV13Flip3Defs
import Srtfp.Tactics

namespace Srtfp.Schubfach

set_option maxRecDepth 16384 in
set_option maxHeartbeats 3200000 in
/-- `flip3` correctness, slow-digit leg (`shiftedSig < 10`). Split from the
main dispatch so each leg's elaboration (and kernel check) peaks alone —
see the memory note on the main theorem. -/
theorem flip3_some_eq_packed_slow
    (m : Nat) (q : Int) (sUo : UInt64) (ko : Int)
    (hopt : shortestUnsigned_u64_opt_flip3 m q = some (sUo, ko))
    (hs10 : ¬ shiftedSig m q (kOfMQ m q) ≥ 10) :
    shortestUnsigned m q = (sUo.toNat, ko) := by
  unfold shortestUnsigned_u64_opt_flip3 at hopt
  simp only [kOfMQ_fast_eq] at hopt
  by_cases hm0 : m = 0
  · rw [dif_pos hm0] at hopt; cases hopt
  rw [dif_neg hm0] at hopt
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
  have hkMin_lit : pow10Table128_kMin = (-324 : Int) := rfl
  have hkMax_lit : pow10Table128_kMax = (324 : Int) := rfl
  have hm_lt : m < (1 <<< 58 : Nat) := by
    have : (1 <<< 53 : Nat) < (1 <<< 58 : Nat) := by decide
    omega
  have hm_pos : m ≥ 1 := Nat.pos_of_ne_zero hm0
  by_cases hqh127 : -q + (pow10Lookup128 (-(kOfMQ m q + 1))).2.2 < 127
  · rw [dif_pos hqh127] at hopt; cases hopt
  rw [dif_neg hqh127] at hopt
  by_cases hqh_hi : -q + (pow10Lookup128 (-(kOfMQ m q + 1))).2.2 > 132
  · rw [dif_pos hqh_hi] at hopt; cases hopt
  rw [dif_neg hqh_hi] at hopt
  push_neg at hqh127 hqh_hi
  have hqh_lo : 64 ≤ -q + (pow10Lookup128 (-(kOfMQ m q + 1))).2.2 := by omega
  set gT := pow10Lookup128 (-(kOfMQ m q + 1)) with hgT
  set m4 : UInt64 := UInt64.ofNat m <<< 2 with hm4
  set pLo : UInt64 := m4 * gT.2.1 with hpLo
  set pLoH : UInt64 := mulHi64 m4 gT.2.1 with hpLoH
  set pHi : UInt64 := m4 * gT.1 with hpHi
  set pHiH : UInt64 := mulHi64 m4 gT.1 with hpHiH
  set pMid : UInt64 := pHi + pLoH with hpMid
  set pC : UInt64 := (if pMid < pHi then (1 : UInt64) else 0) with hpC
  set pH : UInt64 := pHiH + pC with hpH
  set p4 := shl2_192 pH pMid pLo with hp4
  set p5 := add192_192 p4.1 p4.2.1 p4.2.2 pH pMid pLo with hp5
  have hG_lt : gT.1.toNat * 2 ^ 64 + gT.2.1.toNat < 2 ^ 128 := by
    have h1 := gT.1.toNat_lt; have h2 := gT.2.1.toNat_lt
    omega
  have hm4_toNat : m4.toNat = 4 * m := by
    rw [hm4, uint64_shiftLeft_2, UInt64.toNat_mul,
        toNat_ofNat_bounded (show m < 2 ^ 64 by omega),
        show ((4 : UInt64)).toNat = 4 from rfl]
    exact Nat.mod_eq_of_lt (by omega)
  have hmulG_lt : ∀ b : Nat, b ≤ 4 * m + 2 →
      b * (gT.1.toNat * 2 ^ 64 + gT.2.1.toNat) < 2 ^ 192 := by
    intro b hb
    have h3 : b * (gT.1.toNat * 2 ^ 64 + gT.2.1.toNat) ≤ 2 ^ 60 * 2 ^ 128 :=
      Nat.mul_le_mul (by omega) (by omega)
    have h4 : (2 : Nat) ^ 60 * 2 ^ 128 < 2 ^ 192 := by
      rw [← Nat.pow_add]
      exact Nat.pow_lt_pow_right (by omega) (by omega)
    omega
  have htrip0G : triple192Nat 0 gT.1 gT.2.1
      = gT.1.toNat * 2 ^ 64 + gT.2.1.toNat := by
    unfold triple192Nat
    simp only [show ((0 : UInt64)).toNat = 0 from rfl]
    omega
  have hP_val : triple192Nat pH pMid pLo
      = 4 * m * (gT.1.toNat * 2 ^ 64 + gT.2.1.toNat) := by
    have h := mul192_b_g_toNat m4 gT.1 gT.2.1
    simp only [] at h
    rw [← hpLo, ← hpLoH, ← hpHi, ← hpHiH, ← hpMid, ← hpC, ← hpH] at h
    rw [hm4_toNat, Nat.mod_eq_of_lt (hmulG_lt (4 * m) (by omega))] at h
    exact h
  have hmulG_lt2 : ∀ b : Nat, b ≤ 32 * m →
      b * (gT.1.toNat * 2 ^ 64 + gT.2.1.toNat) < 2 ^ 192 := by
    intro b hb
    have h3 : b * (gT.1.toNat * 2 ^ 64 + gT.2.1.toNat) ≤ 2 ^ 63 * 2 ^ 128 :=
      Nat.mul_le_mul (by omega) (by omega)
    have h4 : (2 : Nat) ^ 63 * 2 ^ 128 < 2 ^ 192 := by
      rw [← Nat.pow_add]
      exact Nat.pow_lt_pow_right (by omega) (by omega)
    omega
  have hp4_val : triple192Nat p4.1 p4.2.1 p4.2.2
      = 16 * m * (gT.1.toNat * 2 ^ 64 + gT.2.1.toNat) := by
    rw [hp4, shl2_192_toNat pH pMid pLo (by
      rw [hP_val]
      rw [show 4 * (4 * m * (gT.1.toNat * 2 ^ 64 + gT.2.1.toNat))
            = 16 * m * (gT.1.toNat * 2 ^ 64 + gT.2.1.toNat) from by grind]
      exact hmulG_lt2 (16 * m) (by omega)), hP_val]
    grind
  have hp5_val : triple192Nat p5.1 p5.2.1 p5.2.2
      = 20 * m * (gT.1.toNat * 2 ^ 64 + gT.2.1.toNat) := by
    rw [hp5, add192_192_toNat _ _ _ _ _ _ (by
      rw [hp4_val, hP_val]
      rw [show 16 * m * (gT.1.toNat * 2 ^ 64 + gT.2.1.toNat)
            + 4 * m * (gT.1.toNat * 2 ^ 64 + gT.2.1.toNat)
            = 20 * m * (gT.1.toNat * 2 ^ 64 + gT.2.1.toNat) from by grind]
      exact hmulG_lt2 (20 * m) (by omega)), hp4_val, hP_val]
    grind
  have ht_lt : (-q + gT.2.2 - 127).toNat < 64 := by omega
  have hext := triple192_top_extract p5.1 p5.2.1 p5.2.2 _ ht_lt
  rw [hp5_val] at hext
  have h128t : 128 + (-q + gT.2.2 - 127).toNat = (-q + gT.2.2).toNat + 1 := by
    omega
  rw [h128t] at hext
  have hhalf : 20 * m * (gT.1.toNat * 2 ^ 64 + gT.2.1.toNat)
        / 2 ^ ((-q + gT.2.2).toNat + 1)
      = 10 * m * (gT.1.toNat * 2 ^ 64 + gT.2.1.toNat) / 2 ^ (-q + gT.2.2).toNat := by
    rw [show (2 : Nat) ^ ((-q + gT.2.2).toNat + 1)
          = 2 ^ (-q + gT.2.2).toNat * 2 from Nat.pow_succ _ _,
        show 20 * m * (gT.1.toNat * 2 ^ 64 + gT.2.1.toNat)
          = 10 * m * (gT.1.toNat * 2 ^ 64 + gT.2.1.toNat) * 2 from by grind,
        Nat.mul_div_mul_right _ _ (by grind : (0 : Nat) < 2)]
  have hfl := sFromP_floor m q hm_pos (by
      have : (1 <<< 53 : Nat) = 2 ^ 53 := by decide
      omega) hq_lo hq_hi
    (by rw [hkMin_lit]; omega) (by rw [hkMax_lit]; omega)
    (by rw [← hgT]; omega)
    (by
      by_cases hirr : isIrregular m q = true
      · right
        unfold isIrregular at hirr
        rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hirr
        rw [hirr.1]
        unfold minNormalSignificand
        have : (1 <<< 52 : Nat) = 2 ^ 52 := by decide
        omega
      · left
        have hk_eq : kOfMQ m q = floorLog10Pow2 q := by
          unfold kOfMQ
          rw [if_neg hirr]
        rw [hk_eq]
        exact wReg_at q (by omega) (by omega)
          (by rw [← hk_eq]; omega) (by rw [← hk_eq]; omega))
  rw [← hgT] at hfl
  have hexp_eq : ((gT.2.2 - q)).toNat = (-q + gT.2.2).toNat := by omega
  rw [hexp_eq] at hfl
  have hs_eq : (p5.1 >>> UInt64.ofNat ((-q + gT.2.2 - 127)).toNat).toNat
      = shiftedSig m q (kOfMQ m q) := by
    rw [hext, hhalf]
    exact hfl
  have hsU_form : p5.1 >>> UInt64.ofNat ((-q + gT.2.2 - 127)).toNat
      = UInt64.ofNat (shiftedSig m q (kOfMQ m q)) := by
    rw [← hs_eq, UInt64.ofNat_toNat]
  rw [hsU_form] at hopt
  have hbound64 : shiftedSig m q (kOfMQ m q) < 2 ^ 64 := by
    rw [← hs_eq]
    exact (p5.1 >>> UInt64.ofNat ((-q + gT.2.2 - 127)).toNat).toNat_lt
  by_cases h_s : UInt64.ofNat (shiftedSig m q (kOfMQ m q)) ≥ (144115188075855872 : UInt64)
  · rw [dif_pos h_s] at hopt; cases hopt
  rw [dif_neg h_s] at hopt
  have hs_ge : shiftedSig m q (kOfMQ m q) < (1 <<< 57 : Nat) := by
    by_contra hc
    push_neg at hc
    apply h_s
    rw [ge_iff_le, UInt64.le_iff_toNat_le, toNat_ofNat_bounded hbound64,
        show ((144115188075855872 : UInt64)).toNat = (1 <<< 57 : Nat) from rfl]
    exact hc
  have e10 : (UInt64.ofNat (shiftedSig m q (kOfMQ m q)) ≥ (10 : UInt64))
      = (shiftedSig m q (kOfMQ m q) ≥ 10) := by
    rw [propext (uint64_ge_10 _), toNat_ofNat_bounded hbound64]
  have e0 : (UInt64.ofNat (shiftedSig m q (kOfMQ m q)) = 0)
      = (shiftedSig m q (kOfMQ m q) = 0) := by
    rw [propext (uint64_eq_0 _), toNat_ofNat_bounded hbound64]
  simp only [e10, e0] at hopt
  unfold shortestUnsigned
  rw [if_neg hs10]
  push_neg at hs10
  simp only [show (shiftedSig m q (kOfMQ m q) ≥ 10) = False from by simp [hs10],
    if_false] at hopt
  by_cases hs_zero : shiftedSig m q (kOfMQ m q) = 0
  · rw [dif_pos hs_zero] at hopt; cases hopt
  rw [dif_neg hs_zero] at hopt
  by_cases hqh2_lo : -q + (pow10Lookup128 (-(kOfMQ m q))).2.2 < 64
  · rw [dif_pos hqh2_lo] at hopt; cases hopt
  rw [dif_neg hqh2_lo] at hopt
  by_cases hqh2_hi : -q + (pow10Lookup128 (-(kOfMQ m q))).2.2 > 132
  · rw [dif_pos hqh2_hi] at hopt; cases hopt
  rw [dif_neg hqh2_hi] at hopt
  push_neg at hqh2_lo hqh2_hi
  set gT2 := pow10Lookup128 (-(kOfMQ m q)) with hgT2
  set m4 : UInt64 := UInt64.ofNat m <<< 2 with hm4
  set leftU : UInt64 := (if isIrregular m q = true then m4 - 1 else m4 - 2) with hleftU
  have hm4_toNat : m4.toNat = 4 * m := by
    rw [hm4, uint64_shiftLeft_2, UInt64.toNat_mul,
        toNat_ofNat_bounded (show m < 2 ^ 64 by omega),
        show ((4 : UInt64)).toNat = 4 from rfl]
    exact Nat.mod_eq_of_lt (by omega)
  set pLo2 : UInt64 := m4 * gT2.2.1 with hpLo2
  set pLoH2 : UInt64 := mulHi64 m4 gT2.2.1 with hpLoH2
  set pHi2 : UInt64 := m4 * gT2.1 with hpHi2
  set pHiH2 : UInt64 := mulHi64 m4 gT2.1 with hpHiH2
  set pMid2 : UInt64 := pHi2 + pLoH2 with hpMid2
  set pC2 : UInt64 := (if pMid2 < pHi2 then (1 : UInt64) else 0) with hpC2
  set pH2 : UInt64 := pHiH2 + pC2 with hpH2
  set tg2 := add192_192 0 gT2.1 gT2.2.1 0 gT2.1 gT2.2.1 with htg2
  set sbHi2 : UInt64 := (if isIrregular m q = true then 0 else tg2.1) with hsbHi2
  set sbMid2 : UInt64 := (if isIrregular m q = true then gT2.1 else tg2.2.1) with hsbMid2
  set sbLo2 : UInt64 := (if isIrregular m q = true then gT2.2.1 else tg2.2.2) with hsbLo2
  set lB2 := sub192_192 pH2 pMid2 pLo2 sbHi2 sbMid2 sbLo2 with hlB2
  set rB2 := add192_192 pH2 pMid2 pLo2 tg2.1 tg2.2.1 tg2.2.2 with hrB2
  set mH2 := shr1_192 pH2 pMid2 pLo2 with hmH2
  have hG2_lt : gT2.1.toNat * 2 ^ 64 + gT2.2.1.toNat < 2 ^ 128 := by
    have h1 := gT2.1.toNat_lt; have h2 := gT2.2.1.toNat_lt
    grind
  have hmulG2_lt : ∀ b : Nat, b ≤ 4 * m + 2 →
      b * (gT2.1.toNat * 2 ^ 64 + gT2.2.1.toNat) < 2 ^ 192 := by
    intro b hb
    have h3 : b * (gT2.1.toNat * 2 ^ 64 + gT2.2.1.toNat) ≤ 2 ^ 60 * 2 ^ 128 :=
      Nat.mul_le_mul (by omega) (by omega)
    have h4 : (2 : Nat) ^ 60 * 2 ^ 128 < 2 ^ 192 := by
      rw [← Nat.pow_add]
      exact Nat.pow_lt_pow_right (by omega) (by omega)
    omega
  have htrip0G2 : triple192Nat 0 gT2.1 gT2.2.1
      = gT2.1.toNat * 2 ^ 64 + gT2.2.1.toNat := by
    unfold triple192Nat
    simp only [show ((0 : UInt64)).toNat = 0 from rfl]
    omega
  have hP2_val : triple192Nat pH2 pMid2 pLo2
      = 4 * m * (gT2.1.toNat * 2 ^ 64 + gT2.2.1.toNat) := by
    have h := mul192_b_g_toNat m4 gT2.1 gT2.2.1
    simp only [] at h
    rw [← hpLo2, ← hpLoH2, ← hpHi2, ← hpHiH2, ← hpMid2, ← hpC2, ← hpH2] at h
    rw [hm4_toNat, Nat.mod_eq_of_lt (hmulG2_lt (4 * m) (by omega))] at h
    exact h
  have h2G2_val : triple192Nat tg2.1 tg2.2.1 tg2.2.2
      = 2 * (gT2.1.toNat * 2 ^ 64 + gT2.2.1.toNat) := by
    rw [htg2, add192_192_toNat 0 gT2.1 gT2.2.1 0 gT2.1 gT2.2.1 (by
      rw [htrip0G2]; grind), htrip0G2]
    omega
  have hlB2_val : triple192Nat lB2.1 lB2.2.1 lB2.2.2
      = (if isIrregular m q = true then 4 * m - 1 else 4 * m - 2)
          * (gT2.1.toNat * 2 ^ 64 + gT2.2.1.toNat) := by
    rw [hlB2, hsbHi2, hsbMid2, hsbLo2]
    by_cases hirr : isIrregular m q = true
    · rw [if_pos hirr, if_pos hirr, if_pos hirr, if_pos hirr,
          sub192_192_toNat pH2 pMid2 pLo2 0 gT2.1 gT2.2.1 (by
            rw [htrip0G2, hP2_val]
            exact Nat.le_mul_of_pos_left _ (by omega)),
          hP2_val, htrip0G2, Nat.sub_mul, Nat.one_mul]
    · rw [if_neg hirr, if_neg hirr, if_neg hirr, if_neg hirr,
          sub192_192_toNat pH2 pMid2 pLo2 tg2.1 tg2.2.1 tg2.2.2 (by
            rw [h2G2_val, hP2_val]
            exact Nat.mul_le_mul_right _ (by omega)),
          hP2_val, h2G2_val, Nat.sub_mul]
  have hrB2_val : triple192Nat rB2.1 rB2.2.1 rB2.2.2
      = (4 * m + 2) * (gT2.1.toNat * 2 ^ 64 + gT2.2.1.toNat) := by
    rw [hrB2, add192_192_toNat pH2 pMid2 pLo2 tg2.1 tg2.2.1 tg2.2.2 (by
          rw [hP2_val, h2G2_val]
          have := hmulG2_lt (4 * m + 2) (by omega)
          rw [Nat.add_mul] at this
          omega),
        hP2_val, h2G2_val, Nat.add_mul]
  have hmH2_val : triple192Nat mH2.1 mH2.2.1 mH2.2.2
      = 2 * m * (gT2.1.toNat * 2 ^ 64 + gT2.2.1.toNat) := by
    rw [hmH2, shr1_192_toNat, hP2_val,
        show 4 * m * (gT2.1.toNat * 2 ^ 64 + gT2.2.1.toNat)
            = 2 * (2 * m * (gT2.1.toNat * 2 ^ 64 + gT2.2.1.toNat)) from by grind,
        Nat.mul_div_cancel_left _ (by omega)]
  have hk_lo2 : pow10Table128_kMin ≤ -(kOfMQ m q) := by omega
  have hk_hi2 : -(kOfMQ m q) ≤ pow10Table128_kMax := by omega
  match hp : pickNearer_u64_flipped lB2.1 lB2.2.1 lB2.2.2 leftU
               rB2.1 rB2.2.1 rB2.2.2 (m4 + 2) mH2.1 mH2.2.1 mH2.2.2
               (UInt64.ofNat m <<< 1)
               (UInt64.ofNat (-q + gT2.2.2).toNat)
               (UInt64.ofNat (shiftedSig m q (kOfMQ m q))) with
  | none => rw [hp] at hopt; cases hopt
  | some chosen =>
    rw [hp] at hopt
    have hpkd : pickNearer (shiftedSig m q (kOfMQ m q)) (kOfMQ m q) m q = chosen.toNat :=
      pickNearer_u64_flipped_some_eq q (kOfMQ m q) (shiftedSig m q (kOfMQ m q)) m
        (isIrregular m q) chosen lB2.1 lB2.2.1 lB2.2.2 rB2.1 rB2.2.1 rB2.2.2
        mH2.1 mH2.2.1 mH2.2.2
        hm_pos (by omega) hm_lt hs_ge hk_lo2 hk_hi2 hqh2_lo hqh2_hi rfl
        hlB2_val hrB2_val hmH2_val hp
    rw [hpkd]
    cases hopt
    rfl






end Srtfp.Schubfach

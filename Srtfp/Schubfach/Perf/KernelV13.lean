import Srtfp.Schubfach.Perf.KernelV13Flip3
import Srtfp.Tactics

/- v13 — `s` from the boundary product (Giulietti §9 at 128 bits).

   The kernel already computes `P = 4m·g′` (`g′ =` pow10 entry for
   `-(k+1)`) for the flipped interval tests. Since
   `s = ⌊m·2^q·10^(-k)⌋ = ⌊(10m)·g′/2^w⌋` for `w = h′ - q` (the same
   in-window shift), the digit count comes from `5P = P + (P <<< 2)`
   by extracting the top limb — no 192-bit table, no 5-limb multiply.

   Soundness: the existing certified far bound (`band{1,2}_far`, the
   §9.7 sweep at `a = 71`) gives the R20 residue at multiplicand `10m`
   for shift `w ≥ 128`; the reachable window is `w ∈ [127, 131]` with
   `w = 127` only on irregular bands (excluded by the runtime guard,
   falling back to the packed path). -/


namespace Srtfp.Schubfach
/-! ## Biased-window bridges at the `[5198, 5202]` guard -/

theorem wB128_lt (q h : Int) (h1 : ¬ q < -1074) (h2 : ¬ q > 971)
    (hh : -2048 ≤ h ∧ h < 2048) :
    (((UInt64.ofNat (h + 2048).toNat + 4096) - UInt64.ofNat (q + 1074).toNat)
        < (5197 : UInt64)) = (-q + h < 127) := by
  have ht := toNat_tA q h h1 h2 hh
  rw [show (((UInt64.ofNat (h + 2048).toNat + 4096) - UInt64.ofNat (q + 1074).toNat)
        < (5197 : UInt64)) ↔ _ from UInt64.lt_iff_toNat_lt,
      show ((5197 : UInt64)).toNat = 5197 from rfl]
  exact propext (by omega)

theorem wB128_gt (q h : Int) (h1 : ¬ q < -1074) (h2 : ¬ q > 971)
    (hh : -2048 ≤ h ∧ h < 2048) :
    (((UInt64.ofNat (h + 2048).toNat + 4096) - UInt64.ofNat (q + 1074).toNat)
        > (5202 : UInt64)) = (-q + h > 132) := by
  have ht := toNat_tA q h h1 h2 hh
  rw [show (((UInt64.ofNat (h + 2048).toNat + 4096) - UInt64.ofNat (q + 1074).toNat)
        > (5202 : UInt64)) ↔ _ from UInt64.lt_iff_toNat_lt,
      show ((5202 : UInt64)).toNat = 5202 from rfl]
  exact propext (by omega)

theorem wB128_val (q h : Int) (h1 : ¬ q < -1074) (h2 : ¬ q > 971)
    (hh : -2048 ≤ h ∧ h < 2048) (hlo : ¬ -q + h < 127) (hhi : ¬ -q + h > 132) :
    ((UInt64.ofNat (h + 2048).toNat + 4096) - UInt64.ofNat (q + 1074).toNat) - 5197
      = UInt64.ofNat (-q + h - 127).toNat := by
  have ht := toNat_tA q h h1 h2 hh
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_sub_of_le _ _ (by
        rw [UInt64.le_iff_toNat_le, show ((5197 : UInt64)).toNat = 5197 from rfl]
        omega),
      show ((5197 : UInt64)).toNat = 5197 from rfl,
      UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  omega

/-- v12 with `s` from the boundary product: `5P = P + (P <<< 2)`, digit
    count = top limb of `5P` shifted by `uB' - 5197`; window tightened
    to `[5198, 5202]` (`w ∈ [128, 132]`); the 192-bit table, its biased
    windows, and the 5-limb multiply are gone. (v11 with the pickNearer path flipped too: table entry for `-k` at
    biased index `648 - kB`, same `[5134, 5202]` biased window, one
    product `P₂ = 4m·g″` for all fall-through tests, midpoint by exact
    halving. (v8 with the `k+1` interval tests replaced by the flipped scheme:
    table entry for `-(k+1)` at biased index `647 - kB`, window guard
    `uB' = (h'+2048+4096) - qB ∈ [5134, 5202]`, one boundary product
    `P = 4m·g'` shared across `uV`/`wV`, candidate on the shift side. -/
@[inline]
def shortestUnsigned_u64_opt_v13 (mU : UInt64) (qB : UInt64) : Option (UInt64 × Int) :=
  if _h_m0 : mU = 0 then none
  else if _h_m : mU ≥ (9007199254740992 : UInt64) then none
  else if _h_q : qB > 2045 then none
  else
    let irregular := isIrregularB mU qB
    let kB : UInt64 := kBOfMQ mU qB
    if _h_k : kB > 647 then none
    else
      let kBn : Nat := kB.toNat
      let k : Int := (kBn : Int) - 324
      let gT := pow10Table128.getD (647 - kBn) pow10Table128_default
      let uB' : UInt64 := (hB128.getD (647 - kBn) 0 + 4096) - qB
      if _h_qh_lo : uB' < 5197 then none
      else if _h_qh_hi : uB' > 5202 then none
      else
        let w8 : UInt64 := uB' - 5070
        let m4 : UInt64 := mU <<< 2
        let pLo  : UInt64 := m4 * gT.2.1
        let pLoH : UInt64 := mulHi64 m4 gT.2.1
        let pHi  : UInt64 := m4 * gT.1
        let pHiH : UInt64 := mulHi64 m4 gT.1
        let pMidSum : UInt64 := pHi + pLoH
        let pCarry : UInt64 := if pMidSum < pHi then 1 else 0
        let p192Hi : UInt64 := pHiH + pCarry
        let p4 := shl2_192 p192Hi pMidSum pLo
        let p5 := add192_192 p4.1 p4.2.1 p4.2.2 p192Hi pMidSum pLo
        let sU : UInt64 := p5.1 >>> (uB' - 5197)
        if _h_s : sU ≥ (144115188075855872 : UInt64) then none
        else if sU ≥ (10 : UInt64) then
            let sHighU : UInt64 := sU / 10
            let leftU : UInt64 := if irregular then m4 - 1 else m4 - 2
            let rightU : UInt64 := m4 + 2
            let tg := add192_192 0 gT.1 gT.2.1 0 gT.1 gT.2.1
            let sbHi : UInt64 := if irregular then 0 else tg.1
            let sbMid : UInt64 := if irregular then gT.1 else tg.2.1
            let sbLo : UInt64 := if irregular then gT.2.1 else tg.2.2
            let lB := sub192_192 p192Hi pMidSum pLo sbHi sbMid sbLo
            let rB := add192_192 p192Hi pMidSum pLo tg.1 tg.2.1 tg.2.2
            let uV := inRoundingInterval_u64_flipped_u8 lB.1 lB.2.1 lB.2.2 leftU
                        rB.1 rB.2.1 rB.2.2 rightU w8 sHighU
            if uV = inRoundingInterval_u8_AMBIG then none
            else if uV = inRoundingInterval_u8_TRUE then some (sHighU, k + 1)
            else
              let wV := inRoundingInterval_u64_flipped_u8 lB.1 lB.2.1 lB.2.2 leftU
                          rB.1 rB.2.1 rB.2.2 rightU w8 (sHighU + 1)
              if wV = inRoundingInterval_u8_AMBIG then none
              else if wV = inRoundingInterval_u8_TRUE then some (sHighU + 1, k + 1)
              else
                let gT2 := pow10Table128.getD (648 - kBn) pow10Table128_default
                let uC' : UInt64 := (hB128.getD (648 - kBn) 0 + 4096) - qB
                if _h_qh2_lo : uC' < 5134 then none
                else if _h_qh2_hi : uC' > 5202 then none
                else
                  let w28 : UInt64 := uC' - 5070
                  let pLo2  : UInt64 := m4 * gT2.2.1
                  let pLoH2 : UInt64 := mulHi64 m4 gT2.2.1
                  let pHi2  : UInt64 := m4 * gT2.1
                  let pHiH2 : UInt64 := mulHi64 m4 gT2.1
                  let pMidSum2 : UInt64 := pHi2 + pLoH2
                  let pCarry2 : UInt64 := if pMidSum2 < pHi2 then 1 else 0
                  let p192Hi2 : UInt64 := pHiH2 + pCarry2
                  let tg2 := add192_192 0 gT2.1 gT2.2.1 0 gT2.1 gT2.2.1
                  let sbHi2 : UInt64 := if irregular then 0 else tg2.1
                  let sbMid2 : UInt64 := if irregular then gT2.1 else tg2.2.1
                  let sbLo2 : UInt64 := if irregular then gT2.2.1 else tg2.2.2
                  let lB2 := sub192_192 p192Hi2 pMidSum2 pLo2 sbHi2 sbMid2 sbLo2
                  let rB2 := add192_192 p192Hi2 pMidSum2 pLo2 tg2.1 tg2.2.1 tg2.2.2
                  let mH := shr1_192 p192Hi2 pMidSum2 pLo2
                  let twoM : UInt64 := mU <<< 1
                  match pickNearer_u64_flipped lB2.1 lB2.2.1 lB2.2.2 leftU
                          rB2.1 rB2.2.1 rB2.2.2 rightU mH.1 mH.2.1 mH.2.2 twoM w28 sU with
                  | none => none
                  | some chosen => some (chosen, k)
        else if _h_s1 : sU = 0 then none
        else
          let gT2 := pow10Table128.getD (648 - kBn) pow10Table128_default
          let uC' : UInt64 := (hB128.getD (648 - kBn) 0 + 4096) - qB
          if _h_qh2_lo : uC' < 5134 then none
          else if _h_qh2_hi : uC' > 5202 then none
          else
            let w28 : UInt64 := uC' - 5070
            let m4 : UInt64 := mU <<< 2
            let leftU : UInt64 := if irregular then m4 - 1 else m4 - 2
            let rightU : UInt64 := m4 + 2
            let pLo2  : UInt64 := m4 * gT2.2.1
            let pLoH2 : UInt64 := mulHi64 m4 gT2.2.1
            let pHi2  : UInt64 := m4 * gT2.1
            let pHiH2 : UInt64 := mulHi64 m4 gT2.1
            let pMidSum2 : UInt64 := pHi2 + pLoH2
            let pCarry2 : UInt64 := if pMidSum2 < pHi2 then 1 else 0
            let p192Hi2 : UInt64 := pHiH2 + pCarry2
            let tg2 := add192_192 0 gT2.1 gT2.2.1 0 gT2.1 gT2.2.1
            let sbHi2 : UInt64 := if irregular then 0 else tg2.1
            let sbMid2 : UInt64 := if irregular then gT2.1 else tg2.2.1
            let sbLo2 : UInt64 := if irregular then gT2.2.1 else tg2.2.2
            let lB2 := sub192_192 p192Hi2 pMidSum2 pLo2 sbHi2 sbMid2 sbLo2
            let rB2 := add192_192 p192Hi2 pMidSum2 pLo2 tg2.1 tg2.2.1 tg2.2.2
            let mH := shr1_192 p192Hi2 pMidSum2 pLo2
            let twoM : UInt64 := mU <<< 1
            match pickNearer_u64_flipped lB2.1 lB2.2.1 lB2.2.2 leftU
                    rB2.1 rB2.2.1 rB2.2.2 rightU mH.1 mH.2.1 mH.2.2 twoM w28 sU with
            | none => none
            | some chosen => some (chosen, k)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 3200000 in
/-- Arg-biasing transfer: a `some` result of the pure-UInt64 v11 kernel
    is a `some` result of the spec-table flipped kernel. Assembles the
    existing biased-index/window component lemmas. -/
theorem shortestUnsigned_u64_opt_v13_some_eq_flip3 (mU qB : UInt64) (r : UInt64 × Int)
    (hopt : shortestUnsigned_u64_opt_v13 mU qB = some r) :
    shortestUnsigned_u64_opt_flip3 mU.toNat ((qB.toNat : Int) - 1074) = some r := by
  unfold shortestUnsigned_u64_opt_v13 at hopt
  unfold shortestUnsigned_u64_opt_flip3
  by_cases h_m0 : mU = 0
  · rw [dif_pos h_m0] at hopt; cases hopt
  rw [dif_neg h_m0] at hopt
  by_cases h_m : mU ≥ (9007199254740992 : UInt64)
  · rw [dif_pos h_m] at hopt; cases hopt
  rw [dif_neg h_m] at hopt
  rw [dif_neg (show ¬ mU.toNat = 0 from fun hc => h_m0 (by
    apply UInt64.toNat_inj.mp
    rw [hc]; rfl))]
  have h_m' : ¬ mU.toNat ≥ (1 <<< 53 : Nat) := by
    rw [ge_iff_le, UInt64.le_iff_toNat_le,
        show ((9007199254740992 : UInt64)).toNat = 1 <<< 53 from rfl] at h_m
    exact h_m
  rw [dif_neg h_m']
  rw [dif_neg (show ¬ ((qB.toNat : Int) - 1074) < -1074 from by omega)]
  by_cases h_q : qB > 2045
  · rw [dif_pos h_q] at hopt; cases hopt
  rw [dif_neg h_q] at hopt
  have h_q' : qB.toNat ≤ 2045 := by
    rw [gt_iff_lt, UInt64.lt_iff_toNat_lt, show ((2045 : UInt64)).toNat = 2045 from rfl] at h_q
    omega
  rw [dif_neg (show ¬ ((qB.toNat : Int) - 1074) > 971 from by omega)]
  have hkf := kBOfMQ_eq mU qB h_q'
  have hknn := hkf.1
  have hkval := hkf.2
  by_cases h_k : kBOfMQ mU qB > 647
  · rw [dif_pos h_k] at hopt; cases hopt
  rw [dif_neg h_k] at hopt
  have hkB_le : (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) + 324).toNat ≤ 647 := by
    rw [← hkval]
    rw [gt_iff_lt, UInt64.lt_iff_toNat_lt, show ((647 : UInt64)).toNat = 647 from rfl] at h_k
    omega
  have hkMin_lit : pow10Table128_kMin = (-324 : Int) := rfl
  have hkMax_lit : pow10Table128_kMax = (324 : Int) := rfl
  have hklo : ¬ kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) < pow10Table128_kMin := by
    rw [hkMin_lit]; omega
  have hkhi : ¬ kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) + 1 > pow10Table128_kMax := by
    rw [hkMax_lit]; omega
  rw [dif_neg hklo, dif_neg hkhi]
  -- Alignment equations.
  have ekidx : (kBOfMQ mU qB).toNat
      = (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) + 324).toNat := hkval
  have ekexit : (((kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) + 324).toNat : Int)) - 324
      = kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) := by omega
  have eqb : UInt64.ofNat (((qB.toNat : Int) - 1074) + 1074).toNat = qB := by
    rw [show (((qB.toNat : Int) - 1074) + 1074).toNat = qB.toNat from by omega,
        UInt64.ofNat_toNat]
  have em : UInt64.ofNat mU.toNat = mU := UInt64.ofNat_toNat
  have eirr : isIrregular mU.toNat ((qB.toNat : Int) - 1074) = isIrregularB mU qB :=
    (isIrregularB_eq mU qB).symm
  simp only [ekidx, ekexit] at hopt
  -- Index bounds.
  have hiflip : 647 - (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) + 324).toNat
      < pow10Table128.size := by rw [pow10Table128_size_eq]; omega
  have hilow : 648 - (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) + 324).toNat
      < pow10Table128.size := by rw [pow10Table128_size_eq]; omega
  -- Goal side: lookups → getD, ofNat mU.toNat → mU, isIrregular → isIrregularB.
  have eflip := lookup128_negHigh (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074)) hklo hkhi
  have elow := lookup128_neg (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074)) hklo hkhi
  simp only []
  rw [eflip, elow]
  simp only [em, eirr]
  -- hopt side: biased h-tables → ofNat (h + 2048) forms.
  have cflip := hB128_getD _ hiflip
  have clow := hB128_getD _ hilow
  simp only [cflip, clow] at hopt
  -- h bounds at the three entries.
  have hhflip := hBound128_getD _ hiflip
  have hhlow := hBound128_getD _ hilow
  have h_q_lo' : ¬ ((qB.toNat : Int) - 1074) < -1074 := by omega
  have h_q_hi' : ¬ ((qB.toNat : Int) - 1074) > 971 := by omega
  -- Flipped window guards (top-level, tightened to [5198, 5202]).
  have wlt := wB128_lt ((qB.toNat : Int) - 1074) _ h_q_lo' h_q_hi' hhflip
  have wgt := wB128_gt ((qB.toNat : Int) - 1074) _ h_q_lo' h_q_hi' hhflip
  rw [eqb] at wlt wgt
  simp only [wlt, wgt] at hopt
  by_cases hqhlo : -((qB.toNat : Int) - 1074) + (pow10Table128.getD
      (647 - (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) + 324).toNat)
      pow10Table128_default).2.2 < 127
  · rw [dif_pos hqhlo] at hopt; cases hopt
  rw [dif_neg hqhlo] at hopt
  rw [dif_neg hqhlo]
  by_cases hqhhi : -((qB.toNat : Int) - 1074) + (pow10Table128.getD
      (647 - (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) + 324).toNat)
      pow10Table128_default).2.2 > 132
  · rw [dif_pos hqhhi] at hopt; cases hopt
  rw [dif_neg hqhhi] at hopt
  rw [dif_neg hqhhi]
  have hqhlo64 : ¬ -((qB.toNat : Int) - 1074) + (pow10Table128.getD
      (647 - (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) + 324).toNat)
      pow10Table128_default).2.2 < 64 := by omega
  have wval := wB_val ((qB.toNat : Int) - 1074) _ h_q_lo' h_q_hi' hhflip hqhlo64 hqhhi
  rw [eqb] at wval
  rw [wval] at hopt
  have wval197 := wB128_val ((qB.toNat : Int) - 1074) _ h_q_lo' h_q_hi' hhflip hqhlo hqhhi
  rw [eqb] at wval197
  rw [wval197] at hopt
  -- Compact the aligned product pipeline.
  set gTb := (pow10Table128.getD
      (647 - (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) + 324).toNat)
      pow10Table128_default) with hgTb
  set m4b : UInt64 := mU <<< 2 with hm4b
  set pLob : UInt64 := m4b * gTb.2.1 with hpLob
  set pLoHb : UInt64 := mulHi64 m4b gTb.2.1 with hpLoHb
  set pHib : UInt64 := m4b * gTb.1 with hpHib
  set pHiHb : UInt64 := mulHi64 m4b gTb.1 with hpHiHb
  set pMidb : UInt64 := pHib + pLoHb with hpMidb
  set pCb : UInt64 := (if pMidb < pHib then (1 : UInt64) else 0) with hpCb
  set pHb : UInt64 := pHiHb + pCb with hpHb
  set p4b := shl2_192 pHb pMidb pLob with hp4b
  set p5b := add192_192 p4b.1 p4b.2.1 p4b.2.2 pHb pMidb pLob with hp5b
  set sUb : UInt64 := p5b.1 >>> UInt64.ofNat
      (-((qB.toNat : Int) - 1074) + gTb.2.2 - 127).toNat with hsUb
  by_cases h_s : sUb ≥ (144115188075855872 : UInt64)
  · rw [dif_pos h_s] at hopt; cases hopt
  rw [dif_neg h_s] at hopt
  rw [dif_neg h_s]
  -- pickNearer windows propexts (the -k entry).
  have uclt := wB_lt ((qB.toNat : Int) - 1074) _ h_q_lo' h_q_hi' hhlow
  have ucgt := wB_gt ((qB.toNat : Int) - 1074) _ h_q_lo' h_q_hi' hhlow
  rw [eqb] at uclt ucgt
  simp only [uclt, ucgt] at hopt
  by_cases hge10 : sUb ≥ (10 : UInt64)
  · rw [if_pos hge10] at hopt
    rw [if_pos hge10]
    by_cases huc1 : -((qB.toNat : Int) - 1074) + (pow10Table128.getD
        (648 - (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) + 324).toNat)
        pow10Table128_default).2.2 < 64
    · simp only [dif_pos huc1] at hopt ⊢
      exact hopt
    simp only [dif_neg huc1] at hopt ⊢
    by_cases huc2 : -((qB.toNat : Int) - 1074) + (pow10Table128.getD
        (648 - (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) + 324).toNat)
        pow10Table128_default).2.2 > 132
    · simp only [dif_pos huc2] at hopt ⊢
      exact hopt
    simp only [dif_neg huc2] at hopt ⊢
    have ucval := wB_val ((qB.toNat : Int) - 1074) _ h_q_lo' h_q_hi' hhlow huc1 huc2
    rw [eqb] at ucval
    rw [ucval] at hopt
    exact hopt
  · rw [if_neg hge10] at hopt
    rw [if_neg hge10]
    by_cases hs0 : sUb = 0
    · rw [dif_pos hs0] at hopt; cases hopt
    rw [dif_neg hs0] at hopt
    rw [dif_neg hs0]
    by_cases huc1 : -((qB.toNat : Int) - 1074) + (pow10Table128.getD
        (648 - (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) + 324).toNat)
        pow10Table128_default).2.2 < 64
    · simp only [dif_pos huc1] at hopt ⊢
      exact hopt
    simp only [dif_neg huc1] at hopt ⊢
    by_cases huc2 : -((qB.toNat : Int) - 1074) + (pow10Table128.getD
        (648 - (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) + 324).toNat)
        pow10Table128_default).2.2 > 132
    · simp only [dif_pos huc2] at hopt ⊢
      exact hopt
    simp only [dif_neg huc2] at hopt ⊢
    have ucval := wB_val ((qB.toNat : Int) - 1074) _ h_q_lo' h_q_hi' hhlow huc1 huc2
    rw [eqb] at ucval
    rw [ucval] at hopt
    exact hopt

/-! ## Wrapper, exponent range, emit, entry point -/

/-- v13 entry: same packed fallback as v8/v9. -/
@[inline]
def shortestUnsigned_v13 (mU qB : UInt64) : Nat × Int :=
  match shortestUnsigned_u64_opt_v13 mU qB with
  | some (sU, k) => (sU.toNat, k)
  | none => shortestUnsigned_packed mU.toNat ((qB.toNat : Int) - 1074)

theorem shortestUnsigned_v13_eq_packed (mU qB : UInt64) :
    shortestUnsigned_v13 mU qB
      = shortestUnsigned_packed mU.toNat ((qB.toNat : Int) - 1074) := by
  unfold shortestUnsigned_v13
  match h : shortestUnsigned_u64_opt_v13 mU qB with
  | none => rfl
  | some (sU, k) =>
    exact (shortestUnsigned_u64_opt_flip3_some_eq_packed _ _ _ _
      (shortestUnsigned_u64_opt_v13_some_eq_flip3 mU qB (sU, k) h)).symm

set_option maxHeartbeats 1600000 in
/-- Every successful v11 exit carries an exponent in `[-324, 325]`
    (mirror of the v11 one). -/
theorem shortestUnsigned_u64_opt_v13_k_range (mU qB : UInt64)
    (s : UInt64) (k : Int)
    (h : shortestUnsigned_u64_opt_v13 mU qB = some (s, k)) :
    -324 ≤ k ∧ k ≤ 325 := by
  by_cases h1 : mU = 0
  · rw [show shortestUnsigned_u64_opt_v13 mU qB = none from by
      unfold shortestUnsigned_u64_opt_v13; rw [dif_pos h1]] at h
    cases h
  by_cases h2 : mU ≥ (9007199254740992 : UInt64)
  · rw [show shortestUnsigned_u64_opt_v13 mU qB = none from by
      unfold shortestUnsigned_u64_opt_v13; rw [dif_neg h1, dif_pos h2]] at h
    cases h
  by_cases h3 : qB > 2045
  · rw [show shortestUnsigned_u64_opt_v13 mU qB = none from by
      unfold shortestUnsigned_u64_opt_v13; rw [dif_neg h1, dif_neg h2, dif_pos h3]] at h
    cases h
  by_cases h4 : kBOfMQ mU qB > 647
  · rw [show shortestUnsigned_u64_opt_v13 mU qB = none from by
      unfold shortestUnsigned_u64_opt_v13;
        rw [dif_neg h1, dif_neg h2, dif_neg h3, dif_pos h4]] at h
    cases h
  -- Transfer the value to the spec through the chain.
  have hwrap : shortestUnsigned mU.toNat ((qB.toNat : Int) - 1074) = (s.toNat, k) := by
    have h11 : shortestUnsigned_v13 mU qB = (s.toNat, k) := by
      unfold shortestUnsigned_v13
      rw [h]
    rw [← shortestUnsigned_packed_eq, ← shortestUnsigned_v13_eq_packed, h11]
  have hsnd : (shortestUnsigned mU.toNat ((qB.toNat : Int) - 1074)).2 = k := by
    rw [hwrap]
  have hmem : k = kOfMQ mU.toNat ((qB.toNat : Int) - 1074)
      ∨ k = kOfMQ mU.toNat ((qB.toNat : Int) - 1074) + 1 := by
    unfold shortestUnsigned at hsnd
    dsimp only [] at hsnd
    split at hsnd
    · split at hsnd
      · right; exact hsnd.symm
      · split at hsnd
        · right; exact hsnd.symm
        · left; exact hsnd.symm
    · left; exact hsnd.symm
  have hq_le : qB.toNat ≤ 2045 := by
    have := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp h3)
    simpa using this
  have hkof := kBOfMQ_eq mU qB hq_le
  have hk_le : (kBOfMQ mU qB).toNat ≤ 647 := by
    have := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp h4)
    simpa using this
  have hk_hi : kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) ≤ 323 := by
    rw [hkof.2] at hk_le
    omega
  have hkk : kOfMQ mU.toNat ((qB.toNat : Int) - 1074)
      = kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) :=
    congrFun (congrFun kOfMQ_eq_fast_csimp mU.toNat) ((qB.toNat : Int) - 1074)
  have hk_lo := hkof.1
  rcases hmem with rfl | rfl <;> rw [hkk] <;> omega

/-- `emitTail7` over the v13 kernel. -/
@[inline]
def emitTail7 (sign : Bool) (mU qB : UInt64) : String :=
  if mU = 0 then (if sign then "-0" else "0")
  else
    match shortestUnsigned_u64_opt_v13 mU qB with
    | some (sU, exp) =>
      let sig := sU.toNat
      if sig = 0 then (if sign then "-0" else "0")
      else if sig % 10 ≠ 0 then
        emitCheckedIdx sign sig exp
      else
        let (sig', exp') := Srtfp.Decimal.canonicaliseAux sig exp
        if sig' = 0 then (if sign then "-0" else "0")
        else emitChecked sign sig' exp'
    | none =>
      let (sig, exp) := shortestUnsigned_packed mU.toNat ((qB.toNat : Int) - 1074)
      if sig = 0 then (if sign then "-0" else "0")
      else if sig % 10 ≠ 0 then
        emitChecked sign sig exp
      else
        let (sig', exp') := Srtfp.Decimal.canonicaliseAux sig exp
        if sig' = 0 then (if sign then "-0" else "0")
        else emitChecked sign sig' exp'

theorem emitTail7_eq (sign : Bool) (mU qB : UInt64) :
    emitTail7 sign mU qB = emitTail2 sign mU qB := by
  unfold emitTail7 emitTail2
  by_cases h0 : mU = 0
  · rw [if_pos h0, if_pos h0]
  rw [if_neg h0, if_neg h0]
  have h8pk : shortestUnsigned_v8 mU qB
      = shortestUnsigned_packed mU.toNat ((qB.toNat : Int) - 1074) := by
    rw [shortestUnsigned_v8_eq_v7, shortestUnsigned_v7_eq_v5, shortestUnsigned_v5_eq,
        ← shortestUnsigned_packed_eq]
  rw [h8pk]
  cases hv : shortestUnsigned_u64_opt_v13 mU qB with
  | none => rfl
  | some p =>
    obtain ⟨sU, exp⟩ := p
    have hpk : shortestUnsigned_packed mU.toNat ((qB.toNat : Int) - 1074)
        = (sU.toNat, exp) :=
      shortestUnsigned_u64_opt_flip3_some_eq_packed _ _ _ _
        (shortestUnsigned_u64_opt_v13_some_eq_flip3 mU qB (sU, exp) hv)
    rw [hpk]
    have hrange := shortestUnsigned_u64_opt_v13_k_range mU qB sU exp hv
    simp only []
    rw [emitCheckedIdx_eq sign sU.toNat exp hrange.1]

/-- `toStringFast9` over the v13 kernel. -/
@[inline]
def toStringFast9 (f : _root_.Float) : String :=
  let bits := f.toBits
  let expBits : UInt64 := (bits >>> 52) &&& 0x7FF
  let mantBits : UInt64 := bits &&& 0x000F_FFFF_FFFF_FFFF
  if expBits = 0x7FF then
    if mantBits ≠ 0 then "NaN"
    else if (bits >>> 63) ≠ 0 then "-Infinity" else "Infinity"
  else
    emitTail7 (decide (bits >>> 63 ≠ 0))
      (if expBits = 0 then mantBits else mantBits + 4503599627370496)
      (if expBits = 0 then 0 else expBits - 1)

theorem toStringFast9_eq (f : _root_.Float) : toStringFast9 f = toStringFast4 f := by
  unfold toStringFast9 toStringFast4
  simp only [emitTail7_eq]

@[csimp]
theorem floatToStrRef_eq_toStringFast9 : @floatToStrRef = @toStringFast9 := by
  funext f
  rw [toStringFast9_eq]
  exact congrFun floatToStrRef_eq_toStringFast4 f

end Srtfp.Schubfach

/- KernelV13, flip3 kernel: 192-bit shift/top-extract helpers and the
   flip3 kernel definition. The per-leg spec proofs live in the
   KernelV13Flip3Leg* modules — one process each, because elaboration
   memory accumulates across a module's declarations on ≥4.32
   toolchains and the legs are individually multi-GB. -/

import Srtfp.Schubfach.Perf.KernelV13Resid
import Srtfp.Tactics

namespace Srtfp.Schubfach

/-! ## 192-bit shift-left-2 and top-limb extraction -/

/-- `4·` a 192-bit triple (exact when `4·value < 2^192`). -/
@[inline]
def shl2_192 (hi mid lo : UInt64) : UInt64 × UInt64 × UInt64 :=
  ((hi <<< 2) + (mid >>> 62), (mid <<< 2) + (lo >>> 62), lo <<< 2)

theorem shl2_192_toNat (hi mid lo : UInt64)
    (hno : 4 * triple192Nat hi mid lo < 2 ^ 192) :
    triple192Nat (shl2_192 hi mid lo).1 (shl2_192 hi mid lo).2.1
      (shl2_192 hi mid lo).2.2
      = 4 * triple192Nat hi mid lo := by
  unfold shl2_192 triple192Nat
  unfold triple192Nat at hno
  simp only []
  have h1 := hi.toNat_lt; have h2 := mid.toNat_lt; have h3 := lo.toNat_lt
  have h2c : (2 : UInt64) = UInt64.ofNat 2 := rfl
  have h62 : (62 : UInt64) = UInt64.ofNat 62 := rfl
  have eL : (lo <<< (2 : UInt64)).toNat = lo.toNat * 4 % 2 ^ 64 := by
    rw [h2c, UInt64_shl_toNat_lt lo 2 (by omega)]
  have eM : (mid <<< (2 : UInt64)).toNat = mid.toNat * 4 % 2 ^ 64 := by
    rw [h2c, UInt64_shl_toNat_lt mid 2 (by omega)]
  have eH : (hi <<< (2 : UInt64)).toNat = hi.toNat * 4 % 2 ^ 64 := by
    rw [h2c, UInt64_shl_toNat_lt hi 2 (by omega)]
  have eMs : (mid >>> (62 : UInt64)).toNat = mid.toNat / 2 ^ 62 := by
    rw [h62, UInt64_shr_toNat_lt mid 62 (by omega)]
  have eLs : (lo >>> (62 : UInt64)).toNat = lo.toNat / 2 ^ 62 := by
    rw [h62, UInt64_shr_toNat_lt lo 62 (by omega)]
  have hHi4 : hi.toNat * 4 < 2 ^ 64 := by omega
  have m1 : ((hi <<< (2 : UInt64)) + (mid >>> (62 : UInt64))).toNat
      = hi.toNat * 4 % 2 ^ 64 + mid.toNat / 2 ^ 62 := by
    rw [UInt64.toNat_add, eH, eMs, Nat.mod_eq_of_lt (by omega)]
  have m2 : ((mid <<< (2 : UInt64)) + (lo >>> (62 : UInt64))).toNat
      = mid.toNat * 4 % 2 ^ 64 + lo.toNat / 2 ^ 62 := by
    rw [UInt64.toNat_add, eM, eLs, Nat.mod_eq_of_lt (by omega)]
  rw [m1, m2, eL]
  rw [Nat.mod_eq_of_lt (by omega : hi.toNat * 4 < 2 ^ 64)]
  omega

/-- Top-limb extraction: bits `[128 + t, 192)` of a 192-bit triple. -/
theorem triple192_top_extract (hi mid lo : UInt64) (t : Nat)
    (ht : t < 64) :
    (hi >>> (UInt64.ofNat t)).toNat
      = triple192Nat hi mid lo / 2 ^ (128 + t) := by
  rw [UInt64_shr_toNat_lt hi t ht]
  unfold triple192Nat
  have h2 := mid.toNat_lt; have h3 := lo.toNat_lt
  have hsplit : hi.toNat * 2 ^ 128 + mid.toNat * 2 ^ 64 + lo.toNat
      = hi.toNat * 2 ^ 128 + (mid.toNat * 2 ^ 64 + lo.toNat) := by grind
  rw [hsplit]
  have hrem : mid.toNat * 2 ^ 64 + lo.toNat < 2 ^ 128 := by omega
  have hdiv128 : (hi.toNat * 2 ^ 128 + (mid.toNat * 2 ^ 64 + lo.toNat)) / 2 ^ 128
      = hi.toNat := by
    rw [Nat.mul_comm (hi.toNat) (2 ^ 128), Nat.mul_add_div (by omega),
        Nat.div_eq_of_lt hrem]
    omega
  rw [show (128 : Nat) + t = 128 + t from rfl, Nat.pow_add, ← Nat.div_div_eq_div_mul,
      hdiv128]

/-- flip2 with `s` extracted from the boundary product: `5P = P + 4P`,
    digit count = top limb shifted by `w - 127` (licensed by
    `sFromP_floor`, window `[128, 132]`). (Also: the pickNearer path flipped
    too: one product per table entry, all tests on shared boundary
    triples, midpoint by exact halving. Base-level (spec-table) kernel with the Giulietti-style flipped
    `k+1` interval tests: one boundary product `P = 4m·g'` per decode,
    boundary products derived by 192-bit add/sub, candidate on the
    exact-shift side, shared across the `uV`/`wV` tests. Everything
    else matches `shortestUnsigned_u64_opt`. -/
@[inline]
def shortestUnsigned_u64_opt_flip3 (m : Nat) (q : Int) : Option (UInt64 × Int) :=
  if _h_m0 : m = 0 then none
  else if _h_m : m ≥ (1 <<< 53 : Nat) then none
  else if _h_q_lo : q < (-1074 : Int) then none
  else if _h_q_hi : q > 971 then none
  else
    let irregular := isIrregular m q
    let k := kOfMQ_fast m q
    if _h_k_lo : k < pow10Table128_kMin then none
    else if _h_k_hi : k + 1 > pow10Table128_kMax then none
    else
    let mU : UInt64 := UInt64.ofNat m
    let kHigh : Int := k + 1
    let gT := pow10Lookup128 (-kHigh)
    let wPlusH : Int := -q + gT.2.2
    if _h_qh_lo : wPlusH < 127 then none
    else if _h_qh_hi : wPlusH > 132 then none
    else
      let w8 : UInt64 := UInt64.ofNat wPlusH.toNat
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
      let sU : UInt64 := p5.1 >>> (UInt64.ofNat (wPlusH - 127).toNat)
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
          else if uV = inRoundingInterval_u8_TRUE then some (sHighU, kHigh)
          else
            let wV := inRoundingInterval_u64_flipped_u8 lB.1 lB.2.1 lB.2.2 leftU
                        rB.1 rB.2.1 rB.2.2 rightU w8 (sHighU + 1)
            if wV = inRoundingInterval_u8_AMBIG then none
            else if wV = inRoundingInterval_u8_TRUE then some (sHighU + 1, kHigh)
            else
              let gT2 := pow10Lookup128 (-k)
              let w2PlusH : Int := -q + gT2.2.2
              if _h_qh2_lo : w2PlusH < 64 then none
              else if _h_qh2_hi : w2PlusH > 132 then none
              else
                let w28 : UInt64 := UInt64.ofNat w2PlusH.toNat
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
        let gT2 := pow10Lookup128 (-k)
        let w2PlusH : Int := -q + gT2.2.2
        if _h_qh2_lo : w2PlusH < 64 then none
        else if _h_qh2_hi : w2PlusH > 132 then none
        else
          let w28 : UInt64 := UInt64.ofNat w2PlusH.toNat
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


/-! ## Regular bands never reach `w = 127`

A per-`q` table sweep: for every binary64 `q` with the *regular*
Schubfach exponent `k = floorLog10Pow2 q` (and the `-(k+1)` entry in
range), the flipped window satisfies `h' - q ≥ 128`. Hence `w = 127`
occurs only on irregular bands, where `m = 2^52` and the certificate
covers the slack directly. -/


end Srtfp.Schubfach

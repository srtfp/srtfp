/- v9 — shared uV/wV boundary triples.

   In v8, the two `inRoundingInterval_u64_packed_u8` calls (for `sHighU`
   and `sHighU + 1`) each recompute the left/right boundary triples
   `cmpScaledMixed_u64_L leftU/rightU qPlusH8`, although those depend
   only on `(mU, irregular, qPlusH8)`. v9 hoists the two triples out and
   passes them to a precomputed-boundary variant of the interval test,
   saving the recomputation on the two-call path (the triples are needed
   by the first call regardless, so the single-call path pays nothing
   beyond the right-triple on the rare AMBIG short-circuit).

   Proven equal to v8 leaf-by-leaf; `toStringFast5` re-targets the
   `floatToStrRef` `@[csimp]` (CsimpPin asserts the new live pair). -/

import Srtfp.Numeric.Schubfach.Perf.DigitsFast

namespace PP.Numeric.Schubfach

/-- `inRoundingInterval_u64_packed_u8` with the boundary triples
    precomputed by the caller, passed as six scalars (a tuple here would
    cross the call boundary boxed and pay an allocation per call). -/
@[inline]
def inRoundingInterval_u64_pre
    (gHi gLo : UInt64)
    (l_hi_L l_mid_L l_lo_L : UInt64)
    (l_hi_R l_mid_R l_lo_R : UInt64)
    (sU : UInt64) : UInt8 :=
  let s4U : UInt64 := sU <<< 2
  let rLo  : UInt64 := s4U * gLo
  let rLoH : UInt64 := mulHi64 s4U gLo
  let rHi  : UInt64 := s4U * gHi
  let rHiH : UInt64 := mulHi64 s4U gHi
  let midSum   : UInt64 := rHi + rLoH
  let midCarry : UInt64 := if midSum < rHi then 1 else 0
  let r192_hi  : UInt64 := rHiH + midCarry
  let r192_mid : UInt64 := midSum
  let r192_lo  : UInt64 := rLo
  let cmpL := cmpVerdict_u64_inner l_hi_L l_mid_L l_lo_L r192_hi r192_mid r192_lo s4U
  if cmpL = 0 then inRoundingInterval_u8_AMBIG
  else
    let cmpR := cmpVerdict_u64_inner l_hi_R l_mid_R l_lo_R r192_hi r192_mid r192_lo s4U
    if cmpR = 0 then inRoundingInterval_u8_AMBIG
    else
      if cmpL < 0 && cmpR > 0 then inRoundingInterval_u8_TRUE
      else inRoundingInterval_u8_FALSE

theorem inRoundingInterval_u64_pre_eq
    (gHi gLo qPlusH8 sU mU : UInt64) (irregular : Bool) :
    (let (l_hi_L, l_mid_L, l_lo_L) := cmpScaledMixed_u64_L
        (if irregular then (mU <<< 2) - 1 else (mU <<< 2) - 2) qPlusH8
     let (l_hi_R, l_mid_R, l_lo_R) := cmpScaledMixed_u64_L ((mU <<< 2) + 2) qPlusH8
     inRoundingInterval_u64_pre gHi gLo l_hi_L l_mid_L l_lo_L l_hi_R l_mid_R l_lo_R sU)
      = inRoundingInterval_u64_packed_u8 gHi gLo qPlusH8 sU mU irregular := by
  unfold inRoundingInterval_u64_pre inRoundingInterval_u64_packed_u8
  rfl

/-- v8 with the boundary triples shared across the `uV`/`wV` calls. -/
@[inline]
def shortestUnsigned_u64_opt_v9 (mU : UInt64) (qB : UInt64) : Option (UInt64 × Int) :=
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
      let sigTuple := pow10Table192.getD (648 - kBn) pow10Table192_default
      let tA : UInt64 := (hB192.getD (648 - kBn) 0 + 4096) - qB
      let s : Nat :=
        if _h_s_lo : tA < 5258 then
          shiftedSig mU.toNat ((qB.toNat : Int) - 1074) k
        else if _h_s_hi : tA ≥ 5326 then
          shiftedSig mU.toNat ((qB.toNat : Int) - 1074) k
        else
          (shiftedSig_u192_kernel mU sigTuple.1 sigTuple.2.1
            sigTuple.2.2.1 (tA - 5070)).toNat
      if _h_s : s ≥ (1 <<< 57 : Nat) then none
      else
        let sU : UInt64 := UInt64.ofNat s
        if sU ≥ (10 : UInt64) then
          let cmpTupleH := pow10Table128.getD (kBn + 1) pow10Table128_default
          let uB : UInt64 := qB + hB128.getD (kBn + 1) 0
          if _h_qh_lo : uB < 3186 then none
          else if _h_qh_hi : uB > 3254 then none
          else
            let cmpHQPlusH8 : UInt64 := uB - 3122
            let sHighU : UInt64 := sU / 10
            -- Shared boundary triples (independent of the digit candidate),
            -- destructured at the binding site so they stay scalar.
            let (lhL, lmL, llL) := cmpScaledMixed_u64_L
              (if irregular then (mU <<< 2) - 1 else (mU <<< 2) - 2) cmpHQPlusH8
            let (lhR, lmR, llR) := cmpScaledMixed_u64_L ((mU <<< 2) + 2) cmpHQPlusH8
            let uV := inRoundingInterval_u64_pre cmpTupleH.1 cmpTupleH.2.1
                        lhL lmL llL lhR lmR llR sHighU
            if uV = inRoundingInterval_u8_AMBIG then none
            else if uV = inRoundingInterval_u8_TRUE then some (sHighU, k + 1)
            else
              let wV := inRoundingInterval_u64_pre cmpTupleH.1 cmpTupleH.2.1
                          lhL lmL llL lhR lmR llR (sHighU + 1)
              if wV = inRoundingInterval_u8_AMBIG then none
              else if wV = inRoundingInterval_u8_TRUE then some (sHighU + 1, k + 1)
              else
                let cmpTuple := pow10Table128.getD kBn pow10Table128_default
                let uC : UInt64 := qB + hB128.getD kBn 0
                if _h_qh2_lo : uC < 3186 then none
                else if _h_qh2_hi : uC > 3254 then none
                else
                  let cmpQPlusH8 : UInt64 := uC - 3122
                  match pickNearer_u64_opt cmpTuple.1 cmpTuple.2.1 cmpQPlusH8 sU mU irregular with
                  | none => none
                  | some chosen => some (chosen, k)
        else if _h_s1 : sU = 0 then none
        else
          let cmpTuple := pow10Table128.getD kBn pow10Table128_default
          let uC : UInt64 := qB + hB128.getD kBn 0
          if _h_qh2_lo : uC < 3186 then none
          else if _h_qh2_hi : uC > 3254 then none
          else
            let cmpQPlusH8 : UInt64 := uC - 3122
            match pickNearer_u64_opt cmpTuple.1 cmpTuple.2.1 cmpQPlusH8 sU mU irregular with
            | none => none
            | some chosen => some (chosen, k)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1600000 in
theorem shortestUnsigned_u64_opt_v9_eq_v8 (mU qB : UInt64) :
    shortestUnsigned_u64_opt_v9 mU qB = shortestUnsigned_u64_opt_v8 mU qB := by
  unfold shortestUnsigned_u64_opt_v9 shortestUnsigned_u64_opt_v8
  simp only []
  rfl

/-- v9 entry: same fallback as v8. -/
@[inline]
def shortestUnsigned_v9 (mU qB : UInt64) : Nat × Int :=
  match shortestUnsigned_u64_opt_v9 mU qB with
  | some (sU, k) => (sU.toNat, k)
  | none => shortestUnsigned_packed mU.toNat ((qB.toNat : Int) - 1074)

theorem shortestUnsigned_v9_eq_v8 (mU qB : UInt64) :
    shortestUnsigned_v9 mU qB = shortestUnsigned_v8 mU qB := by
  unfold shortestUnsigned_v9 shortestUnsigned_v8
  rw [shortestUnsigned_u64_opt_v9_eq_v8]
  rfl

/-- `emitTail2` over the v9 kernel. -/
@[inline]
def emitTail3 (sign : Bool) (mU qB : UInt64) : String :=
  if mU = 0 then (if sign then "-0" else "0")
  else
    let (sig, exp) := shortestUnsigned_v9 mU qB
    if sig = 0 then (if sign then "-0" else "0")
    else if sig % 10 ≠ 0 then
      emitChecked sign sig exp
    else
      let (sig', exp') := PP.Numeric.Decimal.canonicaliseAux sig exp
      if sig' = 0 then (if sign then "-0" else "0")
      else emitChecked sign sig' exp'

theorem emitTail3_eq (sign : Bool) (mU qB : UInt64) :
    emitTail3 sign mU qB = emitTail2 sign mU qB := by
  unfold emitTail3 emitTail2
  rw [shortestUnsigned_v9_eq_v8]

/-- `toStringFast4` over the v9 kernel. -/
@[inline]
def toStringFast5 (f : _root_.Float) : String :=
  let bits := f.toBits
  let expBits : UInt64 := (bits >>> 52) &&& 0x7FF
  let mantBits : UInt64 := bits &&& 0x000F_FFFF_FFFF_FFFF
  if expBits = 0x7FF then
    if mantBits ≠ 0 then "NaN"
    else if (bits >>> 63) ≠ 0 then "-Infinity" else "Infinity"
  else
    emitTail3 (decide (bits >>> 63 ≠ 0))
      (if expBits = 0 then mantBits else mantBits + 4503599627370496)
      (if expBits = 0 then 0 else expBits - 1)

theorem toStringFast5_eq (f : _root_.Float) : toStringFast5 f = toStringFast4 f := by
  unfold toStringFast5 toStringFast4
  simp only [emitTail3_eq]

@[csimp]
theorem floatToStrRef_eq_toStringFast5 : @floatToStrRef = @toStringFast5 := by
  funext f
  rw [toStringFast5_eq]
  exact congrFun floatToStrRef_eq_toStringFast4 f

end PP.Numeric.Schubfach

module
/- PROTOTYPE — UNVERIFIED, NOT REGISTERED. Do not import from `Srtfp.Perf`.

   v14: the v13 kernel with every boxed value removed from the hot path.
   Measured purpose only (benches/profiling/BenchProfile.lean): it puts a
   number on how much of the v13 kernel's time is Lean's boxing model
   rather than arithmetic. Differences from `shortestUnsigned_u64_opt_v13`:

   * verdicts are `UInt8` (0 ambiguous, 1 greater, 2 less) instead of `Int`
     (`-1`/`0`/`1` as boxed `Int` scalars, compared through
     `lean_int_dec_lt` / `lean_int_dec_eq`, and `-1` built by `lean_int_neg`
     at runtime);
   * the decimal exponent travels as the biased table index
     `kB = k + 324 : UInt64` (which the emit indexes `expTable` with
     directly) instead of `k : Int` (`lean_nat_to_int`, `lean_int_sub`,
     `lean_int_add`, `Int.toNat` per call);
   * `mulHi64 aU (1 <<< s)` (four 32×32 multiplies) is the shift
     `aU >>> (64 - s)` it computes;
   * the trailing-zero test runs on the `UInt64` significand.

   Everything else (table entries, window guards, 192-bit boundary
   products, flipped interval tests, tie-break) is v13 verbatim, so a
   proof of `shortestUnsigned_u64_opt_v14 mU qB = (shortestUnsigned_u64_opt_v13 mU qB).map (biased)`
   would be a leaf-by-leaf transfer in the style of
   `shortestUnsigned_u64_opt_v13_some_eq_flip3`. Not attempted here. -/

public import Srtfp.Perf.KernelV13

@[expose] public section

namespace Srtfp.Schubfach

/-! ## Unboxed verdicts -/

/-- `cmpScaledMixed_u64_L` with the `s < 64` leg's multiply-high replaced by
    the shift it computes (`mulHi64 aU (1 <<< s) = aU >>> (64 - s)` for
    `0 < s < 64`, `0` for `s = 0`). -/
@[inline]
def cmpScaledMixed_u64_L_v14 (aU : UInt64) (s : UInt64) : UInt64 × UInt64 × UInt64 :=
  if s < 64 then
    if s = 0 then (0, 0, aU) else (0, aU >>> (64 - s), aU <<< s)
  else if s < 128 then
    let s64 := s - 64
    if s64 = 0 then (0, aU, 0)
    else (aU >>> (64 - s64), aU <<< s64, 0)
  else
    let s64 := s - 128
    if s64 = 0 then (aU, 0, 0)
    else (aU <<< s64, 0, 0)

/-- `cmpVerdict_u64_inner` with a `UInt8` verdict: `1` for `L > R`,
    `2` for `L + b ≤ R`, `0` ambiguous. -/
@[inline]
def cmpVerdict_u8 (l_hi l_mid l_lo r_hi r_mid r_lo bU : UInt64) : UInt8 :=
  if gt192 l_hi l_mid l_lo r_hi r_mid r_lo then 1
  else
    let (lpb_hi, lpb_mid, lpb_lo) := add192_64 l_hi l_mid l_lo bU
    if le192 lpb_hi lpb_mid lpb_lo r_hi r_mid r_lo then 2
    else 0

/-- `inRoundingInterval_u64_flipped_u8` over `cmpVerdict_u8`. -/
@[inline]
def inRoundingInterval_v14
    (lLHi lLMid lLLo leftU lRHi lRMid lRLo rightU : UInt64)
    (w8 sU : UInt64) : UInt8 :=
  let s4U : UInt64 := sU <<< 2
  let (cHi, cMid, cLo) := cmpScaledMixed_u64_L_v14 s4U w8
  let cmpLf := cmpVerdict_u8 cHi cMid cLo lLHi lLMid lLLo leftU
  if cmpLf = 0 then inRoundingInterval_u8_AMBIG
  else
    let cmpRf := cmpVerdict_u8 cHi cMid cLo lRHi lRMid lRLo rightU
    if cmpRf = 0 then inRoundingInterval_u8_AMBIG
    else if cmpLf = 1 && cmpRf = 2 then inRoundingInterval_u8_TRUE
    else inRoundingInterval_u8_FALSE

/-- `pickNearer_u64_flipped` over `UInt8` verdicts. -/
@[inline]
def pickNearer_v14
    (lLHi lLMid lLLo leftU lRHi lRMid lRLo rightU : UInt64)
    (mHHi mHMid mHLo twoM : UInt64)
    (w8 sU : UInt64) : Option UInt64 :=
  let uV := inRoundingInterval_v14 lLHi lLMid lLLo leftU lRHi lRMid lRLo rightU w8 sU
  if uV = inRoundingInterval_u8_AMBIG then none
  else
    let wV := inRoundingInterval_v14 lLHi lLMid lLLo leftU lRHi lRMid lRLo rightU w8 (sU + 1)
    if wV = inRoundingInterval_u8_AMBIG then none
    else
      let uIn : Bool := uV = inRoundingInterval_u8_TRUE
      let wIn : Bool := wV = inRoundingInterval_u8_TRUE
      if uIn && !wIn then some sU
      else if !uIn && wIn then some (sU + 1)
      else
        let (cHi, cMid, cLo) := cmpScaledMixed_u64_L_v14 ((sU <<< 1) + 1) w8
        let cmpMf := cmpVerdict_u8 cHi cMid cLo mHHi mHMid mHLo twoM
        if cmpMf = 0 then none
        else if cmpMf = 1 then some sU
        else some (sU + 1)

/-! ## The kernel: v13 with a biased `UInt64` exponent -/

/-- Returns `(sU, kB)` with `kB = exp + 324`, the `expTable` index. -/
@[inline]
def shortestUnsigned_u64_opt_v14 (mU : UInt64) (qB : UInt64) : Option (UInt64 × UInt64) :=
  if mU = 0 then none
  else if mU ≥ (9007199254740992 : UInt64) then none
  else if qB > 2045 then none
  else
    let irregular := isIrregularB mU qB
    let kB : UInt64 := kBOfMQ mU qB
    if kB > 647 then none
    else
      let kBn : Nat := kB.toNat
      let gT := pow10Table128.getD (647 - kBn) pow10Table128_default
      let uB' : UInt64 := (hB128.getD (647 - kBn) 0 + 4096) - qB
      if uB' < 5197 then none
      else if uB' > 5202 then none
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
        if sU ≥ (144115188075855872 : UInt64) then none
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
            let uV := inRoundingInterval_v14 lB.1 lB.2.1 lB.2.2 leftU
                        rB.1 rB.2.1 rB.2.2 rightU w8 sHighU
            if uV = inRoundingInterval_u8_AMBIG then none
            else if uV = inRoundingInterval_u8_TRUE then some (sHighU, kB + 1)
            else
              let wV := inRoundingInterval_v14 lB.1 lB.2.1 lB.2.2 leftU
                          rB.1 rB.2.1 rB.2.2 rightU w8 (sHighU + 1)
              if wV = inRoundingInterval_u8_AMBIG then none
              else if wV = inRoundingInterval_u8_TRUE then some (sHighU + 1, kB + 1)
              else
                let gT2 := pow10Table128.getD (648 - kBn) pow10Table128_default
                let uC' : UInt64 := (hB128.getD (648 - kBn) 0 + 4096) - qB
                if uC' < 5134 then none
                else if uC' > 5202 then none
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
                  match pickNearer_v14 lB2.1 lB2.2.1 lB2.2.2 leftU
                          rB2.1 rB2.2.1 rB2.2.2 rightU mH.1 mH.2.1 mH.2.2 twoM w28 sU with
                  | none => none
                  | some chosen => some (chosen, kB)
        else if sU = 0 then none
        else
          let gT2 := pow10Table128.getD (648 - kBn) pow10Table128_default
          let uC' : UInt64 := (hB128.getD (648 - kBn) 0 + 4096) - qB
          if uC' < 5134 then none
          else if uC' > 5202 then none
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
            match pickNearer_v14 lB2.1 lB2.2.1 lB2.2.2 leftU
                    rB2.1 rB2.2.1 rB2.2.2 rightU mH.1 mH.2.1 mH.2.2 twoM w28 sU with
            | none => none
            | some chosen => some (chosen, kB)

/-! ## Emit over the biased index -/

/-- `emitCheckedIdx` with the `expTable` index supplied directly. -/
@[inline]
def emitIdx (sign : Bool) (sig : Nat) (idx : Nat) : String :=
  if h : idx ≤ 616 then
    let core := toString sig ++ expTable[idx]'(by rw [expTable_size]; omega)
    if sign then "-" ++ core else core
  else
    (if sign then "-" else "") ++ toString sig ++ "e" ++ intToStrRef ((idx : Int) - 324)

/-- `emitTail7` over the v14 kernel. -/
@[inline]
def emitTail8 (sign : Bool) (mU qB : UInt64) : String :=
  if mU = 0 then (if sign then "-0" else "0")
  else
    match shortestUnsigned_u64_opt_v14 mU qB with
    | some (sU, kB) =>
      if sU % 10 ≠ 0 then
        emitIdx sign sU.toNat kB.toNat
      else
        let (sig', exp') := Srtfp.Decimal.canonicaliseAux sU.toNat ((kB.toNat : Int) - 324)
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

/-- `toStringFast9` over the v14 kernel. PROTOTYPE: not proven, not registered. -/
@[inline]
def toStringFast10 (f : _root_.Float) : String :=
  let bits := f.toBits
  let expBits : UInt64 := (bits >>> 52) &&& 0x7FF
  let mantBits : UInt64 := bits &&& 0x000F_FFFF_FFFF_FFFF
  if expBits = 0x7FF then
    if mantBits ≠ 0 then "NaN"
    else if (bits >>> 63) ≠ 0 then "-Infinity" else "Infinity"
  else
    emitTail8 (decide (bits >>> 63 ≠ 0))
      (if expBits = 0 then mantBits else mantBits + 4503599627370496)
      (if expBits = 0 then 0 else expBits - 1)

/-- Kernel-only entry for the profiler: `(sU, kB)` or the packed fallback. -/
@[inline]
def shortestUnsigned_v14 (mU qB : UInt64) : UInt64 × UInt64 :=
  match shortestUnsigned_u64_opt_v14 mU qB with
  | some p => p
  | none =>
    let (s, k) := shortestUnsigned_packed mU.toNat ((qB.toNat : Int) - 1074)
    (UInt64.ofNat s, UInt64.ofNat (k + 324).toNat)

end Srtfp.Schubfach

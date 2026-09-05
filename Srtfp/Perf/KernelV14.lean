module
/- v14 — the v13 kernel with no boxed value on the hot path.

   Same table entries, window guards, 192-bit boundary products, flipped
   interval tests and tie-break as `shortestUnsigned_u64_opt_v13`; the
   differences are representational:

   * verdicts are `UInt8` (0 ambiguous, 1 greater, 2 less) instead of
     `Int` (`-1`/`0`/`1` as boxed scalars, `-1` built at runtime);
   * the decimal exponent travels as the biased table index
     `kB = k + 324 : UInt64`, which the emit indexes `expTable` with
     directly, instead of `k : Int`;
   * the `s < 64` leg of `cmpScaledMixed_u64_L` computes the shift
     `aU >>> (64 - s)` instead of `mulHi64 aU (1 <<< s)`;
   * the trailing-zero test runs on the `UInt64` significand.

   Verified by a leaf-by-leaf transfer to v13:
   `shortestUnsigned_u64_opt_v14_some_eq_v13` lifts every `some` exit to
   the v13 exit with the unbiased exponent, so `toStringFast10` and
   `toDecimal_v14` ride the v13 correctness chain and are registered as
   the live `@[csimp]` rewrites (pinned in `CsimpPin.lean`). -/

public import Srtfp.Perf.KernelV13
public import Srtfp.Perf.DecimalV13

@[expose] public section

open Float.Model.UnpackedFloat (Sign)

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
def emitIdx (sign : Sign) (sig : Nat) (idx : Nat) : String :=
  if h : idx ≤ 616 then
    let core := toString sig ++ expTable[idx]'(by rw [expTable_size]; omega)
    withSign sign core
  else
    withSign sign (toString sig ++ "e" ++ intToStrRef ((idx : Int) - 324))

/-- `emitTail7` over the v14 kernel. -/
@[inline]
def emitTail8 (sign : Sign) (mU qB : UInt64) : String :=
  if mU = 0 then withSign sign "0"
  else
    match shortestUnsigned_u64_opt_v14 mU qB with
    | some (sU, kB) =>
      if sU % 10 ≠ 0 then
        emitIdx sign sU.toNat kB.toNat
      else
        let (sig', exp') := Srtfp.Decimal.canonicaliseAux sU.toNat ((kB.toNat : Int) - 324)
        if sig' = 0 then withSign sign "0"
        else emitChecked sign sig' exp'
    | none =>
      let (sig, exp) := shortestUnsigned_packed mU.toNat ((qB.toNat : Int) - 1074)
      if sig = 0 then withSign sign "0"
      else if sig % 10 ≠ 0 then
        emitChecked sign sig exp
      else
        let (sig', exp') := Srtfp.Decimal.canonicaliseAux sig exp
        if sig' = 0 then withSign sign "0"
        else emitChecked sign sig' exp'

/-- `toStringFast9` over the v14 kernel. -/
@[inline]
def toStringFast10 (f : _root_.Float) : String :=
  let bits := f.toBits
  let expBits : UInt64 := (bits >>> 52) &&& 0x7FF
  let mantBits : UInt64 := bits &&& 0x000F_FFFF_FFFF_FFFF
  if expBits = 0x7FF then
    if mantBits ≠ 0 then "NaN"
    else if (bits >>> 63) ≠ 0 then "-Infinity" else "Infinity"
  else
    emitTail8 (if bits >>> 63 = 0 then .positive else .negative)
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

/-! ## Leaf transfers to v13 -/

theorem cmpScaledMixed_u64_L_v14_eq (aU s : UInt64) :
    cmpScaledMixed_u64_L_v14 aU s = cmpScaledMixed_u64_L aU s := by
  unfold cmpScaledMixed_u64_L_v14 cmpScaledMixed_u64_L
  by_cases hs : s < 64
  · rw [if_pos hs, if_pos hs]
    have hs' : s.toNat < 64 := by
      rw [UInt64.lt_iff_toNat_lt] at hs; exact hs
    by_cases hs0 : s = 0
    · rw [if_pos hs0]
      subst hs0
      have h1 : mulHi64 aU (1 <<< (0 : UInt64)) = 0 := by
        apply UInt64.toNat_inj.mp
        rw [mulHi64_toNat_eq, show ((1 : UInt64) <<< (0 : UInt64)) = 1 from rfl,
            show ((1 : UInt64)).toNat = 1 from rfl, Nat.mul_one,
            show ((0 : UInt64)).toNat = 0 from rfl]
        exact Nat.div_eq_of_lt aU.toNat_lt
      have h2 : aU <<< (0 : UInt64) = aU := by
        apply UInt64.toNat_inj.mp
        rw [UInt64.toNat_shiftLeft, show ((0 : UInt64)).toNat = 0 from rfl]
        simp [Nat.mod_eq_of_lt aU.toNat_lt]
      rw [h1, h2]
    · rw [if_neg hs0]
      have hpos : 0 < s.toNat := by
        rcases Nat.eq_zero_or_pos s.toNat with h | h
        · exact absurd (UInt64.toNat_inj.mp (by rw [h]; rfl)) hs0
        · exact h
      have h1 : aU >>> (64 - s) = mulHi64 aU (1 <<< s) := by
        apply UInt64.toNat_inj.mp
        have hle : s ≤ 64 := by
          rw [UInt64.le_iff_toNat_le, show ((64 : UInt64)).toNat = 64 from rfl]; omega
        rw [mulHi64_toNat_eq, UInt64.toNat_shiftRight, UInt64.toNat_shiftLeft,
            UInt64.toNat_sub_of_le _ _ hle,
            show ((64 : UInt64)).toNat = 64 from rfl, show ((1 : UInt64)).toNat = 1 from rfl,
            Nat.mod_eq_of_lt (show 64 - s.toNat < 64 by omega),
            Nat.mod_eq_of_lt hs', Nat.shiftLeft_eq, Nat.one_mul,
            Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hs'),
            Nat.shiftRight_eq_div_pow]
        have h64 : (2 : Nat) ^ 64 = 2 ^ s.toNat * 2 ^ (64 - s.toNat) := by
          rw [← Nat.pow_add]; congr 1; omega
        rw [h64, Nat.mul_comm aU.toNat, Nat.mul_div_mul_left _ _ (Nat.two_pow_pos _)]
      rw [h1]
  · rw [if_neg hs, if_neg hs]

/-- The `UInt8` verdict decides the `Int` verdict: `0 ↔ 0`, `1 ↔ 1`,
    `2 ↔ -1`. -/
theorem cmpVerdict_u8_cases (l_hi l_mid l_lo r_hi r_mid r_lo bU : UInt64) :
    (cmpVerdict_u8 l_hi l_mid l_lo r_hi r_mid r_lo bU = 0
        ∧ cmpVerdict_u64_inner l_hi l_mid l_lo r_hi r_mid r_lo bU = 0)
    ∨ (cmpVerdict_u8 l_hi l_mid l_lo r_hi r_mid r_lo bU = 1
        ∧ cmpVerdict_u64_inner l_hi l_mid l_lo r_hi r_mid r_lo bU = 1)
    ∨ (cmpVerdict_u8 l_hi l_mid l_lo r_hi r_mid r_lo bU = 2
        ∧ cmpVerdict_u64_inner l_hi l_mid l_lo r_hi r_mid r_lo bU = -1) := by
  unfold cmpVerdict_u8 cmpVerdict_u64_inner
  by_cases hg : gt192 l_hi l_mid l_lo r_hi r_mid r_lo = true
  · simp only [if_pos hg]
    decide
  · simp only [if_neg hg]
    obtain ⟨a, b, c⟩ := add192_64 l_hi l_mid l_lo bU
    simp only []
    by_cases hl : le192 a b c r_hi r_mid r_lo = true
    · simp only [if_pos hl]
      decide
    · simp only [if_neg hl]
      decide

theorem inRoundingInterval_v14_eq
    (lLHi lLMid lLLo leftU lRHi lRMid lRLo rightU w8 sU : UInt64) :
    inRoundingInterval_v14 lLHi lLMid lLLo leftU lRHi lRMid lRLo rightU w8 sU
      = inRoundingInterval_u64_flipped_u8 lLHi lLMid lLLo leftU lRHi lRMid lRLo rightU w8 sU := by
  unfold inRoundingInterval_v14 inRoundingInterval_u64_flipped_u8
  simp only [cmpScaledMixed_u64_L_v14_eq]
  obtain ⟨cHi, cMid, cLo⟩ := cmpScaledMixed_u64_L (sU <<< 2) w8
  simp only []
  rcases cmpVerdict_u8_cases cHi cMid cLo lLHi lLMid lLLo leftU
      with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rcases cmpVerdict_u8_cases cHi cMid cLo lRHi lRMid lRLo rightU
      with ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
    simp [h1, h2, h3, h4, inRoundingInterval_u8_AMBIG, inRoundingInterval_u8_TRUE,
      inRoundingInterval_u8_FALSE]

theorem pickNearer_v14_eq
    (lLHi lLMid lLLo leftU lRHi lRMid lRLo rightU mHHi mHMid mHLo twoM w8 sU : UInt64) :
    pickNearer_v14 lLHi lLMid lLLo leftU lRHi lRMid lRLo rightU mHHi mHMid mHLo twoM w8 sU
      = pickNearer_u64_flipped lLHi lLMid lLLo leftU lRHi lRMid lRLo rightU
          mHHi mHMid mHLo twoM w8 sU := by
  unfold pickNearer_v14 pickNearer_u64_flipped cmpScaledMixed_u64_flipped
  simp only [inRoundingInterval_v14_eq, cmpScaledMixed_u64_L_v14_eq]
  obtain ⟨cHi, cMid, cLo⟩ := cmpScaledMixed_u64_L ((sU <<< 1) + 1) w8
  simp only []
  rcases cmpVerdict_u8_cases cHi cMid cLo mHHi mHMid mHLo twoM
      with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    simp [h1, h2]

/-! ## The kernel transfer -/

private theorem some_pair_congr {α β : Type} (a : α) {b c : β} (h : b = c) :
    some (a, b) = some (a, c) := by rw [h]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 3200000 in
/-- Every `some` exit of v14 is the v13 exit with the exponent unbiased:
    the guards and products coincide syntactically once the leaves are
    rewritten, so this is a walk down the shared decision tree. -/
theorem shortestUnsigned_u64_opt_v14_some_eq_v13 (mU qB sU kB : UInt64)
    (hopt : shortestUnsigned_u64_opt_v14 mU qB = some (sU, kB)) :
    shortestUnsigned_u64_opt_v13 mU qB = some (sU, (kB.toNat : Int) - 324) := by
  unfold shortestUnsigned_u64_opt_v14 at hopt
  unfold shortestUnsigned_u64_opt_v13
  simp only [inRoundingInterval_v14_eq, pickNearer_v14_eq] at hopt
  by_cases h_m0 : mU = 0
  · rw [if_pos h_m0] at hopt; cases hopt
  rw [if_neg h_m0] at hopt
  rw [dif_neg h_m0]
  by_cases h_m : mU ≥ (9007199254740992 : UInt64)
  · rw [if_pos h_m] at hopt; cases hopt
  rw [if_neg h_m] at hopt
  rw [dif_neg h_m]
  by_cases h_q : qB > 2045
  · rw [if_pos h_q] at hopt; cases hopt
  rw [if_neg h_q] at hopt
  rw [dif_neg h_q]
  by_cases h_k : kBOfMQ mU qB > 647
  · rw [if_pos h_k] at hopt; cases hopt
  rw [if_neg h_k] at hopt
  rw [dif_neg h_k]
  have hk1 : ((kBOfMQ mU qB + 1).toNat : Int) = ((kBOfMQ mU qB).toNat : Int) + 1 := by
    rw [gt_iff_lt, UInt64.lt_iff_toNat_lt, show ((647 : UInt64)).toNat = 647 from rfl] at h_k
    rw [UInt64.toNat_add, show ((1 : UInt64)).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
    omega
  -- Zeta-expand the goal to hopt's shape, then name the shared subterms
  -- so the guards are short.
  simp (config := { maxSteps := 4000000 }) only []
  set gTb := pow10Table128.getD (647 - (kBOfMQ mU qB).toNat) pow10Table128_default with hgTb
  set uBb : UInt64 := hB128.getD (647 - (kBOfMQ mU qB).toNat) 0 + 4096 - qB with huBb
  by_cases h_lo : uBb < 5197
  · rw [if_pos h_lo] at hopt; cases hopt
  rw [if_neg h_lo] at hopt
  rw [dif_neg h_lo]
  by_cases h_hi : uBb > 5202
  · rw [if_pos h_hi] at hopt; cases hopt
  rw [if_neg h_hi] at hopt
  rw [dif_neg h_hi]
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
  set sUb : UInt64 := p5b.1 >>> (uBb - 5197) with hsUb
  by_cases h_s : sUb ≥ (144115188075855872 : UInt64)
  · rw [if_pos h_s] at hopt; cases hopt
  rw [if_neg h_s] at hopt
  rw [dif_neg h_s]
  set irr := isIrregularB mU qB with hirr
  set leftUb : UInt64 := (if irr = true then m4b - 1 else m4b - 2) with hleftUb
  set rightUb : UInt64 := m4b + 2 with hrightUb
  set tgb := add192_192 0 gTb.1 gTb.2.1 0 gTb.1 gTb.2.1 with htgb
  set lBb := sub192_192 pHb pMidb pLob (if irr = true then 0 else tgb.1)
      (if irr = true then gTb.1 else tgb.2.1) (if irr = true then gTb.2.1 else tgb.2.2) with hlBb
  set rBb := add192_192 pHb pMidb pLob tgb.1 tgb.2.1 tgb.2.2 with hrBb
  set uCb : UInt64 := hB128.getD (648 - (kBOfMQ mU qB).toNat) 0 + 4096 - qB with huCb
  by_cases hge10 : sUb ≥ (10 : UInt64)
  · rw [if_pos hge10] at hopt
    rw [if_pos hge10]
    set uVb := inRoundingInterval_u64_flipped_u8 lBb.1 lBb.2.1 lBb.2.2 leftUb
        rBb.1 rBb.2.1 rBb.2.2 rightUb (uBb - 5070) (sUb / 10) with huVb
    by_cases hu0 : uVb = inRoundingInterval_u8_AMBIG
    · rw [if_pos hu0] at hopt; cases hopt
    rw [if_neg hu0] at hopt
    rw [if_neg hu0]
    by_cases hu2 : uVb = inRoundingInterval_u8_TRUE
    · rw [if_pos hu2] at hopt
      rw [if_pos hu2]
      cases hopt
      exact some_pair_congr _ (by omega)
    rw [if_neg hu2] at hopt
    rw [if_neg hu2]
    set wVb := inRoundingInterval_u64_flipped_u8 lBb.1 lBb.2.1 lBb.2.2 leftUb
        rBb.1 rBb.2.1 rBb.2.2 rightUb (uBb - 5070) (sUb / 10 + 1) with hwVb
    by_cases hw0 : wVb = inRoundingInterval_u8_AMBIG
    · rw [if_pos hw0] at hopt; cases hopt
    rw [if_neg hw0] at hopt
    rw [if_neg hw0]
    by_cases hw2 : wVb = inRoundingInterval_u8_TRUE
    · rw [if_pos hw2] at hopt
      rw [if_pos hw2]
      cases hopt
      exact some_pair_congr _ (by omega)
    rw [if_neg hw2] at hopt
    rw [if_neg hw2]
    by_cases hc_lo : uCb < 5134
    · rw [if_pos hc_lo] at hopt; cases hopt
    rw [if_neg hc_lo] at hopt
    rw [dif_neg hc_lo]
    by_cases hc_hi : uCb > 5202
    · rw [if_pos hc_hi] at hopt; cases hopt
    rw [if_neg hc_hi] at hopt
    rw [dif_neg hc_hi]
    split at hopt
    · cases hopt
    · rename_i chosen heq
      rw [heq]
      cases hopt
      rfl
  · rw [if_neg hge10] at hopt
    rw [if_neg hge10]
    by_cases hs0 : sUb = 0
    · rw [if_pos hs0] at hopt; cases hopt
    rw [if_neg hs0] at hopt
    rw [dif_neg hs0]
    by_cases hc_lo : uCb < 5134
    · rw [if_pos hc_lo] at hopt; cases hopt
    rw [if_neg hc_lo] at hopt
    rw [dif_neg hc_lo]
    by_cases hc_hi : uCb > 5202
    · rw [if_pos hc_hi] at hopt; cases hopt
    rw [if_neg hc_hi] at hopt
    rw [dif_neg hc_hi]
    split at hopt
    · cases hopt
    · rename_i chosen heq
      rw [heq]
      cases hopt
      rfl

/-! ## Emit and entry points -/

theorem emitIdx_eq (sign : Sign) (sig : Nat) (kB : UInt64) :
    emitIdx sign sig kB.toNat = emitChecked sign sig ((kB.toNat : Int) - 324) := by
  rw [← emitCheckedIdx_eq sign sig _ (by omega)]
  unfold emitIdx emitCheckedIdx
  have h : (((kB.toNat : Int) - 324) + 324).toNat = kB.toNat := by omega
  simp only [h]

theorem emitTail8_eq (sign : Sign) (mU qB : UInt64) :
    emitTail8 sign mU qB = emitTail2 sign mU qB := by
  unfold emitTail8 emitTail2
  by_cases h0 : mU = 0
  · rw [if_pos h0, if_pos h0]
  rw [if_neg h0, if_neg h0]
  have h8pk : shortestUnsigned_v8 mU qB
      = shortestUnsigned_packed mU.toNat ((qB.toNat : Int) - 1074) := by
    rw [shortestUnsigned_v8_eq_v7, shortestUnsigned_v7_eq_v5, shortestUnsigned_v5_eq,
        ← shortestUnsigned_packed_eq]
  rw [h8pk]
  cases hv : shortestUnsigned_u64_opt_v14 mU qB with
  | none => rfl
  | some p =>
    obtain ⟨sU, kB⟩ := p
    have hpk : shortestUnsigned_packed mU.toNat ((qB.toNat : Int) - 1074)
        = (sU.toNat, (kB.toNat : Int) - 324) :=
      shortestUnsigned_u64_opt_flip3_some_eq_packed _ _ _ _
        (shortestUnsigned_u64_opt_v13_some_eq_flip3 mU qB _
          (shortestUnsigned_u64_opt_v14_some_eq_v13 mU qB sU kB hv))
    rw [hpk]
    simp only []
    rw [emitIdx_eq]
    have hmod : (sU % 10 = 0) ↔ (sU.toNat % 10 = 0) := by
      rw [← UInt64.toNat_inj, UInt64.toNat_mod]; rfl
    by_cases hs0 : sU.toNat = 0
    · rw [if_pos hs0]
      have hm0 : ¬ (sU % 10 ≠ 0) := fun hc => hc (hmod.mpr (by rw [hs0]))
      rw [if_neg hm0, hs0, Srtfp.Decimal.canonicaliseAux_zero]
      simp
    · rw [if_neg hs0]
      by_cases hm : sU.toNat % 10 ≠ 0
      · rw [if_pos hm, if_pos (fun hc => hm (hmod.mp hc))]
      · rw [if_neg hm, if_neg (fun hc => hm (fun hc' => hc (hmod.mpr hc')))]

theorem toStringFast10_eq (f : _root_.Float) : toStringFast10 f = toStringFast4 f := by
  unfold toStringFast10 toStringFast4
  simp only [emitTail8_eq]

/-- The live `Float → String` registration (later registrations win over
    `floatToStrRef_eq_toStringFast9`; `CsimpPin.lean` asserts this one is
    in force). -/
@[csimp]
theorem floatToStrRef_eq_toStringFast10 : @floatToStrRef = @toStringFast10 := by
  funext f
  rw [toStringFast10_eq]
  exact congrFun floatToStrRef_eq_toStringFast4 f

/-! ## `toDecimal` over the v14 kernel -/

/-- `decimalTail` over the v14 kernel: the exponent is unbiased once, at
    the exit. -/
@[inline]
def decimalTail_v14 (sign : Sign) (mU qB : UInt64) : _root_.Srtfp.Decimal :=
  if mU = 0 then ⟨sign, 0, 0⟩
  else
    match shortestUnsigned_u64_opt_v14 mU qB with
    | some (sU, kB) => Srtfp.Decimal.mk' sign sU.toNat ((kB.toNat : Int) - 324)
    | none =>
      let (sig, exp) := shortestUnsigned_packed mU.toNat ((qB.toNat : Int) - 1074)
      Srtfp.Decimal.mk' sign sig exp

theorem decimalTail_v14_eq (sign : Sign) (mU qB : UInt64) :
    decimalTail_v14 sign mU qB
      = decimalTailNat sign mU.toNat ((qB.toNat : Int) - 1074) := by
  unfold decimalTail_v14 decimalTailNat
  by_cases h0 : mU = 0
  · rw [if_pos h0, if_pos (by rw [h0]; rfl)]
  rw [if_neg h0, if_neg (fun hc => h0 (UInt64.toNat_inj.mp (by rw [hc]; rfl)))]
  rw [shortestUnsigned_v7_eq, ← shortestUnsigned_packed_eq]
  cases hv : shortestUnsigned_u64_opt_v14 mU qB with
  | none => rfl
  | some p =>
    obtain ⟨sU, kB⟩ := p
    have hpk : shortestUnsigned_packed mU.toNat ((qB.toNat : Int) - 1074)
        = (sU.toNat, (kB.toNat : Int) - 324) :=
      shortestUnsigned_u64_opt_flip3_some_eq_packed _ _ _ _
        (shortestUnsigned_u64_opt_v13_some_eq_flip3 mU qB _
          (shortestUnsigned_u64_opt_v14_some_eq_v13 mU qB sU kB hv))
    rw [hpk]

/-- `toDecimal_v13` over the v14 kernel: the `Float → Decimal` twin of
    `toStringFast10`. -/
@[inline]
def toDecimal_v14 (f : _root_.Float) : Except String _root_.Srtfp.Decimal :=
  let bits := f.toBits
  let expBits : UInt64 := (bits >>> 52) &&& 0x7FF
  let mantBits : UInt64 := bits &&& 0x000F_FFFF_FFFF_FFFF
  if expBits = 0x7FF then
    if mantBits ≠ 0 then .error "NaN"
    else .error (if (bits >>> 63) ≠ 0 then "-Infinity" else "Infinity")
  else
    .ok (decimalTail_v14 (if bits >>> 63 = 0 then .positive else .negative)
      (if expBits = 0 then mantBits else mantBits + 4503599627370496)
      (if expBits = 0 then 0 else expBits - 1))

theorem toDecimal_v14_eq (f : _root_.Float) : toDecimal_v14 f = toDecimal_v13 f := by
  unfold toDecimal_v14 toDecimal_v13
  simp only [decimalTail_v14_eq, decimalTail_eq]

/-- The live `Float → Decimal` registrations. -/
@[csimp]
theorem toDecimal_eq_v14_csimp : @toDecimal = @toDecimal_v14 := by
  funext f
  rw [toDecimal_v14_eq, toDecimal_v13_eq, toDecimal_v7_eq]

@[csimp]
theorem printer_toDecimal_eq_v14_csimp : @Printer.toDecimal = @toDecimal_v14 := by
  funext f
  rw [toDecimal_v14_eq, toDecimal_v13_eq, toDecimal_v7_eq_printer]

end Srtfp.Schubfach

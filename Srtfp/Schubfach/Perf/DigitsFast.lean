/- Fast emit: minimize extern calls, not allocations.

   Every Lean string mutation is an out-of-line extern call (~6-10ns),
   so per-digit-pair appends LOSE to the extern `std::to_string` path
   (measured 81 vs 53 ns/call; see git history for the two-digit-table
   emitter and its proofs).  What does win is cutting the number of
   calls: the exponent of a canonical binary64 shortest decimal lies in
   [-324, 292], so the entire "e<exp>" suffix is one of 617 memoized
   strings.  The emit becomes one extern repr + one (or two) appends.

   Verified: `toStringFast2 = floatToStrRef`, wired via `@[csimp]`
   (overrides StringFast's registration; later csimps win). -/
import Srtfp.Schubfach.Perf.StringFast
import Srtfp.Schubfach.Perf.KernelV6
import Srtfp.Tactics

namespace Srtfp.Schubfach

/-! ## The exponent suffix table -/

/-- `"e-324"`, `"e-323"`, ..., `"e292"`: every canonical binary64
    shortest-decimal exponent, with the `'e'` pre-attached. -/
def expTable : Array String :=
  Array.ofFn (fun i : Fin 617 => "e" ++ intToStrRef ((i.val : Int) - 324))

theorem expTable_size : expTable.size = 617 := by
  simp [expTable]

/-- Fast emit when `exp` is in the canonical binary64 range (always, for
    Schubfach outputs), reference emit otherwise. -/
@[inline]
def emitChecked (sign : Bool) (sig : Nat) (exp : Int) : String :=
  if h : -324 ≤ exp ∧ exp ≤ 292 then
    let core := toString sig ++
      expTable[(exp + 324).toNat]'(by rw [expTable_size]; omega)
    if sign then "-" ++ core else core
  else
    (if sign then "-" else "") ++ toString sig ++ "e" ++ intToStrRef exp

theorem emitChecked_eq (sign : Bool) (sig : Nat) (exp : Int) :
    emitChecked sign sig exp =
      (if sign then "-" else "") ++ toString sig ++ "e" ++ intToStrRef exp := by
  unfold emitChecked
  split
  · rename_i h
    rw [show expTable[(exp + 324).toNat]'(by rw [expTable_size]; omega)
          = "e" ++ intToStrRef (((exp + 324).toNat : Int) - 324) from by
      simp [expTable]]
    rw [show (((exp + 324).toNat : Int) - 324) = exp from by omega]
    cases sign
    · simp [String.empty_append, String.append_assoc]
    · simp [String.append_assoc]
  · rfl

/-! ## `toStringFast2`, `toStringFast3` -/

open Srtfp.Float in
/-- Everything after the bit fields are known. -/
@[inline]
def emitTail (sign : Bool) (m : Nat) (q : Int) : String :=
  if m = 0 then (if sign then "-0" else "0")
  else
    let (sig, exp) := shortestUnsigned_v7 m q
    if sig = 0 then (if sign then "-0" else "0")
    else if sig % 10 ≠ 0 then
      emitChecked sign sig exp
    else
      let (sig', exp') := Srtfp.Decimal.canonicaliseAux sig exp
      if sig' = 0 then (if sign then "-0" else "0")
      else emitChecked sign sig' exp'

open Srtfp.Float in
/-- `toStringFast` with the emit sites routed through `emitChecked`. -/
@[inline]
def toStringFast2 (f : _root_.Float) : String :=
  if isNaNBits f then "NaN"
  else if isInfBits f then (if signBit f then "-Infinity" else "Infinity")
  else
    let d := decode f
    emitTail d.sign d.m d.q

theorem toStringFast2_eq (f : _root_.Float) : toStringFast2 f = toStringFast f := by
  unfold toStringFast2 toStringFast emitTail
  simp only [shortestUnsigned_v7_eq_v5, emitChecked_eq]

/-! `toStringFast2` still reads `f.toBits` five to seven times (inside
`isNaNBits`, `isInfBits`, `signBit`, three times in `decode`) and
allocates a `Decoded` per call.  v3 reads the bits once and keeps the
fields as scalars. -/

open Srtfp.Float in
@[inline]
def toStringFast3 (f : _root_.Float) : String :=
  let bits := f.toBits
  let expBits : UInt64 := (bits >>> 52) &&& 0x7FF
  let mantBits : UInt64 := bits &&& 0x000F_FFFF_FFFF_FFFF
  if expBits = 0x7FF then
    if mantBits ≠ 0 then "NaN"
    else if (bits >>> 63) ≠ 0 then "-Infinity" else "Infinity"
  else
    emitTail (decide (bits >>> 63 ≠ 0))
      (if expBits = 0 then mantBits.toNat
       else (mantBits + (4503599627370496 : UInt64)).toNat)
      (if expBits = 0 then -1074 else (expBits.toNat : Int) - 1075)

open Srtfp.Float in
theorem toStringFast3_eq (f : _root_.Float) : toStringFast3 f = toStringFast2 f := by
  unfold toStringFast3 toStringFast2
  -- field bridges (definitional)
  have hexp : ((f.toBits >>> 52) &&& 0x7FF : UInt64).toNat = biasedExpBits f := rfl
  have hmant : (f.toBits &&& 0x000F_FFFF_FFFF_FFFF : UInt64).toNat = mantissaBits f := rfl
  by_cases h7 : ((f.toBits >>> 52) &&& 0x7FF : UInt64) = 0x7FF
  · rw [if_pos h7]
    have hbE : biasedExpBits f = 2047 := by rw [← hexp, h7]; rfl
    by_cases hm : (f.toBits &&& 0x000F_FFFF_FFFF_FFFF : UInt64) = 0
    · -- infinity
      have hm0 : mantissaBits f = 0 := by rw [← hmant, hm]; rfl
      have hNaN : ¬ isNaNBits f = true := by simp [isNaNBits, hbE, hm0]
      have hInf : isInfBits f = true := by simp [isInfBits, hbE, hm0]
      rw [if_neg (by simp [hm]), if_neg hNaN, if_pos hInf]
      simp [signBit]
    · -- NaN
      have hm0 : mantissaBits f ≠ 0 := by
        intro hc
        exact hm (UInt64.toNat_inj.mp (by rw [hmant, hc]; rfl))
      have hNaN : isNaNBits f = true := by simp [isNaNBits, hbE, hm0]
      rw [if_pos hm, if_pos hNaN]
  · -- finite
    have hbE : biasedExpBits f ≠ 2047 := by
      intro hc
      exact h7 (UInt64.toNat_inj.mp (by rw [hexp, hc]; rfl))
    have hNaN : ¬ isNaNBits f = true := by simp [isNaNBits, hbE]
    have hInf : ¬ isInfBits f = true := by simp [isInfBits, hbE]
    rw [if_neg h7, if_neg hNaN, if_neg hInf]
    show emitTail _ _ _ = emitTail (decode f).sign (decode f).m (decode f).q
    congr 1
    · -- sign
      show decide (f.toBits >>> 63 ≠ 0) = (decode f).sign
      have : (decode f).sign = signBit f := by
        unfold decode
        by_cases h : biasedExpBits f = 0 <;> simp [h]
      rw [this]; rfl
    · -- m
      by_cases h0 : ((f.toBits >>> 52) &&& 0x7FF : UInt64) = 0
      · have hbE0 : biasedExpBits f = 0 := by rw [← hexp, h0]; rfl
        rw [if_pos h0, show (decode f).m = mantissaBits f from by simp [decode, hbE0]]
        exact hmant
      · have hbE0 : biasedExpBits f ≠ 0 := by
          intro hc
          exact h0 (UInt64.toNat_inj.mp (by rw [hexp, hc]; rfl))
        have hmlt : mantissaBits f < 2 ^ 52 := by
          simp only [mantissaBits, UInt64.toNat_and,
            show (0x000F_FFFF_FFFF_FFFF : UInt64).toNat = 0x000F_FFFF_FFFF_FFFF from rfl]
          have := Nat.and_le_right (n := f.toBits.toNat) (m := 0x000F_FFFF_FFFF_FFFF)
          omega
        rw [if_neg h0,
          show (decode f).m = mantissaBits f + (1 <<< 52) from by simp [decode, hbE0]]
        rw [UInt64.toNat_add, hmant,
          show ((4503599627370496 : UInt64)).toNat = 1 <<< 52 from rfl]
        exact Nat.mod_eq_of_lt (by omega)
    · -- q
      by_cases h0 : ((f.toBits >>> 52) &&& 0x7FF : UInt64) = 0
      · have hbE0 : biasedExpBits f = 0 := by rw [← hexp, h0]; rfl
        rw [if_pos h0, show (decode f).q = -1074 from by simp [decode, hbE0]]
      · have hbE0 : biasedExpBits f ≠ 0 := by
          intro hc
          exact h0 (UInt64.toNat_inj.mp (by rw [hexp, hc]; rfl))
        rw [if_neg h0,
          show (decode f).q = (biasedExpBits f : Int) - 1023 - 52 from by
            simp [decode, hbE0]]
        rw [hexp]
        omega


/-! ## All-scalar surface: `emitTail2` and `toStringFast4` -/

open Srtfp.Float in
@[inline]
def emitTail2 (sign : Bool) (mU qB : UInt64) : String :=
  if mU = 0 then (if sign then "-0" else "0")
  else
    let (sig, exp) := shortestUnsigned_v8 mU qB
    if sig = 0 then (if sign then "-0" else "0")
    else if sig % 10 ≠ 0 then
      emitChecked sign sig exp
    else
      let (sig', exp') := Srtfp.Decimal.canonicaliseAux sig exp
      if sig' = 0 then (if sign then "-0" else "0")
      else emitChecked sign sig' exp'

theorem emitTail2_eq (sign : Bool) (mU qB : UInt64) :
    emitTail2 sign mU qB = emitTail sign mU.toNat ((qB.toNat : Int) - 1074) := by
  unfold emitTail2 emitTail
  by_cases h : mU.toNat = 0
  · rw [if_pos h, if_pos (UInt64.toNat_inj.mp h)]
  · rw [if_neg h, if_neg (fun hc => h (by rw [hc]; rfl)),
        shortestUnsigned_v8_eq_v7]

open Srtfp.Float in
@[inline]
def toStringFast4 (f : _root_.Float) : String :=
  let bits := f.toBits
  let expBits : UInt64 := (bits >>> 52) &&& 0x7FF
  let mantBits : UInt64 := bits &&& 0x000F_FFFF_FFFF_FFFF
  if expBits = 0x7FF then
    if mantBits ≠ 0 then "NaN"
    else if (bits >>> 63) ≠ 0 then "-Infinity" else "Infinity"
  else
    emitTail2 (decide (bits >>> 63 ≠ 0))
      (if expBits = 0 then mantBits else mantBits + 4503599627370496)
      (if expBits = 0 then 0 else expBits - 1)

open Srtfp.Float in
theorem toStringFast4_eq (f : _root_.Float) : toStringFast4 f = toStringFast3 f := by
  unfold toStringFast4 toStringFast3
  by_cases h7 : ((f.toBits >>> 52) &&& 0x7FF : UInt64) = 0x7FF
  · rw [if_pos h7, if_pos h7]
  rw [if_neg h7, if_neg h7,
    emitTail2_eq]
  congr 1
  · -- m
    by_cases h0 : ((f.toBits >>> 52) &&& 0x7FF : UInt64) = 0
    · rw [if_pos h0, if_pos h0]
    · rw [if_neg h0, if_neg h0]
  · -- q
    by_cases h0 : ((f.toBits >>> 52) &&& 0x7FF : UInt64) = 0
    · rw [if_pos h0, if_pos h0]
      rfl
    · rw [if_neg h0, if_neg h0]
      have h1 : (1 : UInt64) ≤ ((f.toBits >>> 52) &&& 0x7FF) := by
        rw [UInt64.le_iff_toNat_le, show ((1 : UInt64)).toNat = 1 from rfl]
        by_contra hc
        exact h0 (UInt64.toNat_inj.mp
          (by rw [show ((0 : UInt64)).toNat = 0 from rfl]; omega))
      rw [UInt64.toNat_sub_of_le _ _ h1, show ((1 : UInt64)).toNat = 1 from rfl]
      have h2 : 1 ≤ ((f.toBits >>> 52) &&& 0x7FF : UInt64).toNat := by
        rw [UInt64.le_iff_toNat_le] at h1
        exact h1
      omega

@[csimp]
theorem floatToStrRef_eq_toStringFast4 : @floatToStrRef = @toStringFast4 := by
  funext f
  rw [toStringFast4_eq, toStringFast3_eq, toStringFast2_eq]
  exact (toStringFast_eq_ref f).symm

end Srtfp.Schubfach

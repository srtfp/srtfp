/- v10 — biased-index emit.

   `emitChecked` pays two boxed-`Int` comparisons per call to validate
   the exponent before indexing the suffix table, although the v9
   kernel can only emit exponents in `[-324, 325]` (its `k` is
   `kB.toNat - 324` with `kB ≤ 647`, plus one). v10 proves that range
   once (`shortestUnsigned_u64_opt_v9_k_range`), converts the exponent
   to a table index a single time, and validates with one `Nat`
   comparison. The `Int` form survives only on the cold paths
   (trailing-zero canonicalisation, fallback kernel, out-of-table). -/

import Srtfp.Schubfach.Perf.KernelV9

namespace Srtfp.Schubfach

set_option maxHeartbeats 1600000 in
/-- Every successful v9 exit carries an exponent in `[-324, 325]`.

    Proven by transferring the success through the verified chain to the
    spec (`shortestUnsigned`), whose leaves carry `kOfMQ` or `kOfMQ + 1`,
    and bounding `kOfMQ` from the kernel's table guard. -/
theorem shortestUnsigned_u64_opt_v9_k_range (mU qB : UInt64)
    (s : UInt64) (k : Int)
    (h : shortestUnsigned_u64_opt_v9 mU qB = some (s, k)) :
    -324 ≤ k ∧ k ≤ 325 := by
  rw [shortestUnsigned_u64_opt_v9_eq_v8] at h
  -- The guards: a successful v8 exit forces them all false.
  by_cases h1 : mU = 0
  · rw [show shortestUnsigned_u64_opt_v8 mU qB = none from by
      unfold shortestUnsigned_u64_opt_v8; rw [dif_pos h1]] at h
    cases h
  by_cases h2 : mU ≥ (9007199254740992 : UInt64)
  · rw [show shortestUnsigned_u64_opt_v8 mU qB = none from by
      unfold shortestUnsigned_u64_opt_v8; rw [dif_neg h1, dif_pos h2]] at h
    cases h
  by_cases h3 : qB > 2045
  · rw [show shortestUnsigned_u64_opt_v8 mU qB = none from by
      unfold shortestUnsigned_u64_opt_v8; rw [dif_neg h1, dif_neg h2, dif_pos h3]] at h
    cases h
  by_cases h4 : kBOfMQ mU qB > 647
  · rw [show shortestUnsigned_u64_opt_v8 mU qB = none from by
      unfold shortestUnsigned_u64_opt_v8;
        rw [dif_neg h1, dif_neg h2, dif_neg h3, dif_pos h4]] at h
    cases h
  -- Transfer the value to the spec through the chain.
  have hwrap : shortestUnsigned mU.toNat ((qB.toNat : Int) - 1074) = (s.toNat, k) := by
    have h9 : shortestUnsigned_v8 mU qB = (s.toNat, k) := by
      unfold shortestUnsigned_v8
      rw [h]
    rw [← shortestUnsigned_v5_eq, ← shortestUnsigned_v7_eq_v5,
        ← shortestUnsigned_v8_eq_v7, h9]
  -- The spec's exponent is kOfMQ or kOfMQ + 1.
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
  -- Bound kOfMQ from the table guard.
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

/-- `emitChecked` with the table index pre-computed and validated by a
    single `Nat` comparison. Faithful only for `-324 ≤ exp` (the caller
    holds `shortestUnsigned_u64_opt_v9_k_range`). -/
@[inline]
def emitCheckedIdx (sign : Bool) (sig : Nat) (exp : Int) : String :=
  let idx : Nat := (exp + 324).toNat
  if h : idx ≤ 616 then
    let core := toString sig ++
      expTable[idx]'(by rw [expTable_size]; omega)
    if sign then "-" ++ core else core
  else
    (if sign then "-" else "") ++ toString sig ++ "e" ++ intToStrRef exp

theorem emitCheckedIdx_eq (sign : Bool) (sig : Nat) (exp : Int)
    (hlo : -324 ≤ exp) :
    emitCheckedIdx sign sig exp = emitChecked sign sig exp := by
  unfold emitCheckedIdx emitChecked
  by_cases hhi : exp ≤ 292
  · rw [dif_pos (by omega), dif_pos ⟨hlo, hhi⟩]
  · rw [dif_neg (by omega), dif_neg (by omega)]

/-- `emitTail3` with the biased-index emit on the hot path. -/
@[inline]
def emitTail4 (sign : Bool) (mU qB : UInt64) : String :=
  if mU = 0 then (if sign then "-0" else "0")
  else
    match shortestUnsigned_u64_opt_v9 mU qB with
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

theorem emitTail4_eq (sign : Bool) (mU qB : UInt64) :
    emitTail4 sign mU qB = emitTail3 sign mU qB := by
  unfold emitTail4 emitTail3 shortestUnsigned_v9
  by_cases h0 : mU = 0
  · rw [if_pos h0, if_pos h0]
  rw [if_neg h0, if_neg h0]
  cases hv : shortestUnsigned_u64_opt_v9 mU qB with
  | none => rfl
  | some p =>
    obtain ⟨sU, exp⟩ := p
    have hrange := shortestUnsigned_u64_opt_v9_k_range mU qB sU exp hv
    simp only
    rw [emitCheckedIdx_eq sign sU.toNat exp hrange.1]

/-- `toStringFast5` with the biased-index emit. -/
@[inline]
def toStringFast6 (f : _root_.Float) : String :=
  let bits := f.toBits
  let expBits : UInt64 := (bits >>> 52) &&& 0x7FF
  let mantBits : UInt64 := bits &&& 0x000F_FFFF_FFFF_FFFF
  if expBits = 0x7FF then
    if mantBits ≠ 0 then "NaN"
    else if (bits >>> 63) ≠ 0 then "-Infinity" else "Infinity"
  else
    emitTail4 (decide (bits >>> 63 ≠ 0))
      (if expBits = 0 then mantBits else mantBits + 4503599627370496)
      (if expBits = 0 then 0 else expBits - 1)

theorem toStringFast6_eq (f : _root_.Float) : toStringFast6 f = toStringFast5 f := by
  unfold toStringFast6 toStringFast5
  simp only [emitTail4_eq]

-- Superseded registration: `floatToStrRef_eq_toStringFast7` (KernelV11)
-- is the live @[csimp].
theorem floatToStrRef_eq_toStringFast6 : @floatToStrRef = @toStringFast6 := by
  funext f
  rw [toStringFast6_eq]
  exact congrFun floatToStrRef_eq_toStringFast5 f

end Srtfp.Schubfach

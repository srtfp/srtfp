module
/- `toDecimal` over the v13 kernel.

   The live `Float → String` path (`toStringFast9`, KernelV13.lean) reads
   the bit fields once and hands `(mU, qB) : UInt64 × UInt64` to the v13
   kernel, while the live `Float → Decimal` path (`toDecimal_v7`,
   KernelV6.lean) still allocates a `Decoded`, passes `(m : Nat, q : Int)`
   to the v7 kernel and re-derives the biased index inside it. This module
   gives `Printer.toDecimal` / `Schubfach.toDecimal` the same front end as
   the string path: `toDecimal_v13` is `toStringFast9` with the emit
   replaced by `Decimal.mk'` (itself `@[csimp]`-rewritten to the
   allocation-once `mk'_fast2`). Proven equal to `toDecimal_v7`, hence to
   the reference, and registered as the live `@[csimp]` rewrite (pinned in
   `CsimpPin.lean`). -/

public import Srtfp.Perf.KernelV13

@[expose] public section

open Float.Model.UnpackedFloat (Sign)

namespace Srtfp.Schubfach

open Srtfp.Float

/-- The `(m : Nat, q : Int)` shape of `toDecimal_v7`'s finite branch. -/
@[inline]
def decimalTailNat (sign : Sign) (m : Nat) (q : Int) : _root_.Srtfp.Decimal :=
  if m = 0 then ⟨sign, 0, 0⟩
  else
    let (sig, exp) := shortestUnsigned_v7 m q
    Srtfp.Decimal.mk' sign sig exp

/-- Everything after the bit fields are known: the `Decimal` analogue of
    `emitTail7`. -/
@[inline]
def decimalTail (sign : Sign) (mU qB : UInt64) : _root_.Srtfp.Decimal :=
  if mU = 0 then ⟨sign, 0, 0⟩
  else
    match shortestUnsigned_u64_opt_v13 mU qB with
    | some (sU, exp) => Srtfp.Decimal.mk' sign sU.toNat exp
    | none =>
      let (sig, exp) := shortestUnsigned_packed mU.toNat ((qB.toNat : Int) - 1074)
      Srtfp.Decimal.mk' sign sig exp

theorem decimalTail_eq (sign : Sign) (mU qB : UInt64) :
    decimalTail sign mU qB = decimalTailNat sign mU.toNat ((qB.toNat : Int) - 1074) := by
  unfold decimalTail decimalTailNat
  by_cases h0 : mU = 0
  · rw [if_pos h0, if_pos (by rw [h0]; rfl)]
  rw [if_neg h0, if_neg (fun hc => h0 (UInt64.toNat_inj.mp (by rw [hc]; rfl)))]
  rw [shortestUnsigned_v7_eq, ← shortestUnsigned_packed_eq]
  cases hv : shortestUnsigned_u64_opt_v13 mU qB with
  | none => rfl
  | some p =>
    obtain ⟨sU, exp⟩ := p
    have hpk : shortestUnsigned_packed mU.toNat ((qB.toNat : Int) - 1074)
        = (sU.toNat, exp) :=
      shortestUnsigned_u64_opt_flip3_some_eq_packed _ _ _ _
        (shortestUnsigned_u64_opt_v13_some_eq_flip3 mU qB (sU, exp) hv)
    rw [hpk]

/-- `toDecimal` from the raw bit fields, over the v13 kernel: the
    `Float → Decimal` twin of `toStringFast9`. -/
@[inline]
def toDecimal_v13 (f : _root_.Float) : Option _root_.Srtfp.Decimal :=
  let bits := f.toBits
  let expBits : UInt64 := (bits >>> 52) &&& 0x7FF
  let mantBits : UInt64 := bits &&& 0x000F_FFFF_FFFF_FFFF
  if expBits = 0x7FF then none
  else
    some (decimalTail (if bits >>> 63 = 0 then .positive else .negative)
      (if expBits = 0 then mantBits else mantBits + 4503599627370496)
      (if expBits = 0 then 0 else expBits - 1))

theorem toDecimal_v7_finite (f : _root_.Float)
    (hNaN : ¬ isNaNBits f = true) (hInf : ¬ isInfBits f = true) :
    toDecimal_v7 f = some (decimalTailNat (decode f).sign (decode f).m (decode f).q) := by
  unfold toDecimal_v7 decimalTailNat
  rw [if_neg hNaN, if_neg hInf]
  simp only []
  split <;> rfl

theorem toDecimal_v13_eq (f : _root_.Float) : toDecimal_v13 f = toDecimal_v7 f := by
  unfold toDecimal_v13
  have hexp : ((f.toBits >>> 52) &&& 0x7FF : UInt64).toNat = biasedExpBits f := rfl
  have hmant : (f.toBits &&& 0x000F_FFFF_FFFF_FFFF : UInt64).toNat = mantissaBits f := rfl
  by_cases h7 : ((f.toBits >>> 52) &&& 0x7FF : UInt64) = 0x7FF
  · rw [if_pos h7]
    unfold toDecimal_v7
    have hbE : biasedExpBits f = 2047 := by rw [← hexp, h7]; rfl
    by_cases hm0 : mantissaBits f = 0
    · have hInf : isInfBits f = true := by simp [isInfBits, hbE, hm0]
      simp [hInf]
    · have hNaN : isNaNBits f = true := by simp [isNaNBits, hbE, hm0]
      simp [hNaN]
  · -- finite
    have hbE : biasedExpBits f ≠ 2047 := by
      intro hc
      exact h7 (UInt64.toNat_inj.mp (by rw [hexp, hc]; rfl))
    have hNaN : ¬ isNaNBits f = true := by simp [isNaNBits, hbE]
    have hInf : ¬ isInfBits f = true := by simp [isInfBits, hbE]
    rw [if_neg h7, toDecimal_v7_finite f hNaN hInf, decimalTail_eq]
    congr 2
    · -- sign
      show (if f.toBits >>> 63 = 0 then Sign.positive else Sign.negative) = (decode f).sign
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
        rfl
      · have hbE0 : biasedExpBits f ≠ 0 := by
          intro hc
          exact h0 (UInt64.toNat_inj.mp (by rw [hexp, hc]; rfl))
        rw [if_neg h0,
          show (decode f).q = (biasedExpBits f : Int) - 1023 - 52 from by
            simp [decode, hbE0]]
        have h1 : (1 : UInt64) ≤ ((f.toBits >>> 52) &&& 0x7FF) := by
          rw [UInt64.le_iff_toNat_le, show ((1 : UInt64)).toNat = 1 from rfl]
          by_contra hc
          exact h0 (UInt64.toNat_inj.mp
            (by rw [show ((0 : UInt64)).toNat = 0 from rfl]; omega))
        rw [UInt64.toNat_sub_of_le _ _ h1, show ((1 : UInt64)).toNat = 1 from rfl, hexp]
        have h2 : 1 ≤ biasedExpBits f := by
          rw [UInt64.le_iff_toNat_le] at h1
          exact h1
        omega

/-- The live registrations: kernel 0 and the reference printer both compile
    to the fused v13 kernel. (Later registrations win; `CsimpPin.lean`
    asserts these are the ones in force.) -/
@[csimp]
theorem toDecimal_eq_v13_csimp : @toDecimal = @toDecimal_v13 := by
  funext f
  rw [toDecimal_v13_eq, toDecimal_v7_eq]

@[csimp]
theorem printer_toDecimal_eq_v13_csimp : @Printer.toDecimal = @toDecimal_v13 := by
  funext f
  rw [toDecimal_v13_eq, toDecimal_v7_eq_printer]

end Srtfp.Schubfach

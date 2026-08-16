/- `toDecimalBits` output lies in R_v (M3.8.7).

   This file wraps the M3.8.6 result `shortestUnsigned_mem_rv` together with
   the bit-level invariants of `Word.decode` to prove that
   `Schubfach.toDecimalBits w` succeeds on finite binary64 words and that the
   produced `Decimal`'s underlying significand / exponent pair lies in the
   rounding interval `R_v` of `(m, q) = Word.decode w`. Everything is stated
   on the pure word pipeline (axiom-free); the `Float`-level statements at
   the end are instantiations at `w := f.toBits` (also axiom-free — only the
   `ofBits` direction ever needs the runtime axiom).

   The statement is phrased existentially: there exist `sig, exp` such that
   `Decimal.mk' d.sign sig exp = result` and the pair `(sig, exp)` satisfies
   `inRoundingInterval`. The canonicalisation performed by `mk'` strips
   trailing decimal zeros from the `Decimal`'s fields; this loses information
   about the raw `(sig, exp)` pair, so we keep the raw pair as the existential
   witness. The Clinger correctness theorem (M4) can then consume the
   `inRoundingInterval` witness independently of any canonicalisation. -/

import Srtfp.Proofs.Schubfach.Shorter

namespace Srtfp.Schubfach

open Srtfp.Float
open Srtfp

/-! ## Word.decode invariants

For finite words, `Word.decode` produces `(m, q)` satisfying the binary64
range `m < 2^53`, `-1074 ≤ q ≤ 971`. -/

theorem decode_q_ge_bits {w : UInt64} (_h : Word.isFinite w = true) :
    -1074 ≤ (Word.decode w).q := by
  unfold Word.decode
  by_cases he : Word.biasedExp w = 0
  · simp [he]
  · simp [he]
    have h1 : 1 ≤ Word.biasedExp w := Nat.one_le_iff_ne_zero.mpr he
    omega

theorem decode_q_le_bits {w : UInt64} (h : Word.isFinite w = true) :
    (Word.decode w).q ≤ 971 := by
  have hfin : Word.biasedExp w < 2047 := by
    unfold Word.isFinite at h; simpa using h
  unfold Word.decode
  by_cases he : Word.biasedExp w = 0
  · simp [he]
  · simp [he]
    have hle : Word.biasedExp w ≤ 2046 := Nat.lt_succ_iff.mp hfin
    omega

theorem decode_m_lt_bits {w : UInt64} (h : Word.isFinite w = true) :
    (Word.decode w).m < 2 ^ 53 := by
  have hfin : Word.biasedExp w < 2047 := by
    unfold Word.isFinite at h; simpa using h
  unfold Word.decode
  by_cases he : Word.biasedExp w = 0
  · simp [he]
    have h1 := word_mantissa_lt w
    have h2 : (2 : Nat) ^ 52 < 2 ^ 53 := by decide
    omega
  · simp [he]
    have hmb := word_mantissa_lt w
    have h52 : (2 : Nat) ^ 52 = 4503599627370496 := by decide
    have h53 : (2 : Nat) ^ 53 = 9007199254740992 := by decide
    omega

/-- Convenience bundle: `Word.decode` outputs satisfy the Schubfach
hypotheses. -/
theorem decode_invariants_bits (w : UInt64) (h : Word.isFinite w = true) :
    (Word.decode w).m < 2 ^ 53 ∧ -1074 ≤ (Word.decode w).q ∧ (Word.decode w).q ≤ 971 :=
  ⟨decode_m_lt_bits h, decode_q_ge_bits h, decode_q_le_bits h⟩

/-! ## NaN / Infinity rejection -/

/-- `toDecimalBits` rejects NaN patterns. -/
theorem toDecimalBits_nan_rejected (w : UInt64) (h : Word.isNaN w = true) :
    ¬ ∃ d, toDecimalBits w = .ok d := by
  intro ⟨d, hd⟩
  unfold toDecimalBits at hd
  rw [h] at hd
  simp at hd

/-- `toDecimalBits` rejects Infinity patterns. -/
theorem toDecimalBits_inf_rejected (w : UInt64) (h : Word.isInf w = true) :
    ¬ ∃ d, toDecimalBits w = .ok d := by
  intro ⟨d, hd⟩
  unfold toDecimalBits at hd
  -- Word.isInf → biasedExp = 2047 ∧ mantissa = 0.
  -- That makes Word.isNaN false (which needs mantissa ≠ 0).
  have hmb : Word.mantissa w = 0 := by
    unfold Word.isInf at h; simp at h; exact h.2
  have hnan : Word.isNaN w = false := by
    unfold Word.isNaN; simp [hmb]
  rw [hnan, h] at hd
  simp at hd

/-! ## Zero case -/

/-- For a finite word with `(Word.decode w).m = 0`, `toDecimalBits` returns
    the signed canonical zero. -/
theorem toDecimalBits_zero (w : UInt64)
    (h_fin : Word.isFinite w = true)
    (h_zero : (Word.decode w).m = 0) :
    toDecimalBits w = .ok ⟨(Word.decode w).sign, 0, 0⟩ := by
  unfold toDecimalBits
  -- Word.isFinite → biasedExp < 2047 → ¬ isNaN and ¬ isInf.
  have hfin_lt : Word.biasedExp w < 2047 := by
    unfold Word.isFinite at h_fin; simpa using h_fin
  have hnan : Word.isNaN w = false := by
    unfold Word.isNaN
    have : ¬ Word.biasedExp w = 2047 := by omega
    simp [this]
  have hinf : Word.isInf w = false := by
    unfold Word.isInf
    have : ¬ Word.biasedExp w = 2047 := by omega
    simp [this]
  rw [hnan, hinf]
  simp [h_zero]

/-! ## Non-zero finite case: the main theorem -/

/-- For a finite non-zero binary64 word, `toDecimalBits` returns `.ok d`
    where `d` is `Decimal.mk' sign sig exp` for some `(sig, exp)` lying in
    the rounding interval `R_v` of `(m, q) = Word.decode w`. -/
theorem toDecimalBits_in_Rv
    (w : UInt64)
    (h_fin : Word.isFinite w = true) :
    let d := Word.decode w
    d.m ≠ 0 →
    ∃ result, toDecimalBits w = .ok result ∧
      ∃ sig exp,
        Decimal.mk' d.sign sig exp = result ∧
        inRoundingInterval sig exp d.m d.q (isIrregular d.m d.q) = true := by
  intro d hm_ne
  -- Discharge non-finite branches of toDecimalBits.
  have hfin_lt : Word.biasedExp w < 2047 := by
    unfold Word.isFinite at h_fin; simpa using h_fin
  have hnan : Word.isNaN w = false := by
    unfold Word.isNaN
    have : ¬ Word.biasedExp w = 2047 := by omega
    simp [this]
  have hinf : Word.isInf w = false := by
    unfold Word.isInf
    have : ¬ Word.biasedExp w = 2047 := by omega
    simp [this]
  -- Decode invariants.
  have ⟨h_m_lt, h_q_lo, h_q_hi⟩ := decode_invariants_bits w h_fin
  -- 1 ≤ m from m ≠ 0.
  have h_m_pos : 1 ≤ d.m := Nat.one_le_iff_ne_zero.mpr hm_ne
  -- R_v membership from M3.8.6.
  have h_rv :
      inRoundingInterval (shortestUnsigned d.m d.q).1 (shortestUnsigned d.m d.q).2
        d.m d.q (isIrregular d.m d.q) = true :=
    shortestUnsigned_mem_rv d.m d.q h_m_pos h_m_lt h_q_lo h_q_hi
  -- Witnesses.
  refine ⟨Decimal.mk' d.sign (shortestUnsigned d.m d.q).1 (shortestUnsigned d.m d.q).2,
          ?_, (shortestUnsigned d.m d.q).1, (shortestUnsigned d.m d.q).2, rfl, h_rv⟩
  -- toDecimalBits w = .ok (Decimal.mk' d.sign ...).
  unfold toDecimalBits
  rw [hnan, hinf]
  -- After rewriting NaN/Inf branches off, the remaining branch matches.
  -- `d` is `Word.decode w` definitionally; route via the m ≠ 0 branch.
  have hm_ne' : (Word.decode w).m ≠ 0 := hm_ne
  simp [hm_ne']
  rfl

/-! ## Float-level instantiations (axiom-free: `w := f.toBits`) -/

theorem decode_q_ge_of_finite
    {f : _root_.Float} (h : isFiniteBits f = true) :
    -1074 ≤ (decode f).q := decode_q_ge_bits (w := f.toBits) h

theorem decode_q_le_of_finite
    {f : _root_.Float} (h : isFiniteBits f = true) :
    (decode f).q ≤ 971 := decode_q_le_bits (w := f.toBits) h

theorem decode_m_lt_of_finite
    {f : _root_.Float} (h : isFiniteBits f = true) :
    (decode f).m < 2 ^ 53 := decode_m_lt_bits (w := f.toBits) h

/-- Convenience bundle: `decode` outputs satisfy the Schubfach hypotheses. -/
theorem decode_invariants_of_finite (f : _root_.Float)
    (h : isFiniteBits f = true) :
    (decode f).m < 2 ^ 53 ∧ -1074 ≤ (decode f).q ∧ (decode f).q ≤ 971 :=
  decode_invariants_bits f.toBits h

/-- `toDecimal` rejects NaN. -/
theorem toDecimal_nan_rejected (f : _root_.Float) (h : isNaNBits f = true) :
    ¬ ∃ d, toDecimal f = .ok d := toDecimalBits_nan_rejected f.toBits h

/-- `toDecimal` rejects Infinity. -/
theorem toDecimal_inf_rejected (f : _root_.Float) (h : isInfBits f = true) :
    ¬ ∃ d, toDecimal f = .ok d := toDecimalBits_inf_rejected f.toBits h

/-- For finite `f` with `(decode f).m = 0`, `toDecimal` returns the signed
    canonical zero. -/
theorem toDecimal_zero (f : _root_.Float)
    (h_fin : isFiniteBits f = true)
    (h_zero : (decode f).m = 0) :
    toDecimal f = .ok ⟨(decode f).sign, 0, 0⟩ :=
  toDecimalBits_zero f.toBits h_fin h_zero

/-- For a finite non-zero `Float`, `toDecimal` returns `.ok d` where `d` is
    `Decimal.mk' sign sig exp` for some `(sig, exp)` lying in the
    rounding interval `R_v` of `(m, q) = decode f`. -/
theorem toDecimal_in_Rv
    (f : _root_.Float)
    (h_fin : isFiniteBits f = true) :
    let d := decode f
    d.m ≠ 0 →
    ∃ result, toDecimal f = .ok result ∧
      ∃ sig exp,
        Decimal.mk' d.sign sig exp = result ∧
        inRoundingInterval sig exp d.m d.q (isIrregular d.m d.q) = true :=
  toDecimalBits_in_Rv f.toBits h_fin

end Srtfp.Schubfach

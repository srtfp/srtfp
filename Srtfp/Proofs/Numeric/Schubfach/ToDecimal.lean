/- `toDecimal` output lies in R_v (M3.8.7).

   This file wraps the M3.8.6 result `shortestUnsigned_mem_rv` together with
   the bit-level invariants of `decode` (extracted locally from `Float/Bits.lean`)
   to prove that `Schubfach.toDecimal f` succeeds on finite Floats and that the
   produced `Decimal`'s underlying significand / exponent pair lies in the
   rounding interval `R_v` of `(m, q) = decode f`.

   The statement is phrased existentially: there exist `sig, exp` such that
   `Decimal.mk' d.sign sig exp = result` and the pair `(sig, exp)` satisfies
   `inRoundingInterval`. The canonicalisation performed by `mk'` strips
   trailing decimal zeros from the `Decimal`'s fields; this loses information
   about the raw `(sig, exp)` pair, so we keep the raw pair as the existential
   witness. The Clinger correctness theorem (M4) can then consume the
   `inRoundingInterval` witness independently of any canonicalisation. -/

import Srtfp.Proofs.Numeric.Schubfach.Shorter

namespace PP.Numeric.Schubfach

open PP.Numeric.Float
open PP.Numeric

/-! ## decode invariants

For finite `Float`s, `decode` produces `(m, q)` satisfying the binary64
range `m < 2^53`, `-1074 ≤ q ≤ 971`. These lemmas mirror the private
ones in `Float/Rep.lean` (kept private there to avoid namespace pollution).
We re-expose them here scoped to Schubfach because the public API of M3.8.7
needs them as hypotheses to `shortestUnsigned_mem_rv`. -/

private theorem mantissaBits_lt (f : _root_.Float) :
    mantissaBits f < 2 ^ 52 := by
  unfold mantissaBits
  rw [UInt64.toNat_and]
  have hmask : ((0x000F_FFFF_FFFF_FFFF : UInt64).toNat) = 4503599627370495 := by decide
  rw [hmask]
  have hle : f.toBits.toNat &&& 4503599627370495 ≤ 4503599627370495 := Nat.and_le_right
  have hpow : (2 : Nat) ^ 52 = 4503599627370496 := by decide
  omega

theorem decode_q_ge_of_finite
    {f : _root_.Float} (_h : isFiniteBits f = true) :
    -1074 ≤ (decode f).q := by
  unfold decode
  by_cases he : biasedExpBits f = 0
  · simp [he]
  · simp [he]
    have h1 : 1 ≤ biasedExpBits f := Nat.one_le_iff_ne_zero.mpr he
    omega

theorem decode_q_le_of_finite
    {f : _root_.Float} (h : isFiniteBits f = true) :
    (decode f).q ≤ 971 := by
  have hfin : biasedExpBits f < 2047 := by
    unfold isFiniteBits at h; simpa using h
  unfold decode
  by_cases he : biasedExpBits f = 0
  · simp [he]
  · simp [he]
    have hle : biasedExpBits f ≤ 2046 := Nat.lt_succ_iff.mp hfin
    omega

theorem decode_m_lt_of_finite
    {f : _root_.Float} (h : isFiniteBits f = true) :
    (decode f).m < 2 ^ 53 := by
  have hfin : biasedExpBits f < 2047 := by
    unfold isFiniteBits at h; simpa using h
  unfold decode
  by_cases he : biasedExpBits f = 0
  · simp [he]
    have h1 := mantissaBits_lt f
    have h2 : (2 : Nat) ^ 52 < 2 ^ 53 := by decide
    omega
  · simp [he]
    have hmb := mantissaBits_lt f
    have h52 : (2 : Nat) ^ 52 = 4503599627370496 := by decide
    have h53 : (2 : Nat) ^ 53 = 9007199254740992 := by decide
    omega

/-- Convenience bundle: `decode` outputs satisfy the Schubfach hypotheses. -/
theorem decode_invariants_of_finite (f : _root_.Float)
    (h : isFiniteBits f = true) :
    (decode f).m < 2 ^ 53 ∧ -1074 ≤ (decode f).q ∧ (decode f).q ≤ 971 :=
  ⟨decode_m_lt_of_finite h, decode_q_ge_of_finite h, decode_q_le_of_finite h⟩

/-! ## NaN / Infinity rejection -/

/-- `toDecimal` rejects NaN. -/
theorem toDecimal_nan_rejected (f : _root_.Float) (h : isNaNBits f = true) :
    ¬ ∃ d, toDecimal f = .ok d := by
  intro ⟨d, hd⟩
  unfold toDecimal at hd
  rw [h] at hd
  simp at hd

/-- `toDecimal` rejects Infinity. -/
theorem toDecimal_inf_rejected (f : _root_.Float) (h : isInfBits f = true) :
    ¬ ∃ d, toDecimal f = .ok d := by
  intro ⟨d, hd⟩
  unfold toDecimal at hd
  -- isInfBits → biasedExpBits = 2047 ∧ mantissaBits = 0.
  -- That makes isNaNBits false (which needs mantissaBits ≠ 0).
  have hmb : mantissaBits f = 0 := by
    unfold isInfBits at h; simp at h; exact h.2
  have hnan : isNaNBits f = false := by
    unfold isNaNBits; simp [hmb]
  rw [hnan, h] at hd
  simp at hd

/-! ## Zero case -/

/-- For finite `f` with `(decode f).m = 0`, `toDecimal` returns the signed
    canonical zero. -/
theorem toDecimal_zero (f : _root_.Float)
    (h_fin : isFiniteBits f = true)
    (h_zero : (decode f).m = 0) :
    toDecimal f = .ok ⟨(decode f).sign, 0, 0⟩ := by
  unfold toDecimal
  -- isFiniteBits → biasedExpBits < 2047 → ¬ isNaNBits and ¬ isInfBits.
  have hfin_lt : biasedExpBits f < 2047 := by
    unfold isFiniteBits at h_fin; simpa using h_fin
  have hnan : isNaNBits f = false := by
    unfold isNaNBits
    have : ¬ biasedExpBits f = 2047 := by omega
    simp [this]
  have hinf : isInfBits f = false := by
    unfold isInfBits
    have : ¬ biasedExpBits f = 2047 := by omega
    simp [this]
  rw [hnan, hinf]
  simp [h_zero]

/-! ## Non-zero finite case: the main theorem -/

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
        inRoundingInterval sig exp d.m d.q (isIrregular d.m d.q) = true := by
  intro d hm_ne
  -- Discharge non-finite branches of toDecimal.
  have hfin_lt : biasedExpBits f < 2047 := by
    unfold isFiniteBits at h_fin; simpa using h_fin
  have hnan : isNaNBits f = false := by
    unfold isNaNBits
    have : ¬ biasedExpBits f = 2047 := by omega
    simp [this]
  have hinf : isInfBits f = false := by
    unfold isInfBits
    have : ¬ biasedExpBits f = 2047 := by omega
    simp [this]
  -- Decode invariants.
  have ⟨h_m_lt, h_q_lo, h_q_hi⟩ := decode_invariants_of_finite f h_fin
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
  -- toDecimal f = .ok (Decimal.mk' d.sign ...).
  unfold toDecimal
  rw [hnan, hinf]
  -- After rewriting NaN/Inf branches off, the remaining branch matches.
  -- `d` is `decode f` definitionally; route via the m ≠ 0 branch.
  have hm_ne' : (decode f).m ≠ 0 := hm_ne
  simp [hm_ne']
  rfl

end PP.Numeric.Schubfach

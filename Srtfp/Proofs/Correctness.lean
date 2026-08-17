/- Schubfach + Clinger correctness — the headline theorem.

   This file is the audit-friendly artefact: it composes the existing
   sub-milestones into a single user-facing statement of what
   `Schubfach.toDecimal` and `Clinger.ofDecimal` together achieve.

   A reader can audit this file in isolation; everything that follows
   (`inRoundingInterval`, `decode`, `kOfMQ`, `pickNearer`, the nine
   M3.8.x sub-milestones) is hidden in the imported proofs.

   ## Contents

   * `correctness_proof`      — `IsCorrectPrinterBits Schubfach.toDecimal`
   * `printer_unique_proof`   — the spec pins the printer extensionally
   * `specOutput_eq_output`   — a spec output IS the algorithm's output
   * `spec_output_exists_unique_proof` — per-float `∃!`

   plus the clause-(3) tie-break machinery (same-digit-length analysis,
   canonical-parity upgrade) they are built from. -/

import Srtfp.Proofs.CorrectnessSpec
import Srtfp.Proofs.RoundTrip
import Srtfp.Proofs.Schubfach.Minimal
import Srtfp.Proofs.Schubfach.TieBreak
import Srtfp.NatLog
import Srtfp.Tactics

open Srtfp.Compat

namespace Srtfp

open Schubfach Clinger Srtfp.Float Decimal
open Srtfp.Schubfach (decDigitLength)

/-! ## Bit-only facts about `decode` and `isFiniteBits`

These are tiny re-exports of facts buried as `private` lemmas in
`FloatParser.lean`. We re-prove them here so this file stands alone. -/

/-- `Word.decode` is a congruence along word equality (kept as a named
lemma so the rewrite sites below read like their `Float` ancestors). -/
private theorem decode_eq_of_toBits_eq
    {w v : UInt64} (h : w = v) :
    Word.decode w = Word.decode v := by
  rw [h]

/-! ## Zero-value vocabulary facts -/

private theorem toRat_zero (d : Decimal) (h : d.significand = 0) :
    Decimal.toRat d = 0 := by
  unfold Decimal.toRat
  rw [h]
  push_cast
  grind

private theorem wordVal_zero (w : UInt64) (h : (Word.decode w).m = 0) :
    Schubfach.wordVal w = 0 := by
  unfold Schubfach.wordVal Schubfach.magVal
  rw [h]
  push_cast
  grind

private theorem toRat_ne_zero (d : Decimal) (h : d.significand ≠ 0) :
    Decimal.toRat d ≠ 0 := by
  unfold Decimal.toRat
  have h1 : ((d.significand : ℚ)) ≠ 0 := by exact_mod_cast h
  have h2 : (10 : ℚ) ^ d.exponent ≠ 0 := Rat.ne_of_gt (Rat.zpow_pos (by decide))
  by_cases hs : d.sign <;> simp only [hs, if_true, if_false, Bool.false_eq_true] <;>
    intro hcon <;>
    rcases Rat.mul_eq_zero.mp (by grind : (d.significand : ℚ) * (10:ℚ) ^ d.exponent = 0) with
      h0 | h0 <;> first | exact h1 h0 | exact h2 h0

/-- `IsSpecOutputBits` with the competitor clauses split into two `∀`s (the
proofs build and consume them separately). -/
private theorem Schubfach.isSpecOutput_iff (w : UInt64) (d : Decimal) :
    Schubfach.IsSpecOutputBits w d ↔
      Decimal.IsCanonical d
    ∧ Schubfach.RoundTripsBits w d
    ∧ (∀ d' : Decimal, Decimal.IsCanonical d' → Schubfach.RoundTripsBits w d' →
         decDigitLength d.significand ≤ decDigitLength d'.significand)
    ∧ (∀ d' : Decimal, Decimal.IsCanonical d' → Schubfach.RoundTripsBits w d' →
         decDigitLength d'.significand = decDigitLength d.significand →
           d = d'
         ∨ |Decimal.toRat d - Schubfach.wordVal w|
             < |Decimal.toRat d' - Schubfach.wordVal w|
         ∨ ( |Decimal.toRat d - Schubfach.wordVal w|
               = |Decimal.toRat d' - Schubfach.wordVal w|
             ∧ d.significand % 2 = 0 )) := by
  constructor
  · rintro ⟨h0, h1, h⟩
    refine ⟨h0, h1, fun d' hc hrt => ?_, fun d' hc hrt hl => ?_⟩
    · by_cases hne : d' = d
      · subst hne; omega
      · rcases h d' hne hc hrt with hlt | ⟨heq, _⟩ <;> omega
    · by_cases hne : d' = d
      · exact Or.inl hne.symm
      · rcases h d' hne hc hrt with hlt | ⟨_, ht⟩
        · exfalso; omega
        · exact Or.inr ht
  · rintro ⟨h0, h1, h2, h3⟩
    refine ⟨h0, h1, fun d' hne hc hrt => ?_⟩
    by_cases hl : decDigitLength d'.significand = decDigitLength d.significand
    · rcases h3 d' hc hrt hl with heq | ht
      · exact absurd heq.symm hne
      · exact Or.inr ⟨hl, ht⟩
    · have h2' := h2 d' hc hrt
      exact Or.inl (by omega)

/-- The two signed-zero bit patterns are distinct, so bits pin the sign. -/
private theorem pack_zero_sign_inj (s' s : Bool)
    (h : Word.pack s' 0 0 = Word.pack s 0 0) : s' = s := by
  cases s' <;> cases s <;> first
    | rfl
    | exact absurd h (by decide)

/-- For finite `w` with zero magnitude, the signed canonical zero reads
back to exactly `w`'s bits. -/
private theorem ofDecimal_signedZero_bits (w : UInt64)
    (h_m : (Word.decode w).m = 0) :
    Clinger.ofDecimalBits (⟨(Word.decode w).sign, 0, 0⟩ : Decimal) = w := by
  have h_be : Word.biasedExp w = 0 := by
    by_contra he
    have hm_def : (Word.decode w).m = Word.mantissa w + (1 <<< 52) := by
      unfold Word.decode; rw [if_neg he]
    have h52 : (1 : Nat) <<< 52 = 2 ^ 52 := by decide
    rw [hm_def, h52] at h_m
    have hbig : (2 : Nat) ^ 52 = 4503599627370496 := by decide
    omega
  have h_mant : Word.mantissa w = 0 := by
    have hm_def : (Word.decode w).m = Word.mantissa w := by
      unfold Word.decode; rw [if_pos h_be]
    omega
  have h_sign : (Word.decode w).sign = Word.signBit w := by
    unfold Word.decode
    simp [h_be]
  have h_lhs : Clinger.ofDecimalBits (⟨(Word.decode w).sign, 0, 0⟩ : Decimal)
      = Word.pack (Word.decode w).sign 0 0 := by
    show Clinger.decimalToFloatBits (Word.decode w).sign 0 0 = _
    unfold Clinger.decimalToFloatBits
    rw [if_pos rfl]
    rfl
  have h2 : Word.pack (Word.signBit w) (Word.biasedExp w) (Word.mantissa w)
      = Word.pack (Word.decode w).sign 0 0 := by
    rw [h_be, h_mant, h_sign]
  rw [h_lhs, ← h2]
  have h_nan : Word.isNaN w = false := by
    unfold Word.isNaN
    have : ¬ Word.biasedExp w = 2047 := by omega
    simp [this]
  exact pack_decode_eq w h_nan

/-- The bits of `ofDecimal` on a sig-0 decimal, in `Word.pack` form. -/
private theorem ofDecimal_sig0_bits (d : Decimal) (h : d.significand = 0) :
    Clinger.ofDecimalBits d = Word.pack d.sign 0 0 := by
  show Clinger.decimalToFloatBits d.sign d.significand d.exponent = _
  unfold Clinger.decimalToFloatBits
  rw [if_pos h]
  rfl

/-! ## Schubfach output is canonical -/

/-- Helper: for finite nonzero `w`, the Decimal returned by
    `Schubfach.toDecimalBits w` is canonical (its significand is positive and
    not divisible by 10, the second branch of `IsCanonical`). -/
private theorem toDecimal_isCanonical
    (w : UInt64)
    (h_fin : Word.isFinite w = true)
    (h_nz : (Word.decode w).m ≠ 0)
    (d : Decimal)
    (h_eq : Schubfach.toDecimalBits w = .ok d) :
    Decimal.IsCanonical d := by
  -- Unfold toDecimal to extract d's explicit form.
  have h_be_lt : Word.biasedExp w < 2047 := by
    unfold Word.isFinite at h_fin; simpa using h_fin
  have h_nan : Word.isNaN w = false := by
    unfold Word.isNaN
    have : ¬ Word.biasedExp w = 2047 := by omega
    simp [this]
  have h_inf : Word.isInf w = false := by
    unfold Word.isInf
    have : ¬ Word.biasedExp w = 2047 := by omega
    simp [this]
  have ⟨h_m_lt, h_q_lo, h_q_hi⟩ :=
    Srtfp.Schubfach.decode_invariants_bits w h_fin
  have h_m_pos : 1 ≤ (Word.decode w).m := Nat.one_le_iff_ne_zero.mpr h_nz
  have h_sig_pos : 1 ≤ (shortestUnsigned (Word.decode w).m (Word.decode w).q).1 :=
    Srtfp.Schubfach.shortestUnsigned_sig_pos
      (Word.decode w).m (Word.decode w).q h_m_pos h_m_lt h_q_lo h_q_hi
  have h_sig_ne : (shortestUnsigned (Word.decode w).m (Word.decode w).q).1 ≠ 0 :=
    Nat.one_le_iff_ne_zero.mp h_sig_pos
  -- Now unfold toDecimalBits to identify d with Decimal.mk' ...
  unfold Schubfach.toDecimalBits at h_eq
  rw [if_neg (by simp [h_nan]), if_neg (by simp [h_inf])] at h_eq
  simp only [h_nz, ↓reduceIte, Except.ok.injEq] at h_eq
  -- h_eq : Decimal.mk' (Word.decode w).sign (...).1 (...).2 = d
  -- Apply mk_pos_props.
  have ⟨_, h_ne, h_mod, _, _⟩ := mk_pos_props
    (Word.decode w).sign (shortestUnsigned (Word.decode w).m (Word.decode w).q).1
    (shortestUnsigned (Word.decode w).m (Word.decode w).q).2 h_sig_ne
  rw [h_eq] at h_ne h_mod
  -- Conclude: second branch of IsCanonical.
  unfold Decimal.IsCanonical
  exact Or.inr ⟨h_ne, h_mod⟩

/-! ## Clause (3) — tie-breaking at the output scale

The output `(out_sig, out_exp) = shortestUnsigned (Word.decode w).m (Word.decode w).q`
is, *at scale `out_exp`*, the closest grid point to `v = magVal m q` among
all scale-`out_exp` grid points (breaking exact ties toward an even
significand). This is the unsigned core of clause (3); it is then lifted to
signed `Decimal.toRat` distances and to the `Decimal` `d`.

The argument splits on `shortestUnsigned_length_relation`:

  * **fallback** (`out_exp = k`, `out_sig = pickNearer s k`): both floor
    neighbours `s, s+1` lie in `R_v`, so `tieBreak_unsigned_fallback`
    applies for *any* competitor `sig'`.
  * **shorter form** (`out_exp = k+1`): the output is `sHigh` or `sHigh+1`
    with only one of them in `R_v`; `Schubfach_K1_candidates` confines any
    `R_v` competitor to `{sHigh, sHigh+1}`, and
    `tieBreak_unsigned_single_sided` forces equality. -/

/-- **Unsigned clause (3) at scale `out_exp`.** Any scale-`out_exp` grid
point `sig'` in `R_v` is the output `out_sig`, strictly farther from `v`,
or an exact tie with `out_sig` even. -/
private theorem shortestUnsigned_clause3_same_exp
    (m : Nat) (q : Int)
    (hm_pos : 1 ≤ m) (hm_lt : m < 2 ^ 53) (hq_lo : -1074 ≤ q) (hq_hi : q ≤ 971)
    (sig' : Nat) (exp' : Int)
    (h_exp : exp' = (shortestUnsigned m q).2)
    (h_mem : inRoundingInterval sig' exp' m q (isIrregular m q) = true) :
    let out_sig := (shortestUnsigned m q).1
    sig' = out_sig
      ∨ |magVal m q - gridVal out_sig (shortestUnsigned m q).2|
          < |magVal m q - gridVal sig' (shortestUnsigned m q).2|
      ∨ ( |magVal m q - gridVal out_sig (shortestUnsigned m q).2|
            = |magVal m q - gridVal sig' (shortestUnsigned m q).2|
          ∧ out_sig % 2 = 0 ) := by
  intro out_sig
  set k := kOfMQ m q with hk
  set s := shiftedSig m q k with hs
  have h_rel := shortestUnsigned_length_relation m q
  rcases h_rel with ⟨hs_big, h_exp_eq, h_or⟩ | ⟨h_exp_eq, h_sig_eq⟩
  · -- Shorter form: out_exp = k+1, out_sig ∈ {s/10, s/10+1}; single-sided.
    -- All R_v competitors at scale k+1 are confined to {s/10, s/10+1}.
    have h_exp' : exp' = k + 1 := by rw [h_exp, h_exp_eq]
    subst h_exp'
    have h_cands := Schubfach_K1_candidates m q hm_pos hm_lt hq_lo hq_hi sig' h_mem
    -- The output is in R_v at k+1.
    have h_out_mem : inRoundingInterval out_sig (k + 1) m q (isIrregular m q) = true := by
      have h_mem_out := shortestUnsigned_mem_rv m q hm_pos hm_lt hq_lo hq_hi
      have h2 : (shortestUnsigned m q).2 = k + 1 := h_exp_eq
      show inRoundingInterval (shortestUnsigned m q).1 (k + 1) m q (isIrregular m q) = true
      rw [← h2]; exact h_mem_out
    -- The "other" neighbour is not in R_v (at most one of s/10, s/10+1 by strict step).
    -- We feed single-sided with out ∈ {s/10, s/10+1} and the not-membership of its sibling.
    have h_out_cand : out_sig = s / 10 ∨ out_sig = s / 10 + 1 := h_or
    -- Sibling-not-in-R_v: at most one of s/10, s/10+1 in R_v (strict K+1 step).
    have h_at_most_one :
        ¬ (inRoundingInterval (s / 10) (k + 1) m q (isIrregular m q) = true ∧
           inRoundingInterval (s / 10 + 1) (k + 1) m q (isIrregular m q) = true) := by
      rintro ⟨h_uT, h_wT⟩
      have h_strict :
          fourVR m q (k + 1) - fourVL m q (k + 1) (isIrregular m q)
            < fourW (s / 10) q (k + 1) - fourU (s / 10) q (k + 1) :=
        fourVR_sub_fourVL_lt_step_K1 m q hm_pos hm_lt hq_lo hq_hi (s / 10)
      -- Bracket bounds via the connectedness route: s/10 and s/10+1 both in R_v.
      have h_mid : inRoundingInterval (s / 10) (k + 1) m q (isIrregular m q) = true ∧
                   inRoundingInterval (s / 10 + 1) (k + 1) m q (isIrregular m q) = true :=
        ⟨h_uT, h_wT⟩
      -- Use the cleared fourU brackets to contradict the strict step.
      have h_w_eq : fourU (s / 10 + 1) q (k + 1) = fourW (s / 10) q (k + 1) := by
        rw [fourU_eq, fourW_eq]; push_cast; rfl
      have hbu := (inRoundingInterval_iff (s / 10) (k + 1) m q (isIrregular m q)).mp h_uT
      have hbw := (inRoundingInterval_iff (s / 10 + 1) (k + 1) m q (isIrregular m q)).mp h_wT
      obtain ⟨hbuL, _⟩ := hbu
      obtain ⟨_, hbwR⟩ := hbw
      have h_VL_le_u : fourVL m q (k + 1) (isIrregular m q) ≤ fourU (s / 10) q (k + 1) := by
        rcases hbuL with h | ⟨h, _⟩ <;> omega
      have h_w_le_VR : fourU (s / 10 + 1) q (k + 1) ≤ fourVR m q (k + 1) := by
        rcases hbwR with h | ⟨h, _⟩ <;> omega
      rw [h_w_eq] at h_w_le_VR
      omega
    have h_other_not :
        (out_sig = s / 10 → inRoundingInterval (s / 10 + 1) (k + 1) m q (isIrregular m q) = false)
        ∧ (out_sig = s / 10 + 1 → inRoundingInterval (s / 10) (k + 1) m q (isIrregular m q) = false) := by
      constructor
      · intro h_os
        rcases Bool.eq_false_or_eq_true (inRoundingInterval (s / 10 + 1) (k + 1) m q (isIrregular m q)) with h | h
        · exact absurd ⟨by rw [← h_os]; exact h_out_mem, h⟩ h_at_most_one
        · exact h
      · intro h_os
        rcases Bool.eq_false_or_eq_true (inRoundingInterval (s / 10) (k + 1) m q (isIrregular m q)) with h | h
        · exact absurd ⟨h, by rw [← h_os]; exact h_out_mem⟩ h_at_most_one
        · exact h
    -- Apply single-sided at scale k+1.
    have h_eq := tieBreak_unsigned_single_sided m q (k + 1) (s / 10) out_sig
                    h_out_cand h_other_not sig' h_cands h_mem
    exact Or.inl h_eq
  · -- Fallback: out_exp = k, out_sig = pickNearer s k; sig' ∈ R_v at scale k.
    have h_exp' : exp' = k := by rw [h_exp, h_exp_eq]
    subst h_exp'
    have hR11 := shiftedSig_or_succ_mem_rv m q hm_pos hm_lt hq_lo hq_hi
    have h_out_eq : out_sig = pickNearer s k m q := h_sig_eq
    rw [h_out_eq, h_exp_eq]
    -- tieBreak_unsigned_scaleK_pn handles both-in and single-sided fallback
    -- using only sig' ∈ R_v (h_mem) and R_v-connectedness.
    exact tieBreak_unsigned_scaleK_pn m q k s hs.symm hR11 sig' h_mem

/-! ## Clause (3) at same digit length — scale-uniqueness + boundary

We upgrade the scale-`out_exp` tie-break to a same-*digit-length* tie-break.
Let `(cs, ce)` be the canonical output (`= (d.significand, d.exponent)`), with
`out_sig = cs · 10^t` and `ce = out_exp + t`.  A canonical competitor
`(sig', exp')` in `R_v` with `decDigitLength sig' = decDigitLength cs` has, by
`samelen_exp_diff_le_one`, `|exp' - ce| ≤ 1`.

  * `exp' ≥ out_exp` (covers `exp' = ce`, `exp' = ce + 1`, and `exp' = ce - 1`
    when `t ≥ 1`): shift the competitor *down* to scale `out_exp`
    (`gridVal sig' exp' = gridVal (sig' · 10^(exp'-out_exp)) out_exp`) and apply
    `shortestUnsigned_clause3_same_exp`.

  * `exp' < out_exp` (forces `t = 0`, `exp' = out_exp - 1`, the power-of-ten
    *boundary*): the competitor is a finer grid point strictly below `v`'s
    floor neighbour `gridVal sK out_exp` (otherwise the length-`L-1` point `sK`
    would sit in `R_v`, contradicting shortest-ness), so the output — being a
    nearest scale-`out_exp` grid point — is strictly closer. -/

/-- The output value is no farther from `v` than any scale-`out_exp` grid
point: `|v − Ov| ≤ |v − gridVal n out_exp|`.  (Repackaging of
`shortestUnsigned_clause3_same_exp` against the grid point `n`.) -/
private theorem output_le_dist_at_outexp
    (m : Nat) (q : Int)
    (hm_pos : 1 ≤ m) (hm_lt : m < 2 ^ 53) (hq_lo : -1074 ≤ q) (hq_hi : q ≤ 971)
    (n : Nat) (h_mem : inRoundingInterval n (shortestUnsigned m q).2 m q (isIrregular m q) = true) :
    |magVal m q - gridVal (shortestUnsigned m q).1 (shortestUnsigned m q).2|
      ≤ |magVal m q - gridVal n (shortestUnsigned m q).2| := by
  have h := shortestUnsigned_clause3_same_exp m q hm_pos hm_lt hq_lo hq_hi
              n (shortestUnsigned m q).2 rfl h_mem
  simp only at h
  rcases h with h_eq | h_lt | ⟨h_eqd, _⟩
  · rw [h_eq]; exact le_refl _
  · exact le_of_lt h_lt
  · exact le_of_eq h_eqd

/-- **Unsigned clause (3) at the same digit length, competitor scale `≥ out_exp`.**
Let `cs, ce` be the canonical output significand/exponent (so `out_sig = cs · 10^t`,
`ce = out_exp + t`).  A canonical competitor `(sig', exp')` in `R_v` with
`decDigitLength sig' = decDigitLength cs` AND `exp' ≥ out_exp` is the canonical
output, strictly farther from `v`, or an exact tie with the output even.

The `exp' ≥ out_exp` hypothesis covers same-exponent competitors, coarser
competitors, and finer competitors whenever the raw output carries trailing
zeros (`t ≥ 1`).  The complementary boundary case (`exp' = out_exp − 1` with
`t = 0`, the power-of-ten straddle) requires the additional scale-selection
facts `1 ≤ shiftedSig m q out_exp` and `sig' < 10 · shiftedSig m q out_exp`,
not yet available here. -/
private theorem shortestUnsigned_clause3_same_len_ge
    (m : Nat) (q : Int)
    (hm_pos : 1 ≤ m) (hm_lt : m < 2 ^ 53) (hq_lo : -1074 ≤ q) (hq_hi : q ≤ 971)
    (cs : Nat) (ce : Int) (t : Nat)
    (h_cs_pos : 1 ≤ cs) (h_cs_canon : cs % 10 ≠ 0)
    (h_out_sig : (shortestUnsigned m q).1 = cs * 10 ^ t)
    (h_ce : ce = (shortestUnsigned m q).2 + (t : Int))
    (sig' : Nat) (exp' : Int)
    (h_sig'_pos : 1 ≤ sig') (h_sig'_canon : sig' % 10 ≠ 0)
    (h_mem : inRoundingInterval sig' exp' m q (isIrregular m q) = true)
    (h_len : decDigitLength sig' = decDigitLength cs)
    (h_ge : (shortestUnsigned m q).2 ≤ exp') :
    (sig' = cs ∧ exp' = ce)
      ∨ |magVal m q - gridVal cs ce| < |magVal m q - gridVal sig' exp'|
      ∨ ( |magVal m q - gridVal cs ce| = |magVal m q - gridVal sig' exp'|
          ∧ (shortestUnsigned m q).1 % 2 = 0 ) := by
  set out_exp := (shortestUnsigned m q).2 with h_out_exp
  set out_sig := (shortestUnsigned m q).1 with h_out_sig_def
  -- The output value equals gridVal cs ce  (= gridVal out_sig out_exp).
  have h_out_val : gridVal out_sig out_exp = gridVal cs ce := by
    rw [h_out_sig, h_ce, ← gridVal_mul_pow10 cs t out_exp]
  -- cs, ce form the canonical output; its rounding-interval membership.
  -- Decade comparison: |exp' - ce| ≤ 1 via samelen_exp_diff_le_one.
  -- We need the canonical output in R_v: gridVal cs ce ∈ R_v at scale ce.
  have h_out_mem_outexp : inRoundingInterval out_sig out_exp m q (isIrregular m q) = true :=
    shortestUnsigned_mem_rv m q hm_pos hm_lt hq_lo hq_hi
  have h_out_ne : out_sig ≠ 0 := Nat.one_le_iff_ne_zero.mp
    (shortestUnsigned_sig_pos m q hm_pos hm_lt hq_lo hq_hi)
  -- Canonical (cs, ce) is in R_v (value preserved by canonicalisation).
  have h_cs_mem : inRoundingInterval cs ce m q (isIrregular m q) = true := by
    -- cs * 10^t = out_sig, ce = out_exp + t, so shifting cs up to out_sig.
    have hshift := inRoundingInterval_mul10pow_shift_down cs t (out_exp + t) m q (isIrregular m q)
    -- inRI (cs * 10^t) ((out_exp+t) - t) = inRI cs (out_exp+t)
    have he : (out_exp + (t : Int)) - (t : Int) = out_exp := by grind
    rw [he] at hshift
    rw [← h_out_sig] at hshift
    -- hshift : inRI out_sig out_exp = inRI cs (out_exp + t)
    rw [h_ce]
    rw [← hshift]; exact h_out_mem_outexp
  -- Scale gap ≤ 1 between competitor and canonical output.
  have h_gap := samelen_exp_diff_le_one m q hm_pos
    sig' exp' h_sig'_pos h_mem cs ce h_cs_pos h_cs_mem (by rw [h_len])
  -- L := decDigitLength cs.
  set L := decDigitLength cs with hL
  -- Relate decDigitLength out_sig = L + t.
  have h_dl_out : decDigitLength out_sig = L + t := by
    rw [h_out_sig]; exact decDigitLength_mul_pow10 cs t h_cs_pos
  -- exp' ≥ out_exp (hypothesis h_ge).  Shift competitor down to out_exp.
  -- j := (exp' - out_exp).toNat ; sig'' := sig' * 10^j ; gridVal sig'' out_exp = gridVal sig' exp'.
  set j : Nat := (exp' - out_exp).toNat with hj
  have hj_eq : (j : Int) = exp' - out_exp := by
    apply Int.toNat_of_nonneg; omega
  have h_shift_exp : exp' - (j : Int) = out_exp := by rw [hj_eq]; grind
  have h_mem_shift :
      inRoundingInterval (sig' * 10 ^ j) out_exp m q (isIrregular m q) = true := by
    have hs := inRoundingInterval_mul10pow_shift_down sig' j exp' m q (isIrregular m q)
    rw [h_shift_exp] at hs
    rw [hs]; exact h_mem
  have h_grid_shift : gridVal (sig' * 10 ^ j) out_exp = gridVal sig' exp' := by
    rw [gridVal_mul_pow10 sig' j out_exp, hj_eq]
    congr 1; grind
  -- Apply the scale-out_exp tie-break to sig''.
  have h3 := shortestUnsigned_clause3_same_exp m q hm_pos hm_lt hq_lo hq_hi
               (sig' * 10 ^ j) out_exp rfl h_mem_shift
  simp only at h3
  -- Rewrite distances: gridVal out_sig out_exp = gridVal cs ce; gridVal sig'' out_exp = gridVal sig' exp'.
  rw [h_out_val] at h3
  rw [h_grid_shift] at h3
  rcases h3 with h_eqs | h_lt | ⟨h_eqd, h_even⟩
  · -- sig' * 10^j = out_sig = cs * 10^t.  With both canonical, sig'=cs and j=t,
    -- hence exp' = out_exp + j = out_exp + t = ce.
    left
    have h_eq2 : sig' * 10 ^ j = cs * 10 ^ t := by rw [← h_out_sig]; exact h_eqs
    have huniq := canonical_pow10_unique sig' cs j t h_sig'_pos h_cs_pos
                    h_sig'_canon h_cs_canon h_eq2
    refine ⟨huniq.1, ?_⟩
    rw [h_ce]
    have : exp' = out_exp + (j : Int) := by rw [hj_eq]; grind
    rw [this, huniq.2]
  · exact Or.inr (Or.inl h_lt)
  · -- tie; the output significand `out_sig = (shortestUnsigned m q).1` is even.
    exact Or.inr (Or.inr ⟨h_eqd, h_even⟩)

/-! ## Clause (3) boundary case — `exp' = out_exp − 1`

The complementary case to `shortestUnsigned_clause3_same_len_ge`: a canonical
competitor `(sig', out_exp − 1)` of the *same digit length* as the (canonical,
`t = 0`) output, one decade *finer* than the output scale.  Here the output is
always **strictly** closer to `v` (no tie is possible at the boundary).

Let `e := out_exp − 1`, `n := shiftedSig m q out_exp` (the floor neighbour of
`v` at the output scale).  Two clean facts drive the proof:

  * `out_sig ∈ {n, n+1}` (floor/ceil of `v` at scale `out_exp`), and `v` is
    bracketed `gridVal n out_exp ≤ v < gridVal (n+1) out_exp`.
  * `C := gridVal sig' e` is strictly below the floor grid point:
    `sig' < 10·n`, because `sig' < 10^L ≤ 10·10^(L-1) ≤ 10·n` (canonical
    length-`L` competitor vs. `n ≥ 10^(L-1)`).  Hence `C < gridVal n out_exp`.

The conclusion `|v − O| < |v − C|` reduces (since `C < O`) to `C + O < 2v`.
We supply `gridVal n out_exp + O ≤ 2v`:

  * floor (`O = gridVal n out_exp`): `2·gridVal n out_exp ≤ 2v` from the floor
    bracket;
  * ceil with `n ∈ R_v`: directly from `output_le_dist_at_outexp` (the output
    is no farther from `v` than the floor grid point);
  * ceil with `n ∉ R_v` (single-sided): **vacuous** — `C < gridVal n out_exp`
    and `gridVal n out_exp` lying outside `R_v` on the *low* side would force
    `C ∉ R_v`, contradicting `C ∈ R_v`.

Adding `gridVal n out_exp + O ≤ 2v` to `C < gridVal n out_exp` yields
`C + O < gridVal n out_exp + O ≤ 2v`. -/

open Srtfp.Schubfach in
private theorem shortestUnsigned_clause3_same_len_boundary
    (m : Nat) (q : Int)
    (hm_pos : 1 ≤ m) (hm_lt : m < 2 ^ 53) (hq_lo : -1074 ≤ q) (hq_hi : q ≤ 971)
    (sig' : Nat) (h_sig'_pos : 1 ≤ sig') (_h_sig'_canon : sig' % 10 ≠ 0)
    (h_out_canon : (shortestUnsigned m q).1 % 10 ≠ 0)
    (h_mem : inRoundingInterval sig' ((shortestUnsigned m q).2 - 1) m q (isIrregular m q) = true)
    (h_len : decDigitLength sig' = decDigitLength (shortestUnsigned m q).1) :
    |magVal m q - gridVal (shortestUnsigned m q).1 (shortestUnsigned m q).2|
      < |magVal m q - gridVal sig' ((shortestUnsigned m q).2 - 1)| := by
  set out_exp := (shortestUnsigned m q).2 with h_out_exp
  set out_sig := (shortestUnsigned m q).1 with h_out_sig_def
  set e : Int := out_exp - 1 with he
  set k := kOfMQ m q with hk
  set s := shiftedSig m q k with hs
  set n := shiftedSig m q out_exp with hn
  set L := decDigitLength out_sig with hL
  have h_out_pos : 1 ≤ out_sig :=
    shortestUnsigned_sig_pos m q hm_pos hm_lt hq_lo hq_hi
  -- (2)+(3): out_sig ∈ {n, n+1}, and n = shiftedSig m q out_exp, n ≥ 1.
  have h_rel := shortestUnsigned_length_relation m q
  have h_out_cand : out_sig = n ∨ out_sig = n + 1 := by
    rcases h_rel with ⟨hs_big, h_exp_eq, h_or⟩ | ⟨h_exp_eq, h_sig_eq⟩
    · -- shorter form: out_exp = k+1, n = shiftedSig m q (k+1) = s/10.
      have h_n_eq : n = s / 10 := by
        rw [hn, h_out_exp, h_exp_eq, hs, hk]; exact shiftedSig_succ m q (kOfMQ m q)
      rw [h_out_sig_def]; rw [h_n_eq]; exact h_or
    · -- fallback: out_exp = k, n = shiftedSig m q k = s.
      have h_n_eq : n = s := by rw [hn, h_out_exp, h_exp_eq, hs, hk]
      rcases pickNearer_eq_or_succ s k m q with hp | hp
      · left; rw [h_out_sig_def, h_sig_eq, ← hs, ← hk, hp, ← h_n_eq]
      · right; rw [h_out_sig_def, h_sig_eq, ← hs, ← hk, hp, ← h_n_eq]
  -- n ≥ 1.
  have h_n_pos : 1 ≤ n := by
    rcases h_rel with ⟨hs_big, h_exp_eq, _⟩ | ⟨h_exp_eq, _⟩
    · -- n = s/10, s ≥ 10.
      have h_n_eq : n = s / 10 := by
        rw [hn, h_out_exp, h_exp_eq, hs, hk]; exact shiftedSig_succ m q (kOfMQ m q)
      have hs10 : 10 ≤ s := by rw [hs, hk]; exact hs_big
      rw [h_n_eq]; omega
    · -- n = s = shiftedSig m q (kOfMQ m q) ≥ 1.
      have h_n_eq : n = s := by rw [hn, h_out_exp, h_exp_eq, hs, hk]
      rw [h_n_eq, hs, hk]; exact shiftedSig_ge_one m q hm_pos hq_lo hq_hi
  -- L ≥ 1; 10^(L-1) ≤ out_sig; out_sig < 10^L; sig' < 10^L.
  have hL_pos : 1 ≤ L := decDigitLength_pos out_sig
  have h_out_lo : 10 ^ (L - 1) ≤ out_sig := pow10_decDigitLength_pred_le out_sig h_out_pos
  have h_out_hi : out_sig < 10 ^ L := lt_pow10_decDigitLength out_sig h_out_pos
  have h_sig'_hi : sig' < 10 ^ L := by
    have := lt_pow10_decDigitLength sig' h_sig'_pos
    rw [h_len] at this; exact this
  -- n ≥ 10^(L-1).
  have h_n_lo : 10 ^ (L - 1) ≤ n := by
    rcases h_out_cand with h_floor | h_ceil
    · -- out_sig = n.
      rw [h_floor] at h_out_lo; exact h_out_lo
    · -- out_sig = n + 1; canonical ⇒ out_sig ≥ 10^(L-1)+1 (L≥2) or n ≥ 1 (L=1).
      by_cases hL1 : L = 1
      · rw [hL1]; simpa using h_n_pos
      · have hL2 : 2 ≤ L := by omega
        -- out_sig ≠ 10^(L-1) since 10^(L-1) % 10 = 0 for L ≥ 2 but out_sig % 10 ≠ 0.
        have h_div : 10 ^ (L - 1) % 10 = 0 := by
          have : 1 ≤ L - 1 := by omega
          obtain ⟨j, hj⟩ : ∃ j, L - 1 = j + 1 := ⟨L - 2, by omega⟩
          rw [hj, Nat.pow_succ]; omega
        have h_ne : out_sig ≠ 10 ^ (L - 1) := fun h => h_out_canon (by rw [h]; exact h_div)
        have : 10 ^ (L - 1) + 1 ≤ out_sig := by omega
        rw [h_ceil] at this; omega
  -- sig' < 10 * n.
  have h_sig'_lt_10n : sig' < 10 * n := by
    have h1 : 10 ^ L ≤ 10 * n := by
      have h2 : 10 ^ L = 10 * 10 ^ (L - 1) := by
        conv => lhs; rw [show L = (L - 1) + 1 from by omega]
        rw [Nat.pow_succ]; grind
      rw [h2]; exact Nat.mul_le_mul_left 10 h_n_lo
    omega
  -- Geometry.  Floor bracket at scale out_exp.
  have h_bracket := magVal_bracket m q out_exp n hn
  obtain ⟨h_floor_le, h_lt_succ⟩ := h_bracket
  -- gridVal n out_exp = gridVal (10*n) e.
  have h_grid_shift : gridVal n out_exp = gridVal (10 * n) e := by
    rw [show (10 * n) = n * 10 ^ 1 from by grind, gridVal_mul_pow10 n 1 e]
    congr 1; rw [he]; push_cast; grind
  -- Monotonicity of gridVal in the significand (fixed scale).
  have gridVal_mono : ∀ (a b : Nat) (kk : Int), a < b → gridVal a kk < gridVal b kk := by
    intro a b kk hab
    unfold gridVal
    have hpos : (0 : ℚ) < (10 : ℚ) ^ kk := Rat.zpow_pos (by decide)
    have : (a : ℚ) < (b : ℚ) := by exact_mod_cast hab
    exact (mul_lt_mul_iff_of_pos_right hpos).mpr this
  -- C := gridVal sig' e  <  gridVal n out_exp.
  have h_C_lt_floor : gridVal sig' e < gridVal n out_exp := by
    rw [h_grid_shift]; exact gridVal_mono sig' (10 * n) e h_sig'_lt_10n
  -- O := gridVal out_sig out_exp  ≥  gridVal n out_exp.
  have h_O_ge_floor : gridVal n out_exp ≤ gridVal out_sig out_exp := by
    rcases h_out_cand with h | h
    · rw [h]; exact le_refl _
    · rw [h]; exact le_of_lt (gridVal_lt_succ n out_exp)
  -- C < O.
  have h_C_lt_O : gridVal sig' e < gridVal out_sig out_exp :=
    lt_of_lt_of_le h_C_lt_floor h_O_ge_floor
  -- Reduce the goal to a midpoint inequality:  C + O < 2v.
  rw [abs_gt_abs_iff_two_gt (magVal m q) (gridVal sig' e) (gridVal out_sig out_exp) h_C_lt_O]
  -- Suffices:  gridVal n out_exp + O ≤ 2v, then add C < gridVal n out_exp.
  have h_finish : gridVal sig' e + gridVal out_sig out_exp
      < gridVal n out_exp + gridVal out_sig out_exp := by grind
  refine lt_of_lt_of_le h_finish ?_
  -- Now:  gridVal n out_exp + O ≤ 2 * v.
  rcases h_out_cand with h_floor | h_ceil
  · -- FLOOR: out_sig = n, so O = gridVal n out_exp ≤ v.
    rw [h_floor]; grind
  · -- CEIL: out_sig = n + 1.
    by_cases h_n_mem : inRoundingInterval n out_exp m q (isIrregular m q) = true
    · -- n ∈ R_v: the output is no farther from v than the floor grid point n.
      have h_le := output_le_dist_at_outexp m q hm_pos hm_lt hq_lo hq_hi n h_n_mem
      -- h_le : |v - O| ≤ |v - gridVal n out_exp|, with gridVal n < O.
      have h_lt_no : ¬ (|magVal m q - gridVal n out_exp|
          < |magVal m q - gridVal out_sig out_exp|) := by
        intro hcontra; exact absurd h_le (Rat.not_le.mpr hcontra)
      have h_floor_lt_O : gridVal n out_exp < gridVal out_sig out_exp := by
        rw [h_ceil]; exact gridVal_lt_succ n out_exp
      rw [abs_lt_abs_iff_two_lt (magVal m q) (gridVal n out_exp)
            (gridVal out_sig out_exp) h_floor_lt_O] at h_lt_no
      grind
    · -- n ∉ R_v (single-sided ceil): vacuous, derive False.
      exfalso
      have h_n_false : inRoundingInterval n out_exp m q (isIrregular m q) = false :=
        Bool.eq_false_iff.mpr h_n_mem
      -- Shift n up to scale e:  inRI (10*n) e = inRI n out_exp = false.
      have h_10n_false : inRoundingInterval (10 * n) e m q (isIrregular m q) = false := by
        have hshift := inRoundingInterval_mul10pow_shift_down n 1 out_exp m q (isIrregular m q)
        rw [show out_exp - (1 : Nat) = e from by rw [he]; push_cast; grind] at hshift
        rw [show n * 10 ^ 1 = 10 * n from by grind] at hshift
        rw [hshift]; exact h_n_false
      -- fourU monotonicity in the significand at fixed scale.
      have fourU_mono : ∀ (a b : Nat), a ≤ b → fourU a q e ≤ fourU b q e := by
        intro a b hab
        rw [fourU_eq, fourU_eq]
        have hsc : (0 : Int) ≤ (tenPosPow e : Int) * (twoNegPow q : Int) := by
          have := twoNeg_tenPos_pos q e
          have h2 : (0 : Int) < (tenPosPow e : Int) * (twoNegPow q : Int) := by
            have h1 := tenPosPow_pos e
            have h2 := twoNegPow_pos q
            exact Int.mul_pos (by exact_mod_cast h1) (by exact_mod_cast h2)
          exact Int.le_of_lt h2
        have h4 : (4 * (a : Int)) ≤ (4 * (b : Int)) := by
          have : (a : Int) ≤ (b : Int) := by exact_mod_cast hab
          omega
        calc 4 * (a : Int) * (tenPosPow e : Int) * (twoNegPow q : Int)
            = (4 * (a : Int)) * ((tenPosPow e : Int) * (twoNegPow q : Int)) := by grind
          _ ≤ (4 * (b : Int)) * ((tenPosPow e : Int) * (twoNegPow q : Int)) :=
              Int.mul_le_mul_of_nonneg_right h4 hsc
          _ = 4 * (b : Int) * (tenPosPow e : Int) * (twoNegPow q : Int) := by grind
      -- 10*n ≤ s_e := shiftedSig m q e  (since n = s_e / 10).
      have h_n_div : n = shiftedSig m q e / 10 := by
        rw [hn, show out_exp = e + 1 from by rw [he]; grind]
        exact shiftedSig_succ m q e
      have h_10n_le_se : 10 * n ≤ shiftedSig m q e := by
        rw [h_n_div]; omega
      -- rightOK for 10n at e:  fourU (10n) e < fourVR e.
      have h_10n_right : fourU (10 * n) q e < fourVR m q e := by
        have h1 : fourU (10 * n) q e ≤ fourU (shiftedSig m q e) q e :=
          fourU_mono (10 * n) (shiftedSig m q e) h_10n_le_se
        have h2 : fourU (shiftedSig m q e) q e ≤ fourV m q e :=
          fourU_le_fourV (shiftedSig m q e) m q e rfl
        have h3 : fourV m q e < fourVR m q e := fourV_lt_fourVR m q e
        omega
      -- leftOK for sig' (C ∈ R_v):  fourVL e ≤ fourU sig' e.
      have h_sig'_left : fourVL m q e (isIrregular m q) ≤ fourU sig' q e := by
        have := (inRoundingInterval_iff sig' e m q (isIrregular m q)).mp h_mem
        rcases this.1 with h | ⟨h, _⟩ <;> omega
      -- non-membership of 10n + rightOK ⇒ leftOK fails ⇒ fourU (10n) e ≤ fourVL e.
      have h_10n_left : fourU (10 * n) q e ≤ fourVL m q e (isIrregular m q) := by
        by_contra hc
        push_neg at hc
        have h_mem' : inRoundingInterval (10 * n) e m q (isIrregular m q) = true := by
          rw [inRoundingInterval_iff]
          exact ⟨Or.inl hc, Or.inl h_10n_right⟩
        rw [h_10n_false] at h_mem'; exact absurd h_mem' (by decide)
      -- fourU sig' < fourU (10n) from sig' < 10n.
      have h_sig'_lt : fourU sig' q e < fourU (10 * n) q e := by
        rw [fourU_eq, fourU_eq]
        have hsc : (0 : Int) < (tenPosPow e : Int) * (twoNegPow q : Int) := by
          have h1 := tenPosPow_pos e
          have h2 := twoNegPow_pos q
          exact Int.mul_pos (by exact_mod_cast h1) (by exact_mod_cast h2)
        have h4 : (4 * (sig' : Int)) < (4 * ((10 * n : Nat) : Int)) := by
          have : (sig' : Int) < ((10 * n : Nat) : Int) := by exact_mod_cast h_sig'_lt_10n
          omega
        calc 4 * (sig' : Int) * (tenPosPow e : Int) * (twoNegPow q : Int)
            = (4 * (sig' : Int)) * ((tenPosPow e : Int) * (twoNegPow q : Int)) := by grind
          _ < (4 * ((10 * n : Nat) : Int)) * ((tenPosPow e : Int) * (twoNegPow q : Int)) :=
              Int.mul_lt_mul_of_pos_right h4 hsc
          _ = 4 * ((10 * n : Nat) : Int) * (tenPosPow e : Int) * (twoNegPow q : Int) := by grind
      omega

/-- **Unsigned clause (3) at the same digit length (full).** Combines
`shortestUnsigned_clause3_same_len_ge` (competitor scale `≥ out_exp`) with the
power-of-ten boundary `shortestUnsigned_clause3_same_len_boundary`
(`exp' = out_exp − 1`).  A canonical competitor `(sig', exp')` in `R_v` with
`decDigitLength sig' = decDigitLength cs` is the canonical output, strictly
farther from `v`, or an exact tie with the output even — for *any* scale `exp'`
(the `h_ge` hypothesis is discharged internally via `samelen_exp_diff_le_one`). -/
private theorem shortestUnsigned_clause3_same_len
    (m : Nat) (q : Int)
    (hm_pos : 1 ≤ m) (hm_lt : m < 2 ^ 53) (hq_lo : -1074 ≤ q) (hq_hi : q ≤ 971)
    (cs : Nat) (ce : Int) (t : Nat)
    (h_cs_pos : 1 ≤ cs) (h_cs_canon : cs % 10 ≠ 0)
    (h_out_sig : (shortestUnsigned m q).1 = cs * 10 ^ t)
    (h_ce : ce = (shortestUnsigned m q).2 + (t : Int))
    (sig' : Nat) (exp' : Int)
    (h_sig'_pos : 1 ≤ sig') (h_sig'_canon : sig' % 10 ≠ 0)
    (h_mem : inRoundingInterval sig' exp' m q (isIrregular m q) = true)
    (h_len : decDigitLength sig' = decDigitLength cs) :
    (sig' = cs ∧ exp' = ce)
      ∨ |magVal m q - gridVal cs ce| < |magVal m q - gridVal sig' exp'|
      ∨ ( |magVal m q - gridVal cs ce| = |magVal m q - gridVal sig' exp'|
          ∧ (shortestUnsigned m q).1 % 2 = 0 ) := by
  by_cases h_ge : (shortestUnsigned m q).2 ≤ exp'
  · -- exp' ≥ out_exp: directly the `_ge` lemma.
    exact shortestUnsigned_clause3_same_len_ge m q hm_pos hm_lt hq_lo hq_hi
      cs ce t h_cs_pos h_cs_canon h_out_sig h_ce sig' exp' h_sig'_pos h_sig'_canon
      h_mem h_len h_ge
  · -- exp' < out_exp: the boundary case forces exp' = out_exp − 1, t = 0.
    push_neg at h_ge
    set out_exp := (shortestUnsigned m q).2 with h_out_exp
    set out_sig := (shortestUnsigned m q).1 with h_out_sig_def
    -- Canonical output in R_v (to invoke samelen_exp_diff_le_one).
    have h_cs_mem : inRoundingInterval cs ce m q (isIrregular m q) = true := by
      have hshift := inRoundingInterval_mul10pow_shift_down cs t (out_exp + t) m q (isIrregular m q)
      have he2 : (out_exp + (t : Int)) - (t : Int) = out_exp := by grind
      rw [he2] at hshift
      rw [← h_out_sig] at hshift
      rw [h_ce, ← hshift]
      exact shortestUnsigned_mem_rv m q hm_pos hm_lt hq_lo hq_hi
    -- |exp' - ce| ≤ 1; with exp' < out_exp ≤ ce, force exp' = out_exp - 1 and t = 0.
    have h_gap := samelen_exp_diff_le_one m q hm_pos
      sig' exp' h_sig'_pos h_mem cs ce h_cs_pos h_cs_mem (by rw [h_len])
    have h_ce_ge : out_exp ≤ ce := by rw [h_ce]; omega
    have h_t0 : t = 0 := by
      have : (exp' - ce).natAbs ≤ 1 := h_gap
      have h_ce_eq : ce = out_exp + (t : Int) := h_ce
      omega
    subst h_t0
    -- t = 0:  out_sig = cs, ce = out_exp.
    have h_out_eq_cs : out_sig = cs := by simpa using h_out_sig
    have h_ce_eq : ce = out_exp := by rw [h_ce]; simp
    have h_exp'_eq : exp' = out_exp - 1 := by
      have hh : (exp' - ce).natAbs ≤ 1 := h_gap
      rw [h_ce_eq] at hh; omega
    -- Apply the boundary lemma (strict-closer branch).
    have h_out_canon : out_sig % 10 ≠ 0 := by rw [h_out_eq_cs]; exact h_cs_canon
    have h_bd := shortestUnsigned_clause3_same_len_boundary m q hm_pos hm_lt hq_lo hq_hi
      sig' h_sig'_pos h_sig'_canon (by rw [← h_out_sig_def]; exact h_out_canon)
      (by rw [← h_out_exp, ← h_exp'_eq]; exact h_mem)
      (by rw [← h_out_sig_def, h_out_eq_cs]; exact h_len)
    -- Rewrite distances to the (cs, ce) form.
    refine Or.inr (Or.inl ?_)
    rw [h_ce_eq, ← h_out_eq_cs, ← h_out_exp, ← h_exp'_eq] at *
    exact h_bd

/-! ## Tie competitors at the output scale are consecutive

For the uniqueness corollary we need a sharper fact than the disjunctive
clause (3): an exact-tie competitor at the *output scale* `out_exp` differs
from the output significand `out_sig` by exactly one (it is the *other*
floor/ceil neighbour of `v`).  This is exactly the geometry of
`tieBreak_unsigned_fallback`: a genuine tie occurs only when both floor
neighbours `s, s+1` of `v` lie in `R_v`, and the two equidistant grid points
are then the consecutive pair `{s, s+1}`.  Any non-neighbour is *strictly*
farther (`grid_far_of_outside`); the shorter-form (single-sided) branch
admits no tie at all.  Hence a tie forces `|S' - out_sig| = 1`, so `S'` and
`out_sig` have opposite parity. -/

/-- **Tie ⇒ consecutive at the output scale.** A scale-`out_exp` grid point
`sig'` in `R_v` that is an *exact tie* with the output `out_sig` and is not
equal to it must be a neighbour: `sig' = out_sig + 1` or `out_sig = sig' + 1`.
(Genuine ties live only in the fallback branch, where the two equidistant
points are the consecutive floor neighbours of `v`.) -/
private theorem tie_at_outexp_consecutive
    (m : Nat) (q : Int)
    (hm_pos : 1 ≤ m) (hm_lt : m < 2 ^ 53) (hq_lo : -1074 ≤ q) (hq_hi : q ≤ 971)
    (sig' : Nat)
    (h_mem : inRoundingInterval sig' (shortestUnsigned m q).2 m q (isIrregular m q) = true)
    (h_tie : |magVal m q - gridVal (shortestUnsigned m q).1 (shortestUnsigned m q).2|
             = |magVal m q - gridVal sig' (shortestUnsigned m q).2|)
    (h_ne : sig' ≠ (shortestUnsigned m q).1) :
    sig' = (shortestUnsigned m q).1 + 1 ∨ (shortestUnsigned m q).1 = sig' + 1 := by
  set out_sig := (shortestUnsigned m q).1 with h_out_sig
  set out_exp := (shortestUnsigned m q).2 with h_out_exp
  set k := kOfMQ m q with hk
  set s := shiftedSig m q k with hs
  have h_rel := shortestUnsigned_length_relation m q
  rcases h_rel with ⟨hs_big, h_exp_eq, h_or⟩ | ⟨h_exp_eq, h_sig_eq⟩
  · -- Shorter form: out_exp = k+1; the output is single-sided, NO tie possible.
    -- Confine sig' to {s/10, s/10+1} and force equality, contradicting the tie.
    exfalso
    have h_exp' : out_exp = k + 1 := h_exp_eq
    have h_mem' : inRoundingInterval sig' (k + 1) m q (isIrregular m q) = true := by
      rw [← h_exp']; exact h_mem
    have h_cands := Schubfach_K1_candidates m q hm_pos hm_lt hq_lo hq_hi sig' h_mem'
    -- The output is in R_v at k+1.
    have h_out_mem : inRoundingInterval out_sig (k + 1) m q (isIrregular m q) = true := by
      have h_mem_out := shortestUnsigned_mem_rv m q hm_pos hm_lt hq_lo hq_hi
      rw [h_out_sig, ← h_exp_eq]; exact h_mem_out
    have h_at_most_one :
        ¬ (inRoundingInterval (s / 10) (k + 1) m q (isIrregular m q) = true ∧
           inRoundingInterval (s / 10 + 1) (k + 1) m q (isIrregular m q) = true) := by
      rintro ⟨h_uT, h_wT⟩
      have h_strict :
          fourVR m q (k + 1) - fourVL m q (k + 1) (isIrregular m q)
            < fourW (s / 10) q (k + 1) - fourU (s / 10) q (k + 1) :=
        fourVR_sub_fourVL_lt_step_K1 m q hm_pos hm_lt hq_lo hq_hi (s / 10)
      have h_w_eq : fourU (s / 10 + 1) q (k + 1) = fourW (s / 10) q (k + 1) := by
        rw [fourU_eq, fourW_eq]; push_cast; rfl
      have hbu := (inRoundingInterval_iff (s / 10) (k + 1) m q (isIrregular m q)).mp h_uT
      have hbw := (inRoundingInterval_iff (s / 10 + 1) (k + 1) m q (isIrregular m q)).mp h_wT
      obtain ⟨hbuL, _⟩ := hbu
      obtain ⟨_, hbwR⟩ := hbw
      have h_VL_le_u : fourVL m q (k + 1) (isIrregular m q) ≤ fourU (s / 10) q (k + 1) := by
        rcases hbuL with h | ⟨h, _⟩ <;> omega
      have h_w_le_VR : fourU (s / 10 + 1) q (k + 1) ≤ fourVR m q (k + 1) := by
        rcases hbwR with h | ⟨h, _⟩ <;> omega
      rw [h_w_eq] at h_w_le_VR
      omega
    have h_out_cand : out_sig = s / 10 ∨ out_sig = s / 10 + 1 := by
      rw [h_out_sig]; exact h_or
    have h_other_not :
        (out_sig = s / 10 → inRoundingInterval (s / 10 + 1) (k + 1) m q (isIrregular m q) = false)
        ∧ (out_sig = s / 10 + 1 → inRoundingInterval (s / 10) (k + 1) m q (isIrregular m q) = false) := by
      constructor
      · intro h_os
        rcases Bool.eq_false_or_eq_true (inRoundingInterval (s / 10 + 1) (k + 1) m q (isIrregular m q)) with h | h
        · exact absurd ⟨by rw [← h_os]; exact h_out_mem, h⟩ h_at_most_one
        · exact h
      · intro h_os
        rcases Bool.eq_false_or_eq_true (inRoundingInterval (s / 10) (k + 1) m q (isIrregular m q)) with h | h
        · exact absurd ⟨h, by rw [← h_os]; exact h_out_mem⟩ h_at_most_one
        · exact h
    have h_eq := tieBreak_unsigned_single_sided m q (k + 1) (s / 10) out_sig
                    h_out_cand h_other_not sig' h_cands h_mem'
    exact h_ne h_eq
  · -- Fallback: out_exp = k, out_sig = pickNearer s k.
    have h_exp' : out_exp = k := h_exp_eq
    have h_mem' : inRoundingInterval sig' k m q (isIrregular m q) = true := by
      rw [← h_exp']; exact h_mem
    rw [h_exp'] at h_tie
    have h_out_eq_pn : out_sig = pickNearer s k m q := by rw [h_out_sig]; exact h_sig_eq
    -- A genuine tie (equal distance, distinct point) can only occur when BOTH
    -- floor neighbours s, s+1 ∈ R_v (the single-sided case forces equality).
    by_cases h_both : inRoundingInterval s k m q (isIrregular m q) = true ∧
                      inRoundingInterval (s + 1) k m q (isIrregular m q) = true
    · -- Both in R_v: pickNearer is one of {s, s+1}, and the tie partner is the other.
      obtain ⟨pn, other, h_pn_eq, h_pn_other, _⟩ :=
        pickNearer_grid_closer_or_tie_even s k m q h_both
      have h_out_pn : out_sig = pn := by rw [h_out_eq_pn, h_pn_eq]
      -- {pn, other} = {s, s+1}, so out_sig ∈ {s, s+1}; the other neighbour is consecutive.
      obtain ⟨h_below, h_above⟩ := grid_far_of_outside m q k s sig' hs
      rcases h_pn_other with ⟨h_pns, h_oth⟩ | ⟨h_pns1, h_oth⟩
      · -- pn = s, other = s+1.  out_sig = s.
        have h_o_s : out_sig = s := by rw [h_out_pn, h_pns]
        by_cases h_s1 : sig' = s + 1
        · left; rw [h_o_s]; exact h_s1
        · exfalso
          have h_ne_s : sig' ≠ s := by rw [← h_o_s]; exact h_ne
          have h_out : sig' + 1 ≤ s ∨ s + 2 ≤ sig' := by omega
          rcases h_out with hb | ha
          · have h_far := h_below hb; rw [← h_o_s] at h_far
            rw [h_tie] at h_far; exact lt_irrefl _ h_far
          · -- sig' ≥ s+2 strictly farther than s+1; and out_sig = s is the pick, so
            -- dist(s) ≤ dist(s+1) < dist(sig').
            have h_far := h_above ha
            have h_s_le : |magVal m q - gridVal s k| ≤ |magVal m q - gridVal (s + 1) k| := by
              have h_pick := pickNearer_eq_or_succ s k m q
              -- pickNearer = s here; the closer-or-tie-even spec gives dist(s) ≤ dist(s+1).
              obtain ⟨pn2, oth2, h2eq, h2or, h2dist⟩ :=
                pickNearer_grid_closer_or_tie_even s k m q h_both
              have h2pn_s : pn2 = s := by
                have : pn2 = pn := by rw [← h2eq, ← h_pn_eq]
                rw [this, h_pns]
              rcases h2or with ⟨hp, ho⟩ | ⟨hp, ho⟩
              · rw [h2pn_s, ho] at h2dist
                rcases h2dist with hlt | ⟨heq, _⟩
                · exact le_of_lt hlt
                · exact le_of_eq heq
              · -- pn2 = s+1 contradicts pn2 = s.
                rw [h2pn_s] at hp; omega
            have : |magVal m q - gridVal s k| < |magVal m q - gridVal sig' k| :=
              lt_of_le_of_lt h_s_le h_far
            rw [← h_o_s] at this; rw [h_tie] at this; exact lt_irrefl _ this
      · -- pn = s+1, other = s.  out_sig = s+1.
        have h_o_s1 : out_sig = s + 1 := by rw [h_out_pn, h_pns1]
        by_cases h_s : sig' = s
        · right; rw [h_o_s1]; omega
        · exfalso
          have h_ne_s1 : sig' ≠ s + 1 := by rw [← h_o_s1]; exact h_ne
          have h_out : sig' + 1 ≤ s ∨ s + 2 ≤ sig' := by omega
          rcases h_out with hb | ha
          · -- sig' ≤ s-1 strictly farther than s; and out_sig = s+1 is the pick, so
            -- dist(s+1) ≤ dist(s) < dist(sig').
            have h_far := h_below hb
            have h_s1_le : |magVal m q - gridVal (s + 1) k| ≤ |magVal m q - gridVal s k| := by
              obtain ⟨pn2, oth2, h2eq, h2or, h2dist⟩ :=
                pickNearer_grid_closer_or_tie_even s k m q h_both
              have h2pn_s1 : pn2 = s + 1 := by
                have : pn2 = pn := by rw [← h2eq, ← h_pn_eq]
                rw [this, h_pns1]
              rcases h2or with ⟨hp, ho⟩ | ⟨hp, ho⟩
              · rw [h2pn_s1] at hp; omega
              · rw [h2pn_s1, ho] at h2dist
                rcases h2dist with hlt | ⟨heq, _⟩
                · exact le_of_lt hlt
                · exact le_of_eq heq
            have : |magVal m q - gridVal (s + 1) k| < |magVal m q - gridVal sig' k| :=
              lt_of_le_of_lt h_s1_le h_far
            rw [← h_o_s1] at this; rw [h_tie] at this; exact lt_irrefl _ this
          · have h_far := h_above ha; rw [← h_o_s1] at h_far
            rw [h_tie] at h_far; exact lt_irrefl _ h_far
    · -- Single-sided: only one neighbour in R_v.  The in-R_v competitor is strictly
      -- farther unless equal to the output, so no distinct tie exists.
      exfalso
      have h_one : inRoundingInterval s k m q (isIrregular m q) = true ∨
                   inRoundingInterval (s + 1) k m q (isIrregular m q) = true :=
        shiftedSig_or_succ_mem_rv m q hm_pos hm_lt hq_lo hq_hi
      obtain ⟨h_below, h_above⟩ := grid_far_of_outside m q k s sig' hs
      rcases h_one with h_s | h_s1
      · -- s ∈ R_v, s+1 ∉ R_v.  out_sig = pickNearer = s.
        have h_s1_not : inRoundingInterval (s + 1) k m q (isIrregular m q) = false := by
          rcases Bool.eq_false_or_eq_true (inRoundingInterval (s + 1) k m q (isIrregular m q)) with h | h
          · exact absurd ⟨h_s, h⟩ h_both
          · exact h
        have h_pn_s : out_sig = s := by
          rw [h_out_eq_pn]; show pickNearer s k m q = s; simp [pickNearer, h_s, h_s1_not]
        have h_sig_ne_s : sig' ≠ s := by rw [← h_pn_s]; exact h_ne
        have h_sig_ne_s1 : sig' ≠ s + 1 := by
          intro h; rw [h] at h_mem'; rw [h_s1_not] at h_mem'; exact absurd h_mem' (by decide)
        have h_not_above : ¬ s + 2 ≤ sig' := by
          intro ha
          have h_s1_in : inRoundingInterval (s + 1) k m q (isIrregular m q) = true :=
            inRoundingInterval_connected s (s + 1) sig' k m q (by omega) (by omega) h_s h_mem'
          rw [h_s1_not] at h_s1_in; exact absurd h_s1_in (by decide)
        have hb : sig' + 1 ≤ s := by omega
        have h_far := h_below hb; rw [← h_pn_s] at h_far
        rw [h_tie] at h_far; exact lt_irrefl _ h_far
      · -- s+1 ∈ R_v, s ∉ R_v.  out_sig = pickNearer = s+1.
        have h_s_not : inRoundingInterval s k m q (isIrregular m q) = false := by
          rcases Bool.eq_false_or_eq_true (inRoundingInterval s k m q (isIrregular m q)) with h | h
          · exact absurd ⟨h, h_s1⟩ h_both
          · exact h
        have h_pn_s1 : out_sig = s + 1 := by
          rw [h_out_eq_pn]; show pickNearer s k m q = s + 1; simp [pickNearer, h_s_not, h_s1]
        have h_sig_ne_s1 : sig' ≠ s + 1 := by rw [← h_pn_s1]; exact h_ne
        have h_sig_ne_s : sig' ≠ s := by
          intro h; rw [h] at h_mem'; rw [h_s_not] at h_mem'; exact absurd h_mem' (by decide)
        have h_not_below : ¬ sig' + 1 ≤ s := by
          intro hb
          have h_s_in : inRoundingInterval s k m q (isIrregular m q) = true :=
            inRoundingInterval_connected sig' s (s + 1) k m q (by omega) (by omega) h_mem' h_s1
          rw [h_s_not] at h_s_in; exact absurd h_s_in (by decide)
        have ha : s + 2 ≤ sig' := by omega
        have h_far := h_above ha; rw [← h_pn_s1] at h_far
        rw [h_tie] at h_far; exact lt_irrefl _ h_far

/-- **No even–even tie at the same digit length.** A canonical competitor
`(sig', exp')` of the same digit length as the (canonical) output that is
*equidistant* from `v` cannot have an even significand when the output
significand is also even.  Reason: a tie forces `exp' ≥ out_exp` (the
power-of-ten boundary is always *strictly* closer), and the down-shifted
competitor `sig' · 10^(exp'-out_exp)` is *consecutive* to the output
significand `out_sig`, hence of opposite parity.  Since `out_sig` is even,
the shifted competitor is odd, forcing the shift to be `0` and `sig' = `
the shifted competitor odd — contradicting `sig'` even. -/
private theorem samelen_even_tie_false
    (m : Nat) (q : Int)
    (hm_pos : 1 ≤ m) (hm_lt : m < 2 ^ 53) (hq_lo : -1074 ≤ q) (hq_hi : q ≤ 971)
    (cs : Nat) (ce : Int) (t : Nat)
    (h_cs_pos : 1 ≤ cs) (h_cs_canon : cs % 10 ≠ 0)
    (h_out_sig : (shortestUnsigned m q).1 = cs * 10 ^ t)
    (h_ce : ce = (shortestUnsigned m q).2 + (t : Int))
    (sig' : Nat) (exp' : Int)
    (h_sig'_pos : 1 ≤ sig') (h_sig'_canon : sig' % 10 ≠ 0)
    (h_mem : inRoundingInterval sig' exp' m q (isIrregular m q) = true)
    (h_len : decDigitLength sig' = decDigitLength cs)
    (h_distinct : ¬ (sig' = cs ∧ exp' = ce))
    (h_eqd : |magVal m q - gridVal cs ce| = |magVal m q - gridVal sig' exp'|)
    (h_out_even : (shortestUnsigned m q).1 % 2 = 0)
    (h_sig'_even : sig' % 2 = 0) :
    False := by
  set out_exp := (shortestUnsigned m q).2 with h_out_exp
  set out_sig := (shortestUnsigned m q).1 with h_out_sig_def
  -- The output value equals gridVal cs ce.
  have h_out_val : gridVal out_sig out_exp = gridVal cs ce := by
    rw [h_out_sig, h_ce, ← gridVal_mul_pow10 cs t out_exp]
  by_cases h_ge : out_exp ≤ exp'
  · -- exp' ≥ out_exp: shift competitor down to out_exp and use tie_at_outexp_consecutive.
    set j : Nat := (exp' - out_exp).toNat with hj
    have hj_eq : (j : Int) = exp' - out_exp := Int.toNat_of_nonneg (by omega)
    have h_shift_exp : exp' - (j : Int) = out_exp := by rw [hj_eq]; grind
    have h_mem_shift :
        inRoundingInterval (sig' * 10 ^ j) out_exp m q (isIrregular m q) = true := by
      have hs := inRoundingInterval_mul10pow_shift_down sig' j exp' m q (isIrregular m q)
      rw [h_shift_exp] at hs; rw [hs]; exact h_mem
    have h_grid_shift : gridVal (sig' * 10 ^ j) out_exp = gridVal sig' exp' := by
      rw [gridVal_mul_pow10 sig' j out_exp, hj_eq]; congr 1; grind
    -- The shifted competitor is equidistant with out_sig at scale out_exp.
    have h_eqd_shift :
        |magVal m q - gridVal out_sig out_exp|
          = |magVal m q - gridVal (sig' * 10 ^ j) out_exp| := by
      rw [h_out_val, h_grid_shift]; exact h_eqd
    -- Is the shifted competitor equal to out_sig?
    by_cases h_eqs : sig' * 10 ^ j = out_sig
    · -- sig' * 10^j = out_sig = cs * 10^t.  Canonical ⇒ sig' = cs, j = t ⇒ exp' = ce.
      -- That coincides with the output decimal, contradicting distinctness.
      have h_eq2 : sig' * 10 ^ j = cs * 10 ^ t := by rw [← h_out_sig]; exact h_eqs
      have huniq := canonical_pow10_unique sig' cs j t h_sig'_pos h_cs_pos
                      h_sig'_canon h_cs_canon h_eq2
      refine h_distinct ⟨huniq.1, ?_⟩
      rw [h_ce]
      have : exp' = out_exp + (j : Int) := by rw [hj_eq]; grind
      rw [this, huniq.2]
    · -- sig' * 10^j ≠ out_sig: a genuine tie ⇒ consecutive ⇒ opposite parity.
      have h_cons := tie_at_outexp_consecutive m q hm_pos hm_lt hq_lo hq_hi
        (sig' * 10 ^ j)
        h_mem_shift
        h_eqd_shift
        h_eqs
      -- out_sig even; consecutive ⇒ sig'*10^j odd.
      have h_shift_odd : (sig' * 10 ^ j) % 2 = 1 := by
        rcases h_cons with h | h
        · -- sig'*10^j = out_sig + 1, out_sig even ⇒ odd.
          rw [h, ← h_out_sig_def]; omega
        · -- out_sig = sig'*10^j + 1, out_sig even ⇒ sig'*10^j odd.
          rw [← h_out_sig_def] at h; omega
      -- sig' * 10^j odd ⇒ j = 0 and sig' odd.
      have h_j0 : j = 0 := by
        by_contra hj0
        have : 10 ^ j % 2 = 0 := by
          have : 2 ∣ 10 ^ j := Nat.dvd_pow' (by decide) hj0
          omega
        have : (sig' * 10 ^ j) % 2 = 0 := by
          have h2 : 2 ∣ 10 ^ j := Nat.dvd_pow' (by decide) hj0
          have : 2 ∣ sig' * 10 ^ j := Nat.dvd_trans h2 (Nat.dvd_mul_left _ _)
          omega
        omega
      rw [h_j0, Nat.pow_zero, Nat.mul_one] at h_shift_odd
      omega
  · -- exp' < out_exp: boundary case ⇒ STRICT closer ⇒ contradicts equidistance.
    push_neg at h_ge
    -- mirror shortestUnsigned_clause3_same_len: force exp' = out_exp - 1, t = 0.
    have h_cs_mem : inRoundingInterval cs ce m q (isIrregular m q) = true := by
      have hshift := inRoundingInterval_mul10pow_shift_down cs t (out_exp + t) m q (isIrregular m q)
      have he2 : (out_exp + (t : Int)) - (t : Int) = out_exp := by grind
      rw [he2] at hshift; rw [← h_out_sig] at hshift
      rw [h_ce, ← hshift]
      exact shortestUnsigned_mem_rv m q hm_pos hm_lt hq_lo hq_hi
    have h_gap := samelen_exp_diff_le_one m q hm_pos
      sig' exp' h_sig'_pos h_mem cs ce h_cs_pos h_cs_mem (by rw [h_len])
    have h_ce_ge : out_exp ≤ ce := by rw [h_ce]; omega
    have h_t0 : t = 0 := by
      have : (exp' - ce).natAbs ≤ 1 := h_gap
      have h_ce_eq : ce = out_exp + (t : Int) := h_ce
      omega
    subst h_t0
    have h_out_eq_cs : out_sig = cs := by simpa using h_out_sig
    have h_ce_eq : ce = out_exp := by rw [h_ce]; simp
    have h_exp'_eq : exp' = out_exp - 1 := by
      have hh : (exp' - ce).natAbs ≤ 1 := h_gap
      rw [h_ce_eq] at hh; omega
    have h_out_canon : out_sig % 10 ≠ 0 := by rw [h_out_eq_cs]; exact h_cs_canon
    have h_bd := shortestUnsigned_clause3_same_len_boundary m q hm_pos hm_lt hq_lo hq_hi
      sig' h_sig'_pos h_sig'_canon (by rw [← h_out_sig_def]; exact h_out_canon)
      (by rw [← h_out_exp, ← h_exp'_eq]; exact h_mem)
      (by rw [← h_out_sig_def, h_out_eq_cs]; exact h_len)
    -- h_bd : |v - gridVal out_sig out_exp| < |v - gridVal sig' (out_exp - 1)|
    --   (in (shortestUnsigned m q) form).  Fold to out_sig/out_exp, then to cs/exp'.
    rw [← h_out_sig_def, ← h_out_exp, h_out_val, h_ce_eq, ← h_exp'_eq] at h_bd
    -- h_bd : |v - gridVal cs out_exp| < |v - gridVal sig' exp'|.
    rw [h_ce_eq] at h_eqd
    rw [h_eqd] at h_bd
    exact lt_irrefl _ h_bd

/-! ## A genuine tie cannot strip parity

`samelen_tie_canonical_even` upgrades the tie-break parity from the raw
output significand (`shortestUnsigned`) to the *canonical* significand
`cs`. The two differ only when the raw output carries trailing zeros
(`t ≥ 1`), and a same-digit-length tie then forces the unique
configuration `out_sig = 10`, `cs = 1`, competitor `sig' = 9` — i.e.
`v` exactly at `9.5 · 10^e` with both `9·10^e, 10·10^e ∈ R_v`.  That is
impossible in binary64 (`tie_nine_ten_impossible`): membership of both
neighbours caps the grid step by the interval width, giving `2m ≤ 19`,
so `m ≤ 9` forces a subnormal (`q = -1074`), and then
`2m · 10^j = 19 · 2^1074` has no solution (5-adic balance for `e < 0`;
size for `e ≥ 0`). -/

private theorem tie_nine_ten_impossible
    (m : Nat) (q : Int) (e : Int)
    (h_legal : LegalIEEE m q)
    (h_mem9 : inRoundingInterval 9 e m q (isIrregular m q) = true)
    (h_mem10 : inRoundingInterval 10 e m q (isIrregular m q) = true)
    (h_eqd : Equidistant 9 e m q) : False := by
  -- The four cleared scale factors.
  set P : Int := (twoPosPow q : Int) with hP
  set N : Int := (twoNegPow q : Int) with hN
  set T : Int := (tenPosPow e : Int) with hT
  set M : Int := (tenNegPow e : Int) with hM
  have hP_pos : 0 < P := by rw [hP]; exact_mod_cast twoPosPow_pos q
  have hN_pos : 0 < N := by rw [hN]; exact_mod_cast twoNegPow_pos q
  have hT_pos : 0 < T := by rw [hT]; exact_mod_cast tenPosPow_pos e
  have hM_pos : 0 < M := by rw [hM]; exact_mod_cast tenNegPow_pos e
  -- The tie equation `2v = 19·10^e` in cleared form: `2m·P·M = 19·T·N`.
  have h_eq : 2 * (m : Int) * P * M = 19 * T * N := by
    have h1 : cmpScaledMixed.lhs (2 * (m : Int)) q e
        = 2 * (m : Int) * P * M := by
      rw [hP, hM]; unfold cmpScaledMixed.lhs twoPosPow tenNegPow; rfl
    have h2 : cmpScaledMixed.rhs (2 * ((9 : Nat) : Int) + 1) q e
        = 19 * T * N := by
      rw [hT, hN]; unfold cmpScaledMixed.rhs tenPosPow twoNegPow
      grind
    unfold Equidistant at h_eqd
    rw [h1, h2] at h_eqd
    exact h_eqd
  -- Membership brackets: `fourVL ≤ fourU 9` and `fourU 10 ≤ fourVR`.
  have h_left : fourVL m q e (isIrregular m q) ≤ fourU 9 q e := by
    have := (inRoundingInterval_iff 9 e m q (isIrregular m q)).mp h_mem9
    rcases this.1 with h | ⟨h, _⟩ <;> omega
  have h_right : fourU 10 q e ≤ fourVR m q e := by
    have := (inRoundingInterval_iff 10 e m q (isIrregular m q)).mp h_mem10
    rcases this.2 with h | ⟨h, _⟩ <;> omega
  -- Lower bound on `fourVL`: `(4m-2)·P·M` in both regularity cases.
  have h_vl_lo : (4 * (m : Int) - 2) * P * M ≤ fourVL m q e (isIrregular m q) := by
    by_cases h_irr : isIrregular m q = true
    · rw [fourVL_eq_irregular m q e h_irr, hP, hM]
      have : (0 : Int) ≤ (twoPosPow q : Int) * (tenNegPow e : Int) := by
        grind
      grind
    · rw [fourVL_eq_regular m q e h_irr, hP, hM]
      grind
  -- Width condition: grid step `4·T·N ≤ 4·P·M`.
  have h_u9 : fourU 9 q e = 36 * T * N := by
    rw [fourU_eq, hT, hN]; grind
  have h_u10 : fourU 10 q e = 40 * T * N := by
    rw [fourU_eq, hT, hN]; grind
  have h_vr : fourVR m q e = (4 * (m : Int) + 2) * P * M := by
    rw [fourVR_eq, hP, hM]
  -- From `(4m-2)PM ≤ 36TN`, `40TN ≤ (4m+2)PM`, `2mPM = 19TN`:  `TN ≤ PM`.
  have h_TN_le_PM : T * N ≤ P * M := by grind
  -- `2m·PM = 19·TN ≤ 19·PM` ⇒ `2m ≤ 19` ⇒ `m ≤ 9`.
  have h_m_le : (m : Int) ≤ 9 := by
    have hPM_pos : (0 : Int) < P * M := by
      rw [hP, hM]
      have h1 := twoPosPow_pos q
      have h2 := tenNegPow_pos e
      exact Int.mul_pos (by exact_mod_cast h1) (by exact_mod_cast h2)
    have h19 : (19 : Int) * (T * N) ≤ 19 * (P * M) := by omega
    have hprod : (2 * (m : Int)) * (P * M) ≤ 19 * (P * M) := by
      have he : (2 * (m : Int)) * (P * M) = 19 * (T * N) := by grind
      omega
    have := Int.le_of_mul_le_mul_right hprod hPM_pos
    omega
  have h_m_le9 : m ≤ 9 := by exact_mod_cast h_m_le
  -- LegalIEEE: `m ≤ 9 < 2^52` rules out the normal branch ⇒ `q = -1074`.
  have h_q : q = -1074 := by
    rcases h_legal with ⟨_, _, hq⟩ | ⟨h52, _, _, _⟩
    · exact hq
    · exfalso
      have : (2 : Nat) ^ 52 ≤ 9 := Nat.le_trans h52 h_m_le9
      omega
  subst h_q
  -- `P = 1`, `N = 2^1074`.
  have hP1 : P = 1 := by rw [hP]; unfold twoPosPow; grind
  rw [hP1, Int.mul_one] at h_eq
  -- Split on the sign of `e`.
  by_cases h_e : 0 ≤ e
  · -- `M = 1`, so `2m = 19·T·2^1074 ≥ 38 > 18`.
    have hM1 : M = 1 := by
      rw [hM]; unfold tenNegPow
      have : ¬ (e < 0) := Int.not_lt.mpr h_e
      simp [this]
    rw [hM1, Int.mul_one] at h_eq
    have hT1 : 1 ≤ T := hT_pos
    have hN2' : (2 : Int) ≤ N := by
      have h : (2 : Nat) ≤ twoNegPow (-1074) := by
        unfold twoNegPow
        rw [if_pos (by decide : (-1074 : Int) < 0)]
        exact Nat.one_lt_two_pow_iff.mpr (by decide)
      rw [hN]
      exact Int.ofNat_le.mpr h
    have hTN : (2 : Int) ≤ T * N := by
      have hmul := Int.mul_le_mul hT1 hN2' (by omega) (by omega)
      omega
    have hbridge : 19 * T * N = 19 * (T * N) := Int.mul_assoc 19 T N
    omega
  · -- `e < 0`: `T = 1`, `M = 10^j` with `j ≥ 1`; 5-adic contradiction.
    push_neg at h_e
    have hT1 : T = 1 := by
      rw [hT]; unfold tenPosPow
      have : ¬ (e ≥ 0) := Int.not_le.mpr h_e
      simp [this]
    rw [hT1] at h_eq
    -- Pass to ℕ, keeping `twoNegPow (-1074) = 2^1074` *folded* (its
    -- exponent is far past the evaluation threshold).
    set j : Nat := (-e).toNat with hj
    have hj_pos : 1 ≤ j := by
      rw [hj]; omega
    have h_eq2 : 2 * (m : Int) * M = 19 * N := by grind
    have h_nat : 2 * m * tenNegPow e = 19 * twoNegPow (-1074) := by
      rw [hM, hN] at h_eq2
      -- Hide `twoNegPow (-1074)` behind a fresh variable so the cast
      -- normalizer cannot try to evaluate `2^1074`.
      generalize twoNegPow (-1074) = Y at h_eq2 ⊢
      exact_mod_cast h_eq2
    have h_ten : tenNegPow e = 10 ^ j := by
      unfold tenNegPow
      rw [if_pos h_e, hj]
    have h5 : (5 : Nat) ∣ 19 * twoNegPow (-1074) := by
      rw [← h_nat, h_ten]
      exact Nat.dvd_trans (Nat.dvd_pow' (by decide) (by omega)) (Nat.dvd_mul_left _ _)
    -- 5 is coprime to both 19 and 2^1074: contradiction with the divisibility.
    have hco : Nat.Coprime 5 (19 * twoNegPow (-1074)) := by
      apply Nat.Coprime.mul_right
      · decide
      · unfold twoNegPow
        rw [if_pos (by decide : (-1074 : Int) < 0)]
        exact Nat.Coprime.pow_right _ (by decide)
    have h51 : (5 : Nat) = 1 := Nat.Coprime.eq_one_of_dvd hco h5
    omega

set_option maxHeartbeats 800000 in
/-- **Tie parity in canonical (output) vocabulary.**  In the same-length
tie context (`h_eqd` equidistant, competitor distinct from the canonical
output), the *canonical* significand `cs` is even — not merely the raw
`shortestUnsigned` output `cs · 10^t`.  If `t = 0` the two coincide; if
`t ≥ 1` the tie configuration is impossible (`tie_nine_ten_impossible`). -/
private theorem samelen_tie_canonical_even
    (m : Nat) (q : Int)
    (hm_pos : 1 ≤ m) (hm_lt : m < 2 ^ 53) (hq_lo : -1074 ≤ q) (hq_hi : q ≤ 971)
    (h_legal : LegalIEEE m q)
    (cs : Nat) (ce : Int) (t : Nat)
    (h_cs_pos : 1 ≤ cs) (h_cs_canon : cs % 10 ≠ 0)
    (h_out_sig : (shortestUnsigned m q).1 = cs * 10 ^ t)
    (h_ce : ce = (shortestUnsigned m q).2 + (t : Int))
    (sig' : Nat) (exp' : Int)
    (h_sig'_pos : 1 ≤ sig') (h_sig'_canon : sig' % 10 ≠ 0)
    (h_mem : inRoundingInterval sig' exp' m q (isIrregular m q) = true)
    (h_len : decDigitLength sig' = decDigitLength cs)
    (h_distinct : ¬ (sig' = cs ∧ exp' = ce))
    (h_eqd : |magVal m q - gridVal cs ce| = |magVal m q - gridVal sig' exp'|)
    (h_out_even : (shortestUnsigned m q).1 % 2 = 0) :
    cs % 2 = 0 := by
  by_cases h_t0 : t = 0
  · -- `t = 0`: the raw output IS the canonical significand.
    subst h_t0
    rw [Nat.pow_zero, Nat.mul_one] at h_out_sig
    rw [← h_out_sig]
    exact h_out_even
  · -- `t ≥ 1`: the tie configuration is impossible.
    exfalso
    set out_exp := (shortestUnsigned m q).2 with h_out_exp
    set out_sig := (shortestUnsigned m q).1 with h_out_sig_def
    have h_out_val : gridVal out_sig out_exp = gridVal cs ce := by
      rw [h_out_sig, h_ce, ← gridVal_mul_pow10 cs t out_exp]
    by_cases h_ge : out_exp ≤ exp'
    · -- Shift the competitor down to `out_exp`.
      set j : Nat := (exp' - out_exp).toNat with hj
      have hj_eq : (j : Int) = exp' - out_exp := Int.toNat_of_nonneg (by omega)
      have h_shift_exp : exp' - (j : Int) = out_exp := by rw [hj_eq]; grind
      have h_mem_shift :
          inRoundingInterval (sig' * 10 ^ j) out_exp m q (isIrregular m q) = true := by
        have hs := inRoundingInterval_mul10pow_shift_down sig' j exp' m q (isIrregular m q)
        rw [h_shift_exp] at hs; rw [hs]; exact h_mem
      have h_grid_shift : gridVal (sig' * 10 ^ j) out_exp = gridVal sig' exp' := by
        rw [gridVal_mul_pow10 sig' j out_exp, hj_eq]; congr 1; grind
      have h_eqd_shift :
          |magVal m q - gridVal out_sig out_exp|
            = |magVal m q - gridVal (sig' * 10 ^ j) out_exp| := by
        rw [h_out_val, h_grid_shift]; exact h_eqd
      by_cases h_eqs : sig' * 10 ^ j = out_sig
      · -- Shifted competitor coincides with the raw output ⇒ same decimal,
        -- contradicting distinctness.
        have h_eq2 : sig' * 10 ^ j = cs * 10 ^ t := by rw [← h_out_sig]; exact h_eqs
        have huniq := canonical_pow10_unique sig' cs j t h_sig'_pos h_cs_pos
                        h_sig'_canon h_cs_canon h_eq2
        refine h_distinct ⟨huniq.1, ?_⟩
        rw [h_ce]
        have : exp' = out_exp + (j : Int) := by rw [hj_eq]; grind
        rw [this, huniq.2]
      · -- Genuine tie ⇒ consecutive at the output scale.
        have h_cons := tie_at_outexp_consecutive m q hm_pos hm_lt hq_lo hq_hi
          (sig' * 10 ^ j) h_mem_shift h_eqd_shift h_eqs
        -- `t ≥ 1` makes `out_sig ≡ 0 (mod 10)`; a consecutive partner is
        -- `≡ ±1 (mod 10)`, so `j = 0`.
        have h_out_mod : out_sig % 10 = 0 := by
          rw [h_out_sig]
          have : (10 : Nat) ∣ cs * 10 ^ t :=
            Nat.dvd_trans (dvd_pow_self 10 h_t0) (Nat.dvd_mul_left _ _)
          omega
        have h_j0 : j = 0 := by
          by_contra h_jne
          have h_shift_mod : (sig' * 10 ^ j) % 10 = 0 := by
            have : (10 : Nat) ∣ sig' * 10 ^ j :=
              Nat.dvd_trans (dvd_pow_self 10 h_jne) (Nat.dvd_mul_left _ _)
            omega
          rcases h_cons with h | h <;> omega
        rw [h_j0, Nat.pow_zero, Nat.mul_one] at h_cons h_mem_shift h_eqd_shift
        have h_exp'_eq : exp' = out_exp := by omega
        -- Digit-length forcing: only `(cs, out_sig, sig') = (1, 10, 9)` fits.
        set L := decDigitLength cs with hL
        have h_dl_out : decDigitLength out_sig = L + t := by
          rw [h_out_sig]; exact decDigitLength_mul_pow10 cs t h_cs_pos
        have h_out_pos : 1 ≤ out_sig := by
          rw [h_out_sig]
          exact Nat.mul_pos h_cs_pos (Nat.pow_pos (by grind))
        have h_sig'_hi : sig' < 10 ^ L := by
          have := lt_pow10_decDigitLength sig' h_sig'_pos
          rw [h_len] at this; exact this
        have h_out_lo : 10 ^ (L + t - 1) ≤ out_sig := by
          have := pow10_decDigitLength_pred_le out_sig h_out_pos
          rw [h_dl_out] at this; exact this
        have h_pow_mono : 10 ^ L ≤ 10 ^ (L + t - 1) :=
          Nat.pow_le_pow_right (by grind) (by omega)
        rcases h_cons with h_up | h_down
        · -- `sig' = out_sig + 1 ≥ 10^(L+t-1) + 1 > 10^L`: too many digits.
          omega
        · -- `out_sig = sig' + 1`: forces `t = 1`, `out_sig = 10^L`, `L = 1`.
          have h_out_le : out_sig ≤ 10 ^ L := by omega
          have h_t1 : t = 1 := by
            by_contra h_t1
            have h_t2 : 2 ≤ t := by omega
            have : 10 ^ (L + 1) ≤ 10 ^ (L + t - 1) :=
              Nat.pow_le_pow_right (by grind) (by omega)
            have h_strict : 10 ^ L < 10 ^ (L + 1) :=
              Nat.pow_lt_pow_right (by grind) (by omega)
            omega
          subst h_t1
          have h_out_eq : out_sig = 10 ^ L := by omega
          have h_cs10 : cs * 10 = 10 ^ L := by
            rw [← h_out_eq, h_out_sig, Nat.pow_one]
          have hL_pos : 1 ≤ L := decDigitLength_pos cs
          have h_L1 : L = 1 := by
            by_contra h_L1
            have h_L2 : 2 ≤ L := by omega
            -- `cs = 10^(L-1)` is divisible by 10 for `L ≥ 2`.
            have h_cs_eq : cs = 10 ^ (L - 1) := by
              have : cs * 10 = 10 ^ (L - 1) * 10 := by
                rw [h_cs10]
                conv => lhs; rw [show L = (L - 1) + 1 from by omega]
                rw [Nat.pow_succ]
              omega
            have : 10 ^ (L - 1) % 10 = 0 := by
              obtain ⟨i, hi⟩ : ∃ i, L - 1 = i + 1 := ⟨L - 2, by omega⟩
              rw [hi, Nat.pow_succ]; omega
            rw [h_cs_eq] at h_cs_canon
            exact h_cs_canon this
          have h_cs1 : cs = 1 := by
            rw [h_L1] at h_cs10; omega
          have h_out10 : out_sig = 10 := by rw [h_out_eq, h_L1]
          have h_sig'9 : sig' = 9 := by omega
          -- Both `9, 10 ∈ R_v` at `out_exp`, exactly equidistant: impossible.
          have h_mem9 : inRoundingInterval 9 out_exp m q (isIrregular m q) = true := by
            rw [← h_sig'9]; exact h_mem_shift
          have h_mem10 : inRoundingInterval 10 out_exp m q (isIrregular m q) = true := by
            rw [← h_out10]
            exact shortestUnsigned_mem_rv m q hm_pos hm_lt hq_lo hq_hi
          have h_equid : Equidistant 9 out_exp m q := by
            apply (equidistant_iff_rat 9 out_exp m q).mp
            have h_e1 : |magVal m q - gridVal 9 out_exp|
                = |magVal m q - gridVal 10 out_exp| := by
              rw [← h_out10, ← h_sig'9]
              exact h_eqd_shift.symm
            exact h_e1
          exact tie_nine_ten_impossible m q out_exp h_legal h_mem9 h_mem10 h_equid
    · -- `exp' < out_exp`: the decade-gap bound forces `t = 0`, contradiction.
      push_neg at h_ge
      have h_cs_mem : inRoundingInterval cs ce m q (isIrregular m q) = true := by
        have hshift := inRoundingInterval_mul10pow_shift_down cs t (out_exp + t) m q (isIrregular m q)
        have he2 : (out_exp + (t : Int)) - (t : Int) = out_exp := by grind
        rw [he2] at hshift; rw [← h_out_sig] at hshift
        rw [h_ce, ← hshift]
        exact shortestUnsigned_mem_rv m q hm_pos hm_lt hq_lo hq_hi
      have h_gap := samelen_exp_diff_le_one m q hm_pos
        sig' exp' h_sig'_pos h_mem cs ce h_cs_pos h_cs_mem (by rw [h_len])
      have h_ce_eq : ce = out_exp + (t : Int) := h_ce
      omega

/-! ## The headline proofs

`correctness_proof` establishes `IsCorrectPrinterBits Schubfach.toDecimal`
clause by clause. `specOutput_eq_output` shows a spec output IS the
algorithm's output; `printer_unique_proof` (extensional uniqueness) and
`spec_output_exists_unique_proof` (per-float `∃!`) follow. -/

set_option maxHeartbeats 1600000 in
/-- The finite-nonzero clause of `correctness_proof`. -/
private theorem Schubfach.correctness_fin_aux (w : UInt64)
    (h_fin : Word.isFinite w = true) (h_nz : (Word.decode w).m ≠ 0) :
    ∃ d : Decimal, Schubfach.toDecimalBits w = .ok d ∧ Schubfach.IsSpecOutputBits w d := by
  -- Round-trip clause + the algorithm output `d`.
  obtain ⟨d, h_eq, h_rt⟩ := ofDecimal_toDecimal_eq_bits w h_fin h_nz
  -- Decode invariants.
  set m := (Word.decode w).m with hm
  set q := (Word.decode w).q with hq
  have ⟨h_m_lt, h_q_lo, h_q_hi⟩ :=
    Srtfp.Schubfach.decode_invariants_bits w h_fin
  have h_m_pos : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr h_nz
  -- The output decimal d = mk' (Word.decode w).sign out_sig out_exp.
  set out_sig := (shortestUnsigned m q).1 with h_out_sig
  set out_exp := (shortestUnsigned m q).2 with h_out_exp
  have h_out_ne : out_sig ≠ 0 := by
    rw [h_out_sig]; exact Nat.one_le_iff_ne_zero.mp
      (shortestUnsigned_sig_pos m q h_m_pos h_m_lt h_q_lo h_q_hi)
  have h_d_eq : d = Decimal.mk' (Word.decode w).sign out_sig out_exp := by
    have h_be_lt : Word.biasedExp w < 2047 := by
      unfold Word.isFinite at h_fin; simpa using h_fin
    have hnan : Word.isNaN w = false := by
      unfold Word.isNaN; have : ¬ Word.biasedExp w = 2047 := by omega
      simp [this]
    have hinf : Word.isInf w = false := by
      unfold Word.isInf; have : ¬ Word.biasedExp w = 2047 := by omega
      simp [this]
    have h_unfold : Schubfach.toDecimalBits w
        = .ok (Decimal.mk' (Word.decode w).sign out_sig out_exp) := by
      unfold Schubfach.toDecimalBits
      rw [hnan, hinf]; rw [if_neg h_nz]; rfl
    rw [h_unfold] at h_eq; cases h_eq; rfl
  -- Canonical decomposition of d via `mk_pos_props`.
  obtain ⟨h_mk_sign, h_mk_sig_ne, h_mk_canon, h_mk_exp_le, h_mk_decomp⟩ :=
    mk_pos_props (Word.decode w).sign out_sig out_exp h_out_ne
  rw [← h_d_eq] at h_mk_sign h_mk_sig_ne h_mk_canon h_mk_exp_le h_mk_decomp
  set t : Nat := (d.exponent - out_exp).toNat with h_t
  have h_ce : d.exponent = out_exp + (t : Int) := by
    rw [h_t, Int.toNat_of_nonneg (by omega)]; grind
  have h_out_decomp : out_sig = d.significand * 10 ^ t := h_mk_decomp.symm
  have h_cs_pos : 1 ≤ d.significand := Nat.one_le_iff_ne_zero.mpr h_mk_sig_ne
  -- Shared competitor analysis: any canonical round-tripper `d'` has a
  -- nonzero canonical significand, `w`'s sign, and lies in `R_v(Word.decode w)`.
  have h_comp : ∀ d' : Decimal, Decimal.IsCanonical d' →
      Clinger.ofDecimalBits d' = w →
      d'.significand ≠ 0 ∧ d'.significand % 10 ≠ 0 ∧ d'.sign = (Word.decode w).sign ∧
      inRoundingInterval d'.significand d'.exponent m q (isIrregular m q) = true := by
    intro d' h'_canon h'_rt
    have h'_sig_ne : d'.significand ≠ 0 := by
      intro h_sig_zero
      have h_f_bits : w = Word.pack d'.sign 0 0 := by
        rw [← h'_rt]; exact ofDecimal_sig0_bits d' h_sig_zero
      have h_m_zero : (Word.decode w).m = 0 := by
        cases hs : d'.sign
        all_goals
          rw [hs] at h_f_bits
          rw [h_f_bits]
          decide
      exact h_nz h_m_zero
    have h'_finabs : IsFiniteAbs d'.sign d'.significand d'.exponent :=
      Clinger.isFiniteAbs_of_roundtrip_bits d' w h'_sig_ne h_fin h'_rt
    have h'_mod : d'.significand % 10 ≠ 0 := by
      rcases h'_canon with ⟨h_zero, _⟩ | ⟨_, h_mod⟩
      · exact absurd h_zero h'_sig_ne
      · exact h_mod
    have h'_sign : d'.sign = (Word.decode w).sign := roundtrip_sign_eq d' w h'_finabs h'_rt
    have h'_in_Rv : inRoundingInterval d'.significand d'.exponent m q
        (isIrregular m q) = true := by
      have h0 : inRoundingInterval d'.significand d'.exponent
          (Word.decode (Clinger.ofDecimalBits d')).m (Word.decode (Clinger.ofDecimalBits d')).q
          (isIrregular (Word.decode (Clinger.ofDecimalBits d')).m
                       (Word.decode (Clinger.ofDecimalBits d')).q) = true :=
        Clinger.ofDecimalBits_in_Rv d' h'_sig_ne h'_finabs
      rwa [decode_eq_of_toBits_eq h'_rt] at h0
    exact ⟨h'_sig_ne, h'_mod, h'_sign, h'_in_Rv⟩
  refine ⟨d, h_eq, (Schubfach.isSpecOutput_iff w d).mpr
    ⟨toDecimal_isCanonical w h_fin h_nz d h_eq, h_rt, ?shortest, ?tie⟩⟩
  case shortest =>
    intro d' h'_canon h'_rt
    obtain ⟨h'_sig_ne, h'_mod, _, h'_in_Rv⟩ := h_comp d' h'_canon h'_rt
    obtain ⟨result, h_result_eq, h_minimal⟩ := toDecimal_minimal w h_fin h_nz
    have h_result_eq_d : result = d := by
      rw [h_result_eq] at h_eq; cases h_eq; rfl
    rw [h_result_eq_d] at h_minimal
    exact h_minimal d'.sign d'.significand d'.exponent h'_sig_ne h'_mod h'_in_Rv
  case tie =>
    intro d' h'_canon h'_rt h'_len
    obtain ⟨h'_sig_ne, h'_mod, h'_sign, h'_in_Rv⟩ := h_comp d' h'_canon h'_rt
    -- Same-digit-length unsigned tie-break (cs = d.significand, ce = d.exponent).
    have h_unsigned := shortestUnsigned_clause3_same_len m q h_m_pos h_m_lt h_q_lo h_q_hi
      d.significand d.exponent t h_cs_pos h_mk_canon h_out_decomp h_ce
      d'.significand d'.exponent (Nat.one_le_iff_ne_zero.mpr h'_sig_ne)
      h'_mod h'_in_Rv h'_len
    -- Reduce signed distances to unsigned grid distances.
    have h_d_dist : |Decimal.toRat d - Schubfach.wordVal w|
        = |magVal m q - gridVal d.significand d.exponent| :=
      toRat_dist_eq_grid_dist d w h_mk_sign
    have h'_dist : |Decimal.toRat d' - Schubfach.wordVal w|
        = |magVal m q - gridVal d'.significand d'.exponent| :=
      toRat_dist_eq_grid_dist d' w h'_sign
    rw [h_d_dist, h'_dist]
    rcases h_unsigned with ⟨h_sig_eq, h_exp_eq⟩ | h_lt | ⟨h_eqd, h_even⟩
    · -- d' agrees with d on significand, exponent, and sign ⇒ d = d'.
      left
      have hsg : d.sign = d'.sign := by rw [h_mk_sign, h'_sign]
      obtain ⟨ds, dsig, dexp⟩ := d
      obtain ⟨d's, d'sig, d'exp⟩ := d'
      simp only at hsg h_sig_eq h_exp_eq ⊢
      rw [hsg, h_sig_eq, h_exp_eq]
    · exact Or.inr (Or.inl h_lt)
    · -- Tie: upgrade the raw-output parity to the canonical significand.
      by_cases h_same : d'.significand = d.significand ∧ d'.exponent = d.exponent
      · left
        obtain ⟨hsig, hexp⟩ := h_same
        have hsg : d.sign = d'.sign := by rw [h_mk_sign, h'_sign]
        obtain ⟨ds, dsig, dexp⟩ := d
        obtain ⟨d's, d'sig, d'exp⟩ := d'
        simp only at hsg hsig hexp ⊢
        rw [hsg, hsig, hexp]
      · have h_legal : LegalIEEE m q := by
          rw [hm, hq]; exact decode_legalIEEE_bits w h_fin h_nz
        have h_cs_even := samelen_tie_canonical_even m q h_m_pos h_m_lt h_q_lo h_q_hi
          h_legal d.significand d.exponent t h_cs_pos h_mk_canon h_out_decomp h_ce
          d'.significand d'.exponent (Nat.one_le_iff_ne_zero.mpr h'_sig_ne) h'_mod
          h'_in_Rv h'_len h_same h_eqd h_even
        exact Or.inr (Or.inr ⟨h_eqd, h_cs_even⟩)

/-- The zero clause of `correctness_proof`: the signed canonical zero is
THE shortest decimal for `±0`. -/
private theorem Schubfach.correctness_zero_aux (w : UInt64)
    (h_fin : Word.isFinite w = true) (h_nz : (Word.decode w).m = 0) :
    ∃ d : Decimal, Schubfach.toDecimalBits w = .ok d ∧ Schubfach.IsSpecOutputBits w d := by
  refine ⟨⟨(Word.decode w).sign, 0, 0⟩, toDecimalBits_zero w h_fin h_nz,
    (Schubfach.isSpecOutput_iff w _).mpr
      ⟨Or.inl ⟨rfl, rfl⟩, ofDecimal_signedZero_bits w h_nz, ?_, ?_⟩⟩
  · -- shortest: one digit is minimal.
    intro d' _ _
    show decDigitLength 0 ≤ decDigitLength d'.significand
    have h1 := decDigitLength_pos d'.significand
    have h0 : decDigitLength 0 = 1 := decDigitLength_zero
    omega
  · -- tie clause.
    intro d' h'_canon h'_rt h'_len
    by_cases h'_s0 : d'.significand = 0
    · -- a canonical zero competitor has the same sign, hence is equal.
      left
      have h'_exp : d'.exponent = 0 := by
        rcases h'_canon with ⟨_, h⟩ | ⟨h, _⟩
        · exact h
        · exact absurd h'_s0 h
      have h'_bits : Word.pack d'.sign 0 0 = w := by
        rw [← ofDecimal_sig0_bits d' h'_s0]; exact h'_rt
      have h_bits : Word.pack (Word.decode w).sign 0 0 = w := by
        rw [← ofDecimal_sig0_bits (⟨(Word.decode w).sign, 0, 0⟩ : Decimal) rfl]
        exact ofDecimal_signedZero_bits w h_nz
      have h_sign : d'.sign = (Word.decode w).sign :=
        pack_zero_sign_inj _ _ (h'_bits.trans h_bits.symm)
      show (⟨(Word.decode w).sign, 0, 0⟩ : Decimal) = d'
      rcases d' with ⟨ds, dsig, dexp⟩
      simp only at h'_s0 h'_exp h_sign
      rw [h_sign, h'_s0, h'_exp]
    · -- a nonzero competitor is strictly farther from `±0`.
      right; left
      have h_fv : Schubfach.wordVal w = 0 := wordVal_zero w h_nz
      have h_d0 : Decimal.toRat (⟨(Word.decode w).sign, 0, 0⟩ : Decimal) = 0 :=
        toRat_zero _ rfl
      rw [h_fv, h_d0]
      simp only [sub_zero, abs_zero]
      exact abs_pos.mpr (toRat_ne_zero d' h'_s0)

set_option maxHeartbeats 1600000 in
/-- Proof of `Schubfach.correctness`.  The audit-facing statement (with its
rich docstring) is in `Srtfp/Correctness.lean`, which delegates here. -/
theorem Schubfach.correctness_proof :
    Schubfach.IsCorrectPrinterBits Schubfach.toDecimalBits := by
  intro w
  refine ⟨?nanCase, ?infCase, ?finCase⟩
  case nanCase =>
    intro h_nan
    unfold Schubfach.toDecimalBits
    rw [if_pos h_nan]
  case infCase =>
    intro h_inf
    have h_nan : Word.isNaN w = false := by
      unfold Word.isNaN
      unfold Word.isInf at h_inf
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h_inf
      simp [h_inf.2]
    unfold Schubfach.toDecimalBits
    rw [if_neg (by simp [h_nan]), if_pos h_inf]
  case finCase =>
    intro h_fin
    by_cases h_nz : (Word.decode w).m = 0
    · exact Schubfach.correctness_zero_aux w h_fin h_nz
    · exact Schubfach.correctness_fin_aux w h_fin h_nz
set_option maxHeartbeats 1600000 in
/-- `specOutput_eq_output`, finite-nonzero case: pits the spec witness
`d_star` against the output `d` — mutual shortest-ness forces equal digit
length, mutual closest-ness forces equidistance, and a same-length
even–even tie is geometrically impossible (`samelen_even_tie_false`). -/
private theorem Schubfach.specOutput_eq_output_nz (w : UInt64)
    (h_fin : Word.isFinite w = true) (h_nz : (Word.decode w).m ≠ 0)
    (d_star : Decimal)
    (h_canon : Decimal.IsCanonical d_star)
    (h_rt : Schubfach.RoundTripsBits w d_star)
    (h_short : ∀ d' : Decimal, Decimal.IsCanonical d' → Schubfach.RoundTripsBits w d' →
        decDigitLength d_star.significand ≤ decDigitLength d'.significand)
    (h_tie : ∀ d' : Decimal, Decimal.IsCanonical d' → Schubfach.RoundTripsBits w d' →
        decDigitLength d'.significand = decDigitLength d_star.significand →
          d_star = d'
        ∨ |Decimal.toRat d_star - Schubfach.wordVal w| < |Decimal.toRat d' - Schubfach.wordVal w|
        ∨ ( |Decimal.toRat d_star - Schubfach.wordVal w| = |Decimal.toRat d' - Schubfach.wordVal w|
            ∧ d_star.significand % 2 = 0 )) :
    Schubfach.toDecimalBits w = .ok d_star := by
  have h_rt' : Clinger.ofDecimalBits d_star = w := h_rt
  -- The algorithm's own output and its spec properties.
  have h_corr := Schubfach.correctness_proof w
  obtain ⟨_, _, h_main⟩ := h_corr
  obtain ⟨d, h_eq, h_spec_d⟩ := h_main h_fin
  obtain ⟨h_canon_d, h_rt_d, h_min_d, h_tie_d⟩ :=
    (Schubfach.isSpecOutput_iff w d).mp h_spec_d
  have h_rt_d' : Clinger.ofDecimalBits d = w := h_rt_d
  -- Reduce to d = d_star.
  suffices h_de : d = d_star by rw [h_de] at h_eq; exact h_eq
  -- Decode invariants and output decomposition.
  set m := (Word.decode w).m with hm
  set q := (Word.decode w).q with hq
  have ⟨h_m_lt, h_q_lo, h_q_hi⟩ :=
    Srtfp.Schubfach.decode_invariants_bits w h_fin
  have h_m_pos : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr h_nz
  set out_sig := (shortestUnsigned m q).1 with h_out_sig
  set out_exp := (shortestUnsigned m q).2 with h_out_exp
  have h_out_ne : out_sig ≠ 0 := by
    rw [h_out_sig]; exact Nat.one_le_iff_ne_zero.mp
      (shortestUnsigned_sig_pos m q h_m_pos h_m_lt h_q_lo h_q_hi)
  have h_d_eq : d = Decimal.mk' (Word.decode w).sign out_sig out_exp := by
    have h_be_lt : Word.biasedExp w < 2047 := by
      unfold Word.isFinite at h_fin; simpa using h_fin
    have hnan : Word.isNaN w = false := by
      unfold Word.isNaN; have : ¬ Word.biasedExp w = 2047 := by omega
      simp [this]
    have hinf : Word.isInf w = false := by
      unfold Word.isInf; have : ¬ Word.biasedExp w = 2047 := by omega
      simp [this]
    have h_unfold : Schubfach.toDecimalBits w
        = .ok (Decimal.mk' (Word.decode w).sign out_sig out_exp) := by
      unfold Schubfach.toDecimalBits
      rw [hnan, hinf]; rw [if_neg h_nz]; rfl
    rw [h_unfold] at h_eq; cases h_eq; rfl
  obtain ⟨h_mk_sign, h_mk_sig_ne, h_mk_canon, h_mk_exp_le, h_mk_decomp⟩ :=
    mk_pos_props (Word.decode w).sign out_sig out_exp h_out_ne
  rw [← h_d_eq] at h_mk_sign h_mk_sig_ne h_mk_canon h_mk_exp_le h_mk_decomp
  set t : Nat := (d.exponent - out_exp).toNat with h_t
  have h_ce : d.exponent = out_exp + (t : Int) := by
    rw [h_t, Int.toNat_of_nonneg (by omega)]; grind
  have h_out_decomp : out_sig = d.significand * 10 ^ t := h_mk_decomp.symm
  have h_cs_pos : 1 ≤ d.significand := Nat.one_le_iff_ne_zero.mpr h_mk_sig_ne
  -- d_star has a nonzero canonical significand (round-trips to nonzero w).
  have h_star_sig_ne : d_star.significand ≠ 0 := by
    intro h_sig_zero
    have h_f_bits : w = Word.pack d_star.sign 0 0 := by
      rw [← h_rt']; exact ofDecimal_sig0_bits d_star h_sig_zero
    have h_m_zero : (Word.decode w).m = 0 := by
      cases hs : d_star.sign
      all_goals
        rw [hs] at h_f_bits
        rw [h_f_bits]
        decide
    exact h_nz h_m_zero
  have h_star_canon_mod : d_star.significand % 10 ≠ 0 := by
    rcases h_canon with ⟨h_zero, _⟩ | ⟨_, h_mod⟩
    · exact absurd h_zero h_star_sig_ne
    · exact h_mod
  have h_finabs : IsFiniteAbs d_star.sign d_star.significand d_star.exponent :=
    Clinger.isFiniteAbs_of_roundtrip_bits d_star w h_star_sig_ne h_fin h_rt'
  -- Step 1: same digit length L.
  have h_le1 : decDigitLength d.significand ≤ decDigitLength d_star.significand :=
    h_min_d d_star h_canon h_rt
  have h_le2 : decDigitLength d_star.significand ≤ decDigitLength d.significand :=
    h_short d h_canon_d h_rt_d
  have h_len_eq : decDigitLength d.significand = decDigitLength d_star.significand :=
    Nat.le_antisymm h_le1 h_le2
  -- Step 2: mutual tie-break.
  have h_tb_d := h_tie_d d_star h_canon h_rt h_len_eq.symm
  have h_tb_s := h_tie d h_canon_d h_rt_d h_len_eq
  -- Distance reductions to unsigned grid distances.
  have h'_sign : d_star.sign = (Word.decode w).sign := roundtrip_sign_eq d_star w h_finabs h_rt'
  have h_d_dist : |Decimal.toRat d - Schubfach.wordVal w|
      = |magVal m q - gridVal d.significand d.exponent| :=
    toRat_dist_eq_grid_dist d w h_mk_sign
  have h_s_dist : |Decimal.toRat d_star - Schubfach.wordVal w|
      = |magVal m q - gridVal d_star.significand d_star.exponent| :=
    toRat_dist_eq_grid_dist d_star w h'_sign
  -- Resolve the mutual tie-break.
  rcases h_tb_d with h_eqd' | h_lt_d | ⟨h_eqdist_d, h_even_out⟩
  · exact h_eqd'
  · -- |d - w| < |d_star - w|.  Combine with h_tb_s.
    exfalso
    rcases h_tb_s with h_eqs' | h_lt_s | ⟨h_eqdist_s, _⟩
    · exact Rat.ne_of_lt h_lt_d (by rw [h_eqs'])
    · exact absurd (lt_trans h_lt_d h_lt_s) (lt_irrefl _)
    · rw [h_eqdist_s] at h_lt_d; exact lt_irrefl _ h_lt_d
  · -- |d - w| = |d_star - w| and d.significand even.  Combine with h_tb_s.
    rcases h_tb_s with h_eqs' | h_lt_s | ⟨_, h_even_star⟩
    · exact h_eqs'.symm
    · rw [h_eqdist_d] at h_lt_s; exact absurd h_lt_s (lt_irrefl _)
    · -- Both equidistant, both significands even.
      by_cases h_same : d_star.significand = d.significand ∧ d_star.exponent = d.exponent
      · obtain ⟨hsig, hexp⟩ := h_same
        obtain ⟨ds, dsig, dexp⟩ := d
        obtain ⟨d's, d'sig, d'exp⟩ := d_star
        simp only at hsig hexp ⊢
        have hsign : ds = d's := by
          rw [show ds = (Decimal.mk ds dsig dexp).sign from rfl, h_mk_sign,
              show d's = (Decimal.mk d's d'sig d'exp).sign from rfl, h'_sign]
        rw [hsign, hsig, hexp]
      exfalso
      -- The raw output parity, from the canonical parity.
      have h_out_even_int : out_sig % 2 = 0 := by
        rcases Nat.eq_zero_or_pos t with ht0 | ht1
        · rw [h_out_decomp, ht0, Nat.pow_zero, Nat.mul_one]; exact h_even_out
        · have h2 : (2 : Nat) ∣ 10 ^ t := Nat.dvd_pow' (by decide) (by omega)
          have hY : (2 : Nat) ∣ d.significand * 10 ^ t := Nat.dvd_trans h2 (Nat.dvd_mul_left _ _)
          rw [h_out_decomp]
          omega
      -- Reduce equidistance to unsigned grid distances.
      have h_grid_eqd :
          |magVal m q - gridVal d.significand d.exponent|
            = |magVal m q - gridVal d_star.significand d_star.exponent| := by
        rw [← h_d_dist, ← h_s_dist]; exact h_eqdist_d
      have h_star_in_Rv : inRoundingInterval d_star.significand d_star.exponent m q
                            (isIrregular m q) = true := by
        have h0 : inRoundingInterval d_star.significand d_star.exponent
            (Word.decode (Clinger.ofDecimalBits d_star)).m (Word.decode (Clinger.ofDecimalBits d_star)).q
            (isIrregular (Word.decode (Clinger.ofDecimalBits d_star)).m
                         (Word.decode (Clinger.ofDecimalBits d_star)).q) = true :=
          Clinger.ofDecimalBits_in_Rv d_star h_star_sig_ne h_finabs
        rwa [decode_eq_of_toBits_eq h_rt'] at h0
      have h_distinct : ¬ (d_star.significand = d.significand ∧ d_star.exponent = d.exponent) :=
        h_same
      exact samelen_even_tie_false m q h_m_pos h_m_lt h_q_lo h_q_hi
        d.significand d.exponent t h_cs_pos h_mk_canon h_out_decomp h_ce
        d_star.significand d_star.exponent
        (Nat.one_le_iff_ne_zero.mpr h_star_sig_ne) h_star_canon_mod h_star_in_Rv
        h_len_eq.symm h_distinct h_grid_eqd h_out_even_int h_even_star


/-- A decimal satisfying the specification IS the algorithm's output. -/
theorem Schubfach.specOutput_eq_output (w : UInt64)
    (h_fin : Word.isFinite w = true)
    (d_star : Decimal) (h_spec : Schubfach.IsSpecOutputBits w d_star) :
    Schubfach.toDecimalBits w = .ok d_star := by
  obtain ⟨h_canon, h_rt, h_short, h_tie⟩ :=
    (Schubfach.isSpecOutput_iff w d_star).mp h_spec
  by_cases h_nz : (Word.decode w).m = 0
  · -- `w = ±0`: the spec pins `d_star` to the signed canonical zero.
    have h_rt' : Clinger.ofDecimalBits d_star = w := h_rt
    have h_dz_rt : Schubfach.RoundTripsBits w (⟨(Word.decode w).sign, 0, 0⟩ : Decimal) :=
      ofDecimal_signedZero_bits w h_nz
    have h_dz_canon : Decimal.IsCanonical (⟨(Word.decode w).sign, 0, 0⟩ : Decimal) :=
      Or.inl ⟨rfl, rfl⟩
    have h_fv : Schubfach.wordVal w = 0 := wordVal_zero w h_nz
    have h_sig0 : d_star.significand = 0 := by
      by_contra h_ne
      have h_le : decDigitLength d_star.significand ≤ decDigitLength 0 :=
        h_short ⟨(Word.decode w).sign, 0, 0⟩ h_dz_canon h_dz_rt
      have h_len : decDigitLength (⟨(Word.decode w).sign, 0, 0⟩ : Decimal).significand
          = decDigitLength d_star.significand := by
        have h1 := decDigitLength_pos d_star.significand
        have h0 : decDigitLength 0 = 1 := decDigitLength_zero
        show decDigitLength 0 = _
        omega
      have h_tb := h_tie ⟨(Word.decode w).sign, 0, 0⟩ h_dz_canon h_dz_rt h_len
      have h_z : Decimal.toRat (⟨(Word.decode w).sign, 0, 0⟩ : Decimal) = 0 :=
        toRat_zero _ rfl
      rcases h_tb with h_eq' | h_lt | ⟨h_eqd, _⟩
      · rw [h_eq'] at h_ne
        exact h_ne rfl
      · rw [h_fv, h_z] at h_lt
        simp only [sub_zero, abs_zero] at h_lt
        exact absurd h_lt (not_lt.mpr (abs_nonneg _))
      · rw [h_fv, h_z] at h_eqd
        simp only [sub_zero, abs_zero] at h_eqd
        exact toRat_ne_zero d_star h_ne (abs_eq_zero.mp h_eqd)
    have h_exp0 : d_star.exponent = 0 := by
      rcases h_canon with ⟨_, h⟩ | ⟨h, _⟩
      · exact h
      · exact absurd h_sig0 h
    have h_sign : d_star.sign = (Word.decode w).sign := by
      have h1 : Clinger.ofDecimalBits d_star = Word.pack d_star.sign 0 0 :=
        ofDecimal_sig0_bits d_star h_sig0
      have h2 : Word.pack (Word.decode w).sign 0 0 = w := by
        rw [← ofDecimal_sig0_bits (⟨(Word.decode w).sign, 0, 0⟩ : Decimal) rfl]
        exact h_dz_rt
      exact pack_zero_sign_inj _ _ ((h1.symm.trans h_rt').trans h2.symm)
    rw [toDecimalBits_zero w h_fin h_nz]
    rcases d_star with ⟨ds, dsig, dexp⟩
    simp only at h_sig0 h_exp0 h_sign
    rw [h_sign, h_sig0, h_exp0]
  · exact Schubfach.specOutput_eq_output_nz w h_fin h_nz d_star h_canon h_rt h_short h_tie

/-- Proof of `Schubfach.printer_unique`: the specification pins down the
printer extensionally — on each input, case-split the (exhaustive,
mutually exclusive) edge conditions; on finite nonzero inputs both
outputs equal the algorithm's via `specOutput_eq_output`. -/
theorem Schubfach.printer_unique_proof (p₁ p₂ : UInt64 → Except String Decimal)
    (h₁ : Schubfach.IsCorrectPrinterBits p₁) (h₂ : Schubfach.IsCorrectPrinterBits p₂) :
    p₁ = p₂ := by
  funext w
  obtain ⟨h1_nan, h1_inf, h1_main⟩ := h₁ w
  obtain ⟨h2_nan, h2_inf, h2_main⟩ := h₂ w
  by_cases h_nan : Word.isNaN w = true
  · rw [h1_nan h_nan, h2_nan h_nan]
  · by_cases h_inf : Word.isInf w = true
    · rw [h1_inf h_inf, h2_inf h_inf]
    · -- Not NaN, not ∞ ⇒ finite.
      have h_fin : Word.isFinite w = true := by
        have h_be_le : Word.biasedExp w ≤ 2047 := by
          show ((w >>> 52) &&& 0x7FF).toNat ≤ 2047
          rw [UInt64.toNat_and]
          have h_max : (0x7FF : UInt64).toNat = 2047 := by decide
          rw [h_max]
          exact Nat.and_le_right
        unfold Word.isFinite
        rcases Nat.lt_or_ge (Word.biasedExp w) 2047 with h | h
        · simpa using h
        · exfalso
          have h_be : Word.biasedExp w = 2047 := by omega
          by_cases h_m : Word.mantissa w = 0
          · exact h_inf (by unfold Word.isInf; simp [h_be, h_m])
          · exact h_nan (by unfold Word.isNaN; simp [h_be, h_m])
      obtain ⟨d₁, h_eq₁, h_spec₁⟩ := h1_main h_fin
      obtain ⟨d₂, h_eq₂, h_spec₂⟩ := h2_main h_fin
      have e₁ := Schubfach.specOutput_eq_output w h_fin d₁ h_spec₁
      have e₂ := Schubfach.specOutput_eq_output w h_fin d₂ h_spec₂
      rw [h_eq₁, h_eq₂]
      rw [e₁] at e₂
      cases e₂
      rfl

/-- Proof of `Schubfach.spec_output_exists_unique`. -/
theorem Schubfach.spec_output_exists_unique_proof (w : UInt64)
    (h_fin : Word.isFinite w = true) :
    ∃! d : Decimal, Schubfach.IsSpecOutputBits w d := by
  have h_corr := Schubfach.correctness_proof w
  obtain ⟨_, _, h_main⟩ := h_corr
  obtain ⟨d, h_eq, h_spec⟩ := h_main h_fin
  refine ⟨d, h_spec, ?_⟩
  intro d' h_spec'
  have e' := Schubfach.specOutput_eq_output w h_fin d' h_spec'
  rw [h_eq] at e'
  cases e'
  rfl

/-! ## Assembly in the public vocabulary

The public file (`Srtfp/Correctness.lean`) restates the spec with
`digits n = Nat.log 10 n + 1` and delegates to the two theorems below by
`:=` — the kernel's definitional check of those delegations certifies the
restatement.  `decDigitLength_eq_log` is the digit-count bridge. -/

theorem Schubfach.decDigitLength_eq_log (n : Nat) :
    decDigitLength n = Nat.log 10 n + 1 := by
  induction n using decDigitLength.induct with
  | case1 n h =>
    rw [decDigitLength.eq_def]
    simp [Nat.log_eq_zero_iff, h]
  | case2 n h ih =>
    rw [decDigitLength.eq_def]
    have hpos : 0 < Nat.log 10 n := Nat.log_pos (by omega) (by omega)
    have hdiv : Nat.log 10 (n / 10) = Nat.log 10 n - 1 := Nat.log_div_base 10 n
    simp only [if_neg h]
    omega

theorem Schubfach.correct_iff_toDecimal_proof
    (p : UInt64 → Except String Decimal) :
    ( ∀ w : UInt64,
        (Word.isNaN w = true → p w = .error "NaN")
      ∧ (Word.isInf w = true →
           p w = .error (if Word.signBit w then "-Infinity" else "Infinity"))
      ∧ (Word.isFinite w = true →
           ∃ d : Decimal, p w = .ok d
             ∧ ( Decimal.IsCanonical d
               ∧ Schubfach.RoundTripsBits w d
               ∧ (∀ d' : Decimal, d' ≠ d → Decimal.IsCanonical d' →
                    Schubfach.RoundTripsBits w d' →
                    ( Nat.log 10 d.significand + 1
                        < Nat.log 10 d'.significand + 1
                    ∨ ( Nat.log 10 d'.significand + 1
                          = Nat.log 10 d.significand + 1
                      ∧ ( |Decimal.toRat d - Schubfach.wordVal w|
                            < |Decimal.toRat d' - Schubfach.wordVal w|
                        ∨ ( |Decimal.toRat d - Schubfach.wordVal w|
                              = |Decimal.toRat d' - Schubfach.wordVal w|
                            ∧ d.significand % 2 = 0 ))))))) )
    ↔ p = Schubfach.toDecimalBits := by
  simp only [← Schubfach.decDigitLength_eq_log]
  constructor
  · intro h
    exact Schubfach.printer_unique_proof p Schubfach.toDecimalBits h
      Schubfach.correctness_proof
  · rintro rfl
    exact Schubfach.correctness_proof

theorem Schubfach.shortest_decimal_exists_unique_proof (w : UInt64)
    (h_fin : Word.isFinite w = true) :
    ∃! d : Decimal,
        Decimal.IsCanonical d
      ∧ Schubfach.RoundTripsBits w d
      ∧ (∀ d' : Decimal, d' ≠ d → Decimal.IsCanonical d' →
           Schubfach.RoundTripsBits w d' →
           ( Nat.log 10 d.significand + 1 < Nat.log 10 d'.significand + 1
           ∨ ( Nat.log 10 d'.significand + 1 = Nat.log 10 d.significand + 1
             ∧ ( |Decimal.toRat d - Schubfach.wordVal w|
                   < |Decimal.toRat d' - Schubfach.wordVal w|
               ∨ ( |Decimal.toRat d - Schubfach.wordVal w|
                     = |Decimal.toRat d' - Schubfach.wordVal w|
                   ∧ d.significand % 2 = 0 ))))) := by
  have h := Schubfach.spec_output_exists_unique_proof w h_fin
  unfold Schubfach.IsSpecOutputBits at h
  simpa only [← Schubfach.decDigitLength_eq_log] using h

end Srtfp

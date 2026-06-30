import Mathlib.Algebra.ContinuedFractions.Computation.TerminatesIffRat
import Srtfp.Numeric.Schubfach.R20Legendre

/-!
# R20 finite-sweep: sound reduction to a rational-convergent check

This file completes the *sound mathematical reduction* of the R20
`farFromMultipleBelow` obligation to a finite, computable check over the
rational continued fraction of `u/M`.  All results here are sorry-free
(axioms: `propext`, `Quot.sound`, `Classical.choice`).

## What is proven (sorry-free)

* `convs_coe_rat` — the ℝ→ℚ convergent cast bridge: the real CF convergent
  of `↑q` is the cast of the rational CF convergent of `q`.  This makes
  `bad_is_convergent`'s (noncomputable, real) conclusion checkable over the
  computable rational CF.
* `approx_den_fixed` — the reduced ceiling denominator is a ceiling fixed
  point: `approx M u ((approx M u m).den) = approx M u m` for non-divisible
  `m`.  (Ceiling sandwich + integer uniqueness; no gap smallness.)
* `gap_mul_of_approx_eq` / `far_of_far_at_den` — gap multiplicativity along
  divisors with a shared ceiling rational, so `far` at a divisor transfers
  up to its multiples.  This is the sound form of the spike's "every bad
  `m` is a convergent denominator".
* `far_of_far_at_rat_convergents` — **the reduction**: to prove
  `farFromMultipleBelow M u m a` for all `m < bound`, it suffices to verify
  `far` at every `d < bound` whose ceiling rational `approx M u d` equals a
  rational convergent `(of (u/M : ℚ)).convs n`.

## The finite check — now discharged (`R20Keystone.lean` / `R20BandSweep.lean`)

The keystone and decidable sweep are completed in downstream files:

1. `R20Keystone.lean` bridges Mathlib's rational convergents to a fast `Nat`
   Euclidean continuant recurrence: `convs_den_eq` proves the reduced
   denominator `((of (u/M:ℚ)).convs n).den = (denI u M n).natAbs` (integer
   continuants, coprimality from `SimpContFract.of … |>.determinant`, then
   `Rat.den_div_eq_of_coprime`); `index_bound` gives `n < 78`
   (`Nat.fib 79 > 2^53`); `hcheck_of_check`/`farAll_of_sweep` discharge
   `hcheck` via the computable list `convDenoms` (single-pass `fastDenoms`).
2. `R20BandSweep.lean` runs the per-`(q,k)` sweep over the 2046 binary64
   exponents in both bands by ordinary kernel `decide` (no `native_decide`),
   then assembles — together with the elementary small-exponent closers —
   `residueR20Cond_band{1,2}_binary64`: an *unconditional* `residueR20Cond`
   for every binary64 input, with no `B < 2^64` accuracy guard.

Everything in the present file is the *sound reduction* feeding that sweep.
-/

namespace PP.Numeric.Schubfach.R20Sweep

open GenContFract

/-- The `contsAux` of the cast continued fraction `of (↑q : ℝ)` equals the
cast of `(of q).contsAux`. -/
theorem contsAux_coe_rat (q : ℚ) (n : ℕ) :
    (GenContFract.of ((q : ℝ))).contsAux n
      = ((GenContFract.of q).contsAux n).map (Rat.cast : ℚ → ℝ) := by
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    rcases n with _ | _ | n
    · simp [contsAux, Pair.map]
    · simp [contsAux, GenContFract.of, IntFractPair.seq1, IntFractPair.of, Pair.map,
        Rat.floor_cast]
    · -- n+2 case: use the recurrence on both sides
      have hs := GenContFract.coe_of_s_get?_rat_eq (K := ℝ) (q := q) (v := (q : ℝ)) rfl n
      rcases hsq : (GenContFract.of q).s.get? n with _ | gp
      · -- terminated at n: both stable
        have hstableR : (GenContFract.of (q:ℝ)).contsAux (n + 2)
            = (GenContFract.of (q:ℝ)).contsAux (n + 1) :=
          contsAux_stable_of_terminated (n + 1).le_succ
            (show (GenContFract.of (q:ℝ)).s.get? n = none by rw [← hs, hsq]; rfl)
        have hstableQ : (GenContFract.of q).contsAux (n + 2)
            = (GenContFract.of q).contsAux (n + 1) :=
          contsAux_stable_of_terminated (n + 1).le_succ hsq
        rw [hstableR, hstableQ, IH (n + 1) (by omega)]
      · -- some gp: use recurrence on both sides
        have hsR : (GenContFract.of (q:ℝ)).s.get? n = some (gp.map (Rat.cast : ℚ → ℝ)) := by
          rw [← hs, hsq]; rfl
        have hrecR := contsAux_recurrence hsR (rfl) (rfl)
        have hrecQ := contsAux_recurrence hsq (rfl) (rfl)
        rw [hrecR, hrecQ]
        have hppred := IH n (by omega)
        have hpred := IH (n + 1) (by omega)
        rw [hppred, hpred]
        cases hgp : gp
        simp only [Pair.map]; push_cast; ring_nf

/-- ℝ→ℚ bridge for convergents: the `n`th convergent of `(↑q : ℝ)`'s
continued fraction is the coercion of the `n`th convergent of `q`'s. -/
theorem convs_coe_rat (q : ℚ) (n : ℕ) :
    (GenContFract.of ((q : ℝ))).convs n = ((GenContFract.of q).convs n : ℝ) := by
  have hconts : (GenContFract.of (q:ℝ)).conts n
      = ((GenContFract.of q).conts n).map (Rat.cast : ℚ → ℝ) := by
    simp only [conts, Stream'.tail]
    exact contsAux_coe_rat q (n + 1)
  rw [conv_eq_num_div_den, conv_eq_num_div_den, num_eq_conts_a, num_eq_conts_a,
    den_eq_conts_b, den_eq_conts_b, hconts, Pair.map]
  push_cast
  ring

open PP.Numeric.Schubfach (farFromMultipleBelow)
open PP.Numeric.Schubfach.R20Legendre (approx ceilNum gap ceilNum_mul_eq)

/-- The ceiling numerator dominates `m·u/M` and is the *least* such integer:
`m·u ≤ ceilNum·M` and `ceilNum·M < m·u + M` (when not divisible). -/
theorem ceilNum_bounds (M u m : Nat) (hM : 0 < M) (hnd : (m * u) % M ≠ 0) :
    m * u ≤ ceilNum M u m * M ∧ ceilNum M u m * M < m * u + M := by
  have h := ceilNum_mul_eq M u m hM hnd
  have hgap_pos : 1 ≤ gap M u m := by
    unfold gap; have : (m * u) % M < M := Nat.mod_lt _ hM; omega
  have hgap_le : gap M u m ≤ M := by unfold gap; omega
  -- gap = M iff residue 0; here residue ≠ 0 so gap < M
  have hgap_lt : gap M u m < M := by
    unfold gap
    have : 0 < (m * u) % M := Nat.pos_of_ne_zero hnd
    have : (m * u) % M < M := Nat.mod_lt _ hM
    omega
  rw [h]; omega

/-- **Reduced-denominator ceiling stability.**  Let `c = approx M u m` with
reduced denominator `d = c.den`.  When `m·u` is not a multiple of `M`, the
ceiling rational at `d` equals `c` again: `approx M u d = approx M u m`.
This is the key "the reduced denominator is itself a ceiling fixed point"
fact, requiring no smallness on the gap — only non-divisibility. -/
theorem approx_den_fixed
    (M u m : Nat) (hM : 0 < M) (hm : 0 < m) (hnd : (m * u) % M ≠ 0) :
    approx M u ((approx M u m).den) = approx M u m := by
  set c := approx M u m with hc
  set d := c.den with hd_def
  have hd_pos : 0 < d := c.pos
  have hd_dvd : (d : Int) ∣ (m : Int) := by
    have hden := Rat.den_dvd (ceilNum M u m : Int) (m : Int)
    have heq : ((ceilNum M u m : ℚ) / (m : ℚ)) = Rat.divInt (ceilNum M u m) (m : Int) := by
      rw [Rat.divInt_eq_div]; push_cast; ring
    have : (c.den : Int) ∣ (m : Int) := by
      have : c = Rat.divInt (ceilNum M u m) (m : Int) := by rw [hc]; unfold approx; exact heq
      rw [this]; exact hden
    rw [hd_def]; exact this
  have hd_le_m : d ≤ m := by
    have hmpos : (0 : Int) < (m : Int) := by exact_mod_cast hm
    have := Int.le_of_dvd hmpos hd_dvd; exact_mod_cast this
  -- c = num/den, num = c.num, den = d
  have hc_eq : c = (c.num : ℚ) / (d : ℚ) := by
    rw [hd_def]; exact (Rat.num_div_den c).symm
  -- (A): u·d ≤ c.num·M  (from c ≥ u/M)
  -- (B): c.num·M < u·d + M  (from closeness)
  obtain ⟨hcl, hcu⟩ := ceilNum_bounds M u m hM hnd
  have hMr : (0:ℚ) < (M:ℚ) := by exact_mod_cast hM
  have hmr : (0:ℚ) < (m:ℚ) := by exact_mod_cast hm
  have hdr : (0:ℚ) < (d:ℚ) := by exact_mod_cast hd_pos
  -- c value as ceilNum/m
  have hcval : c = (ceilNum M u m : ℚ) / (m : ℚ) := by rw [hc]; unfold approx; ring
  -- num·m = ceilNum·d   (cross multiply c = num/d = ceilNum/m)
  have hcross : (c.num : ℚ) * (m : ℚ) = (ceilNum M u m : ℚ) * (d : ℚ) := by
    have h1 : (c.num : ℚ) / (d:ℚ) = (ceilNum M u m : ℚ) / (m:ℚ) := by rw [← hc_eq, hcval]
    field_simp at h1; linarith [h1]
  have hcrossZ : c.num * (m : Int) = (ceilNum M u m : Int) * (d : Int) := by
    have : ((c.num * (m:Int) : Int) : ℚ) = (((ceilNum M u m : Int) * (d:Int)) : ℚ) := by
      push_cast; linarith [hcross]
    exact_mod_cast this
  -- (A): u·d ≤ c.num·M
  have hA : (u : Int) * (d : Int) ≤ c.num * (M : Int) := by
    -- from ceilNum·M ≥ m·u and num·m = ceilNum·d
    have hclZ : (m : Int) * (u:Int) ≤ (ceilNum M u m : Int) * (M:Int) := by exact_mod_cast hcl
    have hmZ : (0:Int) < (m:Int) := by exact_mod_cast hm
    -- multiply both sides appropriately: num·M·m = ceilNum·d·M ≥ m·u·d
    have step : c.num * (M:Int) * (m:Int) = (ceilNum M u m : Int) * (M:Int) * (d:Int) := by
      rw [show c.num * (M:Int) * (m:Int) = (c.num * (m:Int)) * (M:Int) by ring, hcrossZ]; ring
    nlinarith [step, hclZ, hmZ, Int.ofNat_le.mpr (Nat.zero_le d), sq_nonneg ((d:Int))]
  -- (B): c.num·M < u·d + M
  have hB : c.num * (M:Int) < (u:Int) * (d:Int) + (M:Int) := by
    have hcuZ : (ceilNum M u m : Int) * (M:Int) < (m:Int) * (u:Int) + (M:Int) := by
      exact_mod_cast hcu
    have hmZ : (0:Int) < (m:Int) := by exact_mod_cast hm
    have hdleZ : (d:Int) ≤ (m:Int) := by exact_mod_cast hd_le_m
    -- num·M·m = ceilNum·d·M < (m·u + M)·d = m·u·d + M·d ≤ m·u·d + M·m
    have step : c.num * (M:Int) * (m:Int) = (ceilNum M u m : Int) * (M:Int) * (d:Int) := by
      rw [show c.num * (M:Int) * (m:Int) = (c.num * (m:Int)) * (M:Int) by ring, hcrossZ]; ring
    nlinarith [step, hcuZ, hmZ, hdleZ]
  -- Now ceilNum M u d = c.num (as integers), via ceiling uniqueness
  have hndd : (d * u) % M ≠ 0 := by
    -- m = d·j ⟹ m·u = (d·u)·j; if d·u ≡ 0 mod M then m·u ≡ 0, contradicting hnd
    intro h0
    obtain ⟨j, hj⟩ := (Int.natCast_dvd_natCast.mp hd_dvd)
    apply hnd
    have hmu : m * u = (d * u) * j := by rw [hj]; ring
    rw [hmu, Nat.mul_mod, h0, Nat.zero_mul, Nat.zero_mod]
  have hdbounds := ceilNum_bounds M u d hM hndd
  -- ceilNum M u d · M ∈ [d·u, d·u + M); c.num·M ∈ [u·d, u·d+M); both least integer ≥ du/M
  have hceilZ : (ceilNum M u d : Int) = c.num := by
    have h1 : (d:Int) * (u:Int) ≤ (ceilNum M u d : Int) * (M:Int) := by
      have := hdbounds.1; exact_mod_cast this
    have h2 : (ceilNum M u d : Int) * (M:Int) < (d:Int) * (u:Int) + (M:Int) := by
      have := hdbounds.2; exact_mod_cast this
    have hMZ : (0:Int) < (M:Int) := by exact_mod_cast hM
    -- du ≤ ceilNum·M < du+M  and  du ≤ num·M < du+M  ⟹ ceilNum = num
    have hAud : (d:Int)*(u:Int) ≤ c.num * (M:Int) := by linarith [hA, mul_comm (u:Int) (d:Int)]
    have hBud : c.num * (M:Int) < (d:Int)*(u:Int) + (M:Int) := by
      have : (u:Int)*(d:Int) = (d:Int)*(u:Int) := by ring
      linarith [hB, this]
    nlinarith [h1, h2, hAud, hBud, hMZ]
  -- approx M u d = ceilNum(d)/d = c.num/d = c
  show (ceilNum M u d : ℚ) / (d : ℚ) = c
  rw [hc_eq, ← hceilZ]
  push_cast; ring

/-- **Gap multiplicativity under a shared ceiling rational.**  If `d ∣ m`,
both ceiling rationals coincide (`approx M u m = approx M u d`), and neither
`m·u` nor `d·u` is a multiple of `M`, then the absolute gaps scale:
`gap M u m = (m / d) * gap M u d`. -/
theorem gap_mul_of_approx_eq
    (M u m d : Nat) (hM : 0 < M) (hd : 0 < d) (hdvd : d ∣ m)
    (happrox : approx M u m = approx M u d)
    (hndm : (m * u) % M ≠ 0) (hndd : (d * u) % M ≠ 0) :
    gap M u m = (m / d) * gap M u d := by
  obtain ⟨j, rfl⟩ := hdvd
  have hj : 0 < j := by
    rcases Nat.eq_zero_or_pos j with h | h
    · subst h; simp at hndm
    · exact h
  -- ceilNum (d*j) = j * ceilNum d, from approx equality
  have hce : ceilNum M u (d * j) = ceilNum M u d * j := by
    -- approx equality: ceilNum(dj)/(dj) = ceilNum(d)/d  ⟹ ceilNum(dj)*d = ceilNum(d)*(dj)
    unfold approx at happrox
    have hdr : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
    have hdjr : ((d * j : Nat) : ℚ) ≠ 0 := by
      push_cast; exact mul_ne_zero hdr (by exact_mod_cast hj.ne')
    rw [div_eq_div_iff hdjr hdr] at happrox
    have : (ceilNum M u (d * j) : ℚ) * d = (ceilNum M u d : ℚ) * (d * j) := by
      push_cast at happrox ⊢; linarith [happrox]
    have hnat : ceilNum M u (d * j) * d = ceilNum M u d * (d * j) := by
      exact_mod_cast this
    have hdne : d ≠ 0 := hd.ne'
    have : ceilNum M u (d * j) * d = (ceilNum M u d * j) * d := by
      rw [hnat]; ring
    exact Nat.eq_of_mul_eq_mul_right hd this
  -- gap (d*j) = M*ceilNum(dj) - (dj)*u = j*(M*ceilNum d - d*u) = j*gap d
  have h1 := ceilNum_mul_eq M u (d * j) hM hndm
  have h2 := ceilNum_mul_eq M u d hM hndd
  rw [hce] at h1
  -- h1 : ceilNum M u d * j * M = d * j * u + gap M u (d*j)
  -- h2 : ceilNum M u d * M = d * u + gap M u d
  have hgapd_le : gap M u d ≤ M := by unfold gap; omega
  have : gap M u (d * j) = j * gap M u d := by nlinarith [h1, h2]
  rw [this]
  rw [Nat.mul_div_cancel_left j hd, Nat.mul_comm]

/-- **Monotone transfer of `farFromMultipleBelow` along divisors.**  If the
reduced ceiling denominator `d` (a divisor of `m` with matching ceiling
rational) is far, then `m` is far.  This is the sound version of the spike's
"every bad `m` is a convergent denominator": we only need to check `far` at
the convergent denominators, and multiples inherit it. -/
theorem far_of_far_at_den
    (M u m d a : Nat) (hM : 0 < M) (hd : 0 < d) (hdvd : d ∣ m) (hm : 0 < m)
    (happrox : approx M u m = approx M u d)
    (hFarD : farFromMultipleBelow M u d a) :
    farFromMultipleBelow M u m a := by
  by_cases hndm : (m * u) % M = 0
  · -- m·u multiple of M ⟹ gap = M, trivially far
    unfold farFromMultipleBelow
    rw [hndm, Nat.sub_zero]
    have : M ≤ M * 2 ^ a := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos a)
    omega
  · by_cases hndd : (d * u) % M = 0
    · -- d·u multiple but m·u not: impossible since d ∣ m
      obtain ⟨j, rfl⟩ := hdvd
      have : M ∣ d * u := Nat.dvd_of_mod_eq_zero hndd
      have : M ∣ (d * j) * u := by
        have : (d * j) * u = (d * u) * j := by ring
        rw [this]; exact Dvd.dvd.mul_right ‹M ∣ d * u› j
      exact absurd (Nat.mod_eq_zero_of_dvd this) hndm
    · have hgapmul := gap_mul_of_approx_eq M u m d hM hd hdvd happrox hndm hndd
      unfold farFromMultipleBelow at hFarD ⊢
      -- gap M u m = (m/d) * gap M u d ≥ gap M u d (since m/d ≥ 1)
      have hjpos : 1 ≤ m / d := by
        obtain ⟨j, rfl⟩ := hdvd
        rw [Nat.mul_div_cancel_left _ hd]
        rcases Nat.eq_zero_or_pos j with h | h
        · simp [h] at hm
        · exact h
      have hgd : gap M u d = M - (d * u) % M := rfl
      have hgm : gap M u m = M - (m * u) % M := rfl
      rw [hgm] at hgapmul
      calc M ≤ (M - (d * u) % M) * 2 ^ a := hFarD
        _ = gap M u d * 2 ^ a := by rw [hgd]
        _ ≤ (m / d) * gap M u d * 2 ^ a := by
              apply Nat.mul_le_mul_right
              exact Nat.le_mul_of_pos_left _ hjpos
        _ = (M - (m * u) % M) * 2 ^ a := by rw [← hgapmul]

open PP.Numeric.Schubfach.R20Legendre (bad_is_convergent)

/-- **Convergent-denominator reduction (over ℚ).**  To prove
`farFromMultipleBelow M u m a` for every `m` in range, it suffices to check
`far` at every `d` whose ceiling rational `approx M u d` is a *rational*
convergent of `u/M` (the computable enumeration).  Soundness:

* a bad `m` makes `approx M u m` a real convergent (`bad_is_convergent`);
* via `convs_coe_rat`, that real convergent is the cast of the rational
  convergent `(of (u/M:ℚ)).convs n`;
* the reduced denominator `d = (approx M u m).den` satisfies
  `approx M u d = approx M u m` (`approx_den_fixed`), so `d`'s ceiling
  rational is the *same* rational convergent — `d` is in the swept set;
* `d ∣ m` and `far M u d a` ⟹ `far M u m a` (`far_of_far_at_den`),
  contradicting badness. -/
theorem far_of_far_at_rat_convergents
    (M u a bound : Nat) (hM : 0 < M) (hba : 2 * bound ≤ 2 ^ a)
    (hcheck : ∀ d, 0 < d → d < bound →
      (∃ n, (GenContFract.of ((u : ℚ) / M)).convs n = approx M u d) →
      farFromMultipleBelow M u d a) :
    ∀ m, 0 < m → m < bound → farFromMultipleBelow M u m a := by
  intro m hm hmb
  have hsmall : 2 * m < 2 ^ a := by omega
  by_contra hbad
  -- m is bad ⟹ approx M u m is a real convergent
  obtain ⟨n, hn⟩ := bad_is_convergent M u m a hM hm hbad hsmall
  -- divisible case: m·u % M = 0 ⟹ far trivially, contradiction
  by_cases hndm : (m * u) % M = 0
  · apply hbad
    unfold farFromMultipleBelow
    rw [hndm, Nat.sub_zero]
    have : M ≤ M * 2 ^ a := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos a)
    omega
  · -- cast bridge: (of (u/M:ℚ)).convs n = approx M u m  (over ℚ)
    set d := (approx M u m).den with hd_def
    have hd_pos : 0 < d := (approx M u m).pos
    -- The real convergent equals the cast of the rational convergent.
    have hcastQ : ((u : ℝ) / M) = (((u : ℚ) / M : ℚ) : ℝ) := by push_cast; ring
    rw [hcastQ, convs_coe_rat] at hn
    -- hn : ↑((of (u/M:ℚ)).convs n) = ↑(approx M u m)  in ℝ
    have hnQ : (GenContFract.of ((u : ℚ) / M)).convs n = approx M u m := by
      have : (((GenContFract.of ((u:ℚ)/M)).convs n : ℚ) : ℝ) = ((approx M u m : ℚ) : ℝ) := hn
      exact_mod_cast this
    -- d's approx equals m's approx, which is the rational convergent
    have hfix : approx M u d = approx M u m := approx_den_fixed M u m hM hm hndm
    have hd_conv : (GenContFract.of ((u : ℚ) / M)).convs n = approx M u d := by
      rw [hfix]; exact hnQ
    -- d ∣ m
    have hd_dvd : d ∣ m := by
      have hden := Rat.den_dvd (ceilNum M u m : Int) (m : Int)
      have heq : ((ceilNum M u m : ℚ) / (m : ℚ)) = Rat.divInt (ceilNum M u m) (m : Int) := by
        rw [Rat.divInt_eq_div]; push_cast; ring
      have hZ : (d : Int) ∣ (m : Int) := by
        have hc' : approx M u m = Rat.divInt (ceilNum M u m) (m : Int) := by
          unfold approx; exact heq
        rw [hd_def, hc']; exact hden
      exact Int.natCast_dvd_natCast.mp hZ
    have hd_lt : d < bound := lt_of_le_of_lt (Nat.le_of_dvd hm hd_dvd) hmb
    -- so d is in the swept set: far M u d a
    have hFarD : farFromMultipleBelow M u d a := hcheck d hd_pos hd_lt ⟨n, hd_conv⟩
    -- far_of_far_at_den ⟹ far M u m a, contradiction
    exact hbad (far_of_far_at_den M u m d a hM hd_pos hd_dvd hm hfix.symm hFarD)

end PP.Numeric.Schubfach.R20Sweep

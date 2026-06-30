/- v11 groundwork — 192-bit triple arithmetic + the comparison flip.

   The Giulietti-style dataflow (Schubfach paper §9.8–9.10) multiplies
   the BOUNDARY values by an inverse-power-of-ten estimate once per
   kernel run, instead of multiplying each digit CANDIDATE as v8/v9 do.
   In our verified stack that is a role flip of the existing
   `cmpScaledMixed` comparator:

       cmpScaledMixed a q b k = - cmpScaledMixed b (-q) a (-k)

   so the candidate side becomes the cheap shift-triple and one 192-bit
   product `P = 4m·g'` (with `g'` the `pow10Table128` entry at `-k`)
   serves all boundary comparisons via 192-bit add/sub:

       (4m-2)·g' = P - 2g'    (4m-1)·g' = P - g'    (4m+2)·g' = P + 2g'

   This file provides the triple arithmetic with exact `toNat`
   characterisations and the flip identity; the kernel and its
   some⇒spec proof build on top. -/

import Srtfp.Numeric.Schubfach.Perf.KernelV10

namespace PP.Numeric.Schubfach

/-! ## 192-bit triple add/sub -/

/-- Carry-chain addition of two 192-bit triples (mod `2^192`). -/
@[inline]
def add192_192 (aHi aMid aLo bHi bMid bLo : UInt64) :
    UInt64 × UInt64 × UInt64 :=
  let lo := aLo + bLo
  let c1 : UInt64 := if lo < aLo then 1 else 0
  let mid := aMid + bMid + c1
  let c2 : UInt64 :=
    if aMid + bMid < aMid then 1
    else if mid < aMid + bMid then 1 else 0
  (aHi + bHi + c2, mid, lo)

/-- Borrow-chain subtraction of two 192-bit triples (assuming `b ≤ a`). -/
@[inline]
def sub192_192 (aHi aMid aLo bHi bMid bLo : UInt64) :
    UInt64 × UInt64 × UInt64 :=
  let lo := aLo - bLo
  let b1 : UInt64 := if aLo < bLo then 1 else 0
  let mid := aMid - bMid - b1
  let b2 : UInt64 :=
    if aMid < bMid then 1
    else if aMid - bMid < b1 then 1 else 0
  (aHi - bHi - b2, mid, lo)

set_option maxHeartbeats 800000 in
theorem add192_192_toNat (aHi aMid aLo bHi bMid bLo : UInt64)
    (hno : triple192Nat aHi aMid aLo + triple192Nat bHi bMid bLo < 2 ^ 192) :
    triple192Nat (add192_192 aHi aMid aLo bHi bMid bLo).1
      (add192_192 aHi aMid aLo bHi bMid bLo).2.1
      (add192_192 aHi aMid aLo bHi bMid bLo).2.2
      = triple192Nat aHi aMid aLo + triple192Nat bHi bMid bLo := by
  unfold add192_192 triple192Nat
  unfold triple192Nat at hno
  simp only
  have haH := aHi.toNat_lt; have haM := aMid.toNat_lt; have haL := aLo.toNat_lt
  have hbH := bHi.toNat_lt; have hbM := bMid.toNat_lt; have hbL := bLo.toNat_lt
  have h1n : (1 : UInt64).toNat = 1 := rfl
  have h0n : (0 : UInt64).toNat = 0 := rfl
  by_cases c1 : (aLo + bLo) < aLo
  · have hc1 : aLo.toNat + bLo.toNat ≥ 2 ^ 64 := (add_carry_iff aLo bLo).mp c1
    rw [if_pos c1]
    by_cases c2a : (aMid + bMid) < aMid
    · have hc2a : aMid.toNat + bMid.toNat ≥ 2 ^ 64 := (add_carry_iff aMid bMid).mp c2a
      rw [if_pos c2a]
      simp only [UInt64.toNat_add, h1n]
      omega
    · have hc2a : ¬ aMid.toNat + bMid.toNat ≥ 2 ^ 64 := fun h => c2a ((add_carry_iff aMid bMid).mpr h)
      rw [if_neg c2a]
      by_cases c2b : (aMid + bMid + 1) < aMid + bMid
      · have hc2b : (aMid + bMid).toNat + (1 : UInt64).toNat ≥ 2 ^ 64 :=
          (add_carry_iff (aMid + bMid) 1).mp c2b
        rw [if_pos c2b]
        simp only [UInt64.toNat_add, h1n] at hc2b ⊢
        omega
      · have hc2b : ¬ (aMid + bMid).toNat + (1 : UInt64).toNat ≥ 2 ^ 64 :=
          fun h => c2b ((add_carry_iff (aMid + bMid) 1).mpr h)
        rw [if_neg c2b]
        simp only [UInt64.toNat_add, h1n, h0n] at hc2b ⊢
        omega
  · have hc1 : ¬ aLo.toNat + bLo.toNat ≥ 2 ^ 64 := fun h => c1 ((add_carry_iff aLo bLo).mpr h)
    rw [if_neg c1]
    by_cases c2a : (aMid + bMid) < aMid
    · have hc2a : aMid.toNat + bMid.toNat ≥ 2 ^ 64 := (add_carry_iff aMid bMid).mp c2a
      rw [if_pos c2a]
      simp only [UInt64.toNat_add, h1n, h0n]
      omega
    · have hc2a : ¬ aMid.toNat + bMid.toNat ≥ 2 ^ 64 := fun h => c2a ((add_carry_iff aMid bMid).mpr h)
      rw [if_neg c2a]
      by_cases c2b : (aMid + bMid + 0) < aMid + bMid
      · have hc2b : (aMid + bMid).toNat + (0 : UInt64).toNat ≥ 2 ^ 64 :=
          (add_carry_iff (aMid + bMid) 0).mp c2b
        rw [if_pos c2b]
        simp only [UInt64.toNat_add, h1n, h0n] at hc2b ⊢
        omega
      · have hc2b : ¬ (aMid + bMid).toNat + (0 : UInt64).toNat ≥ 2 ^ 64 :=
          fun h => c2b ((add_carry_iff (aMid + bMid) 0).mpr h)
        rw [if_neg c2b]
        simp only [UInt64.toNat_add, h0n] at hc2b ⊢
        omega

set_option maxHeartbeats 800000 in
theorem sub192_192_toNat (aHi aMid aLo bHi bMid bLo : UInt64)
    (hle : triple192Nat bHi bMid bLo ≤ triple192Nat aHi aMid aLo) :
    triple192Nat (sub192_192 aHi aMid aLo bHi bMid bLo).1
      (sub192_192 aHi aMid aLo bHi bMid bLo).2.1
      (sub192_192 aHi aMid aLo bHi bMid bLo).2.2
      = triple192Nat aHi aMid aLo - triple192Nat bHi bMid bLo := by
  unfold sub192_192 triple192Nat
  unfold triple192Nat at hle
  simp only
  have haH := aHi.toNat_lt; have haM := aMid.toNat_lt; have haL := aLo.toNat_lt
  have hbH := bHi.toNat_lt; have hbM := bMid.toNat_lt; have hbL := bLo.toNat_lt
  have h1n : (1 : UInt64).toNat = 1 := rfl
  have h0n : (0 : UInt64).toNat = 0 := rfl
  have hsub : ∀ (x y : UInt64), (x - y).toNat = (2 ^ 64 - y.toNat + x.toNat) % 2 ^ 64 :=
    fun x y => UInt64.toNat_sub x y
  have hltN : ∀ (x y : UInt64), (x < y) ↔ x.toNat < y.toNat := by
    intro x y; exact UInt64.lt_iff_toNat_lt
  by_cases b1 : aLo < bLo
  · have hb1 : aLo.toNat < bLo.toNat := (hltN _ _).mp b1
    rw [if_pos b1]
    by_cases b2a : aMid < bMid
    · have hb2a : aMid.toNat < bMid.toNat := (hltN _ _).mp b2a
      rw [if_pos b2a]
      simp only [hsub, h1n]
      omega
    · have hb2a : ¬ aMid.toNat < bMid.toNat := fun h => b2a ((hltN _ _).mpr h)
      rw [if_neg b2a]
      by_cases b2b : aMid - bMid < (1 : UInt64)
      · have hb2b : (aMid - bMid).toNat < (1 : UInt64).toNat := (hltN _ _).mp b2b
        rw [if_pos b2b]
        simp only [hsub, h1n] at hb2b ⊢
        omega
      · have hb2b : ¬ (aMid - bMid).toNat < (1 : UInt64).toNat :=
          fun h => b2b ((hltN _ _).mpr h)
        rw [if_neg b2b]
        simp only [hsub, h1n, h0n] at hb2b ⊢
        omega
  · have hb1 : ¬ aLo.toNat < bLo.toNat := fun h => b1 ((hltN _ _).mpr h)
    rw [if_neg b1]
    by_cases b2a : aMid < bMid
    · have hb2a : aMid.toNat < bMid.toNat := (hltN _ _).mp b2a
      rw [if_pos b2a]
      simp only [hsub, h1n, h0n]
      omega
    · have hb2a : ¬ aMid.toNat < bMid.toNat := fun h => b2a ((hltN _ _).mpr h)
      rw [if_neg b2a]
      by_cases b2b : aMid - bMid < (0 : UInt64)
      · have hb2b : (aMid - bMid).toNat < (0 : UInt64).toNat := (hltN _ _).mp b2b
        rw [if_pos b2b]
        simp only [hsub, h1n, h0n] at hb2b ⊢
        omega
      · rw [if_neg b2b]
        simp only [hsub, h0n]
        omega

/-! ## The comparison flip

`cmpScaledMixed a q b k` decides `a·2^q ⋚ b·10^k`. Negating both
exponents swaps the roles of the two sides, so the verdict negates.
This lets the verified u64 comparator run with the boundary product on
the *candidate* side (one wide multiply) and the cheap shift-triples on
the *boundary* side. -/

private theorem cmp3_flip (x y : Int) :
    (if x < y then (-1 : Int) else if x = y then 0 else 1)
      = -(if y < x then (-1 : Int) else if y = x then 0 else 1) := by
  rcases lt_trichotomy x y with h | h | h
  · rw [if_pos h, if_neg (show ¬ y < x by omega), if_neg (show ¬ y = x by omega)]
  · rw [if_neg (show ¬ x < y by omega), if_pos h,
        if_neg (show ¬ y < x by omega), if_pos (show y = x by omega)]
    omega
  · rw [if_neg (show ¬ x < y by omega), if_neg (show ¬ x = y by omega),
        if_pos (show y < x by omega)]
    omega

private theorem cmp3_flip' (x y x' y' : Int) (hx : x' = x) (hy : y' = y) :
    (if x < y then (-1 : Int) else if x = y then 0 else 1)
      = -(if y' < x' then (-1 : Int) else if y' = x' then 0 else 1) := by
  subst hx; subst hy; exact cmp3_flip _ _

private theorem negPos_eq (q : Int) :
    (if -q ≥ 0 then (-q).toNat else 0) = (if q < 0 then (-q).toNat else 0) := by
  rcases lt_trichotomy q 0 with h | h | h
  · rw [if_pos (show -q ≥ 0 by omega), if_pos h]
  · subst h; simp
  · rw [if_neg (show ¬ -q ≥ 0 by omega), if_neg (show ¬ q < 0 by omega)]

private theorem negNeg_eq (q : Int) :
    (if -q < 0 then (- -q).toNat else 0) = (if q ≥ 0 then q.toNat else 0) := by
  rw [neg_neg]
  rcases lt_trichotomy q 0 with h | h | h
  · rw [if_neg (show ¬ -q < 0 by omega), if_neg (show ¬ q ≥ 0 by omega)]
  · subst h; simp
  · rw [if_pos (show -q < 0 by omega), if_pos (show q ≥ 0 by omega)]

theorem cmpScaledMixed_flip (a q b k : Int) :
    cmpScaledMixed a q b k = - cmpScaledMixed b (-q) a (-k) := by
  unfold cmpScaledMixed
  simp only [negPos_eq, negNeg_eq]
  exact cmp3_flip' _ _ _ _ (mul_right_comm a _ _) (mul_right_comm b _ _)

/-! ## Triple identification

`triple192Nat` is injective, so a 192-bit triple derived by add/sub
from the product `P = 4m·g` is componentwise equal to the triple the
4-multiply construction inside `cmpScaledMixed_u64` would produce for
the same boundary value. -/

theorem triple192Nat_inj (h1 m1 l1 h2 m2 l2 : UInt64)
    (h : triple192Nat h1 m1 l1 = triple192Nat h2 m2 l2) :
    h1 = h2 ∧ m1 = m2 ∧ l1 = l2 := by
  unfold triple192Nat at h
  have b1 := h1.toNat_lt; have b2 := m1.toNat_lt; have b3 := l1.toNat_lt
  have b4 := h2.toNat_lt; have b5 := m2.toNat_lt; have b6 := l2.toNat_lt
  refine ⟨UInt64.toNat_inj.mp ?_, UInt64.toNat_inj.mp ?_, UInt64.toNat_inj.mp ?_⟩
  all_goals omega

/-- The 4-multiply construction triple for `(bU, gHi:gLo)` equals any
    triple whose `triple192Nat` value is the exact product `bU·G`
    (no wraparound: `bU·G < 2^192`). -/
theorem construction_triple_eq (bU gHi gLo rHi rMid rLo : UInt64)
    (hval : triple192Nat rHi rMid rLo
      = bU.toNat * (gHi.toNat * 2 ^ 64 + gLo.toNat))
    (hlt : bU.toNat * (gHi.toNat * 2 ^ 64 + gLo.toNat) < 2 ^ 192) :
    (mulHi64 bU gHi + (if bU * gHi + mulHi64 bU gLo < bU * gHi then 1 else 0)) = rHi
    ∧ (bU * gHi + mulHi64 bU gLo) = rMid ∧ (bU * gLo) = rLo := by
  have h := mul192_b_g_toNat bU gHi gLo
  simp only [] at h
  rw [Nat.mod_eq_of_lt hlt] at h
  exact triple192Nat_inj _ _ _ _ _ _ (h.trans hval.symm)

/-- `cmpVerdict_u64_inner` only produces `1`, `-1`, or `0`. -/
theorem cmpVerdict_u64_inner_range
    (l_hi l_mid l_lo r_hi r_mid r_lo bU : UInt64) :
    cmpVerdict_u64_inner l_hi l_mid l_lo r_hi r_mid r_lo bU = 1
    ∨ cmpVerdict_u64_inner l_hi l_mid l_lo r_hi r_mid r_lo bU = -1
    ∨ cmpVerdict_u64_inner l_hi l_mid l_lo r_hi r_mid r_lo bU = 0 := by
  unfold cmpVerdict_u64_inner
  by_cases hgt : gt192 l_hi l_mid l_lo r_hi r_mid r_lo = true
  · simp [hgt]
  · simp only [hgt, if_false, Bool.false_eq_true]
    generalize (add192_64 l_hi l_mid l_lo bU) = LpB
    obtain ⟨lpb_hi, lpb_mid, lpb_lo⟩ := LpB
    by_cases hle : le192 lpb_hi lpb_mid lpb_lo r_hi r_mid r_lo = true
    · simp [hle]
    · simp [hle]

/-! ## Flipped biased-window bridges (constants 5134/5202/5070)

The flipped comparisons run at shift `w = h' - q ∈ [64, 132]`; the
runtime guard tests the biased `uB' = (h'+2048+4096) - (q+1074)
= h' - q + 5070` against `[5134, 5202]`. Mirrors `tA_lt`/`tA_ge`/
`tA_val` (window `[188, 256)` at bias 5070). -/

theorem wB_lt (q h : Int) (h1 : ¬ q < -1074) (h2 : ¬ q > 971)
    (hh : -2048 ≤ h ∧ h < 2048) :
    (((UInt64.ofNat (h + 2048).toNat + 4096) - UInt64.ofNat (q + 1074).toNat)
        < (5134 : UInt64)) = (-q + h < 64) := by
  have ht := toNat_tA q h h1 h2 hh
  rw [show (((UInt64.ofNat (h + 2048).toNat + 4096) - UInt64.ofNat (q + 1074).toNat)
        < (5134 : UInt64)) ↔ _ from UInt64.lt_iff_toNat_lt,
      show ((5134 : UInt64)).toNat = 5134 from rfl]
  exact propext (by omega)

theorem wB_gt (q h : Int) (h1 : ¬ q < -1074) (h2 : ¬ q > 971)
    (hh : -2048 ≤ h ∧ h < 2048) :
    (((UInt64.ofNat (h + 2048).toNat + 4096) - UInt64.ofNat (q + 1074).toNat)
        > (5202 : UInt64)) = (-q + h > 132) := by
  have ht := toNat_tA q h h1 h2 hh
  rw [show (((UInt64.ofNat (h + 2048).toNat + 4096) - UInt64.ofNat (q + 1074).toNat)
        > (5202 : UInt64)) ↔ _ from UInt64.lt_iff_toNat_lt,
      show ((5202 : UInt64)).toNat = 5202 from rfl]
  exact propext (by omega)

theorem wB_val (q h : Int) (h1 : ¬ q < -1074) (h2 : ¬ q > 971)
    (hh : -2048 ≤ h ∧ h < 2048) (hlo : ¬ -q + h < 64) (hhi : ¬ -q + h > 132) :
    ((UInt64.ofNat (h + 2048).toNat + 4096) - UInt64.ofNat (q + 1074).toNat) - 5070
      = UInt64.ofNat (-q + h).toNat := by
  have ht := toNat_tA q h h1 h2 hh
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_sub_of_le _ _ (by
        rw [UInt64.le_iff_toNat_le, show ((5070 : UInt64)).toNat = 5070 from rfl]
        omega),
      show ((5070 : UInt64)).toNat = 5070 from rfl,
      UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  omega

/-- Index transfer for the flipped `k+1` table entry: exponent
    `-(k+1)` lives at biased index `647 - kB`. Mirrors `lookup192_neg`. -/
theorem lookup128_negHigh (k : Int) (hlo : ¬ k < pow10Table128_kMin)
    (hhi : ¬ k + 1 > pow10Table128_kMax) :
    pow10Lookup128 (-(k + 1))
      = pow10Table128.getD (647 - (k + 324).toNat) pow10Table128_default := by
  have hlo' : ¬ k < (-324 : Int) := hlo
  have hhi' : ¬ k + 1 > (324 : Int) := hhi
  have hidx : (-(k + 1) + 324).toNat = 647 - (k + 324).toNat := by omega
  unfold pow10Lookup128
  rw [if_neg (show ¬ (-(k + 1) < pow10Table128_kMin) from
        fun hc => absurd (show -(k + 1) < -324 from hc) (by omega)),
      hidx]

/-! ## The flipped rounding-interval test

Verdicts with the candidate (`4s` shifted by `w = -q + h'`) on the
exact side and the boundary products (`(4m-2)·g'` etc., derived from
the single product `P = 4m·g'`) on the table side. `leftOK`/`rightOK`
read off the *negated* spec comparisons (see `cmpScaledMixed_flip`):
`TRUE ⟺ cmpLf = 1 ∧ cmpRf = -1`. -/

@[inline]
def inRoundingInterval_u64_flipped_u8
    (lLHi lLMid lLLo leftU lRHi lRMid lRLo rightU : UInt64)
    (w8 sU : UInt64) : UInt8 :=
  let s4U : UInt64 := sU <<< 2
  let (cHi, cMid, cLo) := cmpScaledMixed_u64_L s4U w8
  let cmpLf := cmpVerdict_u64_inner cHi cMid cLo lLHi lLMid lLLo leftU
  if cmpLf = 0 then inRoundingInterval_u8_AMBIG
  else
    let cmpRf := cmpVerdict_u64_inner cHi cMid cLo lRHi lRMid lRLo rightU
    if cmpRf = 0 then inRoundingInterval_u8_AMBIG
    else if 0 < cmpLf && cmpRf < 0 then inRoundingInterval_u8_TRUE
    else inRoundingInterval_u8_FALSE

/-- The flipped test in `cmpScaledMixed_u64` form: when the boundary
    triples carry the exact products `leftU·G` / `rightU·G`, each
    verdict is a genuine `cmpScaledMixed_u64` call with the candidate
    on the `a` side and the boundary on the `b` (slack) side. -/
theorem inRoundingInterval_u64_flipped_u8_cmp_form
    (gHi gLo w8 sU leftU rightU : UInt64)
    (lLHi lLMid lLLo lRHi lRMid lRLo : UInt64)
    (hLv : triple192Nat lLHi lLMid lLLo
      = leftU.toNat * (gHi.toNat * 2 ^ 64 + gLo.toNat))
    (hLlt : leftU.toNat * (gHi.toNat * 2 ^ 64 + gLo.toNat) < 2 ^ 192)
    (hRv : triple192Nat lRHi lRMid lRLo
      = rightU.toNat * (gHi.toNat * 2 ^ 64 + gLo.toNat))
    (hRlt : rightU.toNat * (gHi.toNat * 2 ^ 64 + gLo.toNat) < 2 ^ 192) :
    inRoundingInterval_u64_flipped_u8 lLHi lLMid lLLo leftU lRHi lRMid lRLo rightU w8 sU
    = (let cmpLf := cmpScaledMixed_u64 gHi gLo w8 (sU <<< 2) leftU
       if cmpLf = 0 then inRoundingInterval_u8_AMBIG
       else
         let cmpRf := cmpScaledMixed_u64 gHi gLo w8 (sU <<< 2) rightU
         if cmpRf = 0 then inRoundingInterval_u8_AMBIG
         else if 0 < cmpLf && cmpRf < 0 then inRoundingInterval_u8_TRUE
         else inRoundingInterval_u8_FALSE) := by
  obtain ⟨eL1, eL2, eL3⟩ := construction_triple_eq leftU gHi gLo lLHi lLMid lLLo hLv hLlt
  obtain ⟨eR1, eR2, eR3⟩ := construction_triple_eq rightU gHi gLo lRHi lRMid lRLo hRv hRlt
  unfold inRoundingInterval_u64_flipped_u8
  simp only [cmpScaledMixed_u64_eq_cmpVerdict]
  obtain ⟨cHi, cMid, cLo⟩ := cmpScaledMixed_u64_L (sU <<< 2) w8
  simp only []
  rw [eL1, eR1, eL2, eL3, eR2, eR3]

set_option maxHeartbeats 1600000 in
/-- Bridging: a strict flipped verdict pair decides the spec
    `inRoundingInterval` at exponent `k'`, via the flip identity
    `cmpScaledMixed a q b k = -cmpScaledMixed b (-q) a (-k)`. -/
theorem inRoundingInterval_u64_flipped_u8_some_eq
    (q k' : Int) (s m : Nat) (irregular : Bool)
    (lLHi lLMid lLLo lRHi lRMid lRLo : UInt64)
    (hm_pos : m ≥ 1) (hs_pos : s ≥ 1)
    (hm_lt : m < (1 <<< 58 : Nat)) (hs_lt : s < (1 <<< 58 : Nat))
    (hk_lo : pow10Table128_kMin ≤ -k') (hk_hi : -k' ≤ pow10Table128_kMax)
    (hqh_lo : 64 ≤ -q + (pow10Lookup128 (-k')).2.2)
    (hqh_hi : -q + (pow10Lookup128 (-k')).2.2 ≤ 132)
    (hL_val : triple192Nat lLHi lLMid lLLo
      = (if irregular then 4 * m - 1 else 4 * m - 2)
          * ((pow10Lookup128 (-k')).1.toNat * 2 ^ 64 + (pow10Lookup128 (-k')).2.1.toNat))
    (hR_val : triple192Nat lRHi lRMid lRLo
      = (4 * m + 2)
          * ((pow10Lookup128 (-k')).1.toNat * 2 ^ 64 + (pow10Lookup128 (-k')).2.1.toNat))
    (hne : inRoundingInterval_u64_flipped_u8 lLHi lLMid lLLo
            (if irregular then (UInt64.ofNat m) <<< 2 - 1 else (UInt64.ofNat m) <<< 2 - 2)
            lRHi lRMid lRLo ((UInt64.ofNat m) <<< 2 + 2)
            (UInt64.ofNat (-q + (pow10Lookup128 (-k')).2.2).toNat) (UInt64.ofNat s)
          ≠ inRoundingInterval_u8_AMBIG) :
    inRoundingInterval s k' m q irregular
      = decide (inRoundingInterval_u64_flipped_u8 lLHi lLMid lLLo
            (if irregular then (UInt64.ofNat m) <<< 2 - 1 else (UInt64.ofNat m) <<< 2 - 2)
            lRHi lRMid lRLo ((UInt64.ofNat m) <<< 2 + 2)
            (UInt64.ofNat (-q + (pow10Lookup128 (-k')).2.2).toNat) (UInt64.ofNat s)
          = inRoundingInterval_u8_TRUE) := by
  -- Notation.
  set gHi : UInt64 := (pow10Lookup128 (-k')).1 with hgHi_def
  set gLo : UInt64 := (pow10Lookup128 (-k')).2.1 with hgLo_def
  set wPlusH : Int := -q + (pow10Lookup128 (-k')).2.2 with hwPlusH_def
  set w8 : UInt64 := UInt64.ofNat wPlusH.toNat with hw8_def
  set sU : UInt64 := UInt64.ofNat s with hsU_def
  set mU : UInt64 := UInt64.ofNat m with hmU_def
  -- G bound.
  have hG_lt : gHi.toNat * 2 ^ 64 + gLo.toNat < 2 ^ 128 := by
    have h1 := gHi.toNat_lt; have h2 := gLo.toNat_lt
    omega
  -- Product bounds: all boundary values ≤ 4m + 2 < 2^60.
  have hbound_lt : ∀ b : Nat, b ≤ 4 * m + 2 →
      b * (gHi.toNat * 2 ^ 64 + gLo.toNat) < 2 ^ 192 := by
    intro b hb
    have hb60 : b < 2 ^ 60 := by
      have : (1 <<< 58 : Nat) = 2 ^ 58 := by decide
      omega
    have h3 : b * (gHi.toNat * 2 ^ 64 + gLo.toNat) ≤ 2 ^ 60 * 2 ^ 128 :=
      Nat.mul_le_mul (by omega) (by omega)
    have h4 : (2 : Nat) ^ 60 * 2 ^ 128 < 2 ^ 192 := by
      rw [← pow_add]
      exact Nat.pow_lt_pow_right (by omega) (by omega)
    omega
  -- UInt64 boundary correspondences (Bridge helpers).
  have hleftU_reg : UInt64.ofNat (4 * m - 2) = mU <<< 2 - 2 := ofNat_4m_sub_2 hm_pos
  have hleftU_irr : UInt64.ofNat (4 * m - 1) = mU <<< 2 - 1 := ofNat_4m_sub_1 hm_pos
  have hrightU : UInt64.ofNat (4 * m + 2) = mU <<< 2 + 2 := ofNat_4m_add_2 m
  have hbound_toNat : ∀ b : Nat, b ≤ 4 * m + 2 → (UInt64.ofNat b).toNat = b := by
    intro b hb
    apply toNat_ofNat_bounded
    have : (1 <<< 58 : Nat) = 2 ^ 58 := by decide
    omega
  -- Int-side facts for the packed bridge.
  have hm_lt' : (m : Int) < 288230376151711744 := by
    have : (m : Int) < ((1 <<< 58 : Nat) : Int) := by exact_mod_cast hm_lt
    have heq : ((1 <<< 58 : Nat) : Int) = 288230376151711744 := by decide
    omega
  have hs_lt' : (s : Int) < 288230376151711744 := by
    have : (s : Int) < ((1 <<< 58 : Nat) : Int) := by exact_mod_cast hs_lt
    have heq : ((1 <<< 58 : Nat) : Int) = 288230376151711744 := by decide
    omega
  have h60_lit : (1 <<< 60 : Int) = 1152921504606846976 := by decide
  have hs4U_corr : UInt64.ofNat ((4 * (s : Int)).toNat) = sU <<< 2 := by
    rw [toNat_4s_eq s]; exact ofNat_4s s
  -- The strict-verdict spec bridge, parameterised over the boundary side.
  have hstrict_spec : ∀ (bI : Int) (bU : UInt64),
      0 ≤ bI → bI ≠ 0 → bI < (1 <<< 60 : Int) →
      UInt64.ofNat bI.toNat = bU →
      cmpScaledMixed_u64 gHi gLo w8 (sU <<< 2) bU ≠ 0 →
      cmpScaledMixed (4 * (s : Int)) (-q) bI (-k')
        = cmpScaledMixed_u64 gHi gLo w8 (sU <<< 2) bU := by
    intro bI bU hb_nn hb_ne hb_lt hbU hstrict
    have h1 := cmpScaledMixed_packed_eq_u64_of_strict (-q) (-k') gHi gLo wPlusH
      (4 * (s : Int)) bI
      (by positivity) hb_nn hb_ne
      (by rw [h60_lit]; omega) hb_lt
      hk_lo hk_hi hqh_lo hqh_hi
      (by rw [hs4U_corr, hbU]; exact hstrict)
    rw [hs4U_corr, hbU] at h1
    rw [← h1, hwPlusH_def, hgHi_def, hgLo_def]
    exact (cmpScaledMixed_packed_eq (4 * (s : Int)) (-q) bI (-k')).symm
  -- Verdict range for the endgame case split.
  have hrange : ∀ (aU bU : UInt64),
      cmpScaledMixed_u64 gHi gLo w8 aU bU = 1
      ∨ cmpScaledMixed_u64 gHi gLo w8 aU bU = -1
      ∨ cmpScaledMixed_u64 gHi gLo w8 aU bU = 0 := by
    intro aU bU
    rw [cmpScaledMixed_u64_eq_cmpVerdict]
    exact cmpVerdict_u64_inner_range _ _ _ _ _ _ _
  have hmI1 : (1 : Int) ≤ (m : Int) := by exact_mod_cast hm_pos
  -- Case on irregular, then identify the verdicts.
  by_cases hirr : irregular = true
  · simp only [hirr, if_true] at hL_val hne ⊢
    have hLU : (mU <<< 2 - 1).toNat = 4 * m - 1 := by
      rw [← hleftU_irr]; exact hbound_toNat _ (by omega)
    have hRU : (mU <<< 2 + 2).toNat = 4 * m + 2 := by
      rw [← hrightU]; exact hbound_toNat _ (by omega)
    have hcform := inRoundingInterval_u64_flipped_u8_cmp_form gHi gLo w8 sU
      (mU <<< 2 - 1) (mU <<< 2 + 2) lLHi lLMid lLLo lRHi lRMid lRLo
      (by rw [hLU]; exact hL_val)
      (by rw [hLU]; exact hbound_lt _ (by omega))
      (by rw [hRU]; exact hR_val)
      (by rw [hRU]; exact hbound_lt _ (by omega))
    rw [hcform] at hne ⊢
    simp only [] at hne ⊢
    by_cases hL0 : cmpScaledMixed_u64 gHi gLo w8 (sU <<< 2) (mU <<< 2 - 1) = 0
    · rw [if_pos hL0] at hne; exact absurd rfl hne
    rw [if_neg hL0] at hne ⊢
    by_cases hR0 : cmpScaledMixed_u64 gHi gLo w8 (sU <<< 2) (mU <<< 2 + 2) = 0
    · rw [if_pos hR0] at hne; exact absurd rfl hne
    rw [if_neg hR0] at hne ⊢
    have hLspec := hstrict_spec (4 * (m : Int) - 1) (mU <<< 2 - 1)
      (by omega) (by omega) (by rw [h60_lit]; omega)
      (by rw [toNat_4m_sub_1_eq hm_pos]; exact hleftU_irr) hL0
    have hRspec := hstrict_spec (4 * (m : Int) + 2) (mU <<< 2 + 2)
      (by omega) (by omega) (by rw [h60_lit]; omega)
      (by rw [toNat_4m_add_2_eq m]; exact hrightU) hR0
    have hLorig : cmpScaledMixed (4 * (m : Int) - 1) q (4 * (s : Int)) k'
        = - cmpScaledMixed_u64 gHi gLo w8 (sU <<< 2) (mU <<< 2 - 1) := by
      rw [cmpScaledMixed_flip (4 * (m : Int) - 1) q (4 * (s : Int)) k', hLspec]
    have hRorig : cmpScaledMixed (4 * (m : Int) + 2) q (4 * (s : Int)) k'
        = - cmpScaledMixed_u64 gHi gLo w8 (sU <<< 2) (mU <<< 2 + 2) := by
      rw [cmpScaledMixed_flip (4 * (m : Int) + 2) q (4 * (s : Int)) k', hRspec]
    unfold inRoundingInterval
    simp only [if_true]
    rw [hLorig, hRorig]
    rcases hrange (sU <<< 2) (mU <<< 2 - 1) with hX | hX | hX
    all_goals (try (exact absurd hX hL0))
    all_goals (
      rcases hrange (sU <<< 2) (mU <<< 2 + 2) with hY | hY | hY
      all_goals (try (exact absurd hY hR0))
      all_goals (
        rw [hX, hY]
        simp [inRoundingInterval_u8_TRUE, inRoundingInterval_u8_FALSE]))
  · simp only [Bool.not_eq_true] at hirr
    simp only [hirr, Bool.false_eq_true, if_false] at hL_val hne ⊢
    have hLU : (mU <<< 2 - 2).toNat = 4 * m - 2 := by
      rw [← hleftU_reg]; exact hbound_toNat _ (by omega)
    have hRU : (mU <<< 2 + 2).toNat = 4 * m + 2 := by
      rw [← hrightU]; exact hbound_toNat _ (by omega)
    have hcform := inRoundingInterval_u64_flipped_u8_cmp_form gHi gLo w8 sU
      (mU <<< 2 - 2) (mU <<< 2 + 2) lLHi lLMid lLLo lRHi lRMid lRLo
      (by rw [hLU]; exact hL_val)
      (by rw [hLU]; exact hbound_lt _ (by omega))
      (by rw [hRU]; exact hR_val)
      (by rw [hRU]; exact hbound_lt _ (by omega))
    rw [hcform] at hne ⊢
    simp only [] at hne ⊢
    by_cases hL0 : cmpScaledMixed_u64 gHi gLo w8 (sU <<< 2) (mU <<< 2 - 2) = 0
    · rw [if_pos hL0] at hne; exact absurd rfl hne
    rw [if_neg hL0] at hne ⊢
    by_cases hR0 : cmpScaledMixed_u64 gHi gLo w8 (sU <<< 2) (mU <<< 2 + 2) = 0
    · rw [if_pos hR0] at hne; exact absurd rfl hne
    rw [if_neg hR0] at hne ⊢
    have hLspec := hstrict_spec (4 * (m : Int) - 2) (mU <<< 2 - 2)
      (by omega) (by omega) (by rw [h60_lit]; omega)
      (by rw [toNat_4m_sub_2_eq hm_pos]; exact hleftU_reg) hL0
    have hRspec := hstrict_spec (4 * (m : Int) + 2) (mU <<< 2 + 2)
      (by omega) (by omega) (by rw [h60_lit]; omega)
      (by rw [toNat_4m_add_2_eq m]; exact hrightU) hR0
    have hLorig : cmpScaledMixed (4 * (m : Int) - 2) q (4 * (s : Int)) k'
        = - cmpScaledMixed_u64 gHi gLo w8 (sU <<< 2) (mU <<< 2 - 2) := by
      rw [cmpScaledMixed_flip (4 * (m : Int) - 2) q (4 * (s : Int)) k', hLspec]
    have hRorig : cmpScaledMixed (4 * (m : Int) + 2) q (4 * (s : Int)) k'
        = - cmpScaledMixed_u64 gHi gLo w8 (sU <<< 2) (mU <<< 2 + 2) := by
      rw [cmpScaledMixed_flip (4 * (m : Int) + 2) q (4 * (s : Int)) k', hRspec]
    unfold inRoundingInterval
    simp only [Bool.false_eq_true, if_false]
    rw [hLorig, hRorig]
    rcases hrange (sU <<< 2) (mU <<< 2 - 2) with hX | hX | hX
    all_goals (try (exact absurd hX hL0))
    all_goals (
      rcases hrange (sU <<< 2) (mU <<< 2 + 2) with hY | hY | hY
      all_goals (try (exact absurd hY hR0))
      all_goals (
        rw [hX, hY]
        simp [inRoundingInterval_u8_TRUE, inRoundingInterval_u8_FALSE]))

/-! ## The flipped kernel at spec-table level -/

/-- Base-level (spec-table) kernel with the Giulietti-style flipped
    `k+1` interval tests: one boundary product `P = 4m·g'` per decode,
    boundary products derived by 192-bit add/sub, candidate on the
    exact-shift side, shared across the `uV`/`wV` tests. Everything
    else matches `shortestUnsigned_u64_opt`. -/
@[inline]
def shortestUnsigned_u64_opt_flip (m : Nat) (q : Int) : Option (UInt64 × Int) :=
  if _h_m : m ≥ (1 <<< 53 : Nat) then none
  else if _h_q_lo : q < (-1074 : Int) then none
  else if _h_q_hi : q > 971 then none
  else
    let irregular := isIrregular m q
    let k := kOfMQ_fast m q
    if _h_k_lo : k < pow10Table128_kMin then none
    else if _h_k_hi : k + 1 > pow10Table128_kMax then none
    else
    let s := shiftedSig_v3 m q k
    if _h_s : s ≥ (1 <<< 57 : Nat) then none
    else
      let sU : UInt64 := UInt64.ofNat s
      let mU : UInt64 := UInt64.ofNat m
      if s ≥ 10 then
        let kHigh : Int := k + 1
        let gT := pow10Lookup128 (-kHigh)
        let wPlusH : Int := -q + gT.2.2
        if _h_qh_lo : wPlusH < 64 then none
        else if _h_qh_hi : wPlusH > 132 then none
        else
          let w8 : UInt64 := UInt64.ofNat wPlusH.toNat
          let sHighU : UInt64 := sU / 10
          let m4 : UInt64 := mU <<< 2
          let leftU : UInt64 := if irregular then m4 - 1 else m4 - 2
          let rightU : UInt64 := m4 + 2
          let pLo  : UInt64 := m4 * gT.2.1
          let pLoH : UInt64 := mulHi64 m4 gT.2.1
          let pHi  : UInt64 := m4 * gT.1
          let pHiH : UInt64 := mulHi64 m4 gT.1
          let pMidSum : UInt64 := pHi + pLoH
          let pCarry : UInt64 := if pMidSum < pHi then 1 else 0
          let p192Hi : UInt64 := pHiH + pCarry
          let tg := add192_192 0 gT.1 gT.2.1 0 gT.1 gT.2.1
          let sbHi : UInt64 := if irregular then 0 else tg.1
          let sbMid : UInt64 := if irregular then gT.1 else tg.2.1
          let sbLo : UInt64 := if irregular then gT.2.1 else tg.2.2
          let lB := sub192_192 p192Hi pMidSum pLo sbHi sbMid sbLo
          let rB := add192_192 p192Hi pMidSum pLo tg.1 tg.2.1 tg.2.2
          let uV := inRoundingInterval_u64_flipped_u8 lB.1 lB.2.1 lB.2.2 leftU
                      rB.1 rB.2.1 rB.2.2 rightU w8 sHighU
          if uV = inRoundingInterval_u8_AMBIG then none
          else if uV = inRoundingInterval_u8_TRUE then some (sHighU, kHigh)
          else
            let wV := inRoundingInterval_u64_flipped_u8 lB.1 lB.2.1 lB.2.2 leftU
                        rB.1 rB.2.1 rB.2.2 rightU w8 (sHighU + 1)
            if wV = inRoundingInterval_u8_AMBIG then none
            else if wV = inRoundingInterval_u8_TRUE then some (sHighU + 1, kHigh)
            else
              let cmpTuple := pow10Lookup128 k
              let cmpQPlusH : Int := q + cmpTuple.2.2
              if _h_qh2_lo : cmpQPlusH < 64 then none
              else if _h_qh2_hi : cmpQPlusH > 132 then none
              else
                let cmpQPlusH8 : UInt64 := UInt64.ofNat cmpQPlusH.toNat
                match pickNearer_u64_opt cmpTuple.1 cmpTuple.2.1 cmpQPlusH8 sU mU irregular with
                | none => none
                | some chosen => some (chosen, k)
      else if _h_s1 : s = 0 then none
      else
        let cmpTuple := pow10Lookup128 k
        let cmpQPlusH : Int := q + cmpTuple.2.2
        if _h_qh2_lo : cmpQPlusH < 64 then none
        else if _h_qh2_hi : cmpQPlusH > 132 then none
        else
          let cmpQPlusH8 : UInt64 := UInt64.ofNat cmpQPlusH.toNat
          match pickNearer_u64_opt cmpTuple.1 cmpTuple.2.1 cmpQPlusH8 sU mU irregular with
          | none => none
          | some chosen => some (chosen, k)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 3200000 in
/-- Fast-path correctness for the flipped kernel: a `some` result is
    the `shortestUnsigned_packed` (= spec) value. -/
theorem shortestUnsigned_u64_opt_flip_some_eq_packed
    (m : Nat) (q : Int) (sUo : UInt64) (ko : Int)
    (hopt : shortestUnsigned_u64_opt_flip m q = some (sUo, ko)) :
    shortestUnsigned_packed m q = (sUo.toNat, ko) := by
  rw [shortestUnsigned_packed_eq]
  show shortestUnsigned m q = (sUo.toNat, ko)
  unfold shortestUnsigned_u64_opt_flip at hopt
  simp only [kOfMQ_fast_eq, shiftedSig_v3_eq] at hopt
  by_cases hm_ge : m ≥ (1 <<< 53 : Nat)
  · rw [dif_pos hm_ge] at hopt; cases hopt
  rw [dif_neg hm_ge] at hopt
  push_neg at hm_ge
  by_cases hq_lo : q < (-1074 : Int)
  · rw [dif_pos hq_lo] at hopt; cases hopt
  rw [dif_neg hq_lo] at hopt
  by_cases hq_hi : q > 971
  · rw [dif_pos hq_hi] at hopt; cases hopt
  rw [dif_neg hq_hi] at hopt
  push_neg at hq_lo hq_hi
  by_cases hk_lo : kOfMQ m q < pow10Table128_kMin
  · rw [dif_pos hk_lo] at hopt; cases hopt
  rw [dif_neg hk_lo] at hopt
  by_cases hk_hi1 : kOfMQ m q + 1 > pow10Table128_kMax
  · rw [dif_pos hk_hi1] at hopt; cases hopt
  rw [dif_neg hk_hi1] at hopt
  push_neg at hk_lo hk_hi1
  by_cases hs_ge : shiftedSig m q (kOfMQ m q) ≥ (1 <<< 57 : Nat)
  · rw [dif_pos hs_ge] at hopt; cases hopt
  rw [dif_neg hs_ge] at hopt
  push_neg at hs_ge
  have hkMin_lit : pow10Table128_kMin = (-324 : Int) := rfl
  have hkMax_lit : pow10Table128_kMax = (324 : Int) := rfl
  have hm_lt : m < (1 <<< 58 : Nat) := by
    have : (1 <<< 53 : Nat) < (1 <<< 58 : Nat) := by decide
    omega
  have hm_pos : m ≥ 1 := by
    by_contra hcontra
    push_neg at hcontra
    have hm_zero : m = 0 := by omega
    rw [hm_zero, shiftedSig_zero] at hopt
    simp at hopt
  unfold shortestUnsigned
  by_cases hs10 : shiftedSig m q (kOfMQ m q) ≥ 10
  · rw [if_pos hs10]
    simp only [hs10, if_true] at hopt
    by_cases hqh_lo : -q + (pow10Lookup128 (-(kOfMQ m q + 1))).2.2 < 64
    · rw [dif_pos hqh_lo] at hopt; cases hopt
    rw [dif_neg hqh_lo] at hopt
    by_cases hqh_hi : -q + (pow10Lookup128 (-(kOfMQ m q + 1))).2.2 > 132
    · rw [dif_pos hqh_hi] at hopt; cases hopt
    rw [dif_neg hqh_hi] at hopt
    push_neg at hqh_lo hqh_hi
    have hdiv10 : UInt64.ofNat (shiftedSig m q (kOfMQ m q)) / 10 =
        UInt64.ofNat (shiftedSig m q (kOfMQ m q) / 10) := uint64_div_10 hs_ge
    rw [hdiv10] at hopt
    -- Abbreviate the flipped-block subterms (hopt is fully zeta-expanded).
    set gT := pow10Lookup128 (-(kOfMQ m q + 1)) with hgT
    set m4 : UInt64 := UInt64.ofNat m <<< 2 with hm4
    set pLo : UInt64 := m4 * gT.2.1 with hpLo
    set pLoH : UInt64 := mulHi64 m4 gT.2.1 with hpLoH
    set pHi : UInt64 := m4 * gT.1 with hpHi
    set pHiH : UInt64 := mulHi64 m4 gT.1 with hpHiH
    set pMid : UInt64 := pHi + pLoH with hpMid
    set pC : UInt64 := (if pMid < pHi then (1 : UInt64) else 0) with hpC
    set pH : UInt64 := pHiH + pC with hpH
    set tg := add192_192 0 gT.1 gT.2.1 0 gT.1 gT.2.1 with htg
    set sbHi : UInt64 := (if isIrregular m q = true then 0 else tg.1) with hsbHi
    set sbMid : UInt64 := (if isIrregular m q = true then gT.1 else tg.2.1) with hsbMid
    set sbLo : UInt64 := (if isIrregular m q = true then gT.2.1 else tg.2.2) with hsbLo
    set lB := sub192_192 pH pMid pLo sbHi sbMid sbLo with hlB
    set rB := add192_192 pH pMid pLo tg.1 tg.2.1 tg.2.2 with hrB
    set leftU : UInt64 := (if isIrregular m q = true then m4 - 1 else m4 - 2) with hleftU
    set w8 : UInt64 := UInt64.ofNat (-q + gT.2.2).toNat with hw8
    -- Value facts.
    have hG_lt : gT.1.toNat * 2 ^ 64 + gT.2.1.toNat < 2 ^ 128 := by
      have h1 := gT.1.toNat_lt; have h2 := gT.2.1.toNat_lt
      omega
    have hm4_toNat : m4.toNat = 4 * m := by
      rw [hm4, uint64_shiftLeft_2, UInt64.toNat_mul,
          toNat_ofNat_bounded (show m < 2 ^ 64 by omega),
          show ((4 : UInt64)).toNat = 4 from rfl]
      exact Nat.mod_eq_of_lt (by omega)
    have hmulG_lt : ∀ b : Nat, b ≤ 4 * m + 2 →
        b * (gT.1.toNat * 2 ^ 64 + gT.2.1.toNat) < 2 ^ 192 := by
      intro b hb
      have h3 : b * (gT.1.toNat * 2 ^ 64 + gT.2.1.toNat) ≤ 2 ^ 60 * 2 ^ 128 :=
        Nat.mul_le_mul (by omega) (by omega)
      have h4 : (2 : Nat) ^ 60 * 2 ^ 128 < 2 ^ 192 := by
        rw [← pow_add]
        exact Nat.pow_lt_pow_right (by omega) (by omega)
      omega
    have htrip0G : triple192Nat 0 gT.1 gT.2.1
        = gT.1.toNat * 2 ^ 64 + gT.2.1.toNat := by
      unfold triple192Nat
      simp only [show ((0 : UInt64)).toNat = 0 from rfl]
      omega
    have hP_val : triple192Nat pH pMid pLo
        = 4 * m * (gT.1.toNat * 2 ^ 64 + gT.2.1.toNat) := by
      have h := mul192_b_g_toNat m4 gT.1 gT.2.1
      simp only [] at h
      rw [← hpLo, ← hpLoH, ← hpHi, ← hpHiH, ← hpMid, ← hpC, ← hpH] at h
      rw [hm4_toNat, Nat.mod_eq_of_lt (hmulG_lt (4 * m) (by omega))] at h
      exact h
    have h2G_val : triple192Nat tg.1 tg.2.1 tg.2.2
        = 2 * (gT.1.toNat * 2 ^ 64 + gT.2.1.toNat) := by
      rw [htg, add192_192_toNat 0 gT.1 gT.2.1 0 gT.1 gT.2.1 (by
        rw [htrip0G]; omega), htrip0G]
      omega
    have hlB_val : triple192Nat lB.1 lB.2.1 lB.2.2
        = (if isIrregular m q = true then 4 * m - 1 else 4 * m - 2)
            * (gT.1.toNat * 2 ^ 64 + gT.2.1.toNat) := by
      rw [hlB, hsbHi, hsbMid, hsbLo]
      by_cases hirr : isIrregular m q = true
      · rw [if_pos hirr, if_pos hirr, if_pos hirr, if_pos hirr,
            sub192_192_toNat pH pMid pLo 0 gT.1 gT.2.1 (by
              rw [htrip0G, hP_val]
              exact Nat.le_mul_of_pos_left _ (by omega)),
            hP_val, htrip0G, Nat.sub_mul, Nat.one_mul]
      · rw [if_neg hirr, if_neg hirr, if_neg hirr, if_neg hirr,
            sub192_192_toNat pH pMid pLo tg.1 tg.2.1 tg.2.2 (by
              rw [h2G_val, hP_val]
              exact Nat.mul_le_mul_right _ (by omega)),
            hP_val, h2G_val, Nat.sub_mul]
    have hrB_val : triple192Nat rB.1 rB.2.1 rB.2.2
        = (4 * m + 2) * (gT.1.toNat * 2 ^ 64 + gT.2.1.toNat) := by
      rw [hrB, add192_192_toNat pH pMid pLo tg.1 tg.2.1 tg.2.2 (by
            rw [hP_val, h2G_val]
            have := hmulG_lt (4 * m + 2) (by omega)
            rw [Nat.add_mul] at this
            omega),
          hP_val, h2G_val, Nat.add_mul]
    -- Bridge preconditions.
    have hsHigh_pos : shiftedSig m q (kOfMQ m q) / 10 ≥ 1 := by omega
    have hsHigh_lt58 : shiftedSig m q (kOfMQ m q) / 10 < (1 <<< 58 : Nat) := by
      have h1 : shiftedSig m q (kOfMQ m q) / 10 ≤ shiftedSig m q (kOfMQ m q) :=
        Nat.div_le_self _ _
      have h2 : (1 <<< 57 : Nat) < (1 <<< 58 : Nat) := by decide
      omega
    have hsHigh1_lt58 : shiftedSig m q (kOfMQ m q) / 10 + 1 < (1 <<< 58 : Nat) := by
      have h1 : shiftedSig m q (kOfMQ m q) / 10 ≤ shiftedSig m q (kOfMQ m q) :=
        Nat.div_le_self _ _
      have h2 : (1 <<< 57 : Nat) + 1 ≤ (1 <<< 58 : Nat) := by decide
      omega
    have hk_lo' : pow10Table128_kMin ≤ -(kOfMQ m q + 1) := by omega
    have hk_hi' : -(kOfMQ m q + 1) ≤ pow10Table128_kMax := by omega
    -- uV leg.
    by_cases hAmb : inRoundingInterval_u64_flipped_u8 lB.1 lB.2.1 lB.2.2 leftU
        rB.1 rB.2.1 rB.2.2 (m4 + 2) w8
        (UInt64.ofNat (shiftedSig m q (kOfMQ m q) / 10)) = inRoundingInterval_u8_AMBIG
    · rw [if_pos hAmb] at hopt; cases hopt
    rw [if_neg hAmb] at hopt
    have huV := inRoundingInterval_u64_flipped_u8_some_eq q (kOfMQ m q + 1)
      (shiftedSig m q (kOfMQ m q) / 10) m (isIrregular m q)
      lB.1 lB.2.1 lB.2.2 rB.1 rB.2.1 rB.2.2
      hm_pos hsHigh_pos hm_lt hsHigh_lt58 hk_lo' hk_hi' hqh_lo hqh_hi
      hlB_val hrB_val hAmb
    by_cases hT : inRoundingInterval_u64_flipped_u8 lB.1 lB.2.1 lB.2.2 leftU
        rB.1 rB.2.1 rB.2.2 (m4 + 2) w8
        (UInt64.ofNat (shiftedSig m q (kOfMQ m q) / 10)) = inRoundingInterval_u8_TRUE
    · rw [if_pos hT] at hopt
      have huIn_true : inRoundingInterval (shiftedSig m q (kOfMQ m q) / 10)
          (kOfMQ m q + 1) m q (isIrregular m q) = true := by
        rw [huV]
        simp only [decide_eq_true_eq]
        exact hT
      simp only [huIn_true, if_true]
      cases hopt
      have hsHigh_eq : (UInt64.ofNat (shiftedSig m q (kOfMQ m q) / 10)).toNat =
          shiftedSig m q (kOfMQ m q) / 10 := by
        apply toNat_ofNat_bounded
        have : (1 <<< 58 : Nat) < 2 ^ 64 := by decide
        omega
      simp [hsHigh_eq]
    rw [if_neg hT] at hopt
    have huIn_false : inRoundingInterval (shiftedSig m q (kOfMQ m q) / 10)
        (kOfMQ m q + 1) m q (isIrregular m q) = false := by
      rw [huV]
      exact decide_eq_false hT
    simp only [huIn_false, Bool.false_eq_true, if_false]
    -- wV leg.
    have hsHigh1_eq : UInt64.ofNat (shiftedSig m q (kOfMQ m q) / 10) + 1 =
        UInt64.ofNat (shiftedSig m q (kOfMQ m q) / 10 + 1) := (ofNat_succ _).symm
    rw [hsHigh1_eq] at hopt
    by_cases hAmb2 : inRoundingInterval_u64_flipped_u8 lB.1 lB.2.1 lB.2.2 leftU
        rB.1 rB.2.1 rB.2.2 (m4 + 2) w8
        (UInt64.ofNat (shiftedSig m q (kOfMQ m q) / 10 + 1)) = inRoundingInterval_u8_AMBIG
    · rw [if_pos hAmb2] at hopt; cases hopt
    rw [if_neg hAmb2] at hopt
    have hwV := inRoundingInterval_u64_flipped_u8_some_eq q (kOfMQ m q + 1)
      (shiftedSig m q (kOfMQ m q) / 10 + 1) m (isIrregular m q)
      lB.1 lB.2.1 lB.2.2 rB.1 rB.2.1 rB.2.2
      hm_pos (by omega) hm_lt hsHigh1_lt58 hk_lo' hk_hi' hqh_lo hqh_hi
      hlB_val hrB_val hAmb2
    by_cases hT2 : inRoundingInterval_u64_flipped_u8 lB.1 lB.2.1 lB.2.2 leftU
        rB.1 rB.2.1 rB.2.2 (m4 + 2) w8
        (UInt64.ofNat (shiftedSig m q (kOfMQ m q) / 10 + 1)) = inRoundingInterval_u8_TRUE
    · rw [if_pos hT2] at hopt
      have hwIn_true : inRoundingInterval (shiftedSig m q (kOfMQ m q) / 10 + 1)
          (kOfMQ m q + 1) m q (isIrregular m q) = true := by
        rw [hwV]
        simp only [decide_eq_true_eq]
        exact hT2
      simp only [hwIn_true, if_true]
      cases hopt
      have hwIn_eq : (UInt64.ofNat (shiftedSig m q (kOfMQ m q) / 10 + 1)).toNat =
          shiftedSig m q (kOfMQ m q) / 10 + 1 := by
        apply toNat_ofNat_bounded
        have : (1 <<< 58 : Nat) < 2 ^ 64 := by decide
        omega
      simp []
      omega
    rw [if_neg hT2] at hopt
    have hwIn_false : inRoundingInterval (shiftedSig m q (kOfMQ m q) / 10 + 1)
        (kOfMQ m q + 1) m q (isIrregular m q) = false := by
      rw [hwV]
      exact decide_eq_false hT2
    simp only [hwIn_false, Bool.false_eq_true, if_false]
    -- pickNearer fall-through at k.
    by_cases hqh2_lo : q + (pow10Lookup128 (kOfMQ m q)).2.2 < 64
    · rw [dif_pos hqh2_lo] at hopt; cases hopt
    rw [dif_neg hqh2_lo] at hopt
    by_cases hqh2_hi : q + (pow10Lookup128 (kOfMQ m q)).2.2 > 132
    · rw [dif_pos hqh2_hi] at hopt; cases hopt
    rw [dif_neg hqh2_hi] at hopt
    push_neg at hqh2_lo hqh2_hi
    match hp : pickNearer_u64_opt (pow10Lookup128 (kOfMQ m q)).1
                  (pow10Lookup128 (kOfMQ m q)).2.1
                  (UInt64.ofNat (q + (pow10Lookup128 (kOfMQ m q)).2.2).toNat)
                  (UInt64.ofNat (shiftedSig m q (kOfMQ m q)))
                  (UInt64.ofNat m) (isIrregular m q) with
    | none => rw [hp] at hopt; cases hopt
    | some chosen =>
      rw [hp] at hopt
      have hpkd : pickNearer (shiftedSig m q (kOfMQ m q)) (kOfMQ m q) m q = chosen.toNat := by
        rw [← pickNearer_packed_eq]
        exact pickNearer_u64_opt_some_eq_packed q (kOfMQ m q)
          (pow10Lookup128 (kOfMQ m q)).1 (pow10Lookup128 (kOfMQ m q)).2.1
          (q + (pow10Lookup128 (kOfMQ m q)).2.2)
          (shiftedSig m q (kOfMQ m q)) m (isIrregular m q) chosen
          hm_pos (by omega) hm_lt hs_ge (by omega) (by omega) hqh2_lo hqh2_hi rfl hp
      rw [hpkd]
      cases hopt
      rfl
  · rw [if_neg hs10]
    push_neg at hs10
    simp only [show (shiftedSig m q (kOfMQ m q) ≥ 10) = False from by simp [hs10],
      if_false] at hopt
    by_cases hs_zero : shiftedSig m q (kOfMQ m q) = 0
    · rw [dif_pos hs_zero] at hopt; cases hopt
    rw [dif_neg hs_zero] at hopt
    by_cases hqh2_lo : q + (pow10Lookup128 (kOfMQ m q)).2.2 < 64
    · rw [dif_pos hqh2_lo] at hopt; cases hopt
    rw [dif_neg hqh2_lo] at hopt
    by_cases hqh2_hi : q + (pow10Lookup128 (kOfMQ m q)).2.2 > 132
    · rw [dif_pos hqh2_hi] at hopt; cases hopt
    rw [dif_neg hqh2_hi] at hopt
    push_neg at hqh2_lo hqh2_hi
    match hp : pickNearer_u64_opt (pow10Lookup128 (kOfMQ m q)).1
                  (pow10Lookup128 (kOfMQ m q)).2.1
                  (UInt64.ofNat (q + (pow10Lookup128 (kOfMQ m q)).2.2).toNat)
                  (UInt64.ofNat (shiftedSig m q (kOfMQ m q)))
                  (UInt64.ofNat m) (isIrregular m q) with
    | none => rw [hp] at hopt; cases hopt
    | some chosen =>
      rw [hp] at hopt
      have hpkd : pickNearer (shiftedSig m q (kOfMQ m q)) (kOfMQ m q) m q = chosen.toNat := by
        rw [← pickNearer_packed_eq]
        exact pickNearer_u64_opt_some_eq_packed q (kOfMQ m q)
          (pow10Lookup128 (kOfMQ m q)).1 (pow10Lookup128 (kOfMQ m q)).2.1
          (q + (pow10Lookup128 (kOfMQ m q)).2.2)
          (shiftedSig m q (kOfMQ m q)) m (isIrregular m q) chosen
          hm_pos (by omega) hm_lt hs_ge (by omega) (by omega) hqh2_lo hqh2_hi rfl hp
      rw [hpkd]
      cases hopt
      rfl

/-! ## The pure-UInt64 v11 kernel -/

/-- v8 with the `k+1` interval tests replaced by the flipped scheme:
    table entry for `-(k+1)` at biased index `647 - kB`, window guard
    `uB' = (h'+2048+4096) - qB ∈ [5134, 5202]`, one boundary product
    `P = 4m·g'` shared across `uV`/`wV`, candidate on the shift side. -/
@[inline]
def shortestUnsigned_u64_opt_v11 (mU : UInt64) (qB : UInt64) : Option (UInt64 × Int) :=
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
          let gT := pow10Table128.getD (647 - kBn) pow10Table128_default
          let uB' : UInt64 := (hB128.getD (647 - kBn) 0 + 4096) - qB
          if _h_qh_lo : uB' < 5134 then none
          else if _h_qh_hi : uB' > 5202 then none
          else
            let w8 : UInt64 := uB' - 5070
            let sHighU : UInt64 := sU / 10
            let m4 : UInt64 := mU <<< 2
            let leftU : UInt64 := if irregular then m4 - 1 else m4 - 2
            let rightU : UInt64 := m4 + 2
            let pLo  : UInt64 := m4 * gT.2.1
            let pLoH : UInt64 := mulHi64 m4 gT.2.1
            let pHi  : UInt64 := m4 * gT.1
            let pHiH : UInt64 := mulHi64 m4 gT.1
            let pMidSum : UInt64 := pHi + pLoH
            let pCarry : UInt64 := if pMidSum < pHi then 1 else 0
            let p192Hi : UInt64 := pHiH + pCarry
            let tg := add192_192 0 gT.1 gT.2.1 0 gT.1 gT.2.1
            let sbHi : UInt64 := if irregular then 0 else tg.1
            let sbMid : UInt64 := if irregular then gT.1 else tg.2.1
            let sbLo : UInt64 := if irregular then gT.2.1 else tg.2.2
            let lB := sub192_192 p192Hi pMidSum pLo sbHi sbMid sbLo
            let rB := add192_192 p192Hi pMidSum pLo tg.1 tg.2.1 tg.2.2
            let uV := inRoundingInterval_u64_flipped_u8 lB.1 lB.2.1 lB.2.2 leftU
                        rB.1 rB.2.1 rB.2.2 rightU w8 sHighU
            if uV = inRoundingInterval_u8_AMBIG then none
            else if uV = inRoundingInterval_u8_TRUE then some (sHighU, k + 1)
            else
              let wV := inRoundingInterval_u64_flipped_u8 lB.1 lB.2.1 lB.2.2 leftU
                          rB.1 rB.2.1 rB.2.2 rightU w8 (sHighU + 1)
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
set_option maxHeartbeats 3200000 in
/-- Arg-biasing transfer: a `some` result of the pure-UInt64 v11 kernel
    is a `some` result of the spec-table flipped kernel. Assembles the
    existing biased-index/window component lemmas. -/
theorem shortestUnsigned_u64_opt_v11_some_eq_flip (mU qB : UInt64) (r : UInt64 × Int)
    (hopt : shortestUnsigned_u64_opt_v11 mU qB = some r) :
    shortestUnsigned_u64_opt_flip mU.toNat ((qB.toNat : Int) - 1074) = some r := by
  unfold shortestUnsigned_u64_opt_v11 at hopt
  unfold shortestUnsigned_u64_opt_flip
  by_cases h_m0 : mU = 0
  · rw [dif_pos h_m0] at hopt; cases hopt
  rw [dif_neg h_m0] at hopt
  by_cases h_m : mU ≥ (9007199254740992 : UInt64)
  · rw [dif_pos h_m] at hopt; cases hopt
  rw [dif_neg h_m] at hopt
  have h_m' : ¬ mU.toNat ≥ (1 <<< 53 : Nat) := by
    rw [ge_iff_le, UInt64.le_iff_toNat_le,
        show ((9007199254740992 : UInt64)).toNat = 1 <<< 53 from rfl] at h_m
    exact h_m
  rw [dif_neg h_m']
  rw [dif_neg (show ¬ ((qB.toNat : Int) - 1074) < -1074 from by omega)]
  by_cases h_q : qB > 2045
  · rw [dif_pos h_q] at hopt; cases hopt
  rw [dif_neg h_q] at hopt
  have h_q' : qB.toNat ≤ 2045 := by
    rw [gt_iff_lt, UInt64.lt_iff_toNat_lt, show ((2045 : UInt64)).toNat = 2045 from rfl] at h_q
    omega
  rw [dif_neg (show ¬ ((qB.toNat : Int) - 1074) > 971 from by omega)]
  have hkf := kBOfMQ_eq mU qB h_q'
  have hknn := hkf.1
  have hkval := hkf.2
  by_cases h_k : kBOfMQ mU qB > 647
  · rw [dif_pos h_k] at hopt; cases hopt
  rw [dif_neg h_k] at hopt
  have hkB_le : (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) + 324).toNat ≤ 647 := by
    rw [← hkval]
    rw [gt_iff_lt, UInt64.lt_iff_toNat_lt, show ((647 : UInt64)).toNat = 647 from rfl] at h_k
    omega
  have hkMin_lit : pow10Table128_kMin = (-324 : Int) := rfl
  have hkMax_lit : pow10Table128_kMax = (324 : Int) := rfl
  have hklo : ¬ kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) < pow10Table128_kMin := by
    rw [hkMin_lit]; omega
  have hkhi : ¬ kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) + 1 > pow10Table128_kMax := by
    rw [hkMax_lit]; omega
  rw [dif_neg hklo, dif_neg hkhi]
  -- Alignment equations.
  have ekidx : (kBOfMQ mU qB).toNat
      = (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) + 324).toNat := hkval
  have ekexit : (((kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) + 324).toNat : Int)) - 324
      = kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) := by omega
  have eqb : UInt64.ofNat (((qB.toNat : Int) - 1074) + 1074).toNat = qB := by
    rw [show (((qB.toNat : Int) - 1074) + 1074).toNat = qB.toNat from by omega,
        UInt64.ofNat_toNat]
  have em : UInt64.ofNat mU.toNat = mU := UInt64.ofNat_toNat
  have eirr : isIrregular mU.toNat ((qB.toNat : Int) - 1074) = isIrregularB mU qB :=
    (isIrregularB_eq mU qB).symm
  simp only [ekidx, ekexit] at hopt
  -- Index bounds.
  have hi192 : 648 - (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) + 324).toNat
      < pow10Table192.size := by rw [pow10Table192_size_eq]; omega
  have hiflip : 647 - (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) + 324).toNat
      < pow10Table128.size := by rw [pow10Table128_size_eq]; omega
  have hilow : (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) + 324).toNat
      < pow10Table128.size := by rw [pow10Table128_size_eq]; omega
  -- Goal side: lookups → getD, ofNat mU.toNat → mU, isIrregular → isIrregularB.
  have e192 := lookup192_neg (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074)) hklo hkhi
  have eflip := lookup128_negHigh (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074)) hklo hkhi
  have elow := lookup128_low (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074)) hklo
  simp only []
  rw [eflip, elow]
  simp only [em, eirr]
  -- hopt side: biased h-tables → ofNat (h + 2048) forms.
  have c192 := hB192_getD _ hi192
  have cflip := hB128_getD _ hiflip
  have clow := hB128_getD _ hilow
  simp only [c192, cflip, clow] at hopt
  -- h bounds at the three entries.
  have hh192 := hBound192_getD _ hi192
  have hhflip := hBound128_getD _ hiflip
  have hhlow := hBound128_getD _ hilow
  have h_q_lo' : ¬ ((qB.toNat : Int) - 1074) < -1074 := by omega
  have h_q_hi' : ¬ ((qB.toNat : Int) - 1074) > 971 := by omega
  -- s-block windows → Int form.
  have tlt := tA_lt ((qB.toNat : Int) - 1074) _ h_q_lo' h_q_hi' hh192
  have tge := tA_ge ((qB.toNat : Int) - 1074) _ h_q_lo' h_q_hi' hh192
  rw [eqb] at tlt tge
  simp only [tlt, tge] at hopt
  -- The s computation equals shiftedSig_v3.
  have edomk : kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074)
      = kOfMQ mU.toNat ((qB.toNat : Int) - 1074) :=
    (congrFun (congrFun kOfMQ_eq_fast_csimp mU.toNat) ((qB.toNat : Int) - 1074)).symm
  have hdom : 0 < mU.toNat ∧ mU.toNat < 2 ^ 53 ∧ -1074 ≤ ((qB.toNat : Int) - 1074)
      ∧ ((qB.toNat : Int) - 1074) ≤ 971
      ∧ kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074)
          = kOfMQ mU.toNat ((qB.toNat : Int) - 1074) := by
    refine ⟨?_, ?_, by omega, by omega, edomk⟩
    · exact Nat.pos_of_ne_zero (fun hc => h_m0 (by
        apply UInt64.toNat_inj.mp
        rw [hc]; rfl))
    · have : (1 <<< 53 : Nat) = 2 ^ 53 := by decide
      omega
  have e4 : (-(kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074)) < pow10Table192_kMin) = False :=
    eq_false (show ¬ (-(kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074)) < (-324 : Int)) from by
      omega)
  have e5 : (-(kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074)) > pow10Table192_kMax) = False :=
    eq_false (show ¬ (-(kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074)) > (324 : Int)) from by
      omega)
  have hs_eq : (if h_s_lo : (pow10Table192.getD
          (648 - (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) + 324).toNat)
          pow10Table192_default).2.2.2 - ((qB.toNat : Int) - 1074) < 188 then
        shiftedSig mU.toNat ((qB.toNat : Int) - 1074)
          (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074))
      else if h_s_hi : (pow10Table192.getD
          (648 - (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) + 324).toNat)
          pow10Table192_default).2.2.2 - ((qB.toNat : Int) - 1074) ≥ 256 then
        shiftedSig mU.toNat ((qB.toNat : Int) - 1074)
          (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074))
      else
        (shiftedSig_u192_kernel mU
          (pow10Table192.getD
            (648 - (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) + 324).toNat)
            pow10Table192_default).1
          (pow10Table192.getD
            (648 - (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) + 324).toNat)
            pow10Table192_default).2.1
          (pow10Table192.getD
            (648 - (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) + 324).toNat)
            pow10Table192_default).2.2.1
          ((UInt64.ofNat ((pow10Table192.getD
              (648 - (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) + 324).toNat)
              pow10Table192_default).2.2.2 + 2048).toNat + 4096) - qB - 5070)).toNat)
      = shiftedSig_v3 mU.toNat ((qB.toNat : Int) - 1074)
          (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074)) := by
    rw [shiftedSig_v3_eq, ← shiftedSig_v4_eq,
        ← shiftedSig_v4c_eq mU.toNat ((qB.toNat : Int) - 1074)
          (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074)) hdom]
    simp only [shiftedSig_v4c, e192, e4, e5, dite_false, em]
    by_cases hA1 : (pow10Table192.getD
        (648 - (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) + 324).toNat)
        pow10Table192_default).2.2.2 - ((qB.toNat : Int) - 1074) < 188
    · rw [dif_pos hA1, dif_pos hA1]
    rw [dif_neg hA1, dif_neg hA1]
    by_cases hA2 : (pow10Table192.getD
        (648 - (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) + 324).toNat)
        pow10Table192_default).2.2.2 - ((qB.toNat : Int) - 1074) ≥ 256
    · rw [dif_pos hA2, dif_pos hA2]
    rw [dif_neg hA2, dif_neg hA2]
    have tval := tA_val ((qB.toNat : Int) - 1074) _ h_q_lo' h_q_hi' hh192 hA1 hA2
    rw [eqb] at tval
    rw [tval]
  rw [hs_eq] at hopt
  -- s ≥ 2^57 guard.
  by_cases h_s : shiftedSig_v3 mU.toNat ((qB.toNat : Int) - 1074)
      (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074)) ≥ (1 <<< 57 : Nat)
  · rw [dif_pos h_s] at hopt; cases hopt
  rw [dif_neg h_s] at hopt
  rw [dif_neg h_s]
  push_neg at h_s
  have hs64 : shiftedSig_v3 mU.toNat ((qB.toNat : Int) - 1074)
      (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074)) < 2 ^ 64 := by
    have : (1 <<< 57 : Nat) < 2 ^ 64 := by decide
    omega
  -- sU ≥ 10 ↔ s ≥ 10 and sU = 0 ↔ s = 0.
  have e10 : (UInt64.ofNat (shiftedSig_v3 mU.toNat ((qB.toNat : Int) - 1074)
      (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074))) ≥ (10 : UInt64))
      = (shiftedSig_v3 mU.toNat ((qB.toNat : Int) - 1074)
          (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074)) ≥ 10) := by
    rw [propext (uint64_ge_10 _), uint64_ofNat_toNat_self hs64]
  have e0 : (UInt64.ofNat (shiftedSig_v3 mU.toNat ((qB.toNat : Int) - 1074)
      (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074))) = 0)
      = (shiftedSig_v3 mU.toNat ((qB.toNat : Int) - 1074)
          (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074)) = 0) := by
    rw [propext (uint64_eq_0 _), uint64_ofNat_toNat_self hs64]
  simp only [e10, e0] at hopt
  -- Flipped-block windows.
  have wlt := wB_lt ((qB.toNat : Int) - 1074) _ h_q_lo' h_q_hi' hhflip
  have wgt := wB_gt ((qB.toNat : Int) - 1074) _ h_q_lo' h_q_hi' hhflip
  rw [eqb] at wlt wgt
  simp only [wlt, wgt] at hopt
  -- pickNearer windows.
  have uclt := uBC_lt ((qB.toNat : Int) - 1074) _ h_q_lo' h_q_hi' hhlow
  have ucgt := uBC_gt ((qB.toNat : Int) - 1074) _ h_q_lo' h_q_hi' hhlow
  rw [eqb] at uclt ucgt
  simp only [uclt, ucgt] at hopt
  -- Branch on s ≥ 10.
  by_cases hge10 : shiftedSig_v3 mU.toNat ((qB.toNat : Int) - 1074)
      (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074)) ≥ 10
  · simp only [hge10, if_true] at hopt ⊢
    -- Flipped window guards.
    by_cases hqhlo : -((qB.toNat : Int) - 1074) + (pow10Table128.getD
        (647 - (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) + 324).toNat)
        pow10Table128_default).2.2 < 64
    · rw [dif_pos hqhlo] at hopt; cases hopt
    rw [dif_neg hqhlo] at hopt
    rw [dif_neg hqhlo]
    by_cases hqhhi : -((qB.toNat : Int) - 1074) + (pow10Table128.getD
        (647 - (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) + 324).toNat)
        pow10Table128_default).2.2 > 132
    · rw [dif_pos hqhhi] at hopt; cases hopt
    rw [dif_neg hqhhi] at hopt
    rw [dif_neg hqhhi]
    have wval := wB_val ((qB.toNat : Int) - 1074) _ h_q_lo' h_q_hi' hhflip hqhlo hqhhi
    rw [eqb] at wval
    rw [wval] at hopt
    -- uC guards inside the fall-through.
    by_cases huc1 : ((qB.toNat : Int) - 1074) + (pow10Table128.getD
        ((kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) + 324).toNat)
        pow10Table128_default).2.2 < 64
    · simp only [dif_pos huc1] at hopt ⊢
      exact hopt
    simp only [dif_neg huc1] at hopt ⊢
    by_cases huc2 : ((qB.toNat : Int) - 1074) + (pow10Table128.getD
        ((kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) + 324).toNat)
        pow10Table128_default).2.2 > 132
    · simp only [dif_pos huc2] at hopt ⊢
      exact hopt
    simp only [dif_neg huc2] at hopt ⊢
    have ucval := uBC_val ((qB.toNat : Int) - 1074) _ h_q_lo' h_q_hi' hhlow huc1 huc2
    rw [eqb] at ucval
    rw [ucval] at hopt
    exact hopt
  · simp only [hge10, if_false] at hopt ⊢
    by_cases hs0 : shiftedSig_v3 mU.toNat ((qB.toNat : Int) - 1074)
        (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074)) = 0
    · rw [dif_pos hs0] at hopt; cases hopt
    rw [dif_neg hs0] at hopt
    rw [dif_neg hs0]
    by_cases huc1 : ((qB.toNat : Int) - 1074) + (pow10Table128.getD
        ((kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) + 324).toNat)
        pow10Table128_default).2.2 < 64
    · rw [dif_pos huc1] at hopt; cases hopt
    rw [dif_neg huc1] at hopt
    rw [dif_neg huc1]
    by_cases huc2 : ((qB.toNat : Int) - 1074) + (pow10Table128.getD
        ((kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) + 324).toNat)
        pow10Table128_default).2.2 > 132
    · rw [dif_pos huc2] at hopt; cases hopt
    rw [dif_neg huc2] at hopt
    rw [dif_neg huc2]
    have ucval := uBC_val ((qB.toNat : Int) - 1074) _ h_q_lo' h_q_hi' hhlow huc1 huc2
    rw [eqb] at ucval
    rw [ucval] at hopt
    exact hopt

/-! ## Wrapper, exponent range, emit, entry point -/

/-- v11 entry: same packed fallback as v8/v9. -/
@[inline]
def shortestUnsigned_v11 (mU qB : UInt64) : Nat × Int :=
  match shortestUnsigned_u64_opt_v11 mU qB with
  | some (sU, k) => (sU.toNat, k)
  | none => shortestUnsigned_packed mU.toNat ((qB.toNat : Int) - 1074)

theorem shortestUnsigned_v11_eq_packed (mU qB : UInt64) :
    shortestUnsigned_v11 mU qB
      = shortestUnsigned_packed mU.toNat ((qB.toNat : Int) - 1074) := by
  unfold shortestUnsigned_v11
  match h : shortestUnsigned_u64_opt_v11 mU qB with
  | none => rfl
  | some (sU, k) =>
    exact (shortestUnsigned_u64_opt_flip_some_eq_packed _ _ _ _
      (shortestUnsigned_u64_opt_v11_some_eq_flip mU qB (sU, k) h)).symm

theorem shortestUnsigned_v11_eq_v8 (mU qB : UInt64) :
    shortestUnsigned_v11 mU qB = shortestUnsigned_v8 mU qB := by
  rw [shortestUnsigned_v11_eq_packed, shortestUnsigned_packed_eq,
      ← shortestUnsigned_v5_eq, ← shortestUnsigned_v7_eq_v5,
      ← shortestUnsigned_v8_eq_v7]

set_option maxHeartbeats 1600000 in
/-- Every successful v11 exit carries an exponent in `[-324, 325]`
    (mirror of `shortestUnsigned_u64_opt_v9_k_range`). -/
theorem shortestUnsigned_u64_opt_v11_k_range (mU qB : UInt64)
    (s : UInt64) (k : Int)
    (h : shortestUnsigned_u64_opt_v11 mU qB = some (s, k)) :
    -324 ≤ k ∧ k ≤ 325 := by
  by_cases h1 : mU = 0
  · rw [show shortestUnsigned_u64_opt_v11 mU qB = none from by
      unfold shortestUnsigned_u64_opt_v11; rw [dif_pos h1]] at h
    cases h
  by_cases h2 : mU ≥ (9007199254740992 : UInt64)
  · rw [show shortestUnsigned_u64_opt_v11 mU qB = none from by
      unfold shortestUnsigned_u64_opt_v11; rw [dif_neg h1, dif_pos h2]] at h
    cases h
  by_cases h3 : qB > 2045
  · rw [show shortestUnsigned_u64_opt_v11 mU qB = none from by
      unfold shortestUnsigned_u64_opt_v11; rw [dif_neg h1, dif_neg h2, dif_pos h3]] at h
    cases h
  by_cases h4 : kBOfMQ mU qB > 647
  · rw [show shortestUnsigned_u64_opt_v11 mU qB = none from by
      unfold shortestUnsigned_u64_opt_v11;
        rw [dif_neg h1, dif_neg h2, dif_neg h3, dif_pos h4]] at h
    cases h
  -- Transfer the value to the spec through the chain.
  have hwrap : shortestUnsigned mU.toNat ((qB.toNat : Int) - 1074) = (s.toNat, k) := by
    have h11 : shortestUnsigned_v11 mU qB = (s.toNat, k) := by
      unfold shortestUnsigned_v11
      rw [h]
    rw [← shortestUnsigned_packed_eq, ← shortestUnsigned_v11_eq_packed, h11]
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

/-- `emitTail4` over the v11 kernel. -/
@[inline]
def emitTail5 (sign : Bool) (mU qB : UInt64) : String :=
  if mU = 0 then (if sign then "-0" else "0")
  else
    match shortestUnsigned_u64_opt_v11 mU qB with
    | some (sU, exp) =>
      let sig := sU.toNat
      if sig = 0 then (if sign then "-0" else "0")
      else if sig % 10 ≠ 0 then
        emitCheckedIdx sign sig exp
      else
        let (sig', exp') := PP.Numeric.Decimal.canonicaliseAux sig exp
        if sig' = 0 then (if sign then "-0" else "0")
        else emitChecked sign sig' exp'
    | none =>
      let (sig, exp) := shortestUnsigned_packed mU.toNat ((qB.toNat : Int) - 1074)
      if sig = 0 then (if sign then "-0" else "0")
      else if sig % 10 ≠ 0 then
        emitChecked sign sig exp
      else
        let (sig', exp') := PP.Numeric.Decimal.canonicaliseAux sig exp
        if sig' = 0 then (if sign then "-0" else "0")
        else emitChecked sign sig' exp'

theorem emitTail5_eq (sign : Bool) (mU qB : UInt64) :
    emitTail5 sign mU qB = emitTail2 sign mU qB := by
  unfold emitTail5 emitTail2
  by_cases h0 : mU = 0
  · rw [if_pos h0, if_pos h0]
  rw [if_neg h0, if_neg h0]
  have h8pk : shortestUnsigned_v8 mU qB
      = shortestUnsigned_packed mU.toNat ((qB.toNat : Int) - 1074) := by
    rw [shortestUnsigned_v8_eq_v7, shortestUnsigned_v7_eq_v5, shortestUnsigned_v5_eq,
        ← shortestUnsigned_packed_eq]
  rw [h8pk]
  cases hv : shortestUnsigned_u64_opt_v11 mU qB with
  | none => rfl
  | some p =>
    obtain ⟨sU, exp⟩ := p
    have hpk : shortestUnsigned_packed mU.toNat ((qB.toNat : Int) - 1074)
        = (sU.toNat, exp) :=
      shortestUnsigned_u64_opt_flip_some_eq_packed _ _ _ _
        (shortestUnsigned_u64_opt_v11_some_eq_flip mU qB (sU, exp) hv)
    rw [hpk]
    have hrange := shortestUnsigned_u64_opt_v11_k_range mU qB sU exp hv
    simp only []
    rw [emitCheckedIdx_eq sign sU.toNat exp hrange.1]

/-- `toStringFast6` over the v11 kernel. -/
@[inline]
def toStringFast7 (f : _root_.Float) : String :=
  let bits := f.toBits
  let expBits : UInt64 := (bits >>> 52) &&& 0x7FF
  let mantBits : UInt64 := bits &&& 0x000F_FFFF_FFFF_FFFF
  if expBits = 0x7FF then
    if mantBits ≠ 0 then "NaN"
    else if (bits >>> 63) ≠ 0 then "-Infinity" else "Infinity"
  else
    emitTail5 (decide (bits >>> 63 ≠ 0))
      (if expBits = 0 then mantBits else mantBits + 4503599627370496)
      (if expBits = 0 then 0 else expBits - 1)

theorem toStringFast7_eq (f : _root_.Float) : toStringFast7 f = toStringFast4 f := by
  unfold toStringFast7 toStringFast4
  simp only [emitTail5_eq]

-- Superseded registration: `floatToStrRef_eq_toStringFast8` (KernelV12)
-- is the live @[csimp].
theorem floatToStrRef_eq_toStringFast7 : @floatToStrRef = @toStringFast7 := by
  funext f
  rw [toStringFast7_eq]
  exact congrFun floatToStrRef_eq_toStringFast4 f

end PP.Numeric.Schubfach

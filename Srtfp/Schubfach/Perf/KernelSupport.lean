/- Shared u64/192-bit kernel support for the live `KernelV13` kernel:
   carry-chain 192-bit add/sub/shift, the flipped rounding-interval and
   pick-nearer verdicts, and the biased-index digit emit. Extracted
   verbatim (proofs included) from the superseded KernelV9-V12
   optimization generations when those modules were dropped. -/

import Srtfp.Schubfach.Perf.DigitsFast
import Srtfp.Tactics

open Srtfp.Compat

namespace Srtfp.Schubfach

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
  rw [Int.neg_neg]
  rcases lt_trichotomy q 0 with h | h | h
  · rw [if_neg (show ¬ -q < 0 by omega), if_neg (show ¬ q ≥ 0 by omega)]
  · subst h; simp
  · rw [if_pos (show -q < 0 by omega), if_pos (show q ≥ 0 by omega)]

theorem cmpScaledMixed_flip (a q b k : Int) :
    cmpScaledMixed a q b k = - cmpScaledMixed b (-q) a (-k) := by
  unfold cmpScaledMixed
  simp only [negPos_eq, negNeg_eq]
  exact cmp3_flip' _ _ _ _ (by grind) (by grind)

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
      rw [← Nat.pow_add]
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
      (by omega) hb_nn hb_ne
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

/-- Halve a 192-bit triple (exact when the value is even). -/
@[inline]
def shr1_192 (hi mid lo : UInt64) : UInt64 × UInt64 × UInt64 :=
  (hi >>> 1, (mid >>> 1) + ((hi &&& 1) <<< 63), (lo >>> 1) + ((mid &&& 1) <<< 63))

theorem shr1_192_toNat (hi mid lo : UInt64) :
    triple192Nat (shr1_192 hi mid lo).1 (shr1_192 hi mid lo).2.1
      (shr1_192 hi mid lo).2.2
      = triple192Nat hi mid lo / 2 := by
  unfold shr1_192 triple192Nat
  simp only []
  have h1 := hi.toNat_lt; have h2 := mid.toNat_lt; have h3 := lo.toNat_lt
  have hone : (1 : UInt64) = UInt64.ofNat 1 := rfl
  have h63 : (63 : UInt64) = UInt64.ofNat 63 := rfl
  have e1 : (hi >>> (1 : UInt64)).toNat = hi.toNat / 2 := by
    rw [hone, UInt64_shr_toNat_lt hi 1 (by omega), Nat.pow_one]
  have e2 : (mid >>> (1 : UInt64)).toNat = mid.toNat / 2 := by
    rw [hone, UInt64_shr_toNat_lt mid 1 (by omega), Nat.pow_one]
  have e3 : (lo >>> (1 : UInt64)).toNat = lo.toNat / 2 := by
    rw [hone, UInt64_shr_toNat_lt lo 1 (by omega), Nat.pow_one]
  have a1 : (hi &&& 1).toNat = hi.toNat % 2 := by
    rw [UInt64.toNat_and, show ((1 : UInt64)).toNat = 1 from rfl, Nat.and_one_is_mod]
  have a2 : (mid &&& 1).toNat = mid.toNat % 2 := by
    rw [UInt64.toNat_and, show ((1 : UInt64)).toNat = 1 from rfl, Nat.and_one_is_mod]
  have s1 : ((hi &&& 1) <<< (63 : UInt64)).toNat = (hi.toNat % 2) * 2 ^ 63 := by
    rw [h63, UInt64_shl_toNat_lt _ 63 (by omega), a1]
    exact Nat.mod_eq_of_lt (by omega)
  have s2 : ((mid &&& 1) <<< (63 : UInt64)).toNat = (mid.toNat % 2) * 2 ^ 63 := by
    rw [h63, UInt64_shl_toNat_lt _ 63 (by omega), a2]
    exact Nat.mod_eq_of_lt (by omega)
  have m1 : ((mid >>> (1 : UInt64)) + ((hi &&& 1) <<< (63 : UInt64))).toNat
      = mid.toNat / 2 + (hi.toNat % 2) * 2 ^ 63 := by
    rw [UInt64.toNat_add, e2, s1]
    exact Nat.mod_eq_of_lt (by omega)
  have m2 : ((lo >>> (1 : UInt64)) + ((mid &&& 1) <<< (63 : UInt64))).toNat
      = lo.toNat / 2 + (mid.toNat % 2) * 2 ^ 63 := by
    rw [UInt64.toNat_add, e3, s2]
    exact Nat.mod_eq_of_lt (by omega)
  rw [e1, m1, m2]
  omega

/-- Single flipped verdict: candidate `aU` on the exact-shift side,
    boundary triple (value `bU·G`) on the table side, slack `bU`. -/
@[inline]
def cmpScaledMixed_u64_flipped (lHi lMid lLo bU w8 aU : UInt64) : Int :=
  let (cHi, cMid, cLo) := cmpScaledMixed_u64_L aU w8
  cmpVerdict_u64_inner cHi cMid cLo lHi lMid lLo bU

theorem cmpScaledMixed_u64_flipped_eq (gHi gLo w8 aU bU lHi lMid lLo : UInt64)
    (hv : triple192Nat lHi lMid lLo = bU.toNat * (gHi.toNat * 2 ^ 64 + gLo.toNat))
    (hlt : bU.toNat * (gHi.toNat * 2 ^ 64 + gLo.toNat) < 2 ^ 192) :
    cmpScaledMixed_u64_flipped lHi lMid lLo bU w8 aU
      = cmpScaledMixed_u64 gHi gLo w8 aU bU := by
  obtain ⟨e1, e2, e3⟩ := construction_triple_eq bU gHi gLo lHi lMid lLo hv hlt
  unfold cmpScaledMixed_u64_flipped
  simp only [cmpScaledMixed_u64_eq_cmpVerdict]
  obtain ⟨cHi, cMid, cLo⟩ := cmpScaledMixed_u64_L aU w8
  simp only []
  rw [e1, e2, e3]

/-- Flipped `pickNearer`: same dispatch as `pickNearer_u64_opt`, with the
    interval tests through `inRoundingInterval_u64_flipped_u8` and the
    midpoint verdict against the halved boundary product `2m·g″`. -/
@[inline]
def pickNearer_u64_flipped
    (lLHi lLMid lLLo leftU lRHi lRMid lRLo rightU : UInt64)
    (mHHi mHMid mHLo twoM : UInt64)
    (w8 sU : UInt64) : Option UInt64 :=
  let uV := inRoundingInterval_u64_flipped_u8 lLHi lLMid lLLo leftU
              lRHi lRMid lRLo rightU w8 sU
  if uV = inRoundingInterval_u8_AMBIG then none
  else
    let wV := inRoundingInterval_u64_flipped_u8 lLHi lLMid lLLo leftU
                lRHi lRMid lRLo rightU w8 (sU + 1)
    if wV = inRoundingInterval_u8_AMBIG then none
    else
      let uIn : Bool := uV = inRoundingInterval_u8_TRUE
      let wIn : Bool := wV = inRoundingInterval_u8_TRUE
      if uIn && !wIn then some sU
      else if !uIn && wIn then some (sU + 1)
      else
        let cmpMf := cmpScaledMixed_u64_flipped mHHi mHMid mHLo twoM w8 ((sU <<< 1) + 1)
        if cmpMf = 0 then none
        else if (0 : Int) < cmpMf then some sU
        else some (sU + 1)

set_option maxHeartbeats 3200000 in

set_option maxHeartbeats 3200000 in
/-- Bridging for the flipped `pickNearer`: a `some` verdict decides the
    spec `pickNearer` at exponent `k'`. Interval legs through
    `inRoundingInterval_u64_flipped_u8_some_eq`, midpoint through the
    flip identity (note the sign: `cmpMf > 0 ⟺ spec cmp < 0`). -/
theorem pickNearer_u64_flipped_some_eq
    (q k' : Int) (s m : Nat) (irregular : Bool) (chosen : UInt64)
    (lLHi lLMid lLLo lRHi lRMid lRLo mHHi mHMid mHLo : UInt64)
    (hm_pos : m ≥ 1) (hs_pos : s ≥ 1)
    (hm_lt : m < (1 <<< 58 : Nat)) (hs_lt : s < (1 <<< 57 : Nat))
    (hk_lo : pow10Table128_kMin ≤ -k') (hk_hi : -k' ≤ pow10Table128_kMax)
    (hqh_lo : 64 ≤ -q + (pow10Lookup128 (-k')).2.2)
    (hqh_hi : -q + (pow10Lookup128 (-k')).2.2 ≤ 132)
    (hirr_eq : irregular = isIrregular m q)
    (hL_val : triple192Nat lLHi lLMid lLLo
      = (if irregular then 4 * m - 1 else 4 * m - 2)
          * ((pow10Lookup128 (-k')).1.toNat * 2 ^ 64 + (pow10Lookup128 (-k')).2.1.toNat))
    (hR_val : triple192Nat lRHi lRMid lRLo
      = (4 * m + 2)
          * ((pow10Lookup128 (-k')).1.toNat * 2 ^ 64 + (pow10Lookup128 (-k')).2.1.toNat))
    (hM_val : triple192Nat mHHi mHMid mHLo
      = (2 * m)
          * ((pow10Lookup128 (-k')).1.toNat * 2 ^ 64 + (pow10Lookup128 (-k')).2.1.toNat))
    (hopt : pickNearer_u64_flipped lLHi lLMid lLLo
              (if irregular then (UInt64.ofNat m) <<< 2 - 1 else (UInt64.ofNat m) <<< 2 - 2)
              lRHi lRMid lRLo ((UInt64.ofNat m) <<< 2 + 2)
              mHHi mHMid mHLo ((UInt64.ofNat m) <<< 1)
              (UInt64.ofNat (-q + (pow10Lookup128 (-k')).2.2).toNat) (UInt64.ofNat s)
            = some chosen) :
    pickNearer s k' m q = chosen.toNat := by
  have hs_lt58 : s < (1 <<< 58 : Nat) := by
    have : (1 <<< 57 : Nat) ≤ (1 <<< 58 : Nat) := by decide
    omega
  set gHi : UInt64 := (pow10Lookup128 (-k')).1 with hgHi_def
  set gLo : UInt64 := (pow10Lookup128 (-k')).2.1 with hgLo_def
  set wPlusH : Int := -q + (pow10Lookup128 (-k')).2.2 with hwPlusH_def
  set w8 : UInt64 := UInt64.ofNat wPlusH.toNat with hw8_def
  set sU : UInt64 := UInt64.ofNat s with hsU_def
  set mU : UInt64 := UInt64.ofNat m with hmU_def
  unfold pickNearer_u64_flipped at hopt
  simp only [] at hopt
  -- uV leg.
  by_cases hA1 : inRoundingInterval_u64_flipped_u8 lLHi lLMid lLLo
      (if irregular then mU <<< 2 - 1 else mU <<< 2 - 2)
      lRHi lRMid lRLo (mU <<< 2 + 2) w8 sU = inRoundingInterval_u8_AMBIG
  · rw [if_pos hA1] at hopt; cases hopt
  rw [if_neg hA1] at hopt
  have huV := inRoundingInterval_u64_flipped_u8_some_eq q k' s m irregular
    lLHi lLMid lLLo lRHi lRMid lRLo
    hm_pos hs_pos hm_lt hs_lt58 hk_lo hk_hi hqh_lo hqh_hi hL_val hR_val hA1
  -- wV leg (normalise sU + 1).
  have hs1_eq : sU + 1 = UInt64.ofNat (s + 1) := by
    rw [hsU_def, ← ofNat_succ]
  rw [hs1_eq] at hopt
  by_cases hA2 : inRoundingInterval_u64_flipped_u8 lLHi lLMid lLLo
      (if irregular then mU <<< 2 - 1 else mU <<< 2 - 2)
      lRHi lRMid lRLo (mU <<< 2 + 2) w8 (UInt64.ofNat (s + 1)) = inRoundingInterval_u8_AMBIG
  · rw [if_pos hA2] at hopt; cases hopt
  rw [if_neg hA2] at hopt
  have hwV := inRoundingInterval_u64_flipped_u8_some_eq q k' (s + 1) m irregular
    lLHi lLMid lLLo lRHi lRMid lRLo
    hm_pos (by omega) hm_lt (by
      have : (1 <<< 57 : Nat) + 1 ≤ (1 <<< 58 : Nat) := by decide
      omega) hk_lo hk_hi hqh_lo hqh_hi hL_val hR_val hA2
  -- Spec side.
  unfold pickNearer
  simp only []
  rw [← hirr_eq, huV, hwV]
  simp only [← hwPlusH_def, ← hw8_def, ← hsU_def, ← hmU_def]
  -- Midpoint machinery (used in the TT/FF cases).
  have hG_lt : gHi.toNat * 2 ^ 64 + gLo.toNat < 2 ^ 128 := by
    have h1 := gHi.toNat_lt; have h2 := gLo.toNat_lt
    omega
  have h2m_corr : UInt64.ofNat (2 * m) = mU <<< 1 := ofNat_2m m
  have h2m_toNat : (mU <<< 1).toNat = 2 * m := by
    rw [← h2m_corr]
    apply toNat_ofNat_bounded
    have : (1 <<< 58 : Nat) < 2 ^ 63 := by decide
    omega
  have hM_val' : triple192Nat mHHi mHMid mHLo
      = (mU <<< 1).toNat * (gHi.toNat * 2 ^ 64 + gLo.toNat) := by
    rw [h2m_toNat]; exact hM_val
  have hM_lt : (mU <<< 1).toNat * (gHi.toNat * 2 ^ 64 + gLo.toNat) < 2 ^ 192 := by
    rw [h2m_toNat]
    have h3 : 2 * m * (gHi.toNat * 2 ^ 64 + gLo.toNat) ≤ 2 ^ 60 * 2 ^ 128 :=
      Nat.mul_le_mul (by omega) (by omega)
    have h4 : (2 : Nat) ^ 60 * 2 ^ 128 < 2 ^ 192 := by
      rw [← Nat.pow_add]
      exact Nat.pow_lt_pow_right (by omega) (by omega)
    omega
  have hmid_id := cmpScaledMixed_u64_flipped_eq gHi gLo w8 ((sU <<< 1) + 1) (mU <<< 1)
    mHHi mHMid mHLo hM_val' hM_lt
  -- Spec midpoint from a strict flipped verdict.
  have hmI1 : (1 : Int) ≤ (m : Int) := by exact_mod_cast hm_pos
  have h60_lit : (1 <<< 60 : Int) = 1152921504606846976 := by decide
  have hm_ltI : (m : Int) < 288230376151711744 := by
    have : (m : Int) < ((1 <<< 58 : Nat) : Int) := by exact_mod_cast hm_lt
    have heq : ((1 <<< 58 : Nat) : Int) = 288230376151711744 := by decide
    omega
  have hs_ltI : (s : Int) < 144115188075855872 := by
    have : (s : Int) < ((1 <<< 57 : Nat) : Int) := by exact_mod_cast hs_lt
    have heq : ((1 <<< 57 : Nat) : Int) = 144115188075855872 := by decide
    omega
  have h2s1_corr : UInt64.ofNat ((2 * (s : Int) + 1).toNat) = (sU <<< 1) + 1 := by
    rw [toNat_2s_add_1_eq s]
    rw [hsU_def]
    exact ofNat_2s_add_1 s
  have h2m_corrI : UInt64.ofNat ((2 * (m : Int)).toNat) = mU <<< 1 := by
    rw [toNat_2m_eq m]
    rw [hmU_def]
    exact ofNat_2m m
  have hmid_spec : ∀ (hne : cmpScaledMixed_u64 gHi gLo w8 ((sU <<< 1) + 1) (mU <<< 1) ≠ 0),
      cmpScaledMixed (2 * (m : Int)) q (2 * (s : Int) + 1) k'
        = - cmpScaledMixed_u64 gHi gLo w8 ((sU <<< 1) + 1) (mU <<< 1) := by
    intro hne
    have h1 := cmpScaledMixed_packed_eq_u64_of_strict (-q) (-k') gHi gLo wPlusH
      (2 * (s : Int) + 1) (2 * (m : Int))
      (by omega) (by omega) (by omega)
      (by rw [h60_lit]; omega) (by rw [h60_lit]; omega)
      hk_lo hk_hi hqh_lo hqh_hi
      (by rw [h2s1_corr, h2m_corrI]; exact hne)
    rw [h2s1_corr, h2m_corrI] at h1
    have h2 : cmpScaledMixed (2 * (s : Int) + 1) (-q) (2 * (m : Int)) (-k')
        = cmpScaledMixed_u64 gHi gLo w8 ((sU <<< 1) + 1) (mU <<< 1) := by
      rw [← h1, hwPlusH_def, hgHi_def, hgLo_def]
      exact (cmpScaledMixed_packed_eq (2 * (s : Int) + 1) (-q) (2 * (m : Int)) (-k')).symm
    rw [cmpScaledMixed_flip (2 * (m : Int)) q (2 * (s : Int) + 1) k', h2]
  -- Verdict range for the midpoint.
  have hrange : cmpScaledMixed_u64 gHi gLo w8 ((sU <<< 1) + 1) (mU <<< 1) = 1
      ∨ cmpScaledMixed_u64 gHi gLo w8 ((sU <<< 1) + 1) (mU <<< 1) = -1
      ∨ cmpScaledMixed_u64 gHi gLo w8 ((sU <<< 1) + 1) (mU <<< 1) = 0 := by
    rw [cmpScaledMixed_u64_eq_cmpVerdict]
    exact cmpVerdict_u64_inner_range _ _ _ _ _ _ _
  -- The shared midpoint dispatcher.
  have hmidDispatch : ∀ (hbranch :
      (if cmpScaledMixed_u64_flipped mHHi mHMid mHLo (mU <<< 1) w8 ((sU <<< 1) + 1) = 0
       then (none : Option UInt64)
       else if (0 : Int) < cmpScaledMixed_u64_flipped mHHi mHMid mHLo (mU <<< 1) w8 ((sU <<< 1) + 1)
       then some sU
       else some (UInt64.ofNat (s + 1))) = some chosen),
      (if cmpScaledMixed (2 * (m : Int)) q (2 * (s : Int) + 1) k' < 0 then s
       else if cmpScaledMixed (2 * (m : Int)) q (2 * (s : Int) + 1) k' > 0 then s + 1
       else if s % 2 = 0 then s else s + 1) = chosen.toNat := by
    intro hbranch
    rw [hmid_id] at hbranch
    by_cases h0 : cmpScaledMixed_u64 gHi gLo w8 ((sU <<< 1) + 1) (mU <<< 1) = 0
    · rw [if_pos h0] at hbranch; cases hbranch
    rw [if_neg h0] at hbranch
    have hspec := hmid_spec h0
    rcases hrange with h1 | h1 | h1
    · -- verdict 1: kernel takes `some sU`; spec cmp = -1 < 0 takes `s`.
      rw [if_pos (show (0 : Int) < cmpScaledMixed_u64 gHi gLo w8 ((sU <<< 1) + 1) (mU <<< 1)
            from by rw [h1]; omega)] at hbranch
      rw [if_pos (show cmpScaledMixed (2 * (m : Int)) q (2 * (s : Int) + 1) k' < 0
            from by rw [hspec, h1]; omega)]
      have hch : sU = chosen := Option.some.inj hbranch
      rw [← hch, hsU_def]
      exact (toNat_sU_eq hs_lt58).symm
    · -- verdict -1: kernel takes `some (s+1)`; spec cmp = 1 > 0 takes `s+1`.
      rw [if_neg (show ¬ (0 : Int) < cmpScaledMixed_u64 gHi gLo w8 ((sU <<< 1) + 1) (mU <<< 1)
            from by rw [h1]; omega)] at hbranch
      rw [if_neg (show ¬ cmpScaledMixed (2 * (m : Int)) q (2 * (s : Int) + 1) k' < 0
            from by rw [hspec, h1]; omega),
          if_pos (show cmpScaledMixed (2 * (m : Int)) q (2 * (s : Int) + 1) k' > 0
            from by rw [hspec, h1]; omega)]
      have hch : UInt64.ofNat (s + 1) = chosen := Option.some.inj hbranch
      rw [← hch]
      exact (toNat_ofNat_bounded (show s + 1 < 2 ^ 64 from by
        have : (1 <<< 58 : Nat) < 2 ^ 64 := by decide
        omega)).symm
    · exact absurd h1 h0
  -- Four-way dispatch on the two interval verdicts.
  by_cases hUT : inRoundingInterval_u64_flipped_u8 lLHi lLMid lLLo
      (if irregular then mU <<< 2 - 1 else mU <<< 2 - 2)
      lRHi lRMid lRLo (mU <<< 2 + 2) w8 sU = inRoundingInterval_u8_TRUE
  · have hu : decide (inRoundingInterval_u64_flipped_u8 lLHi lLMid lLLo
        (if irregular then mU <<< 2 - 1 else mU <<< 2 - 2)
        lRHi lRMid lRLo (mU <<< 2 + 2) w8 sU = inRoundingInterval_u8_TRUE) = true :=
      decide_eq_true hUT
    by_cases hWT : inRoundingInterval_u64_flipped_u8 lLHi lLMid lLLo
        (if irregular then mU <<< 2 - 1 else mU <<< 2 - 2)
        lRHi lRMid lRLo (mU <<< 2 + 2) w8 (UInt64.ofNat (s + 1)) = inRoundingInterval_u8_TRUE
    · have hw : decide (inRoundingInterval_u64_flipped_u8 lLHi lLMid lLLo
          (if irregular then mU <<< 2 - 1 else mU <<< 2 - 2)
          lRHi lRMid lRLo (mU <<< 2 + 2) w8 (UInt64.ofNat (s + 1)) = inRoundingInterval_u8_TRUE)
          = true := decide_eq_true hWT
      simp only [hu, hw, Bool.not_true, Bool.and_false, Bool.false_and,
        Bool.false_eq_true, if_false] at hopt ⊢
      exact hmidDispatch hopt
    · have hw : decide (inRoundingInterval_u64_flipped_u8 lLHi lLMid lLLo
          (if irregular then mU <<< 2 - 1 else mU <<< 2 - 2)
          lRHi lRMid lRLo (mU <<< 2 + 2) w8 (UInt64.ofNat (s + 1)) = inRoundingInterval_u8_TRUE)
          = false := decide_eq_false hWT
      simp only [hu, hw, Bool.not_false, Bool.and_true, 
        if_true] at hopt ⊢
      have hch : sU = chosen := Option.some.inj hopt
      rw [← hch, hsU_def]
      exact (toNat_sU_eq hs_lt58).symm
  · have hu : decide (inRoundingInterval_u64_flipped_u8 lLHi lLMid lLLo
        (if irregular then mU <<< 2 - 1 else mU <<< 2 - 2)
        lRHi lRMid lRLo (mU <<< 2 + 2) w8 sU = inRoundingInterval_u8_TRUE) = false :=
      decide_eq_false hUT
    by_cases hWT : inRoundingInterval_u64_flipped_u8 lLHi lLMid lLLo
        (if irregular then mU <<< 2 - 1 else mU <<< 2 - 2)
        lRHi lRMid lRLo (mU <<< 2 + 2) w8 (UInt64.ofNat (s + 1)) = inRoundingInterval_u8_TRUE
    · have hw : decide (inRoundingInterval_u64_flipped_u8 lLHi lLMid lLLo
          (if irregular then mU <<< 2 - 1 else mU <<< 2 - 2)
          lRHi lRMid lRLo (mU <<< 2 + 2) w8 (UInt64.ofNat (s + 1)) = inRoundingInterval_u8_TRUE)
          = true := decide_eq_true hWT
      simp only [hu, hw, Bool.not_true, Bool.not_false, Bool.and_true,
        Bool.and_false, Bool.false_eq_true, if_false, if_true] at hopt ⊢
      have hch : UInt64.ofNat (s + 1) = chosen := Option.some.inj hopt
      rw [← hch]
      exact (toNat_ofNat_bounded (show s + 1 < 2 ^ 64 from by
        have : (1 <<< 58 : Nat) < 2 ^ 64 := by decide
        omega)).symm
    · have hw : decide (inRoundingInterval_u64_flipped_u8 lLHi lLMid lLLo
          (if irregular then mU <<< 2 - 1 else mU <<< 2 - 2)
          lRHi lRMid lRLo (mU <<< 2 + 2) w8 (UInt64.ofNat (s + 1)) = inRoundingInterval_u8_TRUE)
          = false := decide_eq_false hWT
      simp only [hu, hw, Bool.not_false, Bool.and_false, Bool.and_true,
        Bool.false_eq_true, if_false] at hopt ⊢
      exact hmidDispatch hopt

/-- Index transfer for the flipped `k` table entry: exponent `-k` lives
    at biased index `648 - kB`. Mirrors `lookup128_negHigh`. -/
theorem lookup128_neg (k : Int) (hlo : ¬ k < pow10Table128_kMin)
    (hhi : ¬ k + 1 > pow10Table128_kMax) :
    pow10Lookup128 (-k)
      = pow10Table128.getD (648 - (k + 324).toNat) pow10Table128_default := by
  have hlo' : ¬ k < (-324 : Int) := hlo
  have hhi' : ¬ k + 1 > (324 : Int) := hhi
  have hidx : (-k + 324).toNat = 648 - (k + 324).toNat := by omega
  unfold pow10Lookup128
  rw [if_neg (show ¬ (-k < pow10Table128_kMin) from
        fun hc => absurd (show -k < -324 from hc) (by omega)),
      hidx]

end Srtfp.Schubfach

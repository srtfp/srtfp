/- v12 — the pickNearer path flipped.

   The fall-through tests at exponent `k` get the v11 treatment: one
   product `P₂ = 4m·g″` (`g″ =` pow10 entry for `-k`), boundary
   products by 192-bit add/sub shared across the `uIn`/`wIn` tests,
   and the midpoint comparison `2m·2^q ⋚ (2s+1)·10^k` flipped with
   the boundary product `2m·g″ = P₂/2` obtained by an exact halving.
   This removes the last per-candidate wide multiplies (the old path
   paid fresh `s4·G` products per test plus a `(2s+1)·G` midpoint
   product) and the `q+h` biased windows at the `k` entry. -/

import Srtfp.Numeric.Schubfach.Perf.KernelV11

namespace PP.Numeric.Schubfach

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
    rw [hone, UInt64_shr_toNat_lt hi 1 (by omega), pow_one]
  have e2 : (mid >>> (1 : UInt64)).toNat = mid.toNat / 2 := by
    rw [hone, UInt64_shr_toNat_lt mid 1 (by omega), pow_one]
  have e3 : (lo >>> (1 : UInt64)).toNat = lo.toNat / 2 := by
    rw [hone, UInt64_shr_toNat_lt lo 1 (by omega), pow_one]
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
      rw [← pow_add]
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

/-- `shortestUnsigned_u64_opt_flip` with the pickNearer path flipped
    too: one product per table entry, all tests on shared boundary
    triples, midpoint by exact halving. Base-level (spec-table) kernel with the Giulietti-style flipped
    `k+1` interval tests: one boundary product `P = 4m·g'` per decode,
    boundary products derived by 192-bit add/sub, candidate on the
    exact-shift side, shared across the `uV`/`wV` tests. Everything
    else matches `shortestUnsigned_u64_opt`. -/
@[inline]
def shortestUnsigned_u64_opt_flip2 (m : Nat) (q : Int) : Option (UInt64 × Int) :=
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
              let gT2 := pow10Lookup128 (-k)
              let w2PlusH : Int := -q + gT2.2.2
              if _h_qh2_lo : w2PlusH < 64 then none
              else if _h_qh2_hi : w2PlusH > 132 then none
              else
                let w28 : UInt64 := UInt64.ofNat w2PlusH.toNat
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
                match pickNearer_u64_flipped lB2.1 lB2.2.1 lB2.2.2 leftU
                        rB2.1 rB2.2.1 rB2.2.2 rightU mH.1 mH.2.1 mH.2.2 twoM w28 sU with
                | none => none
                | some chosen => some (chosen, k)
      else if _h_s1 : s = 0 then none
      else
        let gT2 := pow10Lookup128 (-k)
        let w2PlusH : Int := -q + gT2.2.2
        if _h_qh2_lo : w2PlusH < 64 then none
        else if _h_qh2_hi : w2PlusH > 132 then none
        else
          let w28 : UInt64 := UInt64.ofNat w2PlusH.toNat
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
          match pickNearer_u64_flipped lB2.1 lB2.2.1 lB2.2.2 leftU
                  rB2.1 rB2.2.1 rB2.2.2 rightU mH.1 mH.2.1 mH.2.2 twoM w28 sU with
          | none => none
          | some chosen => some (chosen, k)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 3200000 in
/-- Fast-path correctness for the flipped kernel: a `some` result is
    the `shortestUnsigned_packed` (= spec) value. -/
theorem shortestUnsigned_u64_opt_flip2_some_eq_packed
    (m : Nat) (q : Int) (sUo : UInt64) (ko : Int)
    (hopt : shortestUnsigned_u64_opt_flip2 m q = some (sUo, ko)) :
    shortestUnsigned_packed m q = (sUo.toNat, ko) := by
  rw [shortestUnsigned_packed_eq]
  show shortestUnsigned m q = (sUo.toNat, ko)
  unfold shortestUnsigned_u64_opt_flip2 at hopt
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
    by_cases hqh2_lo : -q + (pow10Lookup128 (-(kOfMQ m q))).2.2 < 64
    · rw [dif_pos hqh2_lo] at hopt; cases hopt
    rw [dif_neg hqh2_lo] at hopt
    by_cases hqh2_hi : -q + (pow10Lookup128 (-(kOfMQ m q))).2.2 > 132
    · rw [dif_pos hqh2_hi] at hopt; cases hopt
    rw [dif_neg hqh2_hi] at hopt
    push_neg at hqh2_lo hqh2_hi
    set gT2 := pow10Lookup128 (-(kOfMQ m q)) with hgT2
    set pLo2 : UInt64 := m4 * gT2.2.1 with hpLo2
    set pLoH2 : UInt64 := mulHi64 m4 gT2.2.1 with hpLoH2
    set pHi2 : UInt64 := m4 * gT2.1 with hpHi2
    set pHiH2 : UInt64 := mulHi64 m4 gT2.1 with hpHiH2
    set pMid2 : UInt64 := pHi2 + pLoH2 with hpMid2
    set pC2 : UInt64 := (if pMid2 < pHi2 then (1 : UInt64) else 0) with hpC2
    set pH2 : UInt64 := pHiH2 + pC2 with hpH2
    set tg2 := add192_192 0 gT2.1 gT2.2.1 0 gT2.1 gT2.2.1 with htg2
    set sbHi2 : UInt64 := (if isIrregular m q = true then 0 else tg2.1) with hsbHi2
    set sbMid2 : UInt64 := (if isIrregular m q = true then gT2.1 else tg2.2.1) with hsbMid2
    set sbLo2 : UInt64 := (if isIrregular m q = true then gT2.2.1 else tg2.2.2) with hsbLo2
    set lB2 := sub192_192 pH2 pMid2 pLo2 sbHi2 sbMid2 sbLo2 with hlB2
    set rB2 := add192_192 pH2 pMid2 pLo2 tg2.1 tg2.2.1 tg2.2.2 with hrB2
    set mH2 := shr1_192 pH2 pMid2 pLo2 with hmH2
    have hG2_lt : gT2.1.toNat * 2 ^ 64 + gT2.2.1.toNat < 2 ^ 128 := by
      have h1 := gT2.1.toNat_lt; have h2 := gT2.2.1.toNat_lt
      omega
    have hmulG2_lt : ∀ b : Nat, b ≤ 4 * m + 2 →
        b * (gT2.1.toNat * 2 ^ 64 + gT2.2.1.toNat) < 2 ^ 192 := by
      intro b hb
      have h3 : b * (gT2.1.toNat * 2 ^ 64 + gT2.2.1.toNat) ≤ 2 ^ 60 * 2 ^ 128 :=
        Nat.mul_le_mul (by omega) (by omega)
      have h4 : (2 : Nat) ^ 60 * 2 ^ 128 < 2 ^ 192 := by
        rw [← pow_add]
        exact Nat.pow_lt_pow_right (by omega) (by omega)
      omega
    have htrip0G2 : triple192Nat 0 gT2.1 gT2.2.1
        = gT2.1.toNat * 2 ^ 64 + gT2.2.1.toNat := by
      unfold triple192Nat
      simp only [show ((0 : UInt64)).toNat = 0 from rfl]
      omega
    have hP2_val : triple192Nat pH2 pMid2 pLo2
        = 4 * m * (gT2.1.toNat * 2 ^ 64 + gT2.2.1.toNat) := by
      have h := mul192_b_g_toNat m4 gT2.1 gT2.2.1
      simp only [] at h
      rw [← hpLo2, ← hpLoH2, ← hpHi2, ← hpHiH2, ← hpMid2, ← hpC2, ← hpH2] at h
      rw [hm4_toNat, Nat.mod_eq_of_lt (hmulG2_lt (4 * m) (by omega))] at h
      exact h
    have h2G2_val : triple192Nat tg2.1 tg2.2.1 tg2.2.2
        = 2 * (gT2.1.toNat * 2 ^ 64 + gT2.2.1.toNat) := by
      rw [htg2, add192_192_toNat 0 gT2.1 gT2.2.1 0 gT2.1 gT2.2.1 (by
        rw [htrip0G2]; omega), htrip0G2]
      omega
    have hlB2_val : triple192Nat lB2.1 lB2.2.1 lB2.2.2
        = (if isIrregular m q = true then 4 * m - 1 else 4 * m - 2)
            * (gT2.1.toNat * 2 ^ 64 + gT2.2.1.toNat) := by
      rw [hlB2, hsbHi2, hsbMid2, hsbLo2]
      by_cases hirr : isIrregular m q = true
      · rw [if_pos hirr, if_pos hirr, if_pos hirr, if_pos hirr,
            sub192_192_toNat pH2 pMid2 pLo2 0 gT2.1 gT2.2.1 (by
              rw [htrip0G2, hP2_val]
              exact Nat.le_mul_of_pos_left _ (by omega)),
            hP2_val, htrip0G2, Nat.sub_mul, Nat.one_mul]
      · rw [if_neg hirr, if_neg hirr, if_neg hirr, if_neg hirr,
            sub192_192_toNat pH2 pMid2 pLo2 tg2.1 tg2.2.1 tg2.2.2 (by
              rw [h2G2_val, hP2_val]
              exact Nat.mul_le_mul_right _ (by omega)),
            hP2_val, h2G2_val, Nat.sub_mul]
    have hrB2_val : triple192Nat rB2.1 rB2.2.1 rB2.2.2
        = (4 * m + 2) * (gT2.1.toNat * 2 ^ 64 + gT2.2.1.toNat) := by
      rw [hrB2, add192_192_toNat pH2 pMid2 pLo2 tg2.1 tg2.2.1 tg2.2.2 (by
            rw [hP2_val, h2G2_val]
            have := hmulG2_lt (4 * m + 2) (by omega)
            rw [Nat.add_mul] at this
            omega),
          hP2_val, h2G2_val, Nat.add_mul]
    have hmH2_val : triple192Nat mH2.1 mH2.2.1 mH2.2.2
        = 2 * m * (gT2.1.toNat * 2 ^ 64 + gT2.2.1.toNat) := by
      rw [hmH2, shr1_192_toNat, hP2_val,
          show 4 * m * (gT2.1.toNat * 2 ^ 64 + gT2.2.1.toNat)
              = 2 * (2 * m * (gT2.1.toNat * 2 ^ 64 + gT2.2.1.toNat)) from by ring,
          Nat.mul_div_cancel_left _ (by omega)]
    have hk_lo2 : pow10Table128_kMin ≤ -(kOfMQ m q) := by omega
    have hk_hi2 : -(kOfMQ m q) ≤ pow10Table128_kMax := by omega
    match hp : pickNearer_u64_flipped lB2.1 lB2.2.1 lB2.2.2 leftU
                 rB2.1 rB2.2.1 rB2.2.2 (m4 + 2) mH2.1 mH2.2.1 mH2.2.2
                 (UInt64.ofNat m <<< 1)
                 (UInt64.ofNat (-q + gT2.2.2).toNat)
                 (UInt64.ofNat (shiftedSig m q (kOfMQ m q))) with
    | none => rw [hp] at hopt; cases hopt
    | some chosen =>
      rw [hp] at hopt
      have hpkd : pickNearer (shiftedSig m q (kOfMQ m q)) (kOfMQ m q) m q = chosen.toNat :=
        pickNearer_u64_flipped_some_eq q (kOfMQ m q) (shiftedSig m q (kOfMQ m q)) m
          (isIrregular m q) chosen lB2.1 lB2.2.1 lB2.2.2 rB2.1 rB2.2.1 rB2.2.2
          mH2.1 mH2.2.1 mH2.2.2
          hm_pos (by omega) hm_lt hs_ge hk_lo2 hk_hi2 hqh2_lo hqh2_hi rfl
          hlB2_val hrB2_val hmH2_val hp
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
    by_cases hqh2_lo : -q + (pow10Lookup128 (-(kOfMQ m q))).2.2 < 64
    · rw [dif_pos hqh2_lo] at hopt; cases hopt
    rw [dif_neg hqh2_lo] at hopt
    by_cases hqh2_hi : -q + (pow10Lookup128 (-(kOfMQ m q))).2.2 > 132
    · rw [dif_pos hqh2_hi] at hopt; cases hopt
    rw [dif_neg hqh2_hi] at hopt
    push_neg at hqh2_lo hqh2_hi
    set gT2 := pow10Lookup128 (-(kOfMQ m q)) with hgT2
    set m4 : UInt64 := UInt64.ofNat m <<< 2 with hm4
    set leftU : UInt64 := (if isIrregular m q = true then m4 - 1 else m4 - 2) with hleftU
    have hm4_toNat : m4.toNat = 4 * m := by
      rw [hm4, uint64_shiftLeft_2, UInt64.toNat_mul,
          toNat_ofNat_bounded (show m < 2 ^ 64 by omega),
          show ((4 : UInt64)).toNat = 4 from rfl]
      exact Nat.mod_eq_of_lt (by omega)
    set pLo2 : UInt64 := m4 * gT2.2.1 with hpLo2
    set pLoH2 : UInt64 := mulHi64 m4 gT2.2.1 with hpLoH2
    set pHi2 : UInt64 := m4 * gT2.1 with hpHi2
    set pHiH2 : UInt64 := mulHi64 m4 gT2.1 with hpHiH2
    set pMid2 : UInt64 := pHi2 + pLoH2 with hpMid2
    set pC2 : UInt64 := (if pMid2 < pHi2 then (1 : UInt64) else 0) with hpC2
    set pH2 : UInt64 := pHiH2 + pC2 with hpH2
    set tg2 := add192_192 0 gT2.1 gT2.2.1 0 gT2.1 gT2.2.1 with htg2
    set sbHi2 : UInt64 := (if isIrregular m q = true then 0 else tg2.1) with hsbHi2
    set sbMid2 : UInt64 := (if isIrregular m q = true then gT2.1 else tg2.2.1) with hsbMid2
    set sbLo2 : UInt64 := (if isIrregular m q = true then gT2.2.1 else tg2.2.2) with hsbLo2
    set lB2 := sub192_192 pH2 pMid2 pLo2 sbHi2 sbMid2 sbLo2 with hlB2
    set rB2 := add192_192 pH2 pMid2 pLo2 tg2.1 tg2.2.1 tg2.2.2 with hrB2
    set mH2 := shr1_192 pH2 pMid2 pLo2 with hmH2
    have hG2_lt : gT2.1.toNat * 2 ^ 64 + gT2.2.1.toNat < 2 ^ 128 := by
      have h1 := gT2.1.toNat_lt; have h2 := gT2.2.1.toNat_lt
      omega
    have hmulG2_lt : ∀ b : Nat, b ≤ 4 * m + 2 →
        b * (gT2.1.toNat * 2 ^ 64 + gT2.2.1.toNat) < 2 ^ 192 := by
      intro b hb
      have h3 : b * (gT2.1.toNat * 2 ^ 64 + gT2.2.1.toNat) ≤ 2 ^ 60 * 2 ^ 128 :=
        Nat.mul_le_mul (by omega) (by omega)
      have h4 : (2 : Nat) ^ 60 * 2 ^ 128 < 2 ^ 192 := by
        rw [← pow_add]
        exact Nat.pow_lt_pow_right (by omega) (by omega)
      omega
    have htrip0G2 : triple192Nat 0 gT2.1 gT2.2.1
        = gT2.1.toNat * 2 ^ 64 + gT2.2.1.toNat := by
      unfold triple192Nat
      simp only [show ((0 : UInt64)).toNat = 0 from rfl]
      omega
    have hP2_val : triple192Nat pH2 pMid2 pLo2
        = 4 * m * (gT2.1.toNat * 2 ^ 64 + gT2.2.1.toNat) := by
      have h := mul192_b_g_toNat m4 gT2.1 gT2.2.1
      simp only [] at h
      rw [← hpLo2, ← hpLoH2, ← hpHi2, ← hpHiH2, ← hpMid2, ← hpC2, ← hpH2] at h
      rw [hm4_toNat, Nat.mod_eq_of_lt (hmulG2_lt (4 * m) (by omega))] at h
      exact h
    have h2G2_val : triple192Nat tg2.1 tg2.2.1 tg2.2.2
        = 2 * (gT2.1.toNat * 2 ^ 64 + gT2.2.1.toNat) := by
      rw [htg2, add192_192_toNat 0 gT2.1 gT2.2.1 0 gT2.1 gT2.2.1 (by
        rw [htrip0G2]; omega), htrip0G2]
      omega
    have hlB2_val : triple192Nat lB2.1 lB2.2.1 lB2.2.2
        = (if isIrregular m q = true then 4 * m - 1 else 4 * m - 2)
            * (gT2.1.toNat * 2 ^ 64 + gT2.2.1.toNat) := by
      rw [hlB2, hsbHi2, hsbMid2, hsbLo2]
      by_cases hirr : isIrregular m q = true
      · rw [if_pos hirr, if_pos hirr, if_pos hirr, if_pos hirr,
            sub192_192_toNat pH2 pMid2 pLo2 0 gT2.1 gT2.2.1 (by
              rw [htrip0G2, hP2_val]
              exact Nat.le_mul_of_pos_left _ (by omega)),
            hP2_val, htrip0G2, Nat.sub_mul, Nat.one_mul]
      · rw [if_neg hirr, if_neg hirr, if_neg hirr, if_neg hirr,
            sub192_192_toNat pH2 pMid2 pLo2 tg2.1 tg2.2.1 tg2.2.2 (by
              rw [h2G2_val, hP2_val]
              exact Nat.mul_le_mul_right _ (by omega)),
            hP2_val, h2G2_val, Nat.sub_mul]
    have hrB2_val : triple192Nat rB2.1 rB2.2.1 rB2.2.2
        = (4 * m + 2) * (gT2.1.toNat * 2 ^ 64 + gT2.2.1.toNat) := by
      rw [hrB2, add192_192_toNat pH2 pMid2 pLo2 tg2.1 tg2.2.1 tg2.2.2 (by
            rw [hP2_val, h2G2_val]
            have := hmulG2_lt (4 * m + 2) (by omega)
            rw [Nat.add_mul] at this
            omega),
          hP2_val, h2G2_val, Nat.add_mul]
    have hmH2_val : triple192Nat mH2.1 mH2.2.1 mH2.2.2
        = 2 * m * (gT2.1.toNat * 2 ^ 64 + gT2.2.1.toNat) := by
      rw [hmH2, shr1_192_toNat, hP2_val,
          show 4 * m * (gT2.1.toNat * 2 ^ 64 + gT2.2.1.toNat)
              = 2 * (2 * m * (gT2.1.toNat * 2 ^ 64 + gT2.2.1.toNat)) from by ring,
          Nat.mul_div_cancel_left _ (by omega)]
    have hk_lo2 : pow10Table128_kMin ≤ -(kOfMQ m q) := by omega
    have hk_hi2 : -(kOfMQ m q) ≤ pow10Table128_kMax := by omega
    match hp : pickNearer_u64_flipped lB2.1 lB2.2.1 lB2.2.2 leftU
                 rB2.1 rB2.2.1 rB2.2.2 (m4 + 2) mH2.1 mH2.2.1 mH2.2.2
                 (UInt64.ofNat m <<< 1)
                 (UInt64.ofNat (-q + gT2.2.2).toNat)
                 (UInt64.ofNat (shiftedSig m q (kOfMQ m q))) with
    | none => rw [hp] at hopt; cases hopt
    | some chosen =>
      rw [hp] at hopt
      have hpkd : pickNearer (shiftedSig m q (kOfMQ m q)) (kOfMQ m q) m q = chosen.toNat :=
        pickNearer_u64_flipped_some_eq q (kOfMQ m q) (shiftedSig m q (kOfMQ m q)) m
          (isIrregular m q) chosen lB2.1 lB2.2.1 lB2.2.2 rB2.1 rB2.2.1 rB2.2.2
          mH2.1 mH2.2.1 mH2.2.2
          hm_pos (by omega) hm_lt hs_ge hk_lo2 hk_hi2 hqh2_lo hqh2_hi rfl
          hlB2_val hrB2_val hmH2_val hp
      rw [hpkd]
      cases hopt
      rfl

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

/-- v11 with the pickNearer path flipped too: table entry for `-k` at
    biased index `648 - kB`, same `[5134, 5202]` biased window, one
    product `P₂ = 4m·g″` for all fall-through tests, midpoint by exact
    halving. (v8 with the `k+1` interval tests replaced by the flipped scheme:
    table entry for `-(k+1)` at biased index `647 - kB`, window guard
    `uB' = (h'+2048+4096) - qB ∈ [5134, 5202]`, one boundary product
    `P = 4m·g'` shared across `uV`/`wV`, candidate on the shift side. -/
@[inline]
def shortestUnsigned_u64_opt_v12 (mU : UInt64) (qB : UInt64) : Option (UInt64 × Int) :=
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
                let gT2 := pow10Table128.getD (648 - kBn) pow10Table128_default
                let uC' : UInt64 := (hB128.getD (648 - kBn) 0 + 4096) - qB
                if _h_qh2_lo : uC' < 5134 then none
                else if _h_qh2_hi : uC' > 5202 then none
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
                  match pickNearer_u64_flipped lB2.1 lB2.2.1 lB2.2.2 leftU
                          rB2.1 rB2.2.1 rB2.2.2 rightU mH.1 mH.2.1 mH.2.2 twoM w28 sU with
                  | none => none
                  | some chosen => some (chosen, k)
        else if _h_s1 : sU = 0 then none
        else
          let gT2 := pow10Table128.getD (648 - kBn) pow10Table128_default
          let uC' : UInt64 := (hB128.getD (648 - kBn) 0 + 4096) - qB
          if _h_qh2_lo : uC' < 5134 then none
          else if _h_qh2_hi : uC' > 5202 then none
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
            match pickNearer_u64_flipped lB2.1 lB2.2.1 lB2.2.2 leftU
                    rB2.1 rB2.2.1 rB2.2.2 rightU mH.1 mH.2.1 mH.2.2 twoM w28 sU with
            | none => none
            | some chosen => some (chosen, k)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 3200000 in
/-- Arg-biasing transfer: a `some` result of the pure-UInt64 v11 kernel
    is a `some` result of the spec-table flipped kernel. Assembles the
    existing biased-index/window component lemmas. -/
theorem shortestUnsigned_u64_opt_v12_some_eq_flip2 (mU qB : UInt64) (r : UInt64 × Int)
    (hopt : shortestUnsigned_u64_opt_v12 mU qB = some r) :
    shortestUnsigned_u64_opt_flip2 mU.toNat ((qB.toNat : Int) - 1074) = some r := by
  unfold shortestUnsigned_u64_opt_v12 at hopt
  unfold shortestUnsigned_u64_opt_flip2
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
  have hilow : 648 - (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) + 324).toNat
      < pow10Table128.size := by rw [pow10Table128_size_eq]; omega
  -- Goal side: lookups → getD, ofNat mU.toNat → mU, isIrregular → isIrregularB.
  have e192 := lookup192_neg (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074)) hklo hkhi
  have eflip := lookup128_negHigh (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074)) hklo hkhi
  have elow := lookup128_neg (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074)) hklo hkhi
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
  have uclt := wB_lt ((qB.toNat : Int) - 1074) _ h_q_lo' h_q_hi' hhlow
  have ucgt := wB_gt ((qB.toNat : Int) - 1074) _ h_q_lo' h_q_hi' hhlow
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
    by_cases huc1 : -((qB.toNat : Int) - 1074) + (pow10Table128.getD
        (648 - (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) + 324).toNat)
        pow10Table128_default).2.2 < 64
    · simp only [dif_pos huc1] at hopt ⊢
      exact hopt
    simp only [dif_neg huc1] at hopt ⊢
    by_cases huc2 : -((qB.toNat : Int) - 1074) + (pow10Table128.getD
        (648 - (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) + 324).toNat)
        pow10Table128_default).2.2 > 132
    · simp only [dif_pos huc2] at hopt ⊢
      exact hopt
    simp only [dif_neg huc2] at hopt ⊢
    have ucval := wB_val ((qB.toNat : Int) - 1074) _ h_q_lo' h_q_hi' hhlow huc1 huc2
    rw [eqb] at ucval
    rw [ucval] at hopt
    exact hopt
  · simp only [hge10, if_false] at hopt ⊢
    by_cases hs0 : shiftedSig_v3 mU.toNat ((qB.toNat : Int) - 1074)
        (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074)) = 0
    · rw [dif_pos hs0] at hopt; cases hopt
    rw [dif_neg hs0] at hopt
    rw [dif_neg hs0]
    by_cases huc1 : -((qB.toNat : Int) - 1074) + (pow10Table128.getD
        (648 - (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) + 324).toNat)
        pow10Table128_default).2.2 < 64
    · rw [dif_pos huc1] at hopt; cases hopt
    rw [dif_neg huc1] at hopt
    rw [dif_neg huc1]
    by_cases huc2 : -((qB.toNat : Int) - 1074) + (pow10Table128.getD
        (648 - (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) + 324).toNat)
        pow10Table128_default).2.2 > 132
    · rw [dif_pos huc2] at hopt; cases hopt
    rw [dif_neg huc2] at hopt
    rw [dif_neg huc2]
    have ucval := wB_val ((qB.toNat : Int) - 1074) _ h_q_lo' h_q_hi' hhlow huc1 huc2
    rw [eqb] at ucval
    rw [ucval] at hopt
    exact hopt

/-! ## Wrapper, exponent range, emit, entry point -/

/-- v12 entry: same packed fallback as v8/v9. -/
@[inline]
def shortestUnsigned_v12 (mU qB : UInt64) : Nat × Int :=
  match shortestUnsigned_u64_opt_v12 mU qB with
  | some (sU, k) => (sU.toNat, k)
  | none => shortestUnsigned_packed mU.toNat ((qB.toNat : Int) - 1074)

theorem shortestUnsigned_v12_eq_packed (mU qB : UInt64) :
    shortestUnsigned_v12 mU qB
      = shortestUnsigned_packed mU.toNat ((qB.toNat : Int) - 1074) := by
  unfold shortestUnsigned_v12
  match h : shortestUnsigned_u64_opt_v12 mU qB with
  | none => rfl
  | some (sU, k) =>
    exact (shortestUnsigned_u64_opt_flip2_some_eq_packed _ _ _ _
      (shortestUnsigned_u64_opt_v12_some_eq_flip2 mU qB (sU, k) h)).symm

theorem shortestUnsigned_v12_eq_v8 (mU qB : UInt64) :
    shortestUnsigned_v12 mU qB = shortestUnsigned_v8 mU qB := by
  rw [shortestUnsigned_v12_eq_packed, shortestUnsigned_packed_eq,
      ← shortestUnsigned_v5_eq, ← shortestUnsigned_v7_eq_v5,
      ← shortestUnsigned_v8_eq_v7]

set_option maxHeartbeats 1600000 in
/-- Every successful v11 exit carries an exponent in `[-324, 325]`
    (mirror of the v11 one). -/
theorem shortestUnsigned_u64_opt_v12_k_range (mU qB : UInt64)
    (s : UInt64) (k : Int)
    (h : shortestUnsigned_u64_opt_v12 mU qB = some (s, k)) :
    -324 ≤ k ∧ k ≤ 325 := by
  by_cases h1 : mU = 0
  · rw [show shortestUnsigned_u64_opt_v12 mU qB = none from by
      unfold shortestUnsigned_u64_opt_v12; rw [dif_pos h1]] at h
    cases h
  by_cases h2 : mU ≥ (9007199254740992 : UInt64)
  · rw [show shortestUnsigned_u64_opt_v12 mU qB = none from by
      unfold shortestUnsigned_u64_opt_v12; rw [dif_neg h1, dif_pos h2]] at h
    cases h
  by_cases h3 : qB > 2045
  · rw [show shortestUnsigned_u64_opt_v12 mU qB = none from by
      unfold shortestUnsigned_u64_opt_v12; rw [dif_neg h1, dif_neg h2, dif_pos h3]] at h
    cases h
  by_cases h4 : kBOfMQ mU qB > 647
  · rw [show shortestUnsigned_u64_opt_v12 mU qB = none from by
      unfold shortestUnsigned_u64_opt_v12;
        rw [dif_neg h1, dif_neg h2, dif_neg h3, dif_pos h4]] at h
    cases h
  -- Transfer the value to the spec through the chain.
  have hwrap : shortestUnsigned mU.toNat ((qB.toNat : Int) - 1074) = (s.toNat, k) := by
    have h11 : shortestUnsigned_v12 mU qB = (s.toNat, k) := by
      unfold shortestUnsigned_v12
      rw [h]
    rw [← shortestUnsigned_packed_eq, ← shortestUnsigned_v12_eq_packed, h11]
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

/-- `emitTail5` over the v12 kernel. -/
@[inline]
def emitTail6 (sign : Bool) (mU qB : UInt64) : String :=
  if mU = 0 then (if sign then "-0" else "0")
  else
    match shortestUnsigned_u64_opt_v12 mU qB with
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

theorem emitTail6_eq (sign : Bool) (mU qB : UInt64) :
    emitTail6 sign mU qB = emitTail2 sign mU qB := by
  unfold emitTail6 emitTail2
  by_cases h0 : mU = 0
  · rw [if_pos h0, if_pos h0]
  rw [if_neg h0, if_neg h0]
  have h8pk : shortestUnsigned_v8 mU qB
      = shortestUnsigned_packed mU.toNat ((qB.toNat : Int) - 1074) := by
    rw [shortestUnsigned_v8_eq_v7, shortestUnsigned_v7_eq_v5, shortestUnsigned_v5_eq,
        ← shortestUnsigned_packed_eq]
  rw [h8pk]
  cases hv : shortestUnsigned_u64_opt_v12 mU qB with
  | none => rfl
  | some p =>
    obtain ⟨sU, exp⟩ := p
    have hpk : shortestUnsigned_packed mU.toNat ((qB.toNat : Int) - 1074)
        = (sU.toNat, exp) :=
      shortestUnsigned_u64_opt_flip2_some_eq_packed _ _ _ _
        (shortestUnsigned_u64_opt_v12_some_eq_flip2 mU qB (sU, exp) hv)
    rw [hpk]
    have hrange := shortestUnsigned_u64_opt_v12_k_range mU qB sU exp hv
    simp only []
    rw [emitCheckedIdx_eq sign sU.toNat exp hrange.1]

/-- `toStringFast7` over the v12 kernel. -/
@[inline]
def toStringFast8 (f : _root_.Float) : String :=
  let bits := f.toBits
  let expBits : UInt64 := (bits >>> 52) &&& 0x7FF
  let mantBits : UInt64 := bits &&& 0x000F_FFFF_FFFF_FFFF
  if expBits = 0x7FF then
    if mantBits ≠ 0 then "NaN"
    else if (bits >>> 63) ≠ 0 then "-Infinity" else "Infinity"
  else
    emitTail6 (decide (bits >>> 63 ≠ 0))
      (if expBits = 0 then mantBits else mantBits + 4503599627370496)
      (if expBits = 0 then 0 else expBits - 1)

theorem toStringFast8_eq (f : _root_.Float) : toStringFast8 f = toStringFast4 f := by
  unfold toStringFast8 toStringFast4
  simp only [emitTail6_eq]

-- Superseded registration: `floatToStrRef_eq_toStringFast9` (KernelV13)
-- is the live @[csimp].
theorem floatToStrRef_eq_toStringFast8 : @floatToStrRef = @toStringFast8 := by
  funext f
  rw [toStringFast8_eq]
  exact congrFun floatToStrRef_eq_toStringFast4 f

end PP.Numeric.Schubfach

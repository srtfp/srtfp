module
/- F9: the Schubfach kernel on 64-bit words, and its correctness against
   `Exact.shortest` (F7) through the integer form `shortestI`. -/

public import Srtfp.Perf.Schubfach.Index
public import Srtfp.Perf.Schubfach.Estimate
public import Srtfp.Perf.Schubfach.Comparisons
public import Srtfp.Perf.Schubfach.Nadezhin

@[expose] public section

open Srtfp.Compat

namespace Srtfp.Schubfach

open Srtfp.Printer Exact

variable {m : Nat} {q : Int}

/-! ## The quantities as `(c̄/4)·2^q·10^{-k}` (§9.8.1) -/

theorem V_eq (m : Nat) (q k : Int) :
    V m q k = ((4 * m : Nat) : Rat) / 4 * (2 : Rat) ^ q * (10 : Rat) ^ (-k) := by
  unfold V v
  rw [Rat.div_def, ← Rat.zpow_neg]
  push_cast; grind

theorem Vr_eq (m : Nat) (q k : Int) :
    Vr m q k = ((4 * m + 2 : Nat) : Rat) / 4 * (2 : Rat) ^ q * (10 : Rat) ^ (-k) := by
  unfold Vr vr
  rw [Rat.div_def, ← Rat.zpow_neg]
  push_cast; grind

theorem Vl_eq_reg (hm : 1 ≤ m) (hirr : isIrregular m q = false) (k : Int) :
    Vl m q k = ((4 * m - 2 : Nat) : Rat) / 4 * (2 : Rat) ^ q * (10 : Rat) ^ (-k) := by
  unfold Vl vl
  rw [if_neg (fun hc => by rw [isIrregular_iff.mpr hc] at hirr; cases hirr), Rat.div_def,
    ← Rat.zpow_neg]
  rw [← Rat.intCast_natCast (4 * m - 2), Int.ofNat_sub (by omega)]; push_cast; grind

theorem Vl_eq_irr (hm : 1 ≤ m) (hirr : isIrregular m q = true) (k : Int) :
    Vl m q k = ((4 * m - 1 : Nat) : Rat) / 4 * (2 : Rat) ^ q * (10 : Rat) ^ (-k) := by
  unfold Vl vl
  rw [if_pos (isIrregular_iff.mp hirr), Rat.div_def, ← Rat.zpow_neg]
  rw [← Rat.intCast_natCast (4 * m - 1), Int.ofNat_sub (by omega)]; push_cast; grind

/-- `0 ≤ r_o(4x) < 2^60` for `x = (c̄/4)·2^q·10^{-k}` with `c̄ < 2^55`. -/
theorem ro_bounds (h : InRange m q) (mb : Nat) (hmb : mb < 2 ^ 55) :
    0 ≤ ro (4 * (((mb : Nat) : Rat) / 4 * (2 : Rat) ^ q * (10 : Rat) ^ (-(kOfMQ m q))))
    ∧ ro (4 * (((mb : Nat) : Rat) / 4 * (2 : Rat) ^ q * (10 : Rat) ^ (-(kOfMQ m q)))) < 2 ^ 60 := by
  obtain ⟨_, hhi⟩ := ratio_bounds h
  generalize kOfMQ m q = k at *
  have hT : (0 : Rat) < 2 ^ q * 10 ^ (-k) := Rat.mul_pos (Rat.zpow_pos (by decide)) (Rat.zpow_pos (by decide))
  have hmb0 : (0 : Rat) ≤ (mb : Rat) := by exact_mod_cast Nat.zero_le mb
  have hmbq : (mb : Rat) < 2 ^ 55 := by exact_mod_cast hmb
  set x : Rat := (mb : Rat) / 4 * (2 : Rat) ^ q * (10 : Rat) ^ (-k) with hx
  have hmb4 : (0 : Rat) ≤ (mb : Rat) / 4 := div_nonneg hmb0 (by decide)
  have hx0 : 0 ≤ x := by rw [hx, Rat.mul_assoc]; exact Rat.mul_nonneg hmb4 (Rat.le_of_lt hT)
  have hx1 : x ≤ (mb : Rat) * 4 := by
    rw [hx, Rat.mul_assoc]
    have := Rat.mul_le_mul_of_nonneg_left (Rat.le_of_lt hhi) hmb4
    rw [show (16 : Rat) = 4 * 4 by decide +kernel, div_mul_mul (by decide)] at this
    exact this
  have hnum : (16 : Rat) * 2 ^ 55 + 1 ≤ (2 : Rat) ^ 60 := by decide +kernel
  constructor
  · exact ro_nonneg (by grind)
  · have := ro_le (4 * x)
    have h1 : (ro (4 * x) : Rat) < ((2 ^ 60 : Int) : Rat) := by push_cast; grind
    exact_mod_cast h1

/-! ## `v̄`, `v̄_l`, `v̄_r` -/

/-- `c̄_l, c̄, c̄_r` (§9.8.1) shifted by `h`, then F8 on each. -/
@[inline] def vbars (mU qB kB : UInt64) : UInt64 × UInt64 × UInt64 :=
  let g1 := g1Table.getD kB.toNat 0
  let g0 := g0Table.getD kB.toNat 0
  let h := hOf qB kB
  let cb := 4 * mU
  let cbl := if isIrregularB mU qB then cb - 1 else cb - 2
  (rop g1 g0 (cb <<< h), rop g1 g0 (cbl <<< h), rop g1 g0 ((cb + 2) <<< h))

theorem shiftLeft_toNat (a h : UInt64) (hh : h.toNat ≤ 5) (ha : a.toNat < 2 ^ 55) :
    (a <<< h).toNat = a.toNat * 2 ^ h.toNat := by
  rw [UInt64.toNat_shiftLeft, Nat.mod_eq_of_lt (by omega : h.toNat < 64), Nat.shiftLeft_eq]
  have : 2 ^ h.toNat ≤ 2 ^ 5 := Nat.pow_le_pow_right (by decide) hh
  exact Nat.mod_eq_of_lt (by
    calc a.toNat * 2 ^ h.toNat < 2 ^ 55 * 2 ^ 5 := Nat.mul_lt_mul_of_lt_of_le ha this (by decide)
      _ ≤ 2 ^ 64 := by decide)

/-- `vbars` computes the three exact `r_o(4·)`, and they are below `2^60`. -/
theorem vbars_eq (h : InRange m q) (mU qB kB : UInt64) (hm : mU.toNat = m)
    (hq : (qB.toNat : Int) = q + 1074) (hk : (kB.toNat : Int) = kOfMQ m q + 324) :
    (((vbars mU qB kB).1.toNat : Int) = ro (4 * V m q (kOfMQ m q))
      ∧ ((vbars mU qB kB).2.1.toNat : Int) = ro (4 * Vl m q (kOfMQ m q))
      ∧ ((vbars mU qB kB).2.2.toNat : Int) = ro (4 * Vr m q (kOfMQ m q)))
    ∧ ((vbars mU qB kB).1.toNat < 2 ^ 60 ∧ (vbars mU qB kB).2.1.toNat < 2 ^ 60
      ∧ (vbars mU qB kB).2.2.toNat < 2 ^ 60) := by
  have hm1 : 1 ≤ m := h.1
  have hm53 : m < 2 ^ 53 := h.2.1
  obtain ⟨hk1, hk2⟩ := k_range h
  obtain ⟨hs, hsl, hsr⟩ := R20 h
  obtain ⟨hqr1, hqr2⟩ := q_add_r h
  have hkB : kB.toNat ≤ 616 := by unfold kMax at hk2; omega
  -- the table halves
  have hg1 : (g1Table.getD kB.toNat 0).toNat = g (kOfMQ m q) / 2 ^ 63 := by
    have := g1Table_getD (kOfMQ m q) hk1 hk2
    rwa [show (kOfMQ m q - kMin).toNat = kB.toNat by unfold kMin; omega] at this
  have hg0 : (g0Table.getD kB.toNat 0).toNat = g (kOfMQ m q) % 2 ^ 63 := by
    have := g0Table_getD (kOfMQ m q) hk1 hk2
    rwa [show (kOfMQ m q - kMin).toNat = kB.toNat by unfold kMin; omega] at this
  -- `h`
  have hE : (qB.toNat : Int) - 1074 + flog2pow10 (324 - kB.toNat) + 2
      = q + r (kOfMQ m q) + 127 := by
    rw [show (324 : Int) - kB.toNat = -(kOfMQ m q) by omega]; have := h_eq h; omega
  have hhq : ((hOf qB kB).toNat : Int) = q + r (kOfMQ m q) + 127 := by
    rw [hOf_toNat qB kB hkB (by omega) (by omega)]; exact hE
  have hh2 : 2 ≤ (hOf qB kB).toNat := by omega
  have hh5 : (hOf qB kB).toNat ≤ 5 := by omega
  -- one word `c̄` at a time
  have step : ∀ (mb : Nat) (cb : UInt64) (x : Rat), cb.toNat = mb → 0 < mb → mb < 2 ^ 55 →
      x = (mb : Rat) / 4 * (2 : Rat) ^ q * (10 : Rat) ^ (-(kOfMQ m q)) → Separated eps (2 * x) →
      ((rop (g1Table.getD kB.toNat 0) (g0Table.getD kB.toNat 0) (cb <<< hOf qB kB)).toNat : Int)
          = ro (4 * x)
        ∧ (rop (g1Table.getD kB.toNat 0) (g0Table.getD kB.toNat 0) (cb <<< hOf qB kB)).toNat
          < 2 ^ 60 := by
    intro mb cb x hcb hmb hmb55 hx hsep
    subst hx
    have e := rop_eq_ro mb q (kOfMQ m q) _ _ (cb <<< hOf qB kB) (hOf qB kB).toNat ⟨hk1, hk2⟩
      hmb55 hg1 hg0
      (by rw [shiftLeft_toNat _ _ hh5 (by omega), hcb]) hh2 hh5 hhq hsep
    exact ⟨e, by have := (ro_bounds h mb hmb55).2; omega⟩
  -- `c̄_l` is one of two words
  obtain ⟨mbl, hmbl, hmbl55, hcbl, hxl⟩ : ∃ mb, 0 < mb ∧ mb < 2 ^ 55
      ∧ (if isIrregularB mU qB then 4 * mU - 1 else 4 * mU - 2).toNat = mb
      ∧ Vl m q (kOfMQ m q) = (mb : Rat) / 4 * (2 : Rat) ^ q * (10 : Rat) ^ (-(kOfMQ m q)) := by
    rw [isIrregularB_eq, hm, show (qB.toNat : Int) - 1074 = q by omega]
    cases hirr : isIrregular m q
    · exact ⟨4 * m - 2, by omega, by omega, by rw [if_neg Bool.false_ne_true]; word,
        Vl_eq_reg hm1 hirr _⟩
    · exact ⟨4 * m - 1, by omega, by omega, by rw [if_pos rfl]; word, Vl_eq_irr hm1 hirr _⟩
  obtain ⟨e1, b1⟩ := step (4 * m) (4 * mU) _ (by word) (by omega) (by omega) (V_eq m q _) hs
  obtain ⟨e2, b2⟩ := step mbl _ _ hcbl hmbl hmbl55 hxl hsl
  obtain ⟨e3, b3⟩ :=
    step (4 * m + 2) (4 * mU + 2) _ (by word) (by omega) (by omega) (Vr_eq m q _) hsr
  unfold vbars
  exact ⟨⟨e1, e2, e3⟩, b1, b2, b3⟩

/-! ## F9 -/

/-- `pick` on words. -/
@[inline] def pickK (out vb vbl vbr s : UInt64) : UInt64 :=
  let t := s + 1
  let uIn : Bool := vbl + out ≤ 4 * s
  let wIn : Bool := 4 * t + out ≤ vbr
  if uIn && !wIn then s
  else if !uIn && wIn then t
  else if vb < 2 * (s + t) then s
  else if 2 * (s + t) < vb then t
  else if s &&& 1 = 0 then s
  else t

/-- F9 on `c = mU` and the biased `qB = q + 1074`: the shortest significand
    and the table index `kB = k − K_min` of its exponent. -/
@[inline] def kernel (mU qB : UInt64) : UInt64 × UInt64 :=
  let kB := kBOfMQ mU qB
  let vs := vbars mU qB kB
  let vb := vs.1
  let vbl := vs.2.1
  let vbr := vs.2.2
  let out := mU &&& 1
  let s := vb >>> 2
  if s ≥ 10 then
    let s' := s / 10
    if vbl + out ≤ 4 * (10 * s') then (s', kB + 1)
    else if 4 * (10 * (s' + 1)) + out ≤ vbr then (s' + 1, kB + 1)
    else (pickK out vb vbl vbr s, kB)
  else (pickK out vb vbl vbr s, kB)

/-! ## Correctness -/

theorem toNat_ite (c : Prop) [Decidable c] (a b : UInt64) :
    (if c then a else b).toNat = if c then a.toNat else b.toNat := by
  split <;> rfl

theorem pickK_eq (out vb vbl vbr s : UInt64) (o pvb pvbl pvbr : Int) (sN : Nat)
    (ho : (out.toNat : Int) = o) (hvb : (vb.toNat : Int) = pvb) (hvbl : (vbl.toNat : Int) = pvbl)
    (hvbr : (vbr.toNat : Int) = pvbr) (hs : s.toNat = sN)
    (hb : vb.toNat < 2 ^ 60 ∧ vbl.toNat < 2 ^ 60 ∧ vbr.toNat < 2 ^ 60 ∧ s.toNat < 2 ^ 60
      ∧ out.toNat ≤ 1) :
    (pickK out vb vbl vbr s).toNat = pickI o pvb pvbl pvbr sN := by
  obtain ⟨b1, b2, b3, b4, b5⟩ := hb
  have c1 : (vbl + out ≤ 4 * s) ↔ (pvbl + o ≤ 4 * (sN : Int)) := by word
  have c2 : (4 * (s + 1) + out ≤ vbr) ↔ (4 * ((sN + 1 : Nat) : Int) + o ≤ pvbr) := by word
  have c3 : (vb < 2 * (s + (s + 1))) ↔ (pvb < 2 * ((sN + (sN + 1) : Nat) : Int)) := by word
  have c4 : (2 * (s + (s + 1)) < vb) ↔ (2 * ((sN + (sN + 1) : Nat) : Int) < pvb) := by word
  have c5 : (s &&& 1 = 0) ↔ (sN % 2 = 0) := by word
  have ht : (s + 1).toNat = sN + 1 := by word
  unfold pickK pickI
  simp only [c1, c2, c3, c4, c5, toNat_ite, hs, ht]

/-- F9 computes F7 (through its integer form). -/
theorem kernel_eq (h : InRange m q) (mU qB : UInt64) (hm : mU.toNat = m)
    (hq : (qB.toNat : Int) = q + 1074) :
    ((kernel mU qB).1.toNat, ((kernel mU qB).2.toNat : Int) - 324) = Exact.shortest m q := by
  rw [← shortestI_eq]
  have hm1 : 1 ≤ m := h.1
  have hq2 : qB.toNat ≤ 2045 := by have := h.2.2.2.1; omega
  obtain ⟨hkr1, hkr2⟩ := k_range h
  unfold kMin at hkr1
  unfold kMax at hkr2
  -- `kB`
  have hkB : ((kBOfMQ mU qB).toNat : Int) = kOfMQ m q + 324 := by
    rw [kBOfMQ_toNat mU qB hq2, hm, show (qB.toNat : Int) - 1074 = q by omega]
  obtain ⟨⟨e1, e2, e3⟩, b1, b2, b3⟩ := vbars_eq h mU qB (kBOfMQ mU qB) hm hq hkB
  have ho : ((mU &&& 1).toNat : Int) = out m := by unfold out; split <;> word
  have hob : (mU &&& 1).toNat ≤ 1 := by word
  unfold kernel shortestI
  simp only []
  generalize hvs : vbars mU qB (kBOfMQ mU qB) = vs at e1 e2 e3 b1 b2 b3
  generalize hkb : kBOfMQ mU qB = kB at hkB
  obtain ⟨vb, vbl, vbr⟩ := vs
  simp only [] at e1 e2 e3 b1 b2 b3 ⊢
  -- `s`
  have hs : (vb >>> 2).toNat = (ro (4 * V m q (kOfMQ m q)) / 4).toNat := by word
  have hsb : (vb >>> 2).toNat < 2 ^ 60 := by word
  generalize hsN : (ro (4 * V m q (kOfMQ m q)) / 4).toNat = sN at hs
  generalize hsU : vb >>> 2 = s at hs hsb
  -- the two exponents
  have hk1 : ((kB + 1).toNat : Int) - 324 = kOfMQ m q + 1 := by word
  have hk0 : (kB.toNat : Int) - 324 = kOfMQ m q := by omega
  -- the tests
  have h10 : (s ≥ 10) ↔ (sN ≥ 10) := by word
  have hs' : (s / 10).toNat = sN / 10 := by word
  have hs'1 : (s / 10 + 1).toNat = sN / 10 + 1 := by word
  have cu : (vbl + (mU &&& 1) ≤ 4 * (10 * (s / 10)))
      ↔ (ro (4 * Vl m q (kOfMQ m q)) + out m ≤ 4 * ((10 * (sN / 10) : Nat) : Int)) := by
    have := ho; word_simp at this ⊢; omega
  have cw : (4 * (10 * (s / 10 + 1)) + (mU &&& 1) ≤ vbr)
      ↔ (4 * ((10 * (sN / 10 + 1) : Nat) : Int) + out m ≤ ro (4 * Vr m q (kOfMQ m q))) := by
    have := ho; word_simp at this ⊢; omega
  have hpick := pickK_eq (mU &&& 1) vb vbl vbr s (out m) _ _ _ sN ho e1 e2 e3 hs
    ⟨b1, b2, b3, hsb, hob⟩
  by_cases hc0 : sN ≥ 10
  · rw [if_pos (h10.mpr hc0), if_pos hc0]
    by_cases hc1 : ro (4 * Vl m q (kOfMQ m q)) + out m ≤ 4 * ((10 * (sN / 10) : Nat) : Int)
    · rw [if_pos (cu.mpr hc1), if_pos hc1, hs', hk1]
    · rw [if_neg (fun hc => hc1 (cu.mp hc)), if_neg hc1]
      by_cases hc2 : 4 * ((10 * (sN / 10 + 1) : Nat) : Int) + out m ≤ ro (4 * Vr m q (kOfMQ m q))
      · rw [if_pos (cw.mpr hc2), if_pos hc2, hs'1, hk1]
      · rw [if_neg (fun hc => hc2 (cw.mp hc)), if_neg hc2, hpick, hk0]
  · rw [if_neg (fun hc => hc0 (h10.mp hc)), if_neg hc0, hpick, hk0]

end Srtfp.Schubfach

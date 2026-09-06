module
/- `Decimal.canonicaliseAux`, `Decimal.canonical` and `Decimal.mk'` on words.

   Schubfach hands `Decimal.mk'` a 16-17 digit significand, so any value
   with few significant digits (integers, currency, coordinates: most of
   a JSON payload) reaches `canonicaliseAux` with up to 16 trailing zeros.
   `canonicaliseAuxFast` strips them by `10^8, 10^8, 10^4, 10^2, 10` with
   the significand and the zero count both in `UInt64` (five divisibility
   tests instead of up to sixteen steps, nothing boxed and nothing
   allocated), adds the count to the exponent once, and ends with one
   `% 10` test whose "still divisible" branch is unreachable (the chunks
   cover every zero count below 20) but is discharged by the reference
   rather than proven unreachable. Each chunk is `j` single steps
   (`canonicaliseAux_div_pow`), so the proof is a fold of the unfolding
   lemmas. `canonicalFast` and `mk'Fast` test the common no-strip case on
   the raw arguments and allocate once. All three are the live `@[csimp]`
   registrations (`CsimpPin.lean`). -/

public import Srtfp.Decimal
public import Srtfp.Proofs.Decimal.Canonical
public import Srtfp.Perf.Word

@[expose] public section

open Float.Model.UnpackedFloat (Sign)

namespace Srtfp.Decimal

theorem UInt64_mod10_eq_zero_iff (s : UInt64) :
    s % 10 = 0 ↔ s.toNat % 10 = 0 := by
  rw [← UInt64.toNat_inj]
  rw [UInt64.toNat_mod]
  rfl

theorem canonicaliseAux_zero (e : Int) : canonicaliseAux 0 e = (0, 0) := by
  unfold canonicaliseAux; simp

/-- Stripping `j` trailing zeros at once is `j` single steps. -/
theorem canonicaliseAux_div_pow (s : Nat) (e : Int) (j : Nat) (hs : s ≠ 0)
    (hd : s % 10 ^ j = 0) :
    canonicaliseAux s e = canonicaliseAux (s / 10 ^ j) (e + j) := by
  induction j generalizing s e with
  | zero => simp
  | succ j ih =>
    have h10 : s % 10 = 0 := by
      have h10p : 10 ∣ 10 ^ (j + 1) := ⟨10 ^ j, by rw [Nat.pow_succ, Nat.mul_comm]⟩
      have : 10 ∣ s := Nat.dvd_trans h10p (Nat.dvd_of_mod_eq_zero hd)
      exact Nat.mod_eq_zero_of_dvd this
    rw [canonicaliseAux_div s e hs h10]
    have hs' : s / 10 ≠ 0 := div_ten_nonzero hs h10
    have hd' : (s / 10) % 10 ^ j = 0 := by
      obtain ⟨t, ht⟩ := Nat.dvd_of_mod_eq_zero hd
      rw [ht, Nat.pow_succ, Nat.mul_comm (10 ^ j) 10, Nat.mul_assoc,
          Nat.mul_div_cancel_left _ (by decide : 0 < 10)]
      exact Nat.mul_mod_right _ _
    rw [ih (s / 10) (e + 1) hs' hd', Nat.div_div_eq_div_mul, ← Nat.pow_succ']
    congr 1
    push_cast
    omega

/-- Significand half of one chunk: divide by `p` when `p ∣ s`. -/
@[inline]
def stripS (p s : UInt64) : UInt64 := if s % p = 0 then s / p else s

/-- Zero-count half of one chunk: add `j` when `p ∣ s`. -/
@[inline]
def stripC (p j s c : UInt64) : UInt64 := if s % p = 0 then c + j else c

theorem stripS_ne_zero (p s : UInt64) (hs : s.toNat ≠ 0) : (stripS p s).toNat ≠ 0 := by
  unfold stripS
  split
  · rename_i h
    word_simp at h ⊢
    intro hc
    have := Nat.div_add_mod s.toNat p.toNat
    rw [hc, h, Nat.mul_zero] at this
    omega
  · exact hs

theorem stripC_le (p j s c : UInt64) (B : Nat) (hc : c.toNat ≤ B) (hj : j.toNat ≤ 8)
    (hB : B + 8 < 2 ^ 64) : (stripC p j s c).toNat ≤ B + 8 := by
  unfold stripC; split <;> word

/-- One chunk keeps `canonicaliseAux` (the exponent carried as `e + count`),
    a nonzero significand, and the count below its bound. -/
theorem chunk (p j : UInt64) (jn B : Nat) {s c : UInt64} {s₀ : Nat} {e : Int}
    (hp : p.toNat = 10 ^ jn) (hj : j.toNat = jn) (hjn : jn ≤ 8) (hs : s.toNat ≠ 0)
    (hc : c.toNat ≤ B) (hB : B + 8 < 2 ^ 64)
    (he : canonicaliseAux s.toNat (e + (c.toNat : Int)) = canonicaliseAux s₀ e) :
    canonicaliseAux (stripS p s).toNat (e + ((stripC p j s c).toNat : Int))
        = canonicaliseAux s₀ e
      ∧ (stripS p s).toNat ≠ 0 ∧ (stripC p j s c).toNat ≤ B + 8 := by
  refine ⟨?_, stripS_ne_zero p s hs, stripC_le p j s c B hc (by omega) hB⟩
  unfold stripS stripC
  by_cases h : s % p = 0
  · rw [if_pos h, if_pos h, ← he]
    word_simp at h ⊢
    rw [hp] at h
    rw [hp, hj]
    rw [Nat.mod_eq_of_lt (by omega : c.toNat + jn < 2 ^ 64),
      show e + ((c.toNat + jn : Nat) : Int) = e + (c.toNat : Int) + (jn : Int) by push_cast; omega]
    exact (canonicaliseAux_div_pow s.toNat (e + (c.toNat : Int)) jn hs h).symm
  · rw [if_neg h, if_neg h]; exact he

/-- `canonicaliseAux` with the trailing zeros stripped in chunks of
    `10^8, 10^8, 10^4, 10^2, 10`, all in `UInt64` (significand and zero
    count), one `Int` addition at the end, and a last `% 10` test whose
    "still divisible" branch is unreachable (the chunks cover every count
    below 20) but is discharged by the reference rather than proven away.
    The `s < 2^64` dispatch is spelled `s >>> 64 = 0`: a scalar shift,
    whereas a literal `2^64` in a `Nat` comparison compiles to a GMP string
    parse at every evaluation. -/
@[inline]
def canonicaliseAuxFast (s : Nat) (e : Int) : Nat × Int :=
  if s = 0 then (0, 0)
  else if s % 10 ≠ 0 then (s, e)
  else if _h : s >>> 64 = 0 then
    let s0 : UInt64 := UInt64.ofNat s
    let s1 := stripS 100000000 s0
    let c1 := stripC 100000000 8 s0 0
    let s2 := stripS 100000000 s1
    let c2 := stripC 100000000 8 s1 c1
    let s3 := stripS 10000 s2
    let c3 := stripC 10000 4 s2 c2
    let s4 := stripS 100 s3
    let c4 := stripC 100 2 s3 c3
    let s5 := stripS 10 s4
    let c5 := stripC 10 1 s4 c4
    let e5 : Int := e + (c5.toNat : Int)
    if s5 % 10 = 0 then canonicaliseAux s5.toNat e5 else (s5.toNat, e5)
  else
    canonicaliseAux s e

theorem canonicaliseAux_eq_fast (s : Nat) (e : Int) :
    canonicaliseAux s e = canonicaliseAuxFast s e := by
  unfold canonicaliseAuxFast
  by_cases hs0 : s = 0
  · rw [if_pos hs0, hs0, canonicaliseAux_zero]
  rw [if_neg hs0]
  by_cases hmod : s % 10 ≠ 0
  · rw [if_pos hmod, canonicaliseAux_not_div s e hs0 hmod]
  rw [if_neg hmod]
  by_cases hlt : s >>> 64 = 0
  · rw [dif_pos hlt]
    have hs64 : s < 2 ^ 64 := by
      rw [Nat.shiftRight_eq_div_pow] at hlt
      exact Nat.lt_of_div_eq_zero (Nat.two_pow_pos 64) hlt
    have hsU : (UInt64.ofNat s).toNat = s := UInt64.toNat_ofNat_of_lt' hs64
    dsimp only
    -- the five chunks: `10^8, 10^8, 10^4, 10^2, 10`
    have e0 : canonicaliseAux (UInt64.ofNat s).toNat (e + ((0 : UInt64).toNat : Int))
        = canonicaliseAux s e := by rw [hsU]; simp
    obtain ⟨e1, n1, b1⟩ := chunk 100000000 8 8 0 rfl rfl (by decide) (by rw [hsU]; exact hs0)
      (by decide) (by decide) e0
    obtain ⟨e2, n2, b2⟩ := chunk 100000000 8 8 8 rfl rfl (by decide) n1 b1 (by decide) e1
    obtain ⟨e3, n3, b3⟩ := chunk 10000 4 4 16 rfl rfl (by decide) n2 b2 (by decide) e2
    obtain ⟨e4, n4, b4⟩ := chunk 100 2 2 24 rfl rfl (by decide) n3 b3 (by decide) e3
    obtain ⟨e5, n5, -⟩ := chunk 10 1 1 32 rfl rfl (by decide) n4 b4 (by decide) e4
    generalize stripS 10 (stripS 100 (stripS 10000 (stripS 100000000 (stripS 100000000
      (UInt64.ofNat s))))) = s5 at e5 n5 ⊢
    -- the finisher
    by_cases hz : s5 % 10 = 0
    · rw [if_pos hz, e5]
    · rw [if_neg hz, ← e5]
      exact canonicaliseAux_not_div _ _ n5 (fun hc => hz ((UInt64_mod10_eq_zero_iff s5).mpr hc))
  · rw [dif_neg hlt]

/-- The live registration for `canonicaliseAux`. -/
@[csimp]
theorem canonicaliseAux_csimp : @canonicaliseAux = @canonicaliseAuxFast := by
  funext s e
  exact canonicaliseAux_eq_fast s e

/-! ## `canonical` and `mk'` -/

/-- `Decimal.canonical` with the common no-strip case answered without
    building anything. -/
def canonicalFast (d : Decimal) : Decimal :=
  let s := d.significand
  if s = 0 then ⟨d.sign, 0, 0⟩
  else if s % 10 ≠ 0 then d
  else
    let (s', e') := canonicaliseAux s d.exponent
    ⟨d.sign, s', e'⟩

theorem canonical_eq_fast (d : Decimal) : Decimal.canonical d = canonicalFast d := by
  unfold canonicalFast Decimal.canonical
  by_cases hs0 : d.significand = 0
  · simp [hs0]
  simp only [hs0, ite_false]
  by_cases hsmod : d.significand % 10 ≠ 0
  · rw [if_pos hsmod, canonicaliseAux_not_div _ _ hs0 hsmod]
  · rw [if_neg hsmod]

@[csimp]
theorem canonical_csimp : @Decimal.canonical = @canonicalFast := by
  funext d
  exact canonical_eq_fast d

/-- `Decimal.mk'` with the canonicalisation conditions tested on the raw
    arguments, so the `Decimal` is allocated exactly once. -/
@[inline]
def mk'Fast (sign : Sign) (significand : Nat) (exponent : Int) : Decimal :=
  if significand = 0 then ⟨sign, 0, 0⟩
  else if significand % 10 ≠ 0 then ⟨sign, significand, exponent⟩
  else
    let (s', e') := canonicaliseAux significand exponent
    ⟨sign, s', e'⟩

theorem mk'_eq_fast (sign : Sign) (significand : Nat) (exponent : Int) :
    Decimal.mk' sign significand exponent = mk'Fast sign significand exponent := by
  rw [Decimal.mk', canonical_eq_fast]
  unfold canonicalFast mk'Fast
  by_cases hs0 : significand = 0
  · simp [hs0]
  simp only [hs0, ite_false]

@[csimp]
theorem mk'_csimp : @Decimal.mk' = @mk'Fast := by
  funext sign sig exp
  exact mk'_eq_fast sign sig exp

end Srtfp.Decimal

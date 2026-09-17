module
/- The fast reader: `Decimal → binary64 word` in 64-bit arithmetic.

   For `x = m · 10^e` with `m < 2^64` and `e ∈ [-324, 308]`, normalise
   `mz = m · 2^z ∈ [2^63, 2^64)` and take the table entry `(g, h)` with
   `10^e ≤ g · 2^{-h} < 10^e + 2^{-h}` (`pow10Lookup128_invariant`). Then

       X = mz · 10^e · 2^h         (exact, a rational)
       P = mz · g                  (a 192-bit integer)
       P - mz < X ≤ P

   and `x = X · 2^{-(h+z)}`. Everything the reference computes is read
   off `P`: the binary exponent from its bit length, the significand as
   the half-even rounding of `X / 2^s`. Each decision is taken on `P` and
   is right for `X` whenever the interval `(P - mz, P]` contains no
   boundary; otherwise the kernel answers `declined` and the caller
   falls back to `readExact`. Three regimes reach the core:

   * `0 ≤ e ≤ 54`: the entry is exact (`g = 10^e · 2^h`), so `X = P`;
   * `e < 0` with `5^{-e} ∣ m`: `x = (m / 5^{-e}) · 2^e` is a binary
     scaling, run through the core with `g = 2^127`, `h = 127 - e`;
   * otherwise the margin test above.

   `readFast_some` (below) shows every answer other than `declined` is
   `Reader.ofDecimalBits d`. -/

public import Srtfp.Perf.ReadExact
public import Srtfp.Proofs.Reader.Spec
public import Srtfp.Perf.TableInvariant
public import Srtfp.Perf.MulHigh128
public import Srtfp.Perf.Unpack
public import Srtfp.Perf.Word

@[expose] public section

open Srtfp.Compat

namespace Srtfp.Reader

open Srtfp.Schubfach (pow10Lookup128 mulHi64 mulHi64_toNat_eq)
open Srtfp.Float
open Float.Model (UnpackedFloat)
open Float.Model.UnpackedFloat (Sign)

/-! ## 192-bit products -/

/-- `a · (gHi · 2^64 + gLo)` as `(hi, mid, lo)`. -/
@[inline]
def mul64x128 (a gHi gLo : UInt64) : UInt64 × UInt64 × UInt64 :=
  let lo := a * gLo
  let loH := mulHi64 a gLo
  let mid := a * gHi
  let midH := mulHi64 a gHi
  let m := mid + loH
  let carry : UInt64 := if m < mid then 1 else 0
  (midH + carry, m, lo)

/-! ## The rounding core -/

/-- The word for `(sign, n, k)` with `0 < n ≤ 2^53`: a subnormal below
    `2^52`, the carry `n = 2^53` renormalised. -/
@[inline]
def packFinite (sign : Sign) (n : UInt64) (k : Int) : UInt64 :=
  if n < 4503599627370496 then Word.pack sign 0 n.toNat
  else if n = 9007199254740992 then Word.pack sign (k + 1076).toNat 0
  else Word.pack sign (k + 1075).toNat (n - 4503599627370496).toNat

/-- `63 - log2 m` for `m ∈ [1, 2^64)`: six compare-and-shift steps on
    the leading zeros. -/
@[inline]
def lzShift (m : UInt64) : UInt64 :=
  let z1 : UInt64 := if m < 4294967296 then 32 else 0
  let m1 := m <<< z1
  let z2 : UInt64 := if m1 < 281474976710656 then 16 else 0
  let m2 := m1 <<< z2
  let z3 : UInt64 := if m2 < 72057594037927936 then 8 else 0
  let m3 := m2 <<< z3
  let z4 : UInt64 := if m3 < 1152921504606846976 then 4 else 0
  let m4 := m3 <<< z4
  let z5 : UInt64 := if m4 < 4611686018427387904 then 2 else 0
  let m5 := m4 <<< z5
  let z6 : UInt64 := if m5 < 9223372036854775808 then 1 else 0
  z1 + z2 + z3 + z4 + z5 + z6

/-- The word the kernel answers when it declines: a NaN pattern, never a
    reader result, so the caller tests it and falls back to `readExact`. -/
def declined : UInt64 := 18446744073709551615

/-- Round `X / 2^s` half-even from `P = (pHi, pMid, pLo)`, where `X` is
    `P` itself (`exact`) or lies in `(P - mz, P]`, and `s = hz + k`. -/
@[inline]
def roundCore (sign : Sign) (mz pHi pMid pLo : UInt64) (hz : Int) (exact : Bool) : UInt64 :=
  let top : UInt64 := pHi >>> 63
  -- bit length of `X`: that of `P`, unless `P` just crossed `2^191`
  if !exact && top = 1 && pHi = 9223372036854775808 && pMid = 0 && pLo < mz then declined
  else
    let t : Int := 190 + (top.toNat : Int) - hz
    if 1023 ≤ t then declined
    else
      let k : Int := max (t - 52) (-1074)
      let s : Int := hz + k
      if s < 130 ∨ 192 < s then declined
      else
        let sN : Nat := s.toNat
        -- `q = P >>> s`, `b` = bit `s - 1`, `lowZero` = the bits below it are zero
        let q : UInt64 := if sN = 192 then 0 else pHi >>> UInt64.ofNat (sN - 128)
        let b : UInt64 := (pHi >>> UInt64.ofNat (sN - 129)) &&& 1
        let restHi : UInt64 := pHi &&& ((1 <<< UInt64.ofNat (sN - 129)) - 1)
        let lowZero : Bool := restHi = 0 && pMid = 0
        -- an inexact `P` whose rest is below `mz` may hide a tie: decline
        if !exact && lowZero && pLo < mz then declined
        else
          let n : UInt64 :=
            if b = 0 then q else if exact && lowZero && pLo = 0 then q + (q &&& 1) else q + 1
          if n = 0 then Word.pack sign 0 0 else packFinite sign n k

/-! ## The kernel -/

/-- Fast `Decimal → binary64 word`; `declined` defers to `readExact`. -/
def readFast (d : Decimal) : UInt64 :=
  let m := d.significand
  let e := d.exponent
  if m = 0 then Word.pack d.sign 0 0
  else if 18446744073709551616 ≤ m then declined
  else if 308 < e then Word.pack d.sign 2047 0
  else if e < -324 then declined
  else
    let mU : UInt64 := UInt64.ofNat m
    let z : UInt64 := lzShift mU
    let mz : UInt64 := mU <<< z
    if 0 ≤ e then
      let g := pow10Lookup128 e        -- `(gHi, gLo, h)`
      let p := mul64x128 mz g.1 g.2.1  -- `(pHi, pMid, pLo)`
      roundCore d.sign mz p.1 p.2.1 p.2.2 (g.2.2 + (z.toNat : Int)) (decide (e ≤ 54))
    else
      let ne : Nat := (-e).toNat
      if ne ≤ 27 ∧ m % 5 ^ ne = 0 then
        let mU' : UInt64 := UInt64.ofNat (m / 5 ^ ne)
        let z' : UInt64 := lzShift mU'
        let mz' : UInt64 := mU' <<< z'
        let p := mul64x128 mz' 9223372036854775808 0
        roundCore d.sign mz' p.1 p.2.1 p.2.2 (127 - e + (z'.toNat : Int)) true
      else
        let g := pow10Lookup128 e
        let p := mul64x128 mz g.1 g.2.1
        roundCore d.sign mz p.1 p.2.1 p.2.2 (g.2.2 + (z.toNat : Int)) false

/-- The live reader: the fast kernel, `readExact` when it declines. -/
def ofDecimalBits_fast (d : Decimal) : UInt64 :=
  let w := readFast d
  if w = declined then (Float.Model.pack (readExact d)).toBits else w

/-! ## Proof: the 192-bit product -/

/-- The value of a `(hi, mid, lo)` triple. -/
def val192 (hi mid lo : UInt64) : Nat := hi.toNat * 2 ^ 128 + mid.toNat * 2 ^ 64 + lo.toNat

theorem val192_lt (hi mid lo : UInt64) : val192 hi mid lo < 2 ^ 192 := by
  unfold val192
  have := hi.toNat_lt; have := mid.toNat_lt; have := lo.toNat_lt
  omega

theorem mul64x128_val (a gHi gLo : UInt64) :
    val192 (mul64x128 a gHi gLo).1 (mul64x128 a gHi gLo).2.1 (mul64x128 a gHi gLo).2.2
      = a.toNat * (gHi.toNat * 2 ^ 64 + gLo.toNat) := by
  unfold mul64x128 val192
  simp only []
  have hA := Nat.mul_le_mul (Nat.le_sub_one_of_lt a.toNat_lt) (Nat.le_sub_one_of_lt gLo.toNat_lt)
  have hB := Nat.mul_le_mul (Nat.le_sub_one_of_lt a.toNat_lt) (Nat.le_sub_one_of_lt gHi.toNat_lt)
  rw [Nat.mul_add, ← Nat.mul_assoc]
  split
  all_goals
    word_simp at *
    simp only [mulHi64_toNat_eq] at *
    generalize a.toNat * gLo.toNat = A at *
    generalize a.toNat * gHi.toNat = B at *
    omega

/-! ## Proof: the packed word -/

open Srtfp.Model Float.Model Float.Model.UnpackedFloat in
theorem sign_toBitVec_toNat (s : Sign) :
    s.toBitVec.toNat = (match s with | .negative => 1 | .positive => 0) := by
  cases s <;> rfl

open Srtfp.Model Float.Model Float.Model.UnpackedFloat in
/-- The three fields, as a word. -/
theorem ofBitVec_packComponents (s : Sign) (e : BitVec 11) (m : BitVec 52) :
    UInt64.ofBitVec (packComponents Format.binary64 s e m) = Word.pack s e.toNat m.toNat := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_ofBitVec, packComponents_toNat, sign_toBitVec_toNat, pack_toNat s _ _ e.isLt m.isLt]
  cases s <;> simp only [] <;> omega

theorem toBits_pack_zero (s : Sign) : (Float.Model.pack (.zero s)).toBits = Word.pack s 0 0 :=
  ofBitVec_packComponents s 0 0

theorem toBits_pack_infinity (s : Sign) : (Float.Model.pack (.infinity s)).toBits = Word.pack s 2047 0 :=
  ofBitVec_packComponents s (-1#_) 0

open Srtfp.Model Float.Model Float.Model.UnpackedFloat in
theorem toBits_pack_finite (s : Sign) {n : Nat} {k : Int} (hn : 0 < n) (hleg : Legal n k) :
    (Float.Model.pack (.finite s n k hn)).toBits
      = Word.pack s (if n < 2 ^ 52 then 0 else (k + 1075).toNat) (n % 2 ^ 52) := by
  obtain ⟨hA, hB, -, -, -⟩ := binary64_facts
  show UInt64.ofBitVec (UnpackedFloat.pack Format.binary64 (.finite s n k hn)) = _
  rw [pack_finite s hn hleg, ofBitVec_packComponents, BitVec.toNat_ofNat, BitVec.toNat_ofNat, hB,
    Nat.mod_eq_of_lt (by have := hleg.2.2.1; split <;> omega)]

/-- The kernel's word for a significand `n ≤ 2^53` on the grid `k` is the
    packing of `readMag`'s result. -/
theorem packFinite_toBits (sign : Sign) {nU : UInt64} {n : Nat} {k : Int} (hn : nU.toNat = n)
    (h53 : n ≤ 2 ^ 53) (hk0 : -1074 ≤ k) (hk1 : k ≤ 970) (h52 : k ≠ -1074 → 2 ^ 52 ≤ n) :
    (if nU = 0 then Word.pack sign 0 0 else packFinite sign nU k)
      = (Float.Model.pack (ofSig sign n k)).toBits := by
  unfold ofSig
  by_cases hn0 : n = 0
  · rw [if_pos (by word), dif_pos hn0, toBits_pack_zero]
  rw [if_neg (by word), dif_neg hn0]
  unfold packFinite
  by_cases hc53 : n = 2 ^ 53
  · rw [if_pos hc53, if_neg (by word), if_pos (by word),
      toBits_pack_finite sign (by decide) ⟨by decide, by omega, by omega, fun _ => Nat.le_refl _⟩,
      if_neg (Nat.lt_irrefl _), Nat.mod_self, show k + 1 + 1075 = k + 1076 by omega]
  rw [if_neg hc53, toBits_pack_finite sign (Nat.pos_of_ne_zero hn0) ⟨by omega, by omega, by omega, h52⟩]
  by_cases hlt : n < 2 ^ 52
  · rw [if_pos (by word), if_pos hlt, Nat.mod_eq_of_lt hlt, hn]
  · rw [if_neg (by word), if_neg (by word), if_neg hlt,
      show (nU - 4503599627370496).toNat = n % 2 ^ 52 by word]

/-! ## Proof: the shifts -/

/-- `x >>> j` for a shift below 64. -/
theorem toNat_shiftRight_lt {x : UInt64} {j : Nat} (hj : j < 64) :
    (x >>> UInt64.ofNat j).toNat = x.toNat / 2 ^ j := by
  rw [UInt64.toNat_shiftRight, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega : j < 2 ^ 64),
    Nat.mod_eq_of_lt hj, Nat.shiftRight_eq_div_pow]

/-- The low `j` bits, for `j < 64`. -/
theorem toNat_and_mask {x : UInt64} {j : Nat} (hj : j < 64) :
    (x &&& ((1 <<< UInt64.ofNat j) - 1)).toNat = x.toNat % 2 ^ j := by
  have h1 : ((1 : UInt64) <<< UInt64.ofNat j).toNat = 2 ^ j := by
    rw [UInt64.toNat_shiftLeft, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega : j < 2 ^ 64),
      Nat.mod_eq_of_lt hj, UInt64.toNat_ofNat, Nat.shiftLeft_eq, show (1 : Nat) % 2 ^ 64 = 1 from rfl,
      Nat.one_mul]
    exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hj)
  rw [UInt64.toNat_and, UInt64.toNat_sub_of_le _ _ (by
      rw [UInt64.le_iff_toNat_le, h1, UInt64.toNat_ofNat]; exact Nat.one_le_two_pow),
    h1, UInt64.toNat_ofNat, show (1 : Nat) % 2 ^ 64 = 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

/-- `P / 2^s`, bit `s - 1` of `P` and the bits below it, read off the
    limbs, for `130 ≤ s ≤ 192`. -/
theorem shift_facts (pHi pMid pLo : UInt64) {sN : Nat} (h130 : 130 ≤ sN) (h192 : sN ≤ 192) :
    (if sN = 192 then (0 : UInt64) else pHi >>> UInt64.ofNat (sN - 128)).toNat = val192 pHi pMid pLo / 2 ^ sN
    ∧ ((pHi >>> UInt64.ofNat (sN - 129)) &&& 1).toNat = val192 pHi pMid pLo / 2 ^ (sN - 1) % 2
    ∧ val192 pHi pMid pLo % 2 ^ (sN - 1)
        = (pHi &&& ((1 <<< UInt64.ofNat (sN - 129)) - 1)).toNat * 2 ^ 128 + pMid.toNat * 2 ^ 64 + pLo.toNat := by
  have hMid := pMid.toNat_lt
  have hLo := pLo.toNat_lt
  -- `P = pHi · 2^128 + low` with `low < 2^128`: for `128 ≤ j`, `P / 2^j` and `P % 2^j` come from `pHi`
  have key : ∀ j, 128 ≤ j → val192 pHi pMid pLo / 2 ^ j = pHi.toNat / 2 ^ (j - 128)
      ∧ val192 pHi pMid pLo % 2 ^ j
        = pHi.toNat % 2 ^ (j - 128) * 2 ^ 128 + pMid.toNat * 2 ^ 64 + pLo.toNat := by
    intro j hj
    have h1 := Nat.div_add_mod pHi.toNat (2 ^ (j - 128))
    have h2 := Nat.mod_lt pHi.toNat (Nat.two_pow_pos (j - 128))
    rw [show 2 ^ j = 2 ^ (j - 128) * 2 ^ 128 by rw [← Nat.pow_add, Nat.sub_add_cancel hj]]
    refine (Nat.div_mod_unique (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _))).mpr ⟨?_, by omega⟩
    unfold val192; rw [Nat.mul_right_comm (2 ^ (j - 128))]; omega
  refine ⟨?_, ?_, ?_⟩
  · split
    · rename_i h; subst h
      rw [UInt64.toNat_ofNat, Nat.div_eq_of_lt (val192_lt _ _ _)]
    · rw [toNat_shiftRight_lt (by omega), (key sN (by omega)).1]
  · rw [UInt64.toNat_and, toNat_shiftRight_lt (by omega), (key (sN - 1) (by omega)).1,
      show sN - 1 - 128 = sN - 129 by omega]; word
  · rw [toNat_and_mask (by omega), (key (sN - 1) (by omega)).2, show sN - 1 - 128 = sN - 129 by omega]

/-! ## Proof: the rounding core -/

/-- Rounding `X / 2^s` from the bits of `P`, for `X = P` (`exact`) or
    `P - mz < X ≤ P` with `mz` at most the bits of `P` below bit `s - 1`:
    the choice among `q`, `q + 1` and the even neighbour on a tie is
    `roundEven`. -/
theorem round_from_bits (Pn sN : Nat) (hs : 1 ≤ sN) (X : Rat) (mz : Nat) (exact : Bool)
    (hXP : X ≤ Pn) (hPX : if exact then X = (Pn : Rat) else (Pn : Rat) - mz < X)
    (hguard : exact = false → mz ≤ Pn % 2 ^ (sN - 1)) :
    roundEven (X / (2 : Rat) ^ sN)
      = ((if Pn / 2 ^ (sN - 1) % 2 = 0 then Pn / 2 ^ sN
          else if exact ∧ Pn % 2 ^ (sN - 1) = 0 then Pn / 2 ^ sN + Pn / 2 ^ sN % 2
          else Pn / 2 ^ sN + 1 : Nat) : Int) := by
  obtain ⟨sN', rfl⟩ : ∃ s', sN = s' + 1 := ⟨sN - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hguard ⊢
  generalize hH : 2 ^ sN' = H at *
  have hH0 : 0 < H := by rw [← hH]; exact Nat.two_pow_pos _
  have h2H : 2 ^ (sN' + 1) = 2 * H := by rw [← hH, Nat.pow_succ, Nat.mul_comm]
  rw [show (2 : Rat) ^ (sN' + 1) = ((2 * H : Nat) : Rat) by rw [← h2H]; norm_cast, h2H]
  -- `P = 2QH + bH + r` with `b` the bit and `r < H` the rest
  have e1 := Nat.div_add_mod Pn H
  have e2 := Nat.div_add_mod (Pn / H) 2
  have hb2 := Nat.mod_lt (Pn / H) (by decide : 0 < 2)
  have hr2 := Nat.mod_lt Pn hH0
  rw [Nat.div_div_eq_div_mul, Nat.mul_comm H 2] at e2
  generalize Pn / (2 * H) = Q at *
  generalize Pn / H % 2 = b at *
  generalize Pn % H = r at *
  have hdec : Pn = 2 * (Q * H) + b * H + r := by grind
  have hP : (Pn : Rat) = 2 * ((Q : Rat) * H) + b * H + r := by rw [hdec]; push_cast; rfl
  have hr : (r : Rat) < H := by exact_mod_cast hr2
  have h2HR : (0 : Rat) < ((2 * H : Nat) : Rat) := by exact_mod_cast Nat.mul_pos (by decide) hH0
  rw [hP] at hXP
  cases exact <;> simp only [Bool.false_eq_true, Bool.true_eq_false, false_and, true_and, if_false,
    if_true, false_implies, forall_const] at hPX hguard ⊢
  · -- inexact: `2QH + bH < X`
    have hmz : (mz : Rat) ≤ r := by exact_mod_cast hguard
    rw [hP] at hPX
    rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl
    · rw [if_pos rfl]; apply roundEven_eq_of_between (by omega : 0 < 2 * H) <;> push_cast <;> grind
    · rw [if_neg (by decide)]; apply roundEven_eq_of_between (by omega : 0 < 2 * H) <;> push_cast <;> grind
  · -- exact: `X = 2QH + bH + r`
    subst hPX
    rw [hP]
    rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl
    · rw [if_pos rfl]; apply roundEven_eq_of_between (by omega : 0 < 2 * H) <;> push_cast <;> grind
    · rw [if_neg (by decide)]
      by_cases hr0 : r = 0
      · rw [if_pos hr0]; subst hr0
        rw [show (2 * ((Q : Rat) * H) + ((1 : Nat) : Rat) * H + ((0 : Nat) : Rat))
            / ((2 * H : Nat) : Rat) = (Q : Rat) + 1/2 by rw [div_eq_iff h2HR]; push_cast; grind]
        exact roundEven_tie Q
      · rw [if_neg hr0]
        have hr1 : (1 : Rat) ≤ r := by exact_mod_cast Nat.pos_of_ne_zero hr0
        apply roundEven_eq_of_between (by omega : 0 < 2 * H) <;> push_cast <;> grind

/-- The rounding core on a product: `P = mz · g` with `g − 1 < Y ≤ g`
    (`Y = g` when `exact`), `mz ≥ 2^63` and `Y ≥ 2^127`, so `X = mz · Y` has
    191 or 192 bits. The word is `readMag` of `X / 2^hz`. -/
theorem roundCore_spec (sign : Sign) (mz pHi pMid pLo : UInt64) (hz : Int) (exact : Bool)
    (Y : Rat) (g : Nat) (hmz : 2 ^ 63 ≤ mz.toNat) (hP : val192 pHi pMid pLo = mz.toNat * g)
    (hY : (2 : Rat) ^ (127 : Nat) ≤ Y) (hYg : Y ≤ g) (hgY : if exact then Y = g else (g : Rat) - 1 < Y)
    {w : UInt64} (h : roundCore sign mz pHi pMid pLo hz exact = w) (hw : w ≠ declined) :
    w = (Float.Model.pack (readMag sign (mz.toNat * Y / (2 : Rat) ^ hz))).toBits := by
  -- `2^190 ≤ X ≤ P`, and `P - mz < X` unless `X = P`
  have hmzR : (2 : Rat) ^ (63 : Nat) ≤ mz.toNat := by exact_mod_cast hmz
  have hmz0 : (0 : Rat) ≤ mz.toNat := Rat.natCast_nonneg
  have hPR : (val192 pHi pMid pLo : Rat) = mz.toNat * g := by rw [hP, Rat.natCast_mul]
  have hX190 : (2 : Rat) ^ (190 : Nat) ≤ mz.toNat * Y := by
    rw [show (2 : Rat) ^ (190 : Nat) = 2 ^ (63 : Nat) * 2 ^ (127 : Nat) by rw [← Rat.pow_add]]
    exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_right hmzR (Rat.pow_nonneg (by decide)))
      (Rat.mul_le_mul_of_nonneg_left hY hmz0)
  have hXP : mz.toNat * Y ≤ (val192 pHi pMid pLo : Rat) := by
    rw [hPR]; exact Rat.mul_le_mul_of_nonneg_left hYg hmz0
  have hPX : if exact then mz.toNat * Y = (val192 pHi pMid pLo : Rat)
      else (val192 pHi pMid pLo : Rat) - mz.toNat < mz.toNat * Y := by
    rw [hPR]
    split at hgY
    · rename_i hex; rw [if_pos hex, hgY]
    · rename_i hex; rw [if_neg hex]
      have := Rat.mul_lt_mul_of_pos_left hgY (lt_of_lt_of_le (Rat.pow_pos (by decide)) hmzR); grind
  generalize mz.toNat * Y = X at *
  have hHi := pHi.toNat_lt
  have hMid := pMid.toNat_lt
  have hLo := pLo.toNat_lt
  have hmz64 := mz.toNat_lt
  have hPval : val192 pHi pMid pLo = pHi.toNat * 2 ^ 128 + pMid.toNat * 2 ^ 64 + pLo.toNat := rfl
  unfold roundCore at h
  dsimp only at h
  iterate 4 (split at h; exact absurd h.symm hw)
  rename_i hmargin ht hs hguard
  generalize htN : (pHi >>> 63).toNat = topN at *
  word_simp at htN
  generalize hk : max (190 + (topN : Int) - hz - 52) (-1074) = k at *
  generalize hsN : (hz + k).toNat = sN at *
  have hs130 : 130 ≤ sN := by omega
  have hs192 : sN ≤ 192 := by omega
  obtain ⟨hq, hb, hrest⟩ := shift_facts pHi pMid pLo hs130 hs192
  generalize hPn : val192 pHi pMid pLo = Pn at *
  generalize hqU : (if sN = 192 then (0 : UInt64) else pHi >>> UInt64.ofNat (sN - 128)) = qU at *
  generalize hbU : (pHi >>> UInt64.ofNat (sN - 129)) &&& 1 = bU at *
  generalize hrU : pHi &&& ((1 <<< UInt64.ofNat (sN - 129)) - 1) = rU at *
  -- the two guards on an inexact `P`, as facts about `P`
  have hmarg : exact = false → topN = 1 → 2 ^ 191 + mz.toNat ≤ Pn := by
    rintro rfl h1
    simp only [Bool.not_false, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq] at hmargin
    word_simp at hmargin; omega
  have hguard' : exact = false → mz.toNat ≤ Pn % 2 ^ (sN - 1) := by
    rintro rfl
    simp only [Bool.not_false, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq] at hguard
    rw [hrest]; word_simp at hguard; omega
  -- the bit length of `X` is that of `P`: `2^(190 + topN) ≤ X < 2^(191 + topN)`
  have hbits : (2 : Rat) ^ (190 + topN : Nat) ≤ X ∧ X < (2 : Rat) ^ (191 + topN : Nat) := by
    have hPhi : Pn < 2 ^ (191 + topN) := by
      rcases (show topN = 0 ∨ topN = 1 by omega) with rfl | rfl <;> omega
    refine ⟨?_, lt_of_le_of_lt hXP (by exact_mod_cast hPhi)⟩
    rcases (show topN = 0 ∨ topN = 1 by omega) with rfl | rfl
    · exact hX190
    cases exact
    · rw [if_neg Bool.false_ne_true] at hPX
      have hm : ((2 ^ 191 + mz.toNat : Nat) : Rat) ≤ Pn := by exact_mod_cast hmarg rfl rfl
      push_cast at hm
      exact Rat.le_of_lt (lt_of_le_of_lt (by grind) hPX)
    · rw [if_pos rfl] at hPX
      rw [hPX]; exact_mod_cast (by omega : 2 ^ (190 + 1) ≤ Pn)
  -- `x = X / 2^hz` lies in the binade `[2^t, 2^(t + 1))`, `t = 190 + topN - hz`
  have hzpos : (0 : Rat) < (2 : Rat) ^ hz := two_zpow_pos hz
  have hx : (2 : Rat) ^ (190 + (topN : Int) - hz) ≤ X / (2 : Rat) ^ hz
      ∧ X / (2 : Rat) ^ hz < (2 : Rat) ^ (190 + (topN : Int) - hz + 1) := by
    rw [le_div_iff hzpos, Rat.div_lt_iff hzpos, ← Rat.zpow_add (by decide), ← Rat.zpow_add (by decide),
      show 190 + (topN : Int) - hz + hz = ((190 + topN : Nat) : Int) by omega,
      show 190 + (topN : Int) - hz + 1 + hz = ((191 + topN : Nat) : Int) by omega,
      Rat.zpow_natCast, Rat.zpow_natCast]
    exact hbits
  generalize hxdef : X / (2 : Rat) ^ hz = x at *
  have hk' : gridExp x = k :=
    gridExp_eq_of (Rat.le_of_lt (lt_of_lt_of_le (two_zpow_pos _) hx.1)) (by omega)
      (lt_of_lt_of_le hx.2 (zpow_le_zpow_right₀ (by decide) (by omega)))
      (Or.imp_right (fun (hc : k + 52 = 190 + (topN : Int) - hz) => hc ▸ hx.1) (by omega))
  have hthr : ¬ ((2 : Rat) ^ 1024 - 2 ^ 970 ≤ x) :=
    Rat.not_le.mpr (lt_of_lt_of_le
      (lt_of_lt_of_le hx.2 (zpow_le_zpow_right₀ (by decide) (by omega : _ ≤ (1023 : Int))))
      (by decide +kernel))
  -- the scaled value `x / 2^k = X / 2^s`
  have hsdef : x / (2 : Rat) ^ k = X / (2 : Rat) ^ sN := by
    rw [← hxdef, ← div_div, ← Rat.zpow_add (by decide), show hz + k = (sN : Int) by omega,
      Rat.zpow_natCast]
  -- the kernel's bits
  have hQlt : Pn / 2 ^ sN < 2 ^ 62 :=
    Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_le (by omega : Pn < 2 ^ 192)
      (by rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)))
  have hqU1 : (qU + 1).toNat = Pn / 2 ^ sN + 1 := by word
  have hqUodd : (qU + (qU &&& 1)).toNat = Pn / 2 ^ sN + Pn / 2 ^ sN % 2 := by word
  have hbU0 : (bU = 0) ↔ Pn / 2 ^ (sN - 1) % 2 = 0 := by word
  have hrestZ : ((exact && (rU = 0 && pMid = 0) && pLo = 0) = true) ↔ (exact ∧ Pn % 2 ^ (sN - 1) = 0) := by
    rw [Bool.and_assoc, Bool.and_eq_true]
    exact and_congr_right fun _ => by simp only [Bool.and_eq_true, decide_eq_true_eq]; rw [hrest]; word
  -- the significand, as `roundEven` and as the kernel's word
  generalize hnN : (if Pn / 2 ^ (sN - 1) % 2 = 0 then Pn / 2 ^ sN
      else if exact ∧ Pn % 2 ^ (sN - 1) = 0 then Pn / 2 ^ sN + Pn / 2 ^ sN % 2
      else Pn / 2 ^ sN + 1 : Nat) = nN
  have hn' : roundEven (x / (2 : Rat) ^ k) = nN := by
    rw [hsdef, round_from_bits Pn sN (by omega) X mz.toNat exact hXP hPX hguard', hnN]
  have hkpos : (0 : Rat) < (2 : Rat) ^ k := two_zpow_pos k
  have hn53 : nN ≤ 2 ^ 53 := by
    have := roundEven_le (x := x / 2 ^ k) (b := 2 ^ 53) (by
      rw [← two_zpow_natCast, Rat.div_lt_iff hkpos, ← Rat.zpow_add (by decide)]
      exact lt_of_lt_of_le hx.2 (zpow_le_zpow_right₀ (by decide) (by omega)))
    rw [hn'] at this; exact_mod_cast this
  have hn52 : k ≠ -1074 → 2 ^ 52 ≤ nN := fun hk1074 => by
    have := roundEven_ge (y := x / 2 ^ k) (b := 2 ^ 52) (by
      rw [← two_zpow_natCast, le_div_iff hkpos, ← Rat.zpow_add (by decide)]
      exact Rat.le_trans (zpow_le_zpow_right₀ (by decide) (by omega)) hx.1)
    rw [hn'] at this; exact_mod_cast this
  -- assemble
  subst h
  rw [packFinite_toBits sign (n := nN) _ hn53 (by omega) (by omega) hn52]
  · unfold readMag; rw [if_neg hthr, hk', hn', Int.toNat_natCast]
  · rw [← hnN]; simp only [apply_ite UInt64.toNat, hq, hqU1, hqUodd, hbU0, hrestZ]

/-! ## Proof: the table entry against `10^e` -/

open Srtfp.Schubfach in
/-- `10^k · 2^h ≥ 2^127` for the table's shift. -/
theorem pow10Num_ge (k : Int) (hLo : -324 ≤ k) (hHi : k ≤ 324) :
    2 ^ 127 * pow10Den k (pow10Shift k) ≤ pow10Num k (pow10Shift k) := by
  unfold pow10Num pow10Den pow10Shift
  by_cases hk : k ≥ 0
  · rw [if_pos hk]
    generalize hn : 10 ^ k.toNat = n
    have hn0 : n ≠ 0 := by rw [← hn]; exact Nat.ne_of_gt (Nat.pow_pos (by decide))
    generalize hL : Nat.log2 n = L
    have h2 : 2 ^ L ≤ n := by rw [← hL]; exact Nat.log2_self_le hn0
    rw [show (-k).toNat = 0 by omega]
    by_cases hL' : L ≤ 127
    · rw [show ((127 : Int) - L).toNat = 127 - L by omega, show (-((127 : Int) - L)).toNat = 0 by omega]
      simp only [Nat.pow_zero, Nat.mul_one]
      calc 2 ^ 127 = 2 ^ L * 2 ^ (127 - L) := by rw [← Nat.pow_add, Nat.add_sub_cancel' hL']
        _ ≤ n * 2 ^ (127 - L) := Nat.mul_le_mul_right _ h2
    · rw [show ((127 : Int) - L).toNat = 0 by omega, show (-((127 : Int) - L)).toNat = L - 127 by omega]
      simp only [Nat.pow_zero, Nat.mul_one, Nat.one_mul]
      rw [← Nat.pow_add, Nat.add_sub_cancel' (by omega)]
      exact h2
  · rw [if_neg hk]
    generalize hn : 10 ^ (-k).toNat = n
    have hn0 : n ≠ 0 := by rw [← hn]; exact Nat.ne_of_gt (Nat.pow_pos (by decide))
    generalize hL : Nat.log2 n = L
    have h1 : n < 2 ^ (L + 1) := by rw [← hL]; exact Nat.lt_log2_self
    rw [show k.toNat = 0 by omega, show ((128 : Int) + L).toNat = 128 + L by omega,
      show (-((128 : Int) + L)).toNat = 0 by omega]
    simp only [Nat.pow_zero, Nat.mul_one, Nat.one_mul]
    rw [show 128 + L = 127 + (L + 1) by omega, Nat.pow_add]
    exact Nat.mul_le_mul_left _ (Nat.le_of_lt h1)

open Srtfp.Schubfach in
/-- For `0 ≤ k ≤ 54` the entry is exact: `2^(-h)` divides `10^k`. -/
theorem pow10Den_dvd (k : Int) (h0 : 0 ≤ k) (h54 : k ≤ 54) :
    pow10Den k (pow10Shift k) ∣ pow10Num k (pow10Shift k) := by
  unfold pow10Num pow10Den pow10Shift
  rw [if_pos h0, show (-k).toNat = 0 by omega, Nat.pow_zero, Nat.one_mul]
  generalize hn : 10 ^ k.toNat = n
  have hn0 : n ≠ 0 := by rw [← hn]; exact Nat.ne_of_gt (Nat.pow_pos (by decide))
  generalize hL : Nat.log2 n = L
  -- `L ≤ 127 + k` since `5^k < 2^127`
  have hLk : L ≤ 127 + k.toNat := by
    have h5 : 5 ^ k.toNat < 2 ^ 127 :=
      Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) (by omega : k.toNat ≤ 54)) (by decide)
    have h10 : n < 2 ^ (128 + k.toNat) := by
      rw [← hn, show (10 : Nat) = 2 * 5 by rfl, Nat.mul_pow, Nat.pow_add, Nat.mul_comm (2 ^ 128)]
      exact Nat.mul_lt_mul_of_pos_left (Nat.lt_of_lt_of_le h5 (Nat.pow_le_pow_right (by decide) (by omega)))
        (Nat.two_pow_pos _)
    have := (Nat.log2_lt hn0).mpr h10
    omega
  by_cases hL' : L ≤ 127
  · rw [show ((127 : Int) - L).toNat = 127 - L by omega, show (-((127 : Int) - L)).toNat = 0 by omega]
    simp only [Nat.pow_zero]
    exact Nat.one_dvd _
  · rw [show ((127 : Int) - L).toNat = 0 by omega, show (-((127 : Int) - L)).toNat = L - 127 by omega]
    simp only [Nat.pow_zero, Nat.mul_one]
    rw [← hn, show (10 : Nat) = 2 * 5 by rfl, Nat.mul_pow]
    exact Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) (Nat.dvd_mul_right _ _)

open Srtfp.Schubfach in
/-- The table entry `(g, h)` for `e`: `10^e · 2^h ∈ (g - 1, g]`, at least `2^127`,
    and exactly `g` when `0 ≤ e ≤ 54`. -/
theorem table_bounds (e : Int) (hLo : -324 ≤ e) (hHi : e ≤ 324) :
    (10 : Rat) ^ e * (2 : Rat) ^ (pow10Lookup128 e).2.2
        ≤ ((pow10Lookup128 e).1.toNat * 2 ^ 64 + (pow10Lookup128 e).2.1.toNat : Nat)
    ∧ (((pow10Lookup128 e).1.toNat * 2 ^ 64 + (pow10Lookup128 e).2.1.toNat : Nat) : Rat) - 1
        < (10 : Rat) ^ e * (2 : Rat) ^ (pow10Lookup128 e).2.2
    ∧ (2 : Rat) ^ (127 : Nat) ≤ (10 : Rat) ^ e * (2 : Rat) ^ (pow10Lookup128 e).2.2
    ∧ (0 ≤ e → e ≤ 54 →
        (((pow10Lookup128 e).1.toNat * 2 ^ 64 + (pow10Lookup128 e).2.1.toNat : Nat) : Rat)
          = (10 : Rat) ^ e * (2 : Rat) ^ (pow10Lookup128 e).2.2) := by
  have hinv := pow10Lookup128_invariant e hLo hHi
  have hge := pow10Num_ge e hLo hHi
  have hdvd := pow10Den_dvd e
  rw [show pow10Shift e = (pow10Lookup128 e).2.2 by rw [pow10Lookup128_eq e hLo hHi]; rfl] at hge hdvd
  generalize (pow10Lookup128 e).1.toNat * 2 ^ 64 + (pow10Lookup128 e).2.1.toNat = g at *
  generalize (pow10Lookup128 e).2.2 = hh at *
  have hden0 := pow10Den_pos e hh
  generalize hnum : pow10Num e hh = num at *
  generalize hden : pow10Den e hh = den at *
  have hdenR : (0 : Rat) < den := by exact_mod_cast hden0
  -- `10^e · 2^h = num / den`
  rw [show (10 : Rat) ^ e * (2 : Rat) ^ hh = (num : Rat) / den by
    rw [zpow_eq_div 10 e, zpow_eq_div 2 hh, div_mul_div_comm, ← hnum, ← hden]
    unfold pow10Num pow10Den; push_cast; rfl]
  refine ⟨(div_le_iff hdenR).mpr (by exact_mod_cast hinv.1), ?_,
    (le_div_iff hdenR).mpr (by exact_mod_cast hge), fun he0 he54 => ?_⟩
  · rw [Rat.lt_div_iff hdenR]
    have := Rat.natCast_lt_natCast.mpr hinv.2; push_cast at this; grind
  · obtain ⟨q, hq⟩ := hdvd he0 he54
    rw [hq] at hinv ⊢
    rw [show g = q by
      rw [← Nat.mul_div_cancel g hden0]
      exact Nat.div_eq_of_lt_le (Nat.mul_comm den q ▸ hinv.1)
        (by rw [Nat.succ_mul, Nat.mul_comm q den]; exact hinv.2)]
    push_cast; rw [Rat.mul_comm]; exact (Rat.mul_div_cancel (Rat.ne_of_gt hdenR)).symm

/-! ## Proof: the normalised significand -/

/-- One step: with `2^(64 - 2w) ≤ x`, shifting by `w` exactly when
    `x < 2^(64 - w)` keeps `x` below `2^64` and lifts it to `2^(64 - w)`. -/
theorem lz_step (x bound w : UInt64) (wN : Nat) (hw : wN ≤ 32)
    (hb : bound.toNat = 2 ^ (64 - wN)) (hwN : w.toNat = wN)
    (hx : 2 ^ (64 - 2 * wN) ≤ x.toNat) :
    let z : UInt64 := if x < bound then w else 0
    (x <<< z).toNat = x.toNat * 2 ^ z.toNat ∧ 2 ^ (64 - wN) ≤ (x <<< z).toNat ∧ z.toNat ≤ wN := by
  intro z
  have hxlt := x.toNat_lt
  have hp := Nat.two_pow_pos wN
  by_cases hc : x < bound
  · rw [show z = w from if_pos hc, UInt64.toNat_shiftLeft, hwN, Nat.mod_eq_of_lt (by omega : wN < 64),
      Nat.shiftLeft_eq]
    rw [UInt64.lt_iff_toNat_lt, hb] at hc
    have hprod : x.toNat * 2 ^ wN < 2 ^ 64 := by
      have := Nat.mul_lt_mul_of_pos_right hc hp
      rwa [← Nat.pow_add, Nat.sub_add_cancel (by omega)] at this
    have hlo : 2 ^ (64 - wN) ≤ x.toNat * 2 ^ wN := by
      have := Nat.mul_le_mul_right (2 ^ wN) hx
      rwa [← Nat.pow_add, show 64 - 2 * wN + wN = 64 - wN by omega] at this
    exact ⟨Nat.mod_eq_of_lt hprod, by rw [Nat.mod_eq_of_lt hprod]; exact hlo, Nat.le_refl _⟩
  · rw [show z = 0 from if_neg hc]
    rw [UInt64.lt_iff_toNat_lt, hb] at hc
    exact ⟨by word, by word, by word⟩

theorem lzShift_spec {m : Nat} (hm0 : m ≠ 0) (hm : m < 2 ^ 64) :
    (lzShift (UInt64.ofNat m)).toNat = 63 - m.log2 := by
  have hmN : (UInt64.ofNat m).toNat = m := by rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt hm]
  unfold lzShift
  dsimp only
  obtain ⟨e1, l1, b1⟩ := lz_step (UInt64.ofNat m) 4294967296 32 32 (by decide) (by decide) (by decide)
    (by rw [hmN]; show 2 ^ 0 ≤ m; omega)
  generalize (if UInt64.ofNat m < 4294967296 then (32 : UInt64) else 0) = z1 at *
  generalize UInt64.ofNat m <<< z1 = m1 at *
  obtain ⟨e2, l2, b2⟩ := lz_step m1 281474976710656 16 16 (by decide) (by decide) (by decide) l1
  generalize (if m1 < 281474976710656 then (16 : UInt64) else 0) = z2 at *
  generalize m1 <<< z2 = m2 at *
  obtain ⟨e3, l3, b3⟩ := lz_step m2 72057594037927936 8 8 (by decide) (by decide) (by decide) l2
  generalize (if m2 < 72057594037927936 then (8 : UInt64) else 0) = z3 at *
  generalize m2 <<< z3 = m3 at *
  obtain ⟨e4, l4, b4⟩ := lz_step m3 1152921504606846976 4 4 (by decide) (by decide) (by decide) l3
  generalize (if m3 < 1152921504606846976 then (4 : UInt64) else 0) = z4 at *
  generalize m3 <<< z4 = m4 at *
  obtain ⟨e5, l5, b5⟩ := lz_step m4 4611686018427387904 2 2 (by decide) (by decide) (by decide) l4
  generalize (if m4 < 4611686018427387904 then (2 : UInt64) else 0) = z5 at *
  generalize m4 <<< z5 = m5 at *
  obtain ⟨e6, l6, b6⟩ := lz_step m5 9223372036854775808 1 1 (by decide) (by decide) (by decide) l5
  generalize (if m5 < 9223372036854775808 then (1 : UInt64) else 0) = z6 at *
  generalize m5 <<< z6 = m6 at *
  have h6lt := m6.toNat_lt
  generalize hZ : z1.toNat + z2.toNat + z3.toNat + z4.toNat + z5.toNat + z6.toNat = Z at *
  rw [show (z1 + z2 + z3 + z4 + z5 + z6).toNat = Z by word]
  -- `2^63 ≤ m · 2^Z < 2^64` pins `log2 m = 63 - Z`
  have hval : m6.toNat = m * 2 ^ Z := by
    rw [e6, e5, e4, e3, e2, e1, hmN, ← hZ]; simp only [Nat.mul_assoc, ← Nat.pow_add]
  have hlog : m.log2 = 63 - Z := (Nat.log2_eq_iff hm0).mpr
    ⟨Nat.le_of_mul_le_mul_right (c := 2 ^ Z)
      (by rw [← Nat.pow_add, show 63 - Z + Z = 63 by omega, ← hval]; exact l6) (Nat.two_pow_pos Z),
     Nat.lt_of_mul_lt_mul_right (a := 2 ^ Z)
      (by rw [← Nat.pow_add, show 63 - Z + 1 + Z = 64 by omega, ← hval]; exact h6lt)⟩
  omega

theorem lzShift_eq {m : Nat} (hm0 : m ≠ 0) (hm : m < 2 ^ 64) :
    lzShift (UInt64.ofNat m) = UInt64.ofNat (63 - m.log2) := by
  apply UInt64.toNat_inj.mp
  rw [lzShift_spec hm0 hm, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]

/-- The normalised significand `mz = m · 2^(63 - log2 m)`, at least `2^63`. -/
theorem mz_facts {m : Nat} (hm0 : m ≠ 0) (hm : m < 2 ^ 64) :
    (UInt64.ofNat m <<< UInt64.ofNat (63 - m.log2)).toNat = m * 2 ^ (63 - m.log2)
    ∧ 2 ^ 63 ≤ m * 2 ^ (63 - m.log2) := by
  have hL1 : 2 ^ m.log2 ≤ m := Nat.log2_self_le hm0
  have hL2 : m < 2 ^ (m.log2 + 1) := Nat.lt_log2_self
  have hL64 : m.log2 < 64 := (Nat.log2_lt hm0).mpr hm
  generalize m.log2 = L at *
  have hlo : 2 ^ 63 ≤ m * 2 ^ (63 - L) := by
    have := Nat.mul_le_mul_right (2 ^ (63 - L)) hL1
    rwa [← Nat.pow_add, Nat.add_sub_cancel' (by omega)] at this
  have hhi : m * 2 ^ (63 - L) < 2 ^ 64 := by
    have := Nat.mul_lt_mul_of_pos_right hL2 (Nat.two_pow_pos (63 - L))
    rwa [← Nat.pow_add, show L + 1 + (63 - L) = 64 by omega] at this
  refine ⟨?_, hlo⟩
  word_simp
  rw [Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt (by omega : 63 - L < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : 63 - L < 64), Nat.mod_eq_of_lt hhi]

/-! ## Proof: the regimes -/

/-- The table regime: `X = mz · 10^e · 2^h` against `P = mz · g`. -/
theorem roundCore_table (sign : Sign) {m : Nat} (hm0 : m ≠ 0) (hm : m < 2 ^ 64) {e : Int}
    (hLo : -324 ≤ e) (hHi : e ≤ 324) (exact : Bool) (hex : exact = true → 0 ≤ e ∧ e ≤ 54)
    {w : UInt64}
    (h : let mz := UInt64.ofNat m <<< lzShift (UInt64.ofNat m)
         let g := pow10Lookup128 e
         let p := mul64x128 mz g.1 g.2.1
         roundCore sign mz p.1 p.2.1 p.2.2 (g.2.2 + ((lzShift (UInt64.ofNat m)).toNat : Int)) exact = w)
    (hw : w ≠ declined) :
    w = (Float.Model.pack (readMag sign ((m : Rat) * (10 : Rat) ^ e))).toBits := by
  dsimp only at h
  rw [lzShift_spec hm0 hm, lzShift_eq hm0 hm] at h
  obtain ⟨hmzN, hmzlo⟩ := mz_facts hm0 hm
  generalize 63 - m.log2 = z at *
  generalize UInt64.ofNat m <<< UInt64.ofNat z = mz at *
  obtain ⟨hb1, hb2, hb3, hb4⟩ := table_bounds e hLo hHi
  have hPval := mul64x128_val mz (pow10Lookup128 e).1 (pow10Lookup128 e).2.1
  generalize (pow10Lookup128 e).1.toNat * 2 ^ 64 + (pow10Lookup128 e).2.1.toNat = g at *
  generalize (pow10Lookup128 e).2.2 = hh at *
  -- `X / 2^(h + z) = m · 10^e`
  rw [show (m : Rat) * (10 : Rat) ^ e
      = (mz.toNat : Rat) * ((10 : Rat) ^ e * (2 : Rat) ^ hh) / (2 : Rat) ^ (hh + (z : Int)) by
    rw [Rat.zpow_add (by decide), Rat.zpow_natCast, hmzN]
    push_cast
    rw [show (m : Rat) * 2 ^ z * ((10 : Rat) ^ e * 2 ^ hh) = (m : Rat) * 10 ^ e * (2 ^ hh * 2 ^ z) by grind,
      Rat.mul_div_cancel (Rat.ne_of_gt (Rat.mul_pos (two_zpow_pos _) (Rat.pow_pos (by decide))))]]
  exact roundCore_spec sign mz _ _ _ _ exact _ g (by omega) hPval hb3 hb1
    (by split
        · exact (hb4 (hex ‹_›).1 (hex ‹_›).2).symm
        · exact hb2) h hw

/-- The exact binary regime: `x = (m / 5^{-e}) · 2^e`, run with `g = 2^127`. -/
theorem roundCore_binary (sign : Sign) {m : Nat} (hm0 : m ≠ 0) (hm : m < 2 ^ 64) {e : Int}
    (he : e < 0) (hdiv : m % 5 ^ (-e).toNat = 0) {w : UInt64}
    (h : let mz := UInt64.ofNat (m / 5 ^ (-e).toNat) <<< lzShift (UInt64.ofNat (m / 5 ^ (-e).toNat))
         let p := mul64x128 mz 9223372036854775808 0
         roundCore sign mz p.1 p.2.1 p.2.2
           (127 - e + ((lzShift (UInt64.ofNat (m / 5 ^ (-e).toNat))).toNat : Int)) true = w)
    (hw : w ≠ declined) :
    w = (Float.Model.pack (readMag sign ((m : Rat) * (10 : Rat) ^ e))).toBits := by
  dsimp only at h
  generalize hne : (-e).toNat = ne at *
  generalize hm' : m / 5 ^ ne = m' at *
  have h5pos : 0 < 5 ^ ne := Nat.pow_pos (by decide)
  have hmm : m = m' * 5 ^ ne := by
    rw [← hm']; exact (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hdiv)).symm
  have hm'0 : m' ≠ 0 := by intro hc; rw [hc, Nat.zero_mul] at hmm; exact hm0 hmm
  have hm'lt : m' < 2 ^ 64 := by
    rw [hmm] at hm; exact Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right _ h5pos) hm
  rw [lzShift_spec hm'0 hm'lt, lzShift_eq hm'0 hm'lt] at h
  obtain ⟨hmzN, hmzlo⟩ := mz_facts hm'0 hm'lt
  generalize 63 - m'.log2 = z at *
  generalize UInt64.ofNat m' <<< UInt64.ofNat z = mz at *
  have hPval := mul64x128_val mz 9223372036854775808 0
  rw [show (9223372036854775808 : UInt64).toNat * 2 ^ 64 + (0 : UInt64).toNat = 2 ^ 127 by decide] at hPval
  -- `X / 2^(127 - e + z) = m · 10^e`
  rw [show (m : Rat) * (10 : Rat) ^ e
      = (mz.toNat : Rat) * ((2 ^ 127 : Nat) : Rat) / (2 : Rat) ^ (127 - e + (z : Int)) by
    have hcast : (m' : Rat) * 2 ^ z * 2 ^ (127 : Nat) * (10 : Rat) ^ ne = (m : Rat) * 2 ^ (127 + ne + z) := by
      exact_mod_cast (show m' * 2 ^ z * 2 ^ 127 * 10 ^ ne = m * 2 ^ (127 + ne + z) by
        rw [hmm, show (10 : Nat) = 2 * 5 by rfl, Nat.mul_pow, Nat.pow_add, Nat.pow_add]; grind)
    rw [hmzN, show e = -(ne : Int) by omega,
      show (127 : Int) - -(ne : Int) + (z : Int) = ((127 + ne + z : Nat) : Int) by omega,
      Rat.zpow_natCast, Rat.zpow_neg, Rat.zpow_natCast, eq_div_iff (Rat.pow_pos (by decide))]
    push_cast
    have hinv : (10 : Rat) ^ ne * ((10 : Rat) ^ ne)⁻¹ = 1 :=
      Rat.mul_inv_cancel _ (Rat.ne_of_gt (Rat.pow_pos (by decide)))
    grind]
  exact roundCore_spec sign mz _ _ _ _ true _ (2 ^ 127) (by omega) hPval (by exact_mod_cast Nat.le_refl _)
    Rat.le_refl (by rw [if_pos rfl]) h hw

/-! ## Proof: the kernel -/

theorem readFast_some (d : Decimal) {w : UInt64} (h : readFast d = w) (hw : w ≠ declined) :
    w = ofDecimalBits d := by
  unfold readFast at h
  dsimp only at h
  rw [ofDecimalBits_eq_reference]
  unfold referenceBits
  rw [read_eq_readMag, abs_toRat]
  split at h
  · rename_i hm0
    rw [← h, hm0]; push_cast; rw [Rat.zero_mul, readMag_zero, toBits_pack_zero]
  rename_i hm0
  split at h
  · exact absurd h.symm hw
  rename_i hm
  split at h
  · rename_i hbig
    rw [← h, readMag_infinity _ (overflow_of_big hm0 hbig), toBits_pack_infinity]
  rename_i hbig
  split at h
  · exact absurd h.symm hw
  rename_i hsmall
  have hm' : d.significand < 2 ^ 64 := by omega
  split at h
  · exact roundCore_table d.sign hm0 hm' (by omega) (by omega) _
      (fun hx => ⟨‹_›, of_decide_eq_true hx⟩) h hw
  split at h
  · rename_i hb; exact roundCore_binary d.sign hm0 hm' (by omega) hb.2 h hw
  · exact roundCore_table d.sign hm0 hm' (by omega) (by omega) false
      (fun hx => absurd hx (by decide)) h hw

/-! ## Registration -/

theorem ofDecimalBits_fast_eq (d : Decimal) : ofDecimalBits_fast d = ofDecimalBits d := by
  unfold ofDecimalBits_fast
  dsimp only
  by_cases hd : readFast d = declined
  · rw [if_pos hd, readExact_eq, ofDecimalBits_eq_reference]; rfl
  · rw [if_neg hd]; exact readFast_some d rfl hd

@[csimp]
theorem ofDecimalBits_eq_fast : @ofDecimalBits = @ofDecimalBits_fast :=
  funext fun d => (ofDecimalBits_fast_eq d).symm

theorem read_ne_nan (d : Decimal) : read d ≠ .notANumber := by
  unfold read
  dsimp only
  split
  · exact fun h => UnpackedFloat.noConfusion h
  · split
    · exact fun h => UnpackedFloat.noConfusion h
    · split <;> exact fun h => UnpackedFloat.noConfusion h

/-- `ofDecimal` through its bits: the model's round-trip on a word that is
    never a NaN. -/
theorem ofDecimal_eq_ofBits (d : Decimal) : ofDecimal d = Float.ofBits (ofDecimalBits d) := by
  show Float.ofModel d.toModel = Float.ofModel (Float.Model.ofBits d.toModel.toBits)
  rw [Upstream.toModel_eq_read]
  apply congrArg
  apply Srtfp.Model.model_ext
  rw [Srtfp.Model.toBits_ofBits _ (by
    show Spec.unpack (referenceBits d) ≠ _
    rw [unpack_referenceBits]; exact read_ne_nan d)]

/-- `ofDecimal` over the fast kernel. -/
def ofDecimal_fast (d : Decimal) : Float := Float.ofBits (ofDecimalBits_fast d)

@[csimp]
theorem ofDecimal_eq_fast : @ofDecimal = @ofDecimal_fast :=
  funext fun d => by
    show ofDecimal d = Float.ofBits (ofDecimalBits_fast d)
    rw [ofDecimal_eq_ofBits, ofDecimalBits_fast_eq]

/-- The verified fast conversion as a replacement for Lean's model operation. -/
def ofScientificFast (m : Nat) (e : Int) : Float.Model where
  toBits := ofDecimalBits_fast ⟨.positive, m, e⟩
  valid := by
    rw [ofDecimalBits_fast_eq]
    exact (Float.Model.ofScientific m e).valid

theorem ofScientificFast_eq (m : Nat) (e : Int) :
    ofScientificFast m e = Float.Model.ofScientific m e := by
  apply Srtfp.Model.model_ext
  exact ofDecimalBits_fast_eq ⟨.positive, m, e⟩

@[csimp]
theorem ofScientific_eq_fast : @Float.Model.ofScientific = @ofScientificFast :=
  funext fun m => funext fun e => (ofScientificFast_eq m e).symm

end Srtfp.Reader

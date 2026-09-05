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
   boundary; otherwise the kernel answers `none` and the caller falls
   back to `readExact`. Three regimes reach the core:

   * `0 ≤ e ≤ 54`: the entry is exact (`g = 10^e · 2^h`), so `X = P`;
   * `e < 0` with `5^{-e} ∣ m`: `x = (m / 5^{-e}) · 2^e` is a binary
     scaling, run through the core with `g = 2^127`, `h = 127 - e`;
   * otherwise the margin test above.

   `readFast_some` (below) shows every `some` answer is
   `Reader.ofDecimalBits d`. -/

public import Srtfp.Perf.ReadExact
public import Srtfp.Proofs.Reader.Spec
public import Srtfp.Perf.TableInvariant
public import Srtfp.Perf.MulHigh128
public import Srtfp.Perf.Unpack

@[expose] public section

open Srtfp.Compat

namespace Srtfp.Reader

open Srtfp.Schubfach (pow10Lookup128 mulHi64 mulHi64_toNat_eq)
open Srtfp.Printer (two_zpow_pos two_zpow_natCast)
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

/-- Round `X / 2^s` half-even from `P = (pHi, pMid, pLo)`, where `X` is
    `P` itself (`exact`) or lies in `(P - mz, P]`, and `s = hz + k`. -/
@[inline]
def roundCore (sign : Sign) (mz pHi pMid pLo : UInt64) (hz : Int) (exact : Bool) : Option UInt64 :=
  let top : UInt64 := pHi >>> 63
  -- bit length of `X`: that of `P`, unless `P` just crossed `2^191`
  if !exact && top = 1 && pHi = 9223372036854775808 && pMid = 0 && pLo < mz then none
  else
    let t : Int := 190 + (top.toNat : Int) - hz
    if 1023 ≤ t then none
    else
      let k : Int := max (t - 52) (-1074)
      let s : Int := hz + k
      if s < 130 ∨ 192 < s then none
      else
        let sN : Nat := s.toNat
        -- `q = P >>> s`, `b` = bit `s - 1`, `rest` = the bits below it
        let q : UInt64 := if sN = 192 then 0 else pHi >>> UInt64.ofNat (sN - 128)
        let b : UInt64 := (pHi >>> UInt64.ofNat (sN - 129)) &&& 1
        let restHi : UInt64 := pHi &&& ((1 <<< UInt64.ofNat (sN - 129)) - 1)
        let restZero : Bool := restHi = 0 && pMid = 0 && pLo = 0
        let restSmall : Bool := restHi = 0 && pMid = 0 && pLo < mz
        if exact then
          let n : UInt64 := if b = 0 then q else if restZero then q + (q &&& 1) else q + 1
          some (if n = 0 then Word.pack sign 0 0 else packFinite sign n k)
        else
          if restSmall then none
          else
            let n : UInt64 := if b = 0 then q else q + 1
            some (if n = 0 then Word.pack sign 0 0 else packFinite sign n k)

/-! ## The kernel -/

/-- Fast `Decimal → binary64 word`; `none` defers to `readExact`. -/
def readFast (d : Decimal) : Option UInt64 :=
  let m := d.significand
  let e := d.exponent
  if m = 0 then some (Word.pack d.sign 0 0)
  else if 18446744073709551616 ≤ m then none
  else if 308 < e then some (Word.pack d.sign 2047 0)
  else if e < -324 then none
  else
    let z : Nat := 63 - m.log2
    let mz : UInt64 := UInt64.ofNat m <<< UInt64.ofNat z
    if 0 ≤ e then
      let (gHi, gLo, h) := pow10Lookup128 e
      let (pHi, pMid, pLo) := mul64x128 mz gHi gLo
      roundCore d.sign mz pHi pMid pLo (h + z) (decide (e ≤ 54))
    else
      let ne : Nat := (-e).toNat
      if ne ≤ 27 ∧ m % 5 ^ ne = 0 then
        let m' := m / 5 ^ ne
        let z' : Nat := 63 - m'.log2
        let mz' : UInt64 := UInt64.ofNat m' <<< UInt64.ofNat z'
        let (pHi, pMid, pLo) := mul64x128 mz' 9223372036854775808 0
        roundCore d.sign mz' pHi pMid pLo (127 - e + z') true
      else
        let (gHi, gLo, h) := pow10Lookup128 e
        let (pHi, pMid, pLo) := mul64x128 mz gHi gLo
        roundCore d.sign mz pHi pMid pLo (h + z) false

/-- The live reader: the fast kernel, `readExact` when it declines. -/
def ofDecimalBits_fast (d : Decimal) : UInt64 :=
  match readFast d with
  | some w => w
  | none => (Float.Model.pack (readExact d)).toBits

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
  have ha := a.toNat_lt
  have hHi := gHi.toNat_lt
  have hLo := gLo.toNat_lt
  have h1 := mulHi64_toNat_eq a gLo
  have h2 := mulHi64_toNat_eq a gHi
  have d1 := Nat.div_add_mod (a.toNat * gLo.toNat) (2 ^ 64)
  have d2 := Nat.div_add_mod (a.toNat * gHi.toNat) (2 ^ 64)
  have hB : a.toNat * gHi.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hA : a.toNat * gLo.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  rw [Nat.mul_add, ← Nat.mul_assoc]
  split
  · rename_i hc
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, UInt64.toNat_mul, h1] at hc
    simp only [UInt64.toNat_add, UInt64.toNat_mul, h1, h2, UInt64.toNat_ofNat]
    generalize a.toNat * gLo.toNat = A at *
    generalize a.toNat * gHi.toNat = B at *
    have hg : B / 2 ^ 64 + 1 < 2 ^ 64 := by omega
    have hsum : B % 2 ^ 64 + A / 2 ^ 64 = (B % 2 ^ 64 + A / 2 ^ 64) % 2 ^ 64 + 2 ^ 64 := by omega
    rw [show (1 : Nat) % 2 ^ 64 = 1 from rfl, Nat.mod_eq_of_lt hg]
    omega
  · rename_i hc
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, UInt64.toNat_mul, h1] at hc
    simp only [UInt64.toNat_add, UInt64.toNat_mul, h1, h2, UInt64.toNat_ofNat]
    generalize a.toNat * gLo.toNat = A at *
    generalize a.toNat * gHi.toNat = B at *
    have hsum : B % 2 ^ 64 + A / 2 ^ 64 = (B % 2 ^ 64 + A / 2 ^ 64) % 2 ^ 64 := by omega
    rw [show (0 : Nat) % 2 ^ 64 = 0 from rfl, Nat.add_zero, Nat.mod_eq_of_lt (by omega : B / 2 ^ 64 < 2 ^ 64)]
    omega

/-! ## Proof: the packed word -/

open Srtfp.Model Float.Model Float.Model.UnpackedFloat in
theorem sign_toBitVec_toNat (s : Sign) :
    s.toBitVec.toNat = (match s with | .negative => 1 | .positive => 0) := by
  cases s <;> rfl

open Srtfp.Model Float.Model Float.Model.UnpackedFloat in
theorem toBits_pack_zero (s : Sign) :
    (Float.Model.pack (.zero s)).toBits = Word.pack s 0 0 := by
  apply UInt64.toNat_inj.mp
  show (UnpackedFloat.pack Format.binary64 (.zero s)).toNat = _
  rw [pack_toNat s 0 0 (by decide) (by decide)]
  show (packComponents Format.binary64 s 0 0).toNat = _
  rw [packComponents_toNat, sign_toBitVec_toNat]
  cases s <;> rfl

open Srtfp.Model Float.Model Float.Model.UnpackedFloat in
theorem toBits_pack_infinity (s : Sign) :
    (Float.Model.pack (.infinity s)).toBits = Word.pack s 2047 0 := by
  apply UInt64.toNat_inj.mp
  show (UnpackedFloat.pack Format.binary64 (.infinity s)).toNat = _
  rw [pack_toNat s 2047 0 (by decide) (by decide)]
  show (packComponents Format.binary64 s (-1#_) 0).toNat = _
  rw [packComponents_toNat, sign_toBitVec_toNat]
  cases s <;> rfl

open Srtfp.Model Float.Model Float.Model.UnpackedFloat in
theorem toBits_pack_finite (s : Sign) {n : Nat} {k : Int} (hn : 0 < n) (hleg : Legal n k) :
    (Float.Model.pack (.finite s n k hn)).toBits
      = Word.pack s (if n < 2 ^ 52 then 0 else (k + 1075).toNat) (n % 2 ^ 52) := by
  obtain ⟨h53, hk0, hk1, hnorm⟩ := hleg
  obtain ⟨hA, hB, hC, hD, hMB⟩ := binary64_facts
  apply UInt64.toNat_inj.mp
  show (UnpackedFloat.pack Format.binary64 (.finite s n k hn)).toNat = _
  rw [pack_toNat s _ _ (by split <;> omega) (Nat.mod_lt _ (by decide))]
  unfold UnpackedFloat.pack
  simp only
  split
  · exfalso; omega
  split
  · rename_i hl
    have hn52 : 2 ^ 52 ≤ n := by
      have := Nat.log2_self_le (by omega : n ≠ 0)
      rw [show n.log2 = 52 by omega] at this
      exact this
    rw [packComponents_toNat, sign_toBitVec_toNat, if_neg (by omega)]
    simp only [BitVec.toNat_ofNat]
    cases s <;> (try simp only []) <;> omega
  · rename_i hl
    have hlt : n < 2 ^ 52 := by
      have h1 : n < 2 ^ (n.log2 + 1) := Nat.lt_log2_self
      have h3 : n.log2 + 1 ≤ 52 := by
        have := (Nat.log2_lt (by omega : n ≠ 0)).mpr h53
        omega
      exact Nat.lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by decide) h3)
    rw [packComponents_toNat, sign_toBitVec_toNat, if_pos hlt]
    simp only [BitVec.toNat_ofNat]
    cases s <;> (try simp only []) <;> omega

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
  have hHi := pHi.toNat_lt
  have hMid := pMid.toNat_lt
  have hLo := pLo.toNat_lt
  have hlow : pMid.toNat * 2 ^ 64 + pLo.toNat < 2 ^ 128 := by omega
  -- `P / 2^j = pHi / 2^(j - 128)` for `128 ≤ j`, and `P % 2^j` likewise
  have hdiv : ∀ j, 128 ≤ j → val192 pHi pMid pLo / 2 ^ j = pHi.toNat / 2 ^ (j - 128) := by
    intro j hj
    unfold val192
    rw [show 2 ^ j = 2 ^ 128 * 2 ^ (j - 128) by rw [← Nat.pow_add, Nat.add_sub_cancel' hj],
      ← Nat.div_div_eq_div_mul, Nat.add_assoc, Nat.mul_comm, Nat.mul_add_div (Nat.two_pow_pos 128),
      Nat.div_eq_of_lt hlow, Nat.add_zero]
  have hmod : ∀ j, 128 ≤ j → val192 pHi pMid pLo % 2 ^ j
      = pHi.toNat % 2 ^ (j - 128) * 2 ^ 128 + pMid.toNat * 2 ^ 64 + pLo.toNat := by
    intro j hj
    have h1 := Nat.div_add_mod (val192 pHi pMid pLo) (2 ^ j)
    have h2 := Nat.div_add_mod pHi.toNat (2 ^ (j - 128))
    rw [hdiv j hj] at h1
    generalize hR : val192 pHi pMid pLo % 2 ^ j = R at *
    have h3 : 2 ^ j = 2 ^ (j - 128) * 2 ^ 128 := by
      rw [← Nat.pow_add, Nat.sub_add_cancel hj]
    rw [h3] at h1
    unfold val192 at h1
    generalize pHi.toNat / 2 ^ (j - 128) = A at *
    generalize pHi.toNat % 2 ^ (j - 128) = B at *
    generalize 2 ^ (j - 128) = T at *
    rw [← h2, Nat.add_mul, Nat.mul_right_comm T (2 ^ 128) A] at h1
    omega
  refine ⟨?_, ?_, ?_⟩
  · split
    · rename_i h; subst h
      rw [UInt64.toNat_ofNat, Nat.div_eq_of_lt (val192_lt _ _ _)]
    · rw [toNat_shiftRight_lt (by omega), hdiv sN (by omega)]
  · rw [UInt64.toNat_and, toNat_shiftRight_lt (by omega), UInt64.toNat_ofNat,
      show (1 : Nat) % 2 ^ 64 = 1 from rfl, Nat.and_one_is_mod, hdiv (sN - 1) (by omega),
      show sN - 1 - 128 = sN - 129 by omega]
  · rw [toNat_and_mask (by omega), hmod (sN - 1) (by omega), show sN - 1 - 128 = sN - 129 by omega]

/-! ## Proof: two rounding facts -/

/-- Strictly inside `(n - 1/2, n + 1/2)`: no tie, so `roundEven` is `n`. -/
theorem roundEven_eq_of_strict {y : Rat} {n : Nat}
    (h1 : (n : Rat) - 1/2 < y) (h2 : y < n + 1/2) : roundEven y = n :=
  roundEven_eq_natCast_of (Rat.le_of_lt h1) (Rat.le_of_lt h2)
    (fun h => absurd h (Rat.ne_of_gt h1)) (fun h => absurd h (Rat.ne_of_lt h2))

/-- Above a natural bound `b`, the rounding stays at or above `b`. -/
theorem roundEven_ge {y : Rat} {b : Nat} (hy : (b : Rat) ≤ y) : (b : Int) ≤ roundEven y := by
  have h := (roundEven_spec y).2.1
  have : ((b : Int) : Rat) < roundEven y + 1 := by push_cast; grind
  have : (b : Int) < roundEven y + 1 := by exact_mod_cast this
  omega

/-! ## Proof: the rounding core -/

/-- `(2 : Rat)^a / 2^j = 2^(a - j)` for a natural `a`. -/
theorem two_pow_div_zpow (a : Nat) (j : Int) :
    (2 : Rat) ^ a / (2 : Rat) ^ j = (2 : Rat) ^ ((a : Int) - j) := by
  rw [Int.sub_eq_add_neg, Rat.zpow_add (by decide), Rat.zpow_neg, Rat.zpow_natCast, Rat.div_def]

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
  have h2H : 2 ^ (sN' + 1) = 2 * H := by rw [Nat.pow_succ, ← hH, Nat.mul_comm]
  have hT : (2 : Rat) ^ (sN' + 1) = ((2 * H : Nat) : Rat) := by rw [← h2H]; norm_cast
  rw [hT, h2H]
  have hb2 := Nat.mod_lt (Pn / H) (by decide : 0 < 2)
  have hr2 := Nat.mod_lt Pn hH0
  have e1 := Nat.div_add_mod Pn H
  have e2 := Nat.div_add_mod (Pn / H) 2
  rw [Nat.div_div_eq_div_mul, Nat.mul_comm H 2] at e2
  generalize hQ : Pn / (2 * H) = Q at *
  generalize hb : Pn / H % 2 = b at *
  generalize hr : Pn % H = r at *
  have hdec : Pn = 2 * (Q * H) + b * H + r := by grind
  have h2H0 : 0 < 2 * H := by omega
  have h2HR : (0 : Rat) < ((2 * H : Nat) : Rat) := by exact_mod_cast h2H0
  have hQ2 : Q * (2 * H) = 2 * (Q * H) := Nat.mul_left_comm Q 2 H
  have hQ2' : (Q + 1) * (2 * H) = 2 * (Q * H) + 2 * H := by rw [Nat.add_mul, Nat.one_mul, hQ2]
  generalize hQH : Q * H = QH at *
  -- `X / 2H ≤ P / 2H`, and the lower end in the inexact case
  have hXs : X / ((2 * H : Nat) : Rat) ≤ (Pn : Rat) / ((2 * H : Nat) : Rat) := by
    rw [Rat.div_def, Rat.div_def]
    exact Rat.mul_le_mul_of_nonneg_right hXP (Rat.le_of_lt (Rat.inv_pos.mpr h2HR))
  have hXlow : exact = false → ((Pn : Rat) - mz) / ((2 * H : Nat) : Rat) < X / ((2 * H : Nat) : Rat) := by
    intro hex
    rw [hex] at hPX
    simp only [Bool.false_eq_true, if_false] at hPX
    rw [Rat.div_def, Rat.div_def]
    exact Rat.mul_lt_mul_of_pos_right hPX (Rat.inv_pos.mpr h2HR)
  have hbH : b * H ≤ 1 * H := Nat.mul_le_mul_right H (by omega)
  rw [Nat.one_mul] at hbH
  have hylt : (Pn : Rat) / ((2 * H : Nat) : Rat) < (Q : Rat) + 1 := by
    rw [Rat.div_lt_iff h2HR]
    exact_mod_cast (show Pn < (Q + 1) * (2 * H) by omega)
  rcases Nat.lt_or_ge b 1 with hb0 | hb1
  · -- bit `s - 1` clear: round down
    have hb0 : b = 0 := by omega
    subst hb0
    rw [if_pos rfl]
    apply roundEven_eq_of_strict
    · -- `Q - 1/2 < X / 2H`: `X` is at least `Q · 2H`
      have hlo : (Q : Rat) ≤ X / ((2 * H : Nat) : Rat) := by
        split at hPX
        · rw [hPX, le_div_iff h2HR]
          exact_mod_cast (show Q * (2 * H) ≤ Pn by omega)
        · rename_i hex
          have hg := hguard (by simpa using hex)
          rw [le_div_iff h2HR]
          have h1 : ((Q * (2 * H) + mz : Nat) : Rat) ≤ (Pn : Rat) := by
            exact_mod_cast (show Q * (2 * H) + mz ≤ Pn by omega)
          push_cast at h1 ⊢
          grind
      grind
    · have hne : (Pn : Rat) / ((2 * H : Nat) : Rat) ≠ (Q : Rat) + 1/2 := by
        rw [Ne, div_eq_add_half h2H0]; omega
      have hle : (Pn : Rat) / ((2 * H : Nat) : Rat) ≤ (Q : Rat) + 1/2 :=
        (div_le_half h2H0).mpr (by omega)
      exact lt_of_le_of_lt hXs (Rat.lt_of_le_of_ne hle hne)
  · -- bit `s - 1` set
    have hb1 : b = 1 := by omega
    subst hb1
    rw [if_neg (by decide)]
    have hyhalf : (Pn : Rat) / ((2 * H : Nat) : Rat) = (Q : Rat) + 1/2 ↔ r = 0 := by
      rw [div_eq_add_half h2H0]; omega
    have hQ1 : ((Q + 1 : Nat) : Rat) - 1/2 = (Q : Rat) + 1/2 := by push_cast; grind
    split
    · -- exact tie: the even neighbour
      rename_i htie
      obtain ⟨hex, hr0⟩ := htie
      subst hex
      simp only [if_true] at hPX
      subst hr0
      rw [hPX]
      have hy := hyhalf.mpr rfl
      rcases Nat.lt_or_ge (Q % 2) 1 with hq0 | hq1
      · have hq0 : Q % 2 = 0 := by omega
        rw [hq0, Nat.add_zero]
        apply roundEven_eq_natCast_of
        · rw [hy]; grind
        · rw [hy]; exact Rat.le_refl
        · rw [hy]; intro h; exfalso; grind
        · intro _; exact hq0
      · have hq1 : Q % 2 = 1 := by omega
        rw [hq1]
        apply roundEven_eq_natCast_of
        · rw [hy]; push_cast; grind
        · rw [hy]; push_cast; grind
        · intro _; omega
        · rw [hy]; push_cast; intro h; exfalso; grind
    · -- no tie: round up
      rename_i hntie
      apply roundEven_eq_of_strict
      · -- `Q + 1/2 < X / 2H`
        rw [hQ1]
        split at hPX
        · rename_i hex
          rw [hPX]
          have hne : (Pn : Rat) / ((2 * H : Nat) : Rat) ≠ (Q : Rat) + 1/2 :=
            fun h => hntie ⟨hex, hyhalf.mp h⟩
          have hge : ((Q + 1 : Nat) : Rat) - 1/2 ≤ (Pn : Rat) / ((2 * H : Nat) : Rat) :=
            (half_le_div h2H0).mpr (by omega)
          rw [hQ1] at hge
          exact Rat.lt_of_le_of_ne hge (Ne.symm hne)
        · rename_i hex
          have hg := hguard (by simpa using hex)
          have h1 : ((Q * (2 * H) + H + mz : Nat) : Rat) ≤ (Pn : Rat) := by
            exact_mod_cast (show Q * (2 * H) + H + mz ≤ Pn by omega)
          have hmid : (Q : Rat) + 1/2 ≤ ((Pn : Rat) - mz) / ((2 * H : Nat) : Rat) := by
            rw [le_div_iff h2HR]; push_cast at h1 ⊢; grind
          exact lt_of_le_of_lt hmid (hXlow (by simpa using hex))
      · have hlt2 : (Pn : Rat) / ((2 * H : Nat) : Rat) < ((Q + 1 : Nat) : Rat) + 1/2 :=
          lt_of_lt_of_le hylt (by push_cast; grind)
        exact lt_of_le_of_lt hXs hlt2

theorem roundCore_spec (sign : Sign) (mz pHi pMid pLo : UInt64) (hz : Int) (exact : Bool)
    (X : Rat) (hX190 : (2 : Rat) ^ (190 : Nat) ≤ X) (hXP : X ≤ (val192 pHi pMid pLo : Rat))
    (hPX : if exact then X = (val192 pHi pMid pLo : Rat) else (val192 pHi pMid pLo : Rat) - mz.toNat < X)
    {w : UInt64} (h : roundCore sign mz pHi pMid pLo hz exact = some w) :
    w = (Float.Model.pack (readMag sign (X / (2 : Rat) ^ hz))).toBits := by
  have htop : (pHi >>> 63).toNat = pHi.toNat / 2 ^ 63 := by
    rw [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]; rfl
  have hHi := pHi.toNat_lt
  have hMid := pMid.toNat_lt
  have hLo := pLo.toNat_lt
  have hmz := mz.toNat_lt
  have hPlt := val192_lt pHi pMid pLo
  have hPval : val192 pHi pMid pLo = pHi.toNat * 2 ^ 128 + pMid.toNat * 2 ^ 64 + pLo.toNat := rfl
  unfold roundCore at h
  dsimp only at h
  split at h
  · cases h
  rename_i hmargin
  split at h
  · cases h
  rename_i ht
  split at h
  · cases h
  rename_i hs
  generalize htN : (pHi >>> 63).toNat = topN at *
  generalize hk : max (190 + (topN : Int) - hz - 52) (-1074) = k at *
  generalize hsN : (hz + k).toNat = sN at *
  have hs130 : 130 ≤ sN := by omega
  have hs192 : sN ≤ 192 := by omega
  have hsInt : (sN : Int) = hz + k := by omega
  generalize hPn : val192 pHi pMid pLo = Pn at *
  -- the bit length of `X` is that of `P`: `2^(190 + topN) ≤ X < 2^(191 + topN)`
  have hbits : (2 : Rat) ^ (190 + topN : Nat) ≤ X ∧ X < (2 : Rat) ^ (191 + topN : Nat) := by
    have hPnat : Pn < 2 ^ (191 + topN) ∧ (topN = 1 → 2 ^ 191 ≤ Pn) := by
      rw [hPval] at hPlt
      constructor
      · have : topN = 0 ∨ topN = 1 := by omega
        rcases this with h0 | h1
        · subst h0; omega
        · subst h1; omega
      · intro h1; subst h1; omega
    have hPR : (Pn : Rat) < (2 : Rat) ^ (191 + topN : Nat) := by
      have := hPnat.1
      rw [← Rat.natCast_lt_natCast] at this
      push_cast at this
      exact this
    refine ⟨?_, lt_of_le_of_lt hXP hPR⟩
    have : topN = 0 ∨ topN = 1 := by omega
    rcases this with h0 | h1
    · subst h0; exact hX190
    · subst h1
      have hP191 : 2 ^ 191 ≤ Pn := hPnat.2 rfl
      split at hPX
      · rw [hPX]
        have := hP191
        rw [← Rat.natCast_le_natCast] at this
        push_cast at this
        exact this
      · -- not exact: `P` is at least `2^191 + mz`
        rename_i hex
        have hmarg : 2 ^ 191 + mz.toNat ≤ Pn := by
          simp only [hex, Bool.not_false, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq] at hmargin
          rw [hPval]
          have h63 : 2 ^ 63 ≤ pHi.toNat := by omega
          rcases Nat.lt_or_ge (2 ^ 63) pHi.toNat with hgt | hge
          · omega
          · have hpHi : pHi = 9223372036854775808 := by
              apply UInt64.toNat_inj.mp
              rw [show (9223372036854775808 : UInt64).toNat = 2 ^ 63 by decide]; omega
            have htop1 : pHi >>> 63 = 1 := UInt64.toNat_inj.mp (by rw [htN]; rfl)
            by_cases hm0 : pMid = 0
            · have hlt : ¬ pLo < mz := fun hc => hmargin ⟨⟨⟨htop1, hpHi⟩, hm0⟩, hc⟩
              rw [UInt64.lt_iff_toNat_lt] at hlt
              subst hm0
              rw [UInt64.toNat_ofNat]
              omega
            · have : pMid.toNat ≠ 0 := fun hc => hm0 (UInt64.toNat_inj.mp (by rw [hc]; rfl))
              omega
        have := hmarg
        rw [← Rat.natCast_le_natCast] at this
        push_cast at this
        exact Rat.le_of_lt (lt_of_le_of_lt (by grind) hPX)
  -- `x = X / 2^hz` lies in the binade `[2^t, 2^(t+1))`, `t = 190 + topN - hz`
  have hzpos : (0 : Rat) < (2 : Rat) ^ hz := two_zpow_pos hz
  have hx : (2 : Rat) ^ (190 + (topN : Int) - hz) ≤ X / (2 : Rat) ^ hz
      ∧ X / (2 : Rat) ^ hz < (2 : Rat) ^ (190 + (topN : Int) - hz + 1) := by
    constructor
    · rw [show 190 + (topN : Int) - hz = ((190 + topN : Nat) : Int) - hz by omega,
        ← two_pow_div_zpow, le_div_iff hzpos, Rat.div_mul_cancel (Rat.ne_of_gt hzpos)]
      exact hbits.1
    · rw [show 190 + (topN : Int) - hz + 1 = ((191 + topN : Nat) : Int) - hz by omega,
        ← two_pow_div_zpow, Rat.div_lt_iff hzpos, Rat.div_mul_cancel (Rat.ne_of_gt hzpos)]
      exact hbits.2
  generalize hxdef : X / (2 : Rat) ^ hz = x at *
  have hxpos : (0 : Rat) < x := lt_of_lt_of_le (two_zpow_pos _) hx.1
  have hk' : gridExp x = k := by
    apply gridExp_eq_of (Rat.le_of_lt hxpos)
    · omega
    · exact lt_of_lt_of_le hx.2 (zpow_le_zpow_right₀ (by decide) (by omega))
    · rcases (show k = -1074 ∨ k = 190 + (topN : Int) - hz - 52 by omega) with hc | hc
      · exact Or.inl hc
      · right
        rw [hc, show 190 + (topN : Int) - hz - 52 + 52 = 190 + (topN : Int) - hz by omega]
        exact hx.1
  have hthr : ¬ ((2 : Rat) ^ 1024 - 2 ^ 970 ≤ x) := by
    intro hc
    have h1 : x < (2 : Rat) ^ (1023 : Int) :=
      lt_of_lt_of_le hx.2 (zpow_le_zpow_right₀ (by decide) (by omega))
    have h2 : (2 : Rat) ^ (1023 : Int) ≤ (2 : Rat) ^ 1024 - 2 ^ 970 := by
      have ha : (2 : Rat) ^ (970 : Int) ≤ (2 : Rat) ^ (1023 : Int) :=
        zpow_le_zpow_right₀ (by decide) (by decide)
      have hb : (2 : Rat) ^ (1024 : Nat) = (2 : Rat) ^ (1023 : Nat) * 2 := Rat.pow_succ 2 1023
      have ha' : (2 : Rat) ^ (970 : Nat) ≤ (2 : Rat) ^ (1023 : Nat) := ha
      show (2 : Rat) ^ (1023 : Nat) ≤ (2 : Rat) ^ (1024 : Nat) - 2 ^ (970 : Nat)
      rw [hb]
      grind
    exact absurd hc (Rat.not_le.mpr (lt_of_lt_of_le h1 h2))
  -- the scaled value `x / 2^k = X / 2^s`
  have hsdef : x / (2 : Rat) ^ k = X / (2 : Rat) ^ sN := by
    rw [← hxdef, Rat.div_def, Rat.div_def, Rat.mul_assoc, ← Rat.inv_mul_rev,
      ← Rat.zpow_add (by decide) k hz, show k + hz = (sN : Int) by omega, Rat.zpow_natCast,
      ← Rat.div_def]
  -- the kernel's bits
  obtain ⟨hq, hb, hrest⟩ := shift_facts pHi pMid pLo hs130 hs192
  rw [hPn] at hq hb hrest
  generalize hqU : (if sN = 192 then (0 : UInt64) else pHi >>> UInt64.ofNat (sN - 128)) = qU at *
  generalize hbU : (pHi >>> UInt64.ofNat (sN - 129)) &&& 1 = bU at *
  generalize hrU : pHi &&& ((1 <<< UInt64.ofNat (sN - 129)) - 1) = rU at *
  have hQlt : Pn / 2 ^ sN < 2 ^ 62 := by
    apply Nat.div_lt_of_lt_mul
    calc Pn < 2 ^ 192 := hPlt
      _ = 2 ^ 130 * 2 ^ 62 := by rw [← Nat.pow_add]
      _ ≤ 2 ^ sN * 2 ^ 62 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) hs130)
  have hqU1 : (qU + 1).toNat = Pn / 2 ^ sN + 1 := by
    rw [UInt64.toNat_add, hq, UInt64.toNat_ofNat, show (1 : Nat) % 2 ^ 64 = 1 from rfl]
    exact Nat.mod_eq_of_lt (by omega)
  have hqUodd : (qU + (qU &&& 1)).toNat = Pn / 2 ^ sN + Pn / 2 ^ sN % 2 := by
    rw [UInt64.toNat_add, UInt64.toNat_and, hq, UInt64.toNat_ofNat,
      show (1 : Nat) % 2 ^ 64 = 1 from rfl, Nat.and_one_is_mod]
    exact Nat.mod_eq_of_lt (by omega)
  have hbU0 : (bU = 0) ↔ Pn / 2 ^ (sN - 1) % 2 = 0 := by
    rw [← UInt64.toNat_inj, hb]; rfl
  have hrestZ : ((rU = 0 && pMid = 0 && pLo = 0) = true) ↔ Pn % 2 ^ (sN - 1) = 0 := by
    simp only [Bool.and_eq_true, decide_eq_true_eq, ← UInt64.toNat_inj, UInt64.toNat_ofNat]
    rw [hrest]
    omega
  have hrestS : ((rU = 0 && pMid = 0 && pLo < mz) = true) ↔ Pn % 2 ^ (sN - 1) < mz.toNat := by
    simp only [Bool.and_eq_true, decide_eq_true_eq, ← UInt64.toNat_inj, UInt64.toNat_ofNat,
      UInt64.lt_iff_toNat_lt]
    rw [hrest]
    omega
  -- the significand, as a natural
  generalize hnN : (if Pn / 2 ^ (sN - 1) % 2 = 0 then Pn / 2 ^ sN
      else if exact ∧ Pn % 2 ^ (sN - 1) = 0 then Pn / 2 ^ sN + Pn / 2 ^ sN % 2
      else Pn / 2 ^ sN + 1 : Nat) = nN
  -- the kernel's word, and the guard it checked
  have hw : ∃ nU : UInt64, nU.toNat = nN ∧ (exact = false → mz.toNat ≤ Pn % 2 ^ (sN - 1))
      ∧ w = (if nU = 0 then Word.pack sign 0 0 else packFinite sign nU k) := by
    split at h
    · rename_i hex
      refine ⟨_, ?_, fun hc => absurd hex (by simp [hc]), (Option.some.inj h).symm⟩
      rw [← hnN]
      split
      · rename_i hb0; rw [if_pos (hbU0.mp hb0)]; exact hq
      · rename_i hb0
        rw [if_neg (fun hc => hb0 (hbU0.mpr hc))]
        split
        · rename_i hz0; rw [if_pos ⟨hex, hrestZ.mp hz0⟩]; exact hqUodd
        · rename_i hz0; rw [if_neg (fun hc => hz0 (hrestZ.mpr hc.2))]; exact hqU1
    · rename_i hex
      have hex' : exact = false := by simpa using hex
      split at h
      · cases h
      rename_i hsmall
      refine ⟨_, ?_, fun _ => Nat.le_of_not_lt (fun hc => hsmall (hrestS.mpr hc)),
        (Option.some.inj h).symm⟩
      rw [← hnN]
      split
      · rename_i hb0; rw [if_pos (hbU0.mp hb0)]; exact hq
      · rename_i hb0
        rw [if_neg (fun hc => hb0 (hbU0.mpr hc)),
          if_neg (fun hc => by rw [hex'] at hc; exact Bool.false_ne_true hc.1)]
        exact hqU1
  obtain ⟨nU, hnU, hguard, hwdef⟩ := hw
  have hround := round_from_bits Pn sN (by omega) X mz.toNat exact hXP hPX hguard
  rw [hnN] at hround
  have hn' : roundEven (x / (2 : Rat) ^ k) = nN := by rw [hsdef, hround]
  -- the significand's bounds
  have hkpos : (0 : Rat) < (2 : Rat) ^ k := two_zpow_pos k
  have hn53 : nN ≤ 2 ^ 53 := by
    have hlt : x / (2 : Rat) ^ k < ((2 ^ 53 : Nat) : Rat) := by
      rw [← two_zpow_natCast, Rat.div_lt_iff hkpos, Rat.mul_comm, ← Rat.zpow_add (by decide)]
      exact lt_of_lt_of_le hx.2 (zpow_le_zpow_right₀ (by decide) (by omega))
    have := roundEven_le hlt
    rw [hn'] at this
    exact_mod_cast this
  have hn52 : k ≠ -1074 → 2 ^ 52 ≤ nN := by
    intro hk1074
    have hkt : k + ((52 : Nat) : Int) = 190 + (topN : Int) - hz := by omega
    have hge : ((2 ^ 52 : Nat) : Rat) ≤ x / (2 : Rat) ^ k := by
      rw [← two_zpow_natCast, le_div_iff hkpos, ← Rat.zpow_add (by decide), Int.add_comm, hkt]
      exact hx.1
    have := roundEven_ge hge
    rw [hn'] at this
    exact_mod_cast this
  -- assemble
  rw [hwdef]
  unfold readMag
  rw [if_neg hthr]
  dsimp only
  rw [hk', hn', Int.toNat_natCast]
  by_cases hn0 : nN = 0
  · have hnU0 : nU = 0 := UInt64.toNat_inj.mp (by rw [hnU, hn0]; rfl)
    rw [if_pos hnU0, dif_pos hn0, toBits_pack_zero]
  · have hnU0 : nU ≠ 0 := fun hc => hn0 (by rw [← hnU, hc]; rfl)
    rw [if_neg hnU0, dif_neg hn0]
    unfold packFinite
    have h52 : (4503599627370496 : UInt64).toNat = 2 ^ 52 := by decide
    have h53 : (9007199254740992 : UInt64).toNat = 2 ^ 53 := by decide
    by_cases hc53 : nN = 2 ^ 53
    · have hnU53 : nU = 9007199254740992 := UInt64.toNat_inj.mp (by rw [hnU, hc53, h53])
      rw [if_pos hc53, if_neg (by rw [UInt64.lt_iff_toNat_lt, hnU, hc53, h52]; decide), if_pos hnU53,
        toBits_pack_finite sign (by decide) ⟨by decide, by omega, by omega, fun _ => Nat.le_refl _⟩,
        if_neg (Nat.lt_irrefl _), Nat.mod_self, show k + 1 + 1075 = k + 1076 by omega]
    · rw [if_neg hc53]
      have hleg : Srtfp.Model.Legal nN k := ⟨by omega, by omega, by omega, hn52⟩
      rw [toBits_pack_finite sign (Nat.pos_of_ne_zero hn0) hleg]
      by_cases hlt : nN < 2 ^ 52
      · rw [if_pos (by rw [UInt64.lt_iff_toNat_lt, hnU, h52]; exact hlt), if_pos hlt,
          Nat.mod_eq_of_lt hlt, hnU]
      · rw [if_neg (by rw [UInt64.lt_iff_toNat_lt, hnU, h52]; exact hlt),
          if_neg (fun hc => hc53 (by rw [← hnU, hc, h53])), if_neg hlt,
          UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hnU, h52]; omega), hnU, h52,
          show nN % 2 ^ 52 = nN - 2 ^ 52 by omega]

/-! ## Proof: the table entry against `10^e` -/

/-- `b^e` as a quotient of natural powers. -/
theorem zpow_eq_div (b : Rat) (e : Int) : b ^ e = b ^ e.toNat / b ^ (-e).toNat := by
  by_cases he : 0 ≤ e
  · generalize hn : e.toNat = n
    rw [show (-e).toNat = 0 by omega, Rat.pow_zero, show e = (n : Int) by omega, Rat.zpow_natCast,
      Rat.div_def, Rat.inv_eq_of_mul_eq_one (Rat.mul_one 1), Rat.mul_one]
  · generalize hn : (-e).toNat = n
    rw [show e.toNat = 0 by omega, Rat.pow_zero, show e = -(n : Int) by omega, Rat.zpow_neg,
      Rat.zpow_natCast, Rat.div_def, Rat.one_mul]

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
  have h3 : pow10Table128_kMin = -324 := rfl
  have h4 : pow10Table128_kMax = 324 := rfl
  have hinv := pow10Lookup128_invariant e (by omega) (by omega)
  dsimp only at hinv
  rw [toNat_of_if, toNat_neg_of_if, toNat_of_if, toNat_neg_of_if] at hinv
  simp only [Nat.mul_assoc] at hinv
  have hlook := pow10Lookup128_eq e (by omega) (by omega)
  have hh : (pow10Lookup128 e).2.2 = pow10Shift e := by rw [hlook]; rfl
  have hge := pow10Num_ge e hLo hHi
  have hdvd := pow10Den_dvd e
  unfold pow10Num pow10Den at hge hdvd
  rw [← hh] at hge hdvd
  generalize hg : (pow10Lookup128 e).1.toNat * 2 ^ 64 + (pow10Lookup128 e).2.1.toNat = g at *
  generalize hhh : (pow10Lookup128 e).2.2 = hh' at *
  generalize hnum : 10 ^ e.toNat * 2 ^ hh'.toNat = num at *
  generalize hden : 10 ^ (-e).toNat * 2 ^ (-hh').toNat = den at *
  have hden0 : 0 < den := by
    rw [← hden]; exact Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos (by decide))
  have hdenR : (0 : Rat) < den := by exact_mod_cast hden0
  -- `10^e · 2^h = num / den`
  have hval : (10 : Rat) ^ e * (2 : Rat) ^ hh' = (num : Rat) / den := by
    rw [zpow_eq_div 10 e, zpow_eq_div 2 hh', ← hnum, ← hden]
    push_cast
    rw [Rat.div_def, Rat.div_def, Rat.div_def, Rat.inv_mul_rev]
    grind
  rw [hval]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [div_le_iff hdenR]
    exact_mod_cast hinv.1
  · rw [Rat.lt_div_iff hdenR]
    have h1' := (Rat.natCast_lt_natCast).mpr hinv.2
    push_cast at h1'
    grind
  · rw [le_div_iff hdenR]
    exact_mod_cast hge
  · intro he0 he54
    have hd := hdvd he0 he54
    obtain ⟨q, hq⟩ := hd
    have h1 := hinv.1
    have h2 := hinv.2
    rw [hq] at h1 h2 ⊢
    have hgq : g = q := by
      have ha : q ≤ g := Nat.le_of_mul_le_mul_left (by rw [Nat.mul_comm den g]; exact h1) hden0
      have hb : g < q + 1 := Nat.lt_of_mul_lt_mul_left (by
        rw [Nat.mul_comm den g]
        calc g * den < den * q + den := h2
          _ = den * (q + 1) := by rw [Nat.mul_add, Nat.mul_one])
      omega
    rw [hgq]
    push_cast
    rw [Rat.mul_comm, Rat.div_def, Rat.mul_assoc, Rat.mul_inv_cancel _ (Rat.ne_of_gt hdenR), Rat.mul_one]

/-! ## Proof: the normalised significand -/

theorem mz_facts {m : Nat} (hm0 : m ≠ 0) (hm : m < 2 ^ 64) :
    (UInt64.ofNat m <<< UInt64.ofNat (63 - m.log2)).toNat = m * 2 ^ (63 - m.log2)
    ∧ 2 ^ 63 ≤ m * 2 ^ (63 - m.log2) ∧ m * 2 ^ (63 - m.log2) < 2 ^ 64 := by
  have hL1 : 2 ^ m.log2 ≤ m := Nat.log2_self_le hm0
  have hL2 : m < 2 ^ (m.log2 + 1) := Nat.lt_log2_self
  have hL64 : m.log2 < 64 := (Nat.log2_lt hm0).mpr hm
  generalize hL : m.log2 = L at *
  have hlo : 2 ^ 63 ≤ m * 2 ^ (63 - L) := by
    calc 2 ^ 63 = 2 ^ L * 2 ^ (63 - L) := by rw [← Nat.pow_add, Nat.add_sub_cancel' (by omega)]
      _ ≤ m * 2 ^ (63 - L) := Nat.mul_le_mul_right _ hL1
  have hhi : m * 2 ^ (63 - L) < 2 ^ 64 := by
    calc m * 2 ^ (63 - L) < 2 ^ (L + 1) * 2 ^ (63 - L) :=
          Nat.mul_lt_mul_of_pos_right hL2 (Nat.two_pow_pos _)
      _ = 2 ^ 64 := by rw [← Nat.pow_add, show L + 1 + (63 - L) = 64 by omega]
  refine ⟨?_, hlo, hhi⟩
  rw [UInt64.toNat_shiftLeft, UInt64.toNat_ofNat', UInt64.toNat_ofNat', Nat.mod_eq_of_lt hm,
    Nat.mod_eq_of_lt (show 63 - L < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show 63 - L < 64 by omega),
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt hhi]

/-! ## Proof: the regimes -/

/-- The table regime: `X = mz · 10^e · 2^h` against `P = mz · g`. -/
theorem roundCore_table (sign : Sign) {m : Nat} (hm0 : m ≠ 0) (hm : m < 2 ^ 64) {e : Int}
    (hLo : -324 ≤ e) (hHi : e ≤ 324) (exact : Bool) (hex : exact = true → 0 ≤ e ∧ e ≤ 54)
    {gHi gLo : UInt64} {hh : Int} (hg : pow10Lookup128 e = (gHi, gLo, hh))
    {pHi pMid pLo : UInt64}
    (hp : mul64x128 (UInt64.ofNat m <<< UInt64.ofNat (63 - m.log2)) gHi gLo = (pHi, pMid, pLo))
    {w : UInt64}
    (h : roundCore sign (UInt64.ofNat m <<< UInt64.ofNat (63 - m.log2)) pHi pMid pLo
      (hh + ((63 - m.log2 : Nat) : Int)) exact = some w) :
    w = (Float.Model.pack (readMag sign ((m : Rat) * (10 : Rat) ^ e))).toBits := by
  obtain ⟨hmzN, hmzlo, hmzhi⟩ := mz_facts hm0 hm
  generalize hz : 63 - m.log2 = z at *
  generalize hmz : UInt64.ofNat m <<< UInt64.ofNat z = mz at *
  obtain ⟨hb1, hb2, hb3, hb4⟩ := table_bounds e hLo hHi
  rw [hg] at hb1 hb2 hb3 hb4
  dsimp only at hb1 hb2 hb3 hb4
  generalize hgN : gHi.toNat * 2 ^ 64 + gLo.toNat = g at *
  have hPval : val192 pHi pMid pLo = mz.toNat * g := by
    have := mul64x128_val mz gHi gLo
    rw [hp] at this
    simpa [hgN] using this
  have hmzR : (2 : Rat) ^ (63 : Nat) ≤ (mz.toNat : Rat) := by rw [hmzN]; exact_mod_cast hmzlo
  have hmzpos : (0 : Rat) < (mz.toNat : Rat) := lt_of_lt_of_le (Rat.pow_pos (by decide)) hmzR
  have hzpos : (0 : Rat) < (2 : Rat) ^ hh * (2 : Rat) ^ (z : Nat) :=
    Rat.mul_pos (two_zpow_pos _) (Rat.pow_pos (by decide))
  have hxeq : (mz.toNat : Rat) * ((10 : Rat) ^ e * (2 : Rat) ^ hh) / (2 : Rat) ^ (hh + (z : Int))
      = (m : Rat) * (10 : Rat) ^ e := by
    rw [Rat.zpow_add (by decide), Rat.zpow_natCast, hmzN]
    push_cast
    rw [show (m : Rat) * 2 ^ z * ((10 : Rat) ^ e * 2 ^ hh) = (m : Rat) * 10 ^ e * (2 ^ hh * 2 ^ z) by grind,
      Rat.mul_div_cancel (Rat.ne_of_gt hzpos)]
  have key := roundCore_spec sign mz pHi pMid pLo (hh + (z : Int)) exact
    ((mz.toNat : Rat) * ((10 : Rat) ^ e * (2 : Rat) ^ hh)) ?_ ?_ ?_ h
  · rw [hxeq] at key; exact key
  · calc (2 : Rat) ^ (190 : Nat) = 2 ^ (63 : Nat) * 2 ^ (127 : Nat) := by rw [← Rat.pow_add]
      _ ≤ (mz.toNat : Rat) * 2 ^ (127 : Nat) :=
          Rat.mul_le_mul_of_nonneg_right hmzR (Rat.pow_nonneg (by decide))
      _ ≤ (mz.toNat : Rat) * ((10 : Rat) ^ e * 2 ^ hh) :=
          Rat.mul_le_mul_of_nonneg_left hb3 (Rat.le_of_lt hmzpos)
  · rw [hPval]; push_cast
    exact Rat.mul_le_mul_of_nonneg_left hb1 (Rat.le_of_lt hmzpos)
  · rw [hPval]; push_cast
    split
    · rename_i hex'
      rw [← hb4 (hex hex').1 (hex hex').2]
    · have := Rat.mul_lt_mul_of_pos_left hb2 hmzpos
      grind

/-- The exact binary regime: `x = (m / 5^{-e}) · 2^e`, run with `g = 2^127`. -/
theorem roundCore_binary (sign : Sign) {m : Nat} (hm0 : m ≠ 0) (hm : m < 2 ^ 64) {e : Int}
    (he : e < 0) (hdiv : m % 5 ^ (-e).toNat = 0)
    {pHi pMid pLo : UInt64}
    (hp : mul64x128 (UInt64.ofNat (m / 5 ^ (-e).toNat)
      <<< UInt64.ofNat (63 - (m / 5 ^ (-e).toNat).log2)) 9223372036854775808 0 = (pHi, pMid, pLo))
    {w : UInt64}
    (h : roundCore sign (UInt64.ofNat (m / 5 ^ (-e).toNat)
      <<< UInt64.ofNat (63 - (m / 5 ^ (-e).toNat).log2)) pHi pMid pLo
      (127 - e + ((63 - (m / 5 ^ (-e).toNat).log2 : Nat) : Int)) true = some w) :
    w = (Float.Model.pack (readMag sign ((m : Rat) * (10 : Rat) ^ e))).toBits := by
  generalize hne : (-e).toNat = ne at *
  generalize hm' : m / 5 ^ ne = m' at *
  have h5pos : 0 < 5 ^ ne := Nat.pow_pos (by decide)
  have hmm : m = m' * 5 ^ ne := by
    rw [← hm']; exact (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hdiv)).symm
  have hm'0 : m' ≠ 0 := by intro hc; rw [hc, Nat.zero_mul] at hmm; exact hm0 hmm
  have hm'lt : m' < 2 ^ 64 := by
    rw [hmm] at hm; exact Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right _ h5pos) hm
  obtain ⟨hmzN, hmzlo, hmzhi⟩ := mz_facts hm'0 hm'lt
  generalize hz : 63 - m'.log2 = z at *
  generalize hmz : UInt64.ofNat m' <<< UInt64.ofNat z = mz at *
  have hPval : val192 pHi pMid pLo = mz.toNat * 2 ^ 127 := by
    have := mul64x128_val mz 9223372036854775808 0
    rw [hp, show (9223372036854775808 : UInt64).toNat = 2 ^ 63 by decide, UInt64.toNat_ofNat,
      show (2 : Nat) ^ 63 * 2 ^ 64 + 0 % 2 ^ 64 = 2 ^ 127 by decide] at this
    exact this
  have hmzR : (2 : Rat) ^ (63 : Nat) ≤ (mz.toNat : Rat) := by rw [hmzN]; exact_mod_cast hmzlo
  have hmzpos : (0 : Rat) < (mz.toNat : Rat) := lt_of_lt_of_le (Rat.pow_pos (by decide)) hmzR
  -- `X / 2^(127 - e + z) = m · 10^e`
  have hxeq : (mz.toNat : Rat) * (2 : Rat) ^ (127 : Nat) / (2 : Rat) ^ (127 - e + (z : Int))
      = (m : Rat) * (10 : Rat) ^ e := by
    have he' : e = -(ne : Int) := by omega
    have hnat : m' * 2 ^ z * 2 ^ 127 * 10 ^ ne = m * 2 ^ (127 + ne + z) := by
      rw [hmm, show (10 : Nat) = 2 * 5 by rfl, Nat.mul_pow, Nat.pow_add, Nat.pow_add]
      grind
    have hcast : (m' : Rat) * 2 ^ z * 2 ^ (127 : Nat) * (10 : Rat) ^ ne = (m : Rat) * 2 ^ (127 + ne + z) := by
      exact_mod_cast hnat
    rw [hmzN, he', show (127 : Int) - -(ne : Int) + (z : Int) = ((127 + ne + z : Nat) : Int) by omega,
      Rat.zpow_natCast, Rat.zpow_neg, Rat.zpow_natCast, div_eq_iff (Rat.pow_pos (by decide))]
    push_cast
    have h10 : (0 : Rat) < (10 : Rat) ^ ne := Rat.pow_pos (by decide)
    have hinv : (10 : Rat) ^ ne * ((10 : Rat) ^ ne)⁻¹ = 1 := Rat.mul_inv_cancel _ (Rat.ne_of_gt h10)
    grind
  have key := roundCore_spec sign mz pHi pMid pLo (127 - e + (z : Int)) true
    ((mz.toNat : Rat) * (2 : Rat) ^ (127 : Nat)) ?_ ?_ ?_ h
  · rw [hxeq] at key; exact key
  · calc (2 : Rat) ^ (190 : Nat) = 2 ^ (63 : Nat) * 2 ^ (127 : Nat) := by rw [← Rat.pow_add]
      _ ≤ (mz.toNat : Rat) * 2 ^ (127 : Nat) :=
          Rat.mul_le_mul_of_nonneg_right hmzR (Rat.pow_nonneg (by decide))
  · rw [hPval]; push_cast; exact Rat.le_refl
  · rw [if_pos rfl, hPval, Rat.natCast_mul, ← two_zpow_natCast, Rat.zpow_natCast]

/-! ## Proof: the kernel -/

theorem threshold_pos : (0 : Rat) < (2 : Rat) ^ 1024 - 2 ^ 970 := by
  have h : (2 : Rat) ^ (970 : Int) < (2 : Rat) ^ (1024 : Int) := by
    have := zpow_le_zpow_right₀ (a := (2 : Rat)) (by decide) (show (970 : Int) ≤ 1023 by decide)
    have h2 := Rat.zpow_add_one (show (2 : Rat) ≠ 0 by decide) 1023
    rw [show (1023 : Int) + 1 = 1024 by decide] at h2
    rw [h2]
    have hpos := two_zpow_pos (1023 : Int)
    grind
  have h' : (2 : Rat) ^ (970 : Nat) < (2 : Rat) ^ (1024 : Nat) := h
  grind

theorem readMag_zero (s : Sign) : readMag s 0 = .zero s := by
  unfold readMag
  rw [if_neg (Rat.not_le.mpr threshold_pos)]
  dsimp only
  have h0 : roundEven (0 / (2 : Rat) ^ gridExp 0) = 0 := by
    rw [Rat.div_def, Rat.zero_mul]
    exact roundEven_eq_of (n := 0) (by grind) (by grind) (fun h => absurd h (by grind))
      (fun h => absurd h (by grind))
  rw [h0]
  rfl

theorem readMag_infinity (s : Sign) {x : Rat} (hx : (2 : Rat) ^ 1024 - 2 ^ 970 ≤ x) :
    readMag s x = .infinity s := by
  unfold readMag; rw [if_pos hx]

/-- `m · 10^e` overflows for `m ≥ 1` and `e ≥ 309`. -/
theorem overflow_of_big {m : Nat} (hm : m ≠ 0) {e : Int} (he : 308 < e) :
    (2 : Rat) ^ 1024 - 2 ^ 970 ≤ (m : Rat) * (10 : Rat) ^ e := by
  have h1 : (2 : Rat) ^ (1024 : Nat) ≤ (10 : Rat) ^ (309 : Nat) := by
    have := Rat.natCast_le_natCast.mpr (show (2 : Nat) ^ 1024 ≤ 10 ^ 309 by decide +kernel)
    rw [Rat.natCast_pow, Rat.natCast_pow] at this
    exact this
  have h2 : (10 : Rat) ^ (309 : Int) ≤ (10 : Rat) ^ e := zpow_le_zpow_right₀ (by decide) (by omega)
  have h2' : (10 : Rat) ^ (309 : Nat) ≤ (10 : Rat) ^ e := h2
  have h3 : (1 : Rat) ≤ (m : Rat) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hm)
  have h4 : (1 : Rat) * (10 : Rat) ^ e ≤ (m : Rat) * (10 : Rat) ^ e :=
    Rat.mul_le_mul_of_nonneg_right h3 (Rat.le_of_lt (Rat.zpow_pos (by decide)))
  have h5 := two_zpow_pos (970 : Int)
  have h5' : (0 : Rat) < (2 : Rat) ^ (970 : Nat) := h5
  grind

theorem readFast_some (d : Decimal) {w : UInt64} (h : readFast d = some w) : w = ofDecimalBits d := by
  unfold readFast at h
  dsimp only at h
  unfold ofDecimalBits
  rw [read_eq_readMag, abs_toRat]
  split at h
  · rename_i hm0
    rw [← Option.some.inj h, hm0]
    push_cast
    rw [Rat.zero_mul, readMag_zero, toBits_pack_zero]
  rename_i hm0
  split at h
  · cases h
  rename_i hm
  split at h
  · rename_i hbig
    rw [← Option.some.inj h, readMag_infinity _ (overflow_of_big hm0 hbig), toBits_pack_infinity]
  rename_i hbig
  split at h
  · cases h
  rename_i hsmall
  have hm' : d.significand < 2 ^ 64 := by omega
  split at h
  · rename_i he
    rcases hg : pow10Lookup128 d.exponent with ⟨gHi, gLo, hh⟩
    rw [hg] at h
    dsimp only at h
    rcases hp : mul64x128 (UInt64.ofNat d.significand <<< UInt64.ofNat (63 - d.significand.log2)) gHi gLo
      with ⟨pHi, pMid, pLo⟩
    rw [hp] at h
    dsimp only at h
    exact roundCore_table d.sign hm0 hm' (by omega) (by omega) _
      (fun hx => ⟨he, of_decide_eq_true hx⟩) hg hp h
  · rename_i he
    split at h
    · rename_i hb
      obtain ⟨-, hdiv⟩ := hb
      rcases hp : mul64x128 (UInt64.ofNat (d.significand / 5 ^ (-d.exponent).toNat)
          <<< UInt64.ofNat (63 - (d.significand / 5 ^ (-d.exponent).toNat).log2)) 9223372036854775808 0
        with ⟨pHi, pMid, pLo⟩
      rw [hp] at h
      dsimp only at h
      exact roundCore_binary d.sign hm0 hm' (by omega) hdiv hp h
    · rcases hg : pow10Lookup128 d.exponent with ⟨gHi, gLo, hh⟩
      rw [hg] at h
      dsimp only at h
      rcases hp : mul64x128 (UInt64.ofNat d.significand <<< UInt64.ofNat (63 - d.significand.log2)) gHi gLo
        with ⟨pHi, pMid, pLo⟩
      rw [hp] at h
      dsimp only at h
      exact roundCore_table d.sign hm0 hm' (by omega) (by omega) false
        (fun hx => absurd hx (by decide)) hg hp h

/-! ## Registration -/

theorem ofDecimalBits_fast_eq (d : Decimal) : ofDecimalBits_fast d = ofDecimalBits d := by
  unfold ofDecimalBits_fast
  split
  · rename_i w hw; exact readFast_some d hw
  · rw [readExact_eq]; rfl

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
  show Float.ofModel (Float.Model.pack (read d))
    = Float.ofModel (Float.Model.ofBits (Float.Model.pack (read d)).toBits)
  apply congrArg
  apply Srtfp.Model.model_ext
  rw [Srtfp.Model.toBits_ofBits _ (by
    show Spec.unpack (ofDecimalBits d) ≠ _
    rw [unpack_ofDecimalBits]; exact read_ne_nan d)]

/-- `ofDecimal` over the fast kernel. -/
def ofDecimal_fast (d : Decimal) : Float := Float.ofBits (ofDecimalBits_fast d)

@[csimp]
theorem ofDecimal_eq_fast : @ofDecimal = @ofDecimal_fast :=
  funext fun d => by
    show ofDecimal d = Float.ofBits (ofDecimalBits_fast d)
    rw [ofDecimal_eq_ofBits, ofDecimalBits_fast_eq]

end Srtfp.Reader

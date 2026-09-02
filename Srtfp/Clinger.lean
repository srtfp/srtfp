module
/- Clinger reader — `Decimal` → binary64 (correctly rounded).

   Given `(-1)^sign · sig · 10^exp`, produce the nearest representable
   binary64 value under round-to-nearest, ties-to-even (Clinger 1990,
   "How to read floating point numbers accurately"). Unbounded `Nat`
   arithmetic throughout: the value is held exactly as a fraction, its
   binary exponent is found by comparison, and a single rounding step
   happens at the bit position that exponent dictates, so there is no
   double rounding.

   The core `decimalToFloatBits` computes the encoded *word*; it is a
   pure `Nat`/`Int`/`UInt64` function and the object the specification
   in `Srtfp/Correctness.lean` is stated against. The `Float`-valued
   entry points are `Float.ofBits` of that word. -/

public import Srtfp.Decimal
public import Srtfp.Float.Bits

@[expose] public section

namespace Srtfp.Clinger

open Srtfp.Float

/-! ## Rounding helper -/

/-- Round `num / denom` to nearest `Nat`, ties to even. Requires `denom > 0`. -/
def roundNearestEven (num denom : Nat) : Nat :=
  let q := num / denom
  let r := num - q * denom
  let twoR := 2 * r
  if twoR < denom then q
  else if twoR > denom then q + 1
  else if q % 2 = 0 then q else q + 1

/-! ## Binary-exponent search -/

/-- Is `b · 2^e ≤ a` as rationals? Handles negative `e` by treating it as
    `b ≤ a · 2^{-e}`. -/
def leBy2e (a b : Nat) (e : Int) : Bool :=
  if e ≥ 0 then b * 2 ^ e.toNat ≤ a
  else b ≤ a * 2 ^ (-e).toNat

/-- Given positive `a, b`, find the unique `e : Int` such that
    `b · 2^e ≤ a < b · 2^{e+1}`. -/
def findBinaryExp (a b : Nat) : Int :=
  -- a/b ∈ [2^{lgA - lgB - 1}, 2^{lgA - lgB + 1}) where lgN = Nat.log2 N
  -- ⇒ e (floor log2 of a/b) ∈ {lgA - lgB - 1, lgA - lgB}.
  let e0 : Int := (Nat.log2 a : Int) - (Nat.log2 b : Int)
  if leBy2e a b e0 then e0 else e0 - 1

/-! ## Scale ratios for the round step -/

/-- Returns `(num, denom)` such that `num/denom = (a/b) · 2^k`.
    Distributes the `2^k` factor between numerator and denominator so both
    stay in `Nat`. -/
def scaleByPow2 (a b : Nat) (k : Int) : Nat × Nat :=
  if k ≥ 0 then (a * 2 ^ k.toNat, b)
  else (a, b * 2 ^ (-k).toNat)

/-! ## Decimal → binary64 word -/

/-- The `±∞` word of the given sign (biased exponent all-ones, mantissa 0). -/
def infWord (sign : Bool) : UInt64 := Word.pack sign 2047 0

/-- The `±0.0` word of the given sign. -/
def zeroWord (sign : Bool) : UInt64 := Word.pack sign 0 0

/-- The encoded word of the binary64 value nearest to `(-1)^sign · sig · 10^exp`. -/
def decimalToFloatBits (sign : Bool) (sig : Nat) (exp : Int) : UInt64 :=
  if sig = 0 then zeroWord sign
  else
    -- v = sig · 10^exp. Express as a/b with a, b ≥ 1.
    let (a, b) : Nat × Nat :=
      if exp ≥ 0 then (sig * 10 ^ exp.toNat, 1)
      else (sig, 10 ^ (-exp).toNat)
    let e := findBinaryExp a b
    -- Cases: overflow / normal / subnormal / underflow.
    if e > 1023 then infWord sign
    else if e ≥ -1022 then
      -- Normal: round m_normal = round(v · 2^{52-e}) into [2^52, 2^53].
      let (num, denom) := scaleByPow2 a b (52 - e)
      let m := roundNearestEven num denom
      if m ≥ 2 ^ 53 then
        -- Rounded across power-of-two boundary; renormalise.
        let e' := e + 1
        if e' > 1023 then infWord sign
        else Word.pack sign (e' + 1023).toNat 0
      else
        Word.pack sign (e + 1023).toNat (m - 2 ^ 52)
    else
      -- Subnormal (or underflow): round at 2^{-1074} scale.
      let (num, denom) := scaleByPow2 a b 1074
      let m := roundNearestEven num denom
      if m = 0 then zeroWord sign
      else if m ≥ 2 ^ 52 then
        -- Rounded up across the subnormal/normal boundary; smallest normal.
        Word.pack sign 1 (m - 2 ^ 52)
      else
        Word.pack sign 0 m

/-- The encoded word of the binary64 value nearest to `d`. -/
def ofDecimalBits (d : Decimal) : UInt64 :=
  decimalToFloatBits d.sign d.significand d.exponent

/-! ## The same on `Float` -/

/-- The `Float` nearest to `(-1)^sign · sig · 10^exp`. -/
def decimalToFloat (sign : Bool) (sig : Nat) (exp : Int) : _root_.Float :=
  _root_.Float.ofBits (decimalToFloatBits sign sig exp)

/-- The `Float` nearest to `d`. -/
def ofDecimal (d : Decimal) : _root_.Float :=
  decimalToFloat d.sign d.significand d.exponent

theorem decimalToFloat_eq_bits (sign : Bool) (sig : Nat) (exp : Int) :
    decimalToFloat sign sig exp
      = _root_.Float.ofBits (decimalToFloatBits sign sig exp) := rfl

theorem ofDecimal_eq_bits (d : Decimal) :
    ofDecimal d = _root_.Float.ofBits (ofDecimalBits d) := rfl

end Srtfp.Clinger

/- Clinger reader — Decimal → Float (correctly rounded).

   M4 milestone. Given a canonical `Decimal` (`sign · sig · 10^exp`) produces
   the closest representable binary64 `Float` under round-to-nearest, ties-
   to-even. The reference is Clinger 1990 (`Read-FP-Numbers-Accurately`).

   This implementation uses unbounded `Nat` arithmetic throughout — slow
   compared to the Eisel-Lemire fast path but trivially correct and free of
   the fixed-precision-table proof obligations that a faster path would
   introduce. The rounding is performed once, at the appropriate bit level
   for the result's binary exponent, to avoid double-rounding bugs. -/

import Srtfp.Numeric.Decimal
import Srtfp.Numeric.Float.Bits

namespace PP.Numeric.Clinger

open PP.Numeric.Float

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

/-! ## Decimal → Float -/

/-- The 11-bit "all-ones" biased exponent used for `±Inf` / NaN. -/
private def infBiasedExp : Nat := 2047

/-- Produce `±Infinity` according to `sign`. -/
private def infOfSign (sign : Bool) : _root_.Float :=
  fromBits sign infBiasedExp 0

/-- Produce `±0.0` according to `sign`. -/
private def zeroOfSign (sign : Bool) : _root_.Float :=
  fromBits sign 0 0

/-- Convert `(sign, sig, exp)` to the closest representable `Float`. -/
def decimalToFloat (sign : Bool) (sig : Nat) (exp : Int) : _root_.Float :=
  if sig = 0 then zeroOfSign sign
  else
    -- v = sig · 10^exp. Express as a/b with a, b ≥ 1.
    let (a, b) : Nat × Nat :=
      if exp ≥ 0 then (sig * 10 ^ exp.toNat, 1)
      else (sig, 10 ^ (-exp).toNat)
    let e := findBinaryExp a b
    -- Cases: overflow / normal / subnormal / underflow.
    if e > 1023 then infOfSign sign
    else if e ≥ -1022 then
      -- Normal: round m_normal = round(v · 2^{52-e}) into [2^52, 2^53].
      let (num, denom) := scaleByPow2 a b (52 - e)
      let m := roundNearestEven num denom
      if m ≥ 2 ^ 53 then
        -- Rounded across power-of-two boundary; renormalise.
        let e' := e + 1
        if e' > 1023 then infOfSign sign
        else fromBits sign (e' + 1023).toNat 0
      else
        fromBits sign (e + 1023).toNat (m - 2 ^ 52)
    else
      -- Subnormal (or underflow): round at 2^{-1074} scale.
      let (num, denom) := scaleByPow2 a b 1074
      let m := roundNearestEven num denom
      if m = 0 then zeroOfSign sign
      else if m ≥ 2 ^ 52 then
        -- Rounded up across the subnormal/normal boundary; smallest normal.
        fromBits sign 1 (m - 2 ^ 52)
      else
        fromBits sign 0 m

/-- Render a `Decimal` as the closest representable `Float`. -/
def ofDecimal (d : Decimal) : _root_.Float :=
  decimalToFloat d.sign d.significand d.exponent

end PP.Numeric.Clinger

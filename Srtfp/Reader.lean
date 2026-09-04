module
/- The reference reader: `Decimal` → binary64 word, correctly rounded
   (round to nearest, ties to even).

   In exact rational arithmetic: the binary64 words around a magnitude
   `x` lie on the grid `2^k` (`gridExp`), so the nearest word's
   significand is `x / 2^k` rounded to an integer (`roundEven`). The word
   itself is assembled by Lean's own `Float.Model.pack`.

   Slow, and meant to be: the fast reader lives under `Srtfp/Perf/` and
   is proven equal to this. -/

public import Srtfp.Spec

@[expose] public section

namespace Srtfp.Reader

open Float.Model (UnpackedFloat)

/-- The integer nearest to `x`, ties to even. -/
def roundEven (x : Rat) : Int :=
  let n := (x + 1/2).floor
  if (n : Rat) = x + 1/2 ∧ n % 2 = 1 then n - 1 else n

/-- Consecutive binary64 words around the magnitude `x` differ by
    `2^(gridExp x)`: `2^(⌊log₂ x⌋ - 52)`, or `2^(-1074)` below the normal
    range. -/
def gridExp (x : Rat) : Int :=
  max ((Nat.log2 (x * 2 ^ 1074).floor.toNat : Int) - 1074 - 52) (-1074)

/-- The binary64 value nearest to `d`, unpacked: the infinity of `d`'s sign
    from the overflow threshold on, else the nearest point of the grid,
    `2^53` grid steps renormalised to the next grid. -/
def read (d : Decimal) : UnpackedFloat :=
  let s := Spec.sign d.sign
  let x := Rat.abs (Spec.toRat d)
  if 2 ^ 1024 - 2 ^ 970 ≤ x then .infinity s
  else
    let k := gridExp x
    let n := (roundEven (x / 2 ^ k)).toNat
    if h : n = 0 then .zero s
    else if n = 2 ^ 53 then .finite s (2 ^ 52) (k + 1) (by decide)
    else .finite s n k (Nat.pos_of_ne_zero h)

/-- The word of the binary64 value nearest to `d`. -/
def ofDecimalBits (d : Decimal) : UInt64 := (Float.Model.pack (read d)).toBits

/-- The `Float` nearest to `d`. -/
def ofDecimal (d : Decimal) : Float := Float.ofModel (Float.Model.pack (read d))

theorem ofDecimal_toBits (d : Decimal) : (ofDecimal d).toBits = ofDecimalBits d := rfl

end Srtfp.Reader

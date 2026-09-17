module
/- An internal arithmetic reader used to prove rounding-interval facts and
   verify the fast kernels. The public reader uses upstream ofScientific;
   Upstream.lean proves this helper equal to it. -/

public import Srtfp.Reader

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
  let s := d.sign
  let x := Rat.abs (Spec.toRat d)
  if 2 ^ 1024 - 2 ^ 970 ≤ x then .infinity s
  else
    let k := gridExp x
    let n := (roundEven (x / 2 ^ k)).toNat
    if h : n = 0 then .zero s
    else if n = 2 ^ 53 then .finite s (2 ^ 52) (k + 1) (by decide)
    else .finite s n k (Nat.pos_of_ne_zero h)

/-- The word of the binary64 value nearest to `d`. -/
def referenceBits (d : Decimal) : UInt64 := (Float.Model.pack (read d)).toBits

end Srtfp.Reader

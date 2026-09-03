module
/- The reference printer: binary64 word → shortest round-trip `Decimal`.

   This is the specification in `Srtfp/Correctness.lean` made effective.
   For a finite non-zero value `v = m · 2^q` the decimals that read back
   to it are those in the rounding interval `R_v` (Giulietti §5). On the
   grid of multiples of `10^i` only the two neighbours of `v` can be
   closest to it, and by convexity of `R_v` the grid meets `R_v` only if
   one of them does. So: walk the grids from coarse to fine, starting at
   the grid of `v`'s leading digit, and stop at the first hit; every
   shorter decimal has been tried by then.

   Everything is exact arithmetic in `Rat`. Slow, and meant to be: the
   fast printer lives under `Srtfp/Perf/` and is proven equal to this. -/

public import Srtfp.Decimal
public import Srtfp.Float.Bits

@[expose] public section

namespace Srtfp.Printer

open Srtfp.Float

/-! ## The rounding interval `R_v` (§5, equations (2) and (3)) -/

/-- Left endpoint of `R_v`: halfway to the predecessor of `v`. The
    predecessor is closer when `v` is a power of two above the smallest
    normal (irregular spacing). -/
def vl (m : Nat) (q : Int) : Rat :=
  if m = 2 ^ 52 ∧ q > -1074 then (m - 1/4) * (2 : Rat) ^ q else (m - 1/2) * (2 : Rat) ^ q

/-- Right endpoint of `R_v`: halfway to the successor of `v`. -/
def vr (m : Nat) (q : Int) : Rat := (m + 1/2) * (2 : Rat) ^ q

/-- `x ∈ R_v`. Round-ties-to-even: both endpoints belong iff `m` is even. -/
def InRv (m : Nat) (q : Int) (x : Rat) : Bool :=
  if m % 2 = 0 then vl m q ≤ x ∧ x ≤ vr m q else vl m q < x ∧ x < vr m q

/-! ## One grid -/

/-- On the grid `10^i`, the candidates are the neighbours `u ≤ v < w` of
    `v`. Returns the one in `R_v` (the nearer, ties to even, if both), or
    `none` if the grid misses `R_v` or is coarser than `v`'s leading digit. -/
def candidate (m : Nat) (q i : Int) : Option (Nat × Int) :=
  let v : Rat := m * (2 : Rat) ^ q
  let s : Nat := (v / (10 : Rat) ^ i).floor.toNat
  if s = 0 then none else
  let u : Rat := s * (10 : Rat) ^ i
  let w : Rat := (s + 1) * (10 : Rat) ^ i
  match InRv m q u, InRv m q w with
  | true,  true  => some (if v - u < w - v ∨ (v - u = w - v ∧ s % 2 = 0) then s else s + 1, i)
  | true,  false => some (s, i)
  | false, true  => some (s + 1, i)
  | false, false => none

/-! ## The scan -/

/-- Coarsest grid first; the first hit is the shortest. Binary64 values
    lie below `10^309`, and the grid `10^{-324}` always meets `R_v`, so
    `633` steps from `308` down to `-324` suffice (proven in
    `Srtfp/Proofs/Printer/Scan.lean`). -/
def shortest (m : Nat) (q : Int) : Nat × Int :=
  go 308 633
where
  go (i : Int) : Nat → Nat × Int
    | 0        => (0, 0)
    | fuel + 1 => (candidate m q i).getD (go (i - 1) fuel)

/-! ## Word → Decimal -/

/-- Render a binary64 *bit pattern* as its shortest round-trip `Decimal`,
    or `.error _` for NaN and Infinity. -/
def toDecimalBits (w : UInt64) : Except String Decimal :=
  if Word.isNaN w then
    .error "NaN"
  else if Word.isInf w then
    .error (if Word.signBit w then "-Infinity" else "Infinity")
  else
    let d := Word.decode w
    if d.m = 0 then .ok ⟨d.sign, 0, 0⟩
    else
      let (sig, exp) := shortest d.m d.q
      .ok (Decimal.mk' d.sign sig exp)

/-- Render a `Float` as its shortest round-trip `Decimal`. -/
def toDecimal (f : _root_.Float) : Except String Decimal :=
  toDecimalBits f.toBits

theorem toDecimal_eq_bits (f : _root_.Float) : toDecimal f = toDecimalBits f.toBits := rfl

end Srtfp.Printer

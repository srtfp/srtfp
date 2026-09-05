module
/- The reference printer: binary64 word → shortest round-trip `Decimal`.

   The specification made effective. For a finite nonzero value
   `v = m · 2^q` the decimals that read back to it are those in the
   rounding interval `R_v` (Giulietti §5). On the grid of multiples of
   `10^i` only the two neighbours of `v` can be nearest to it, and by
   convexity of `R_v` the grid meets `R_v` only if one of them does. So:
   walk the grids from coarse to fine and stop at the first hit. Every
   shorter decimal has been tried by then, and the hit has no trailing
   zero, or the previous grid would have hit.

   Exact arithmetic in `Rat`; slow, and meant to be: the fast printer
   lives under `Srtfp/Perf/` and is proven equal to this. -/

public import Srtfp.Spec

@[expose] public section

namespace Srtfp.Printer

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

/-- On the grid `10^i`, the neighbours `u ≤ v < w` of `v` are the only
    candidates: the one in `R_v` (the nearer, ties to even, if both), or
    `none` when the grid misses `R_v`. -/
def candidate (m : Nat) (q i : Int) : Option Nat :=
  let v : Rat := m * (2 : Rat) ^ q
  let s : Nat := (v / (10 : Rat) ^ i).floor.toNat
  let u : Rat := s * (10 : Rat) ^ i
  let w : Rat := (s + 1) * (10 : Rat) ^ i
  match InRv m q u, InRv m q w with
  | true,  true  => some (if v - u < w - v ∨ (v - u = w - v ∧ s % 2 = 0) then s else s + 1)
  | true,  false => some s
  | false, true  => some (s + 1)
  | false, false => none

/-! ## The scan -/

/-- Coarsest grid first; the first hit is the shortest. Binary64 values
    lie below `10^309`, and the grid `10^{-324}` always meets `R_v`, so
    the `633` grids from `10^308` down to `10^{-324}` suffice (proven in
    `Srtfp/Proofs/Printer/Scan.lean`). -/
def shortest (m : Nat) (q : Int) : Nat × Int :=
  go 308 633
where
  go (i : Int) : Nat → Nat × Int
    | 0        => (0, 0)
    | fuel + 1 =>
      match candidate m q i with
      | some n => (n, i)
      | none   => go (i - 1) fuel

/-! ## Word → Decimal -/

/-- The shortest round-trip `Decimal` of a binary64 *bit pattern*; `none`
    for a NaN or an infinity. -/
def toDecimalBits (w : UInt64) : Option Decimal :=
  match Spec.unpack w with
  | .notANumber => none
  | .infinity _ => none
  | .zero s => some ⟨s, 0, 0⟩
  | .finite s m q _ =>
    let (n, i) := shortest m q
    some ⟨s, n, i⟩

/-- The shortest round-trip `Decimal` of a `Float`; `none` for a NaN or an
    infinity. -/
def toDecimal (f : Float) : Option Decimal := toDecimalBits f.toBits

theorem toDecimal_eq_bits (f : Float) : toDecimal f = toDecimalBits f.toBits := rfl

end Srtfp.Printer

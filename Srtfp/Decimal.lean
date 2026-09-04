module
/- Operations on the spec's `Decimal` (`Srtfp/Spec.lean`): the canonical
   form, constructors, negation. The printer produces a `Decimal`, the
   reader consumes one, and `Srtfp/Text.lean` renders and parses it. -/

public import Srtfp.Spec

@[expose] public section

namespace Srtfp

deriving instance Repr, DecidableEq, Inhabited for Decimal

namespace Decimal

/-- The unique zero. -/
def zero : Decimal := ⟨false, 0, 0⟩

/-- One: `+1 × 10^0`. -/
def one : Decimal := ⟨false, 1, 0⟩

instance (d : Decimal) : Decidable (IsCanonical d) := by
  unfold IsCanonical; exact inferInstance

/-- Helper: strip trailing decimal zeros from a (significand, exponent) pair.
    Result is either `(0, 0)` or has a significand not divisible by 10. -/
def canonicaliseAux (s : Nat) (e : Int) : Nat × Int :=
  if hs : s = 0 then (0, 0)
  else if s % 10 = 0 then canonicaliseAux (s / 10) (e + 1)
  else (s, e)
termination_by s
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero hs) (by decide)

/-- Canonical form: strip trailing zeros from the significand.
    Zero keeps its sign (`⟨true, 0, 0⟩` is canonical negative zero). -/
def canonical (d : Decimal) : Decimal :=
  if d.significand = 0 then ⟨d.sign, 0, 0⟩
  else
    let (s, e) := canonicaliseAux d.significand d.exponent
    ⟨d.sign, s, e⟩

/-- Smart constructor: build a canonical Decimal from raw inputs. -/
def mk' (sign : Bool) (significand : Nat) (exponent : Int) : Decimal :=
  canonical ⟨sign, significand, exponent⟩

/-- Build a Decimal from a Nat (always integer, exponent 0). -/
def ofNat (n : Nat) : Decimal := canonical ⟨false, n, 0⟩

/-- Build a Decimal from an Int (sign + magnitude, exponent 0). -/
def ofInt (i : Int) : Decimal :=
  canonical ⟨i < 0, i.natAbs, 0⟩

/-- Negation: flip sign (zero stays canonical). -/
def neg (d : Decimal) : Decimal :=
  if d.significand = 0 then zero
  else { d with sign := !d.sign }

instance : Neg Decimal := ⟨neg⟩

end Decimal

/-- Lean's decimal/scientific-literal interface for `Decimal`.

`OfScientific.ofScientific mantissa expSign expMag` represents
`mantissa × 10^(±expMag)` (`expSign = true` ↔ negative exponent).

So `(1.23 : Decimal) = ⟨false, 123, -2⟩`, `(1e10 : Decimal) = ⟨false, 1, 10⟩`,
`(-1.5 : Decimal) = ⟨true, 15, -1⟩` (negation via the `Neg Decimal` instance,
applied to the positive `OfScientific` result).

The result is always canonicalised (trailing-zero stripped) via `Decimal.mk'`.-/
instance : OfScientific Decimal where
  ofScientific (mantissa : Nat) (exponentSign : Bool) (decimalExponent : Nat) : Decimal :=
    let exp : Int := if exponentSign then -(decimalExponent : Int) else (decimalExponent : Int)
    Decimal.mk' false mantissa exp

end Srtfp

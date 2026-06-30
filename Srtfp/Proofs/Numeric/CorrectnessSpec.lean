/- INTERNAL spec vocabulary for the correctness proofs.

   The public, self-contained statement is
   `PP.Numeric.Spec.correct_iff_toDecimal` (`PP/Numeric/Correctness.lean`),
   which restates everything below inline; the kernel certifies the two
   spellings agree.  Proof bodies: `PP/Proofs/Numeric/Correctness.lean`. -/

import Srtfp.Numeric.Decimal
import Srtfp.Numeric.Float.Bits
import Srtfp.Numeric.Schubfach
import Srtfp.Numeric.Clinger
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.AbsoluteValue.Basic

namespace PP.Numeric

open Schubfach Clinger PP.Numeric.Float Decimal

/-! ## Vocabulary -/

/-- Exact rational value `(-1)^sign · significand · 10^exponent`. -/
def Decimal.toRat (d : Decimal) : ℚ :=
  (if d.sign then -1 else 1) * ((d.significand : ℚ) * (10 : ℚ) ^ d.exponent)

namespace Schubfach

/-- Unsigned magnitude value `v = m · 2^q`. -/
def magVal (m : Nat) (q : Int) : ℚ := (m : ℚ) * (2 : ℚ) ^ q

/-- Exact rational value of a finite float, read off its IEEE-754 bit fields. -/
def floatVal (f : _root_.Float) : ℚ :=
  (if (PP.Numeric.Float.decode f).sign then -1 else 1)
    * magVal (PP.Numeric.Float.decode f).m (PP.Numeric.Float.decode f).q

/-- Number of base-10 digits in `n`; `decDigitLength 0 = 1`. -/
def decDigitLength (n : Nat) : Nat :=
  if n < 10 then 1
  else decDigitLength (n / 10) + 1
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

/-- Reading `d` back through the verified reader reproduces `f`, bit for bit. -/
def RoundTrips (f : _root_.Float) (d : Decimal) : Prop :=
  (Clinger.ofDecimal d).toBits = f.toBits

/-! ## The specification -/

/-- `d` is THE shortest decimal for `f`: round-trip, fewest digits,
closest — exact ties to the even significand.

Ties exist (`1125899906842624.25`, see `Tests/Ryu.lean`), so clause (3) is
load-bearing.  Canonicity is clause (0): for nonzero `d` it would follow
from (2), but a zero with a junk exponent is value-indistinguishable from
the canonical zero, so no value-based clause can exclude it. -/
def IsSpecOutput (f : _root_.Float) (d : Decimal) : Prop :=
    -- (0) normal form (canonicity is NOT derivable for zeros: a zero with
    -- a junk exponent has the same value, digit count and distances)
    Decimal.IsCanonical d
    -- (1) round-trip
  ∧ RoundTrips f d
    -- against every other canonical round-tripper d':
  ∧ (∀ d' : Decimal, d' ≠ d → Decimal.IsCanonical d' → RoundTrips f d' →
       -- (2) either d is strictly shorter than d'
       ( decDigitLength d.significand < decDigitLength d'.significand
       -- (3) or d' is just as short: then d is closer, ties go to the even one
       ∨ ( decDigitLength d'.significand = decDigitLength d.significand
         ∧ ( |Decimal.toRat d - floatVal f| < |Decimal.toRat d' - floatVal f|
           ∨ ( |Decimal.toRat d - floatVal f| = |Decimal.toRat d' - floatVal f|
               ∧ d.significand % 2 = 0 )))))

/-- What a correct printer returns on every binary64 input.
The four conditions are exhaustive and mutually exclusive. -/
def IsCorrectPrinter (p : _root_.Float → Except String Decimal) : Prop :=
  ∀ f : _root_.Float,
      -- NaN
      (isNaNBits f = true → p f = .error "NaN")
      -- ±∞
    ∧ (isInfBits f = true →
         p f = .error (if signBit f then "-Infinity" else "Infinity"))
      -- every finite float (±0 included): THE shortest decimal
    ∧ (isFiniteBits f = true →
         ∃ d : Decimal, p f = .ok d ∧ IsSpecOutput f d)

end Schubfach

namespace Clinger

open Schubfach

/-! ## The reader specification -/

/-- `f` is THE correctly rounded finite Float for `d`: finite, carries
`d.sign` (visible on a zero only through the sign bit), no finite float
is strictly closer to `d`'s exact value, and an exact tie against a
different float value forces the even mantissa. -/
def IsNearestFloat (d : Decimal) (f : _root_.Float) : Prop :=
    isFiniteBits f = true
  ∧ signBit f = d.sign
  ∧ (∀ g : _root_.Float, isFiniteBits g = true →
       |floatVal f - Decimal.toRat d| ≤ |floatVal g - Decimal.toRat d|)
  ∧ (∀ g : _root_.Float, isFiniteBits g = true →
       floatVal g ≠ floatVal f →
       |floatVal g - Decimal.toRat d| = |floatVal f - Decimal.toRat d| →
       mantissaBits f % 2 = 0)

/-- What a correct reader returns on every decimal: the nearest finite
float while `d`'s value is in range, `±∞` by `d.sign` past the overflow
threshold `2^1024 - 2^970` (the midpoint between the largest finite
float and its would-be successor; ties-to-even sends the midpoint
itself to `∞`). -/
def IsCorrectReader (p : Decimal → _root_.Float) : Prop :=
  ∀ d : Decimal,
      (|Decimal.toRat d| < 2 ^ 1024 - 2 ^ 970 → IsNearestFloat d (p d))
    ∧ ((2 : ℚ) ^ 1024 - 2 ^ 970 ≤ |Decimal.toRat d| →
         isInfBits (p d) = true ∧ signBit (p d) = d.sign)

end Clinger

end PP.Numeric

/- INTERNAL spec vocabulary for the correctness proofs.

   The public, self-contained statement is
   `Srtfp.Spec.correct_iff_toDecimal` (`Srtfp/Correctness.lean`),
   which restates everything below inline; the kernel certifies the two
   spellings agree.  Proof bodies: `Srtfp/Proofs/Correctness.lean`. -/

import Srtfp.Rat
import Srtfp.Decimal
import Srtfp.Float.Bits
import Srtfp.Schubfach
import Srtfp.Clinger

namespace Srtfp

open Schubfach Clinger Srtfp.Float Decimal

/-! ## Vocabulary -/

/-- Exact rational value `(-1)^sign · significand · 10^exponent`. -/
def Decimal.toRat (d : Decimal) : ℚ :=
  (if d.sign then -1 else 1) * ((d.significand : ℚ) * (10 : ℚ) ^ d.exponent)

namespace Schubfach

/-- Unsigned magnitude value `v = m · 2^q`. -/
def magVal (m : Nat) (q : Int) : ℚ := (m : ℚ) * (2 : ℚ) ^ q

/-- Exact rational value of a finite binary64 word, read off its IEEE-754
bit fields. -/
def wordVal (w : UInt64) : ℚ :=
  (if (Word.decode w).sign then -1 else 1)
    * magVal (Word.decode w).m (Word.decode w).q

/-- Exact rational value of a finite float, read off its IEEE-754 bit fields. -/
def floatVal (f : _root_.Float) : ℚ :=
  (if (Srtfp.Float.decode f).sign then -1 else 1)
    * magVal (Srtfp.Float.decode f).m (Srtfp.Float.decode f).q

/-- The two value readers agree definitionally. -/
theorem floatVal_word (f : _root_.Float) : floatVal f = wordVal f.toBits := rfl

/-- Number of base-10 digits in `n`; `decDigitLength 0 = 1`. -/
def decDigitLength (n : Nat) : Nat :=
  if n < 10 then 1
  else decDigitLength (n / 10) + 1
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

/-- Reading `d` back through the verified reader reproduces `f`, bit for bit. -/
def RoundTrips (f : _root_.Float) (d : Decimal) : Prop :=
  (Clinger.ofDecimal d).toBits = f.toBits

/-- Bits-level round-trip: reading `d` back through the pure word reader
reproduces the word `w` exactly. -/
def RoundTripsBits (w : UInt64) (d : Decimal) : Prop :=
  Clinger.ofDecimalBits d = w

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

/-- Bits-level `IsSpecOutput`: `d` is THE shortest decimal for the finite
binary64 word `w` — same clauses, pure word pipeline. -/
def IsSpecOutputBits (w : UInt64) (d : Decimal) : Prop :=
    Decimal.IsCanonical d
  ∧ RoundTripsBits w d
  ∧ (∀ d' : Decimal, d' ≠ d → Decimal.IsCanonical d' → RoundTripsBits w d' →
       ( decDigitLength d.significand < decDigitLength d'.significand
       ∨ ( decDigitLength d'.significand = decDigitLength d.significand
         ∧ ( |Decimal.toRat d - wordVal w| < |Decimal.toRat d' - wordVal w|
           ∨ ( |Decimal.toRat d - wordVal w| = |Decimal.toRat d' - wordVal w|
               ∧ d.significand % 2 = 0 )))))

/-- What a correct bits-level printer returns on every binary64 word. -/
def IsCorrectPrinterBits (p : UInt64 → Except String Decimal) : Prop :=
  ∀ w : UInt64,
      (Word.isNaN w = true → p w = .error "NaN")
    ∧ (Word.isInf w = true →
         p w = .error (if Word.signBit w then "-Infinity" else "Infinity"))
    ∧ (Word.isFinite w = true →
         ∃ d : Decimal, p w = .ok d ∧ IsSpecOutputBits w d)

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

/-- Bits-level `IsNearestFloat`: `w` is THE correctly rounded finite
binary64 word for `d`. Note this quantifies over *all* finite words —
a strictly larger candidate set than the image of `Float.toBits`, so the
bits-level statement is (a priori) stronger than the `Float` one. -/
def IsNearestWord (d : Decimal) (w : UInt64) : Prop :=
    Word.isFinite w = true
  ∧ Word.signBit w = d.sign
  ∧ (∀ v : UInt64, Word.isFinite v = true →
       |wordVal w - Decimal.toRat d| ≤ |wordVal v - Decimal.toRat d|)
  ∧ (∀ v : UInt64, Word.isFinite v = true →
       wordVal v ≠ wordVal w →
       |wordVal v - Decimal.toRat d| = |wordVal w - Decimal.toRat d| →
       Word.mantissa w % 2 = 0)

/-- What a correct bits-level reader returns on every decimal. -/
def IsCorrectReaderBits (p : Decimal → UInt64) : Prop :=
  ∀ d : Decimal,
      (|Decimal.toRat d| < 2 ^ 1024 - 2 ^ 970 → IsNearestWord d (p d))
    ∧ ((2 : ℚ) ^ 1024 - 2 ^ 970 ≤ |Decimal.toRat d| →
         Word.isInf (p d) = true ∧ Word.signBit (p d) = d.sign)

end Clinger

end Srtfp

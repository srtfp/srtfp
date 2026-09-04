module
/- The specification: what it means to be a correct binary64 reader and a
   correct shortest-decimal printer. Stated on raw IEEE-754 bit patterns
   (`UInt64` words). The theorems that the library's functions are the
   unique such reader and printer are in `Srtfp/Correctness.lean`.

   Everything needed to read this file is defined in it or displayed
   below. -/

public import Srtfp.Decimal
public import Srtfp.Float.Bits
public import Srtfp.Clinger

@[expose] public section

namespace Srtfp.Spec

open Float

/-! ## Values -/

/-- `(-1)^sign · m · base^e`. -/
def val (base : Rat) (sign : Bool) (m : Nat) (e : Int) : Rat :=
  (if sign then -1 else 1 : Rat) * (m * base ^ e)

/-- The exact value of a decimal. -/
def toRat (d : Decimal) : Rat := val 10 d.sign d.significand d.exponent

/-- The exact value a finite binary64 word denotes. -/
def wordVal (w : UInt64) : Rat :=
  let ⟨sign, m, q⟩ := Word.decode w
  val 2 sign m q

/-- The distance between a decimal's value and a word's. -/
def dist (d : Decimal) (w : UInt64) : Rat := Rat.abs (wordVal w - toRat d)

/-- Number of base-10 digits (`digits 0 = 1`). -/
def digits (n : Nat) : Nat := if n < 10 then 1 else digits (n / 10) + 1
termination_by n
decreasing_by omega

example (q : Rat) : Rat.abs q = if 0 ≤ q then q else -q := rfl

/-! ## Referenced definitions, displayed here for convenience -/

example (d : Decimal) : d = ⟨d.sign, d.significand, d.exponent⟩ := rfl

example (d : Decimal) : d.IsCanonical ↔
    -- it is 0e0 (no 0e1, 0e2, etc), or
    (d.significand = 0 ∧ d.exponent = 0) ∨
    -- the significand has no trailing zeros (e.g. must be 1e2 not 100e0)
    (d.significand ≠ 0 ∧ d.significand % 10 ≠ 0) := Iff.rfl

example (w : UInt64) : Word.signBit w = ((w >>> 63) ≠ 0 : Bool) := rfl
example (w : UInt64) : Word.biasedExp w = ((w >>> 52) &&& 0x7FF).toNat := rfl
example (w : UInt64) : Word.mantissa w = (w &&& 0x000F_FFFF_FFFF_FFFF).toNat := rfl

example (w : UInt64) : Word.decode w =
    if Word.biasedExp w = 0 then
      ⟨Word.signBit w, Word.mantissa w, -1074⟩
    else
      ⟨Word.signBit w, Word.mantissa w + (1 <<< 52),
       (Word.biasedExp w : Int) - 1023 - 52⟩ := rfl

example (w : UInt64) :
    Word.isNaN w = (Word.biasedExp w = 2047 && Word.mantissa w ≠ 0) := rfl
example (w : UInt64) :
    Word.isInf w = (Word.biasedExp w = 2047 && Word.mantissa w = 0) := rfl
example (w : UInt64) :
    Word.isFinite w = (Word.biasedExp w < 2047 : Bool) := rfl

/-! ## The reader

The printer's specification is stated in terms of the reader, so the
reader is pinned down first. -/

/-- `w` is THE nearest finite binary64 word to `d`, over every finite bit
pattern, not merely those some runtime `Float` happens to produce. -/
structure NearestWord (d : Decimal) (w : UInt64) : Prop where
  finite : Word.isFinite w
  /-- `d`'s sign is carried; on a zero only the sign bit can show it. -/
  sign : Word.signBit w = d.sign
  /-- No finite word is closer to `d`, and an exact tie against a word of a
  different value goes to the even mantissa. -/
  nearest : ∀ v : UInt64, Word.isFinite v →
      dist d w ≤ dist d v
    ∧ (wordVal v ≠ wordVal w → dist d v = dist d w → Word.mantissa w % 2 = 0)

/-- A correct reader returns the nearest word in range, and the infinity
pattern of the decimal's sign at or past the threshold `2^1024 - 2^970`,
the midpoint between the largest finite value and its would-be successor
(ties-to-even sends the midpoint itself to infinity). -/
structure CorrectReader (p : Decimal → UInt64) : Prop where
  inRange : ∀ d : Decimal, Rat.abs (toRat d) < 2 ^ 1024 - 2 ^ 970 → NearestWord d (p d)
  overflow : ∀ d : Decimal, 2 ^ 1024 - 2 ^ 970 ≤ Rat.abs (toRat d) →
    Word.isInf (p d) ∧ Word.signBit (p d) = d.sign

/-! ## The printer -/

/-- The three ways a decimal `d` beats another decimal `d'` for the word `w`:
it is strictly shorter, or just as short and closer to the true value, or
just as short and as close and the even one. -/
inductive Beats (w : UInt64) (d d' : Decimal) : Prop
  | shorter : digits d.significand < digits d'.significand → Beats w d d'
  | closer  : digits d'.significand = digits d.significand → dist d w < dist d' w → Beats w d d'
  | even    : digits d'.significand = digits d.significand → dist d w = dist d' w →
              d.significand % 2 = 0 → Beats w d d'

/-- `d` is THE shortest decimal for `w`. -/
structure ShortestDecimal (w : UInt64) (d : Decimal) : Prop where
  canonical : d.IsCanonical
  /-- Reading `d` back reproduces `w`, bit for bit. -/
  roundTrip : Clinger.ofDecimalBits d = w
  /-- `d` beats every other canonical decimal that reads back to `w`. -/
  shortest : ∀ d' : Decimal, d' ≠ d → d'.IsCanonical → Clinger.ofDecimalBits d' = w →
    Beats w d d'

/-- A correct printer rejects NaN and infinity patterns with the given
errors and returns THE shortest decimal for every finite word. -/
structure CorrectPrinter (p : UInt64 → Except String Decimal) : Prop where
  nan : ∀ w : UInt64, Word.isNaN w → p w = .error "NaN"
  inf : ∀ w : UInt64, Word.isInf w →
    p w = .error (if Word.signBit w then "-Infinity" else "Infinity")
  finite : ∀ w : UInt64, Word.isFinite w → ∃ d : Decimal, p w = .ok d ∧ ShortestDecimal w d

end Srtfp.Spec

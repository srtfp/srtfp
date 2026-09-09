module
/- The specification: what it means to be a correct binary64 reader and a
   correct shortest-decimal printer. Stated on raw IEEE-754 bit patterns
   (`UInt64` words), read through Lean's own model of binary64
   (`Float.Model.UnpackedFloat.unpack`, core since v4.33). The theorems
   that the library's functions are the unique such reader and printer are
   in `Srtfp/Correctness.lean`.

   Everything needed to read this file is core Lean or defined here. -/

public import Init.Data.Float

@[expose] public section

open Float.Model (UnpackedFloat)
open Float.Model.UnpackedFloat (Sign)

namespace Srtfp

/-! ## Decimals -/

/-- An exact base-10 value: `(-1)^sign · significand · 10^exponent`. -/
structure Decimal where
  sign : Sign
  significand : Nat
  exponent : Int

/-- Canonical form: `0e0` (of either sign), or no trailing zero in the
significand (`1e2`, not `100e0`). -/
def Decimal.IsCanonical (d : Decimal) : Prop :=
  (d.significand = 0 ∧ d.exponent = 0) ∨ (d.significand ≠ 0 ∧ d.significand % 10 ≠ 0)

/-- Canonicalisation preserves the sign and moves only trailing zeros into the exponent. -/
def Decimal.Normalizes (sign : Sign) (sig : Nat) (exp : Int) (d : Decimal) : Prop :=
  d.IsCanonical ∧ d.sign = sign ∧
  ((sig = 0 ∧ d.significand = 0) ∨
    ∃ zeros : Nat, sig = d.significand * 10 ^ zeros ∧ d.exponent = exp + zeros)

namespace Spec

/-! ## Words

Lean's model reads a binary64 word as `.finite s m e` (the value
`(-1)^s · m · 2^e`), `.zero s`, `.infinity s`, or `.notANumber`. -/

/-- The word `w`, unpacked. -/
def unpack (w : UInt64) : UnpackedFloat :=
  UnpackedFloat.unpack Float.Model.Format.binary64 w.toBitVec

/-! ## Values -/

/-- `(-1)^sign`. -/
def signVal : Sign → Rat
  | .negative => -1
  | .positive => 1

/-- `(-1)^sign · m · base^e`. -/
def val (base : Rat) (sign : Sign) (m : Nat) (e : Int) : Rat :=
  signVal sign * (m * base ^ e)

/-- The exact value of a decimal. -/
def toRat (d : Decimal) : Rat := val 10 d.sign d.significand d.exponent

/-- The exact value of a finite word. -/
def wordVal (w : UInt64) : Rat :=
  match unpack w with
  | .finite s m e _ => val 2 s m e
  | _ => 0

/-- The sign of a word; a NaN counts as positive. -/
def wordSign (w : UInt64) : Sign :=
  match unpack w with
  | .finite s _ _ _ | .zero s | .infinity s => s
  | .notANumber => .positive

/-- The integer significand of a finite word; `0` for a zero. -/
def wordSig (w : UInt64) : Nat :=
  match unpack w with
  | .finite _ m _ _ => m
  | _ => 0

/-- The distance between a decimal's value and a word's. -/
def dist (d : Decimal) (w : UInt64) : Rat := Rat.abs (wordVal w - toRat d)

/-- Number of base-10 digits (`digits 0 = 1`). -/
def digits (n : Nat) : Nat := (Nat.toDigits 10 n).length

/-! ## The reader

The printer's specification is stated in terms of the reader, so the
reader is pinned down first. -/

/-- `w` is THE nearest finite binary64 word to `d`, over every finite bit
pattern, not merely those some runtime `Float` happens to produce. -/
structure NearestWord (d : Decimal) (w : UInt64) : Prop where
  finite : (unpack w).isFinite
  /-- `d`'s sign is carried; on a zero only the sign can show it. -/
  sign : wordSign w = d.sign
  /-- No finite word is closer to `d`, and an exact tie against a word of a
  different value goes to the even significand. -/
  nearest : ∀ v : UInt64, (unpack v).isFinite →
      dist d w ≤ dist d v
    ∧ (wordVal v ≠ wordVal w → dist d v = dist d w → wordSig w % 2 = 0)

/-- A correct reader returns the nearest word in range, and the infinity of
the decimal's sign at or past the threshold `2^1024 - 2^970`, the midpoint
between the largest finite value and its would-be successor (ties-to-even
sends the midpoint itself to infinity). -/
structure CorrectReader (p : Decimal → UInt64) : Prop where
  inRange : ∀ d : Decimal, Rat.abs (toRat d) < 2 ^ 1024 - 2 ^ 970 → NearestWord d (p d)
  overflow : ∀ d : Decimal, 2 ^ 1024 - 2 ^ 970 ≤ Rat.abs (toRat d) →
    unpack (p d) = .infinity d.sign

/-- `d` reads back to `w` under every correct reader. The existence and
uniqueness theorem `correct_iff_ofDecimal` makes this non-vacuous. -/
def ReadsTo (d : Decimal) (w : UInt64) : Prop := ∀ p, CorrectReader p → p d = w

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
  roundTrip : ReadsTo d w
  /-- `d` beats every other canonical decimal that reads back to `w`. -/
  shortest : ∀ d' : Decimal, d' ≠ d → d'.IsCanonical → ReadsTo d' w → Beats w d d'

/-- A correct printer returns THE shortest decimal for every finite word
and nothing for a NaN or an infinity. -/
structure CorrectPrinter (p : UInt64 → Option Decimal) : Prop where
  special : ∀ w : UInt64, (unpack w).isFinite = false → p w = none
  finite : ∀ w : UInt64, (unpack w).isFinite → ∃ d : Decimal, p w = some d ∧ ShortestDecimal w d

end Spec

end Srtfp

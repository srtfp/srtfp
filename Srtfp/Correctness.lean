/- THE THEOREMS.  Two correctness iffs, one per direction, stated on raw
   IEEE-754 binary64 bit patterns (`UInt64` words) — fully axiom-free:

   - the float PARSER: a function is a correct Decimal to binary64-word
     reader iff it is `Clinger.ofDecimalBits`.
   - the float PRINTER: a function is a correct word to shortest-decimal
     printer iff it is `Schubfach.toDecimalBits`.

   Self-contained: the vocabulary is defined here, and the kernel checks
   the `:=` proof bodies are definitionally the theorems proved in
   `Srtfp/Proofs/{Correctness,ReaderCorrectness}.lean`.  Axioms at the end
   — only `propext`, `Classical.choice`, `Quot.sound`.

   The same statements at the `Float` level (with `Float.toBits` /
   `Float.ofBits` at the boundary) are derived in
   `Srtfp/Bridge/Correctness.lean`; those additionally admit the single
   restricted runtime axiom `Float.toBits_ofBits`
   (see `Srtfp/Float/RuntimeAxiom.lean`). -/

import Srtfp.Proofs.Correctness
import Srtfp.Proofs.ReaderCorrectness
import Srtfp.NatLog

namespace Srtfp.Spec

open Srtfp Srtfp.Float

/-! ## helper functions -/

def val (base : ℚ) (sign : Bool) (m : Nat) (e : Int) : ℚ :=
  (if sign then -1 else 1) * (m * base ^ e)

def toRat (d : Decimal) : ℚ := val 10 d.sign d.significand d.exponent

/-- The exact rational value a finite binary64 word denotes. -/
def wordVal (w : UInt64) : ℚ :=
  val 2 (Word.decode w).sign (Word.decode w).m (Word.decode w).q

/-- Number of base-10 digits -/
def digits (n : Nat) : Nat := Nat.log 10 n + 1
example : digits 0 = 1 := by unfold digits; rw [Nat.log_eq_zero_of_not (by omega)]


/-! ## referenced definitions, displayed here for convenience -/

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


/-! ## the float parser theorem

The printer theorem below is specified in terms of the reader, so the
reader is pinned down first. -/

/-- **The reader specification**: `w` is THE nearest finite binary64 word
to `d` — over *every* finite bit pattern, not merely those some runtime
`Float` happens to produce. -/
def NearestWord (d : Decimal) (w : UInt64) : Prop :=
    Word.isFinite w
    -- d's sign is carried; on a zero only the sign bit can show it
  ∧ Word.signBit w = d.sign
    -- (1) no finite word is closer to d's exact value
  ∧ (∀ v : UInt64, Word.isFinite v →
       |wordVal w - toRat d| ≤ |wordVal v - toRat d|)
    -- (2) an exact tie against a different word value forces the even mantissa
  ∧ (∀ v : UInt64, Word.isFinite v → wordVal v ≠ wordVal w →
       |wordVal v - toRat d| = |wordVal w - toRat d| →
       Word.mantissa w % 2 = 0)

/-- **A function is a correct Decimal to binary64-word reader iff it is
`Clinger.ofDecimalBits`**, bit for bit. The threshold `2^1024 - 2^970` is
the midpoint between the largest finite value and its would-be
successor; ties-to-even sends the midpoint itself to infinity. -/
theorem correct_iff_ofDecimal (p : Decimal → UInt64) :
    ( ∀ d : Decimal,
        -- in range: THE nearest word
        (|toRat d| < 2 ^ 1024 - 2 ^ 970 → NearestWord d (p d))
        -- past the threshold: the infinity pattern of d's sign
      ∧ (2 ^ 1024 - 2 ^ 970 ≤ |toRat d| →
           Word.isInf (p d) ∧ Word.signBit (p d) = d.sign) )
    ↔ ∀ d : Decimal, p d = Clinger.ofDecimalBits d :=
  Clinger.correct_iff_ofDecimal_proof p


/-! ## the float printer theorem -/

/-- **The specification**: `d` is THE shortest decimal for `w`. -/
def ShortestDecimal (w : UInt64) (d : Decimal) : Prop :=
    d.IsCanonical
    -- (1) round-trip: reading d back reproduces w, bit for bit
  ∧ Clinger.ofDecimalBits d = w
    -- against every other round-tripper d':
  ∧ (∀ d' : Decimal, d' ≠ d → d'.IsCanonical →
       Clinger.ofDecimalBits d' = w →
         -- (2) either d is strictly shorter than d'
         ( digits d.significand < digits d'.significand
         -- (3) or d' is just as short
         ∨ ( digits d'.significand = digits d.significand
           -- in which case, d is closer to the true value
           ∧ ( |toRat d - wordVal w| < |toRat d' - wordVal w|
             -- or if they're the same distance, d is the even one
             ∨ ( |toRat d - wordVal w| = |toRat d' - wordVal w|
               ∧ d.significand % 2 = 0 )))))


/-- **A function is a correct shortest-decimal printer iff it is
`Schubfach.toDecimalBits`.**  The forward direction gives uniqueness
(nothing else satisfies the spec); the backward direction gives
correctness (`toDecimalBits` satisfies it). -/
theorem correct_iff_toDecimal (p : UInt64 → Except String Decimal) :
    ( ∀ w : UInt64,
        -- NaN patterns
        (Word.isNaN w → p w = .error "NaN")
        -- ±∞ patterns
      ∧ (Word.isInf w →
           p w = .error (if Word.signBit w then "-Infinity" else "Infinity"))
        -- every finite word: THE shortest decimal
      ∧ (Word.isFinite w →
           ∃ d : Decimal, p w = .ok d ∧ ShortestDecimal w d) )
    ↔ p = Schubfach.toDecimalBits :=
  Schubfach.correct_iff_toDecimal_proof p


/-! ## derived theorem -/

/-- For each finite word, **exactly one** decimal satisfies the
specification: the one `Schubfach.toDecimalBits` returns. -/
theorem shortest_decimal_exists_unique (w : UInt64)
    (h_fin : Word.isFinite w) :
    ∃! d : Decimal, ShortestDecimal w d :=
  Schubfach.shortest_decimal_exists_unique_proof w h_fin

end Srtfp.Spec


/-! ## Axioms — the standard three only; nothing about `Float` is assumed -/

/--
info: 'Srtfp.Spec.correct_iff_ofDecimal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Srtfp.Spec.correct_iff_ofDecimal

/--
info: 'Srtfp.Spec.correct_iff_toDecimal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Srtfp.Spec.correct_iff_toDecimal

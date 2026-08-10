/- THE THEOREMS.  Two correctness iffs, one per direction:

   - the float PARSER: a function is a correct Decimal to Float reader
     iff it is `Clinger.ofDecimal`.
   - the float PRINTER: a function is a correct Float to shortest-decimal
     printer iff it is `Schubfach.toDecimal`.

   Self-contained: the vocabulary is defined here, and the kernel checks
   the `:=` proof bodies are definitionally the theorems proved in
   `Srtfp/Proofs/{Correctness,ReaderCorrectness}.lean`.  Axioms at the end.
-/

import Srtfp.Proofs.Correctness
import Srtfp.Proofs.ReaderCorrectness
import Mathlib.Data.Nat.Log

namespace Srtfp.Spec

open Srtfp Srtfp.Float

/-! ## helper functions -/

def val (base : ℚ) (sign : Bool) (m : Nat) (e : Int) : ℚ :=
  (if sign then -1 else 1) * (m * base ^ e)

def toRat (d : Decimal) : ℚ := val 10 d.sign d.significand d.exponent

def floatVal (f : Float) : ℚ := val 2 (decode f).sign (decode f).m (decode f).q

/-- Number of base-10 digits -/
def digits (n : Nat) : Nat := Nat.log 10 n + 1
example : digits 0 = 1 := by simp [digits]


/-! ## referenced definitions, displayed here for convenience -/

example (d : Decimal) : d = ⟨d.sign, d.significand, d.exponent⟩ := rfl

example (d : Decimal) : d.IsCanonical ↔
    -- it is 0e0 (no 0e1, 0e2, etc), or
    (d.significand = 0 ∧ d.exponent = 0) ∨
    -- the significand has no trailing zeros (e.g. must be 1e2 not 100e0)
    (d.significand ≠ 0 ∧ d.significand % 10 ≠ 0) := Iff.rfl

example (f : Float) : signBit f = ((f.toBits >>> 63) ≠ 0 : Bool) := rfl
example (f : Float) : biasedExpBits f = ((f.toBits >>> 52) &&& 0x7FF).toNat := rfl
example (f : Float) : mantissaBits f = (f.toBits &&& 0x000F_FFFF_FFFF_FFFF).toNat := rfl

example (f : Float) : decode f =
    if biasedExpBits f = 0 then
      ⟨signBit f, mantissaBits f, -1074⟩
    else
      ⟨signBit f, mantissaBits f + (1 <<< 52),
       (biasedExpBits f : Int) - 1023 - 52⟩ := rfl

example (f : Float) :
    isNaNBits f = (biasedExpBits f = 2047 && mantissaBits f ≠ 0) := rfl
example (f : Float) :
    isInfBits f = (biasedExpBits f = 2047 && mantissaBits f = 0) := rfl
example (f : Float) :
    isFiniteBits f = (biasedExpBits f < 2047 : Bool) := rfl


/-! ## the float parser theorem

The printer theorem below is specified in terms of the reader, so the
reader is pinned down first. -/

/-- **The reader specification**: `f` is THE nearest float to `d`. -/
def NearestFloat (d : Decimal) (f : Float) : Prop :=
    isFiniteBits f
    -- d's sign is carried; on a zero only the sign bit can show it
  ∧ signBit f = d.sign
    -- (1) no finite float is closer to d's exact value
  ∧ (∀ g : Float, isFiniteBits g →
       |floatVal f - toRat d| ≤ |floatVal g - toRat d|)
    -- (2) an exact tie against a different float value forces the even mantissa
  ∧ (∀ g : Float, isFiniteBits g → floatVal g ≠ floatVal f →
       |floatVal g - toRat d| = |floatVal f - toRat d| →
       mantissaBits f % 2 = 0)

/-- **A function is a correct Decimal to Float reader iff it is
`Clinger.ofDecimal`**, bit for bit. The threshold `2^1024 - 2^970` is
the midpoint between the largest finite float and its would-be
successor; ties-to-even sends the midpoint itself to infinity. -/
theorem correct_iff_ofDecimal (p : Decimal → Float) :
    ( ∀ d : Decimal,
        -- in range: THE nearest float
        (|toRat d| < 2 ^ 1024 - 2 ^ 970 → NearestFloat d (p d))
        -- past the threshold: the infinity of d's sign
      ∧ (2 ^ 1024 - 2 ^ 970 ≤ |toRat d| →
           isInfBits (p d) ∧ signBit (p d) = d.sign) )
    ↔ ∀ d : Decimal, (p d).toBits = (Clinger.ofDecimal d).toBits :=
  Clinger.correct_iff_ofDecimal_proof p


/-! ## the float printer theorem -/

/-- **The specification**: `d` is THE shortest decimal for `f`. -/
def ShortestDecimal (f : Float) (d : Decimal) : Prop :=
    d.IsCanonical
    -- (1) round-trip: reading d back reproduces f, bit for bit
  ∧ (Clinger.ofDecimal d).toBits = f.toBits
    -- against every other round-tripper d':
  ∧ (∀ d' : Decimal, d' ≠ d → d'.IsCanonical →
       (Clinger.ofDecimal d').toBits = f.toBits →
         -- (2) either d is strictly shorter than d'
         ( digits d.significand < digits d'.significand
         -- (3) or d' is just as short
         ∨ ( digits d'.significand = digits d.significand
           -- in which case, d is closer to the true value
           ∧ ( |toRat d - floatVal f| < |toRat d' - floatVal f|
             -- or if they're the same distance, d is the even one
             ∨ ( |toRat d - floatVal f| = |toRat d' - floatVal f|
               ∧ d.significand % 2 = 0 )))))


/-- **A function is a correct shortest-decimal printer iff it is
`Schubfach.toDecimal`.**  The forward direction gives uniqueness (nothing
else satisfies the spec); the backward direction gives correctness
(`toDecimal` satisfies it). -/
theorem correct_iff_toDecimal (p : Float → Except String Decimal) :
    ( ∀ f : Float,
        -- NaN
        (isNaNBits f → p f = .error "NaN")
        -- ±∞
      ∧ (isInfBits f →
           p f = .error (if signBit f then "-Infinity" else "Infinity"))
        -- every finite float: THE shortest decimal
      ∧ (isFiniteBits f →
           ∃ d : Decimal, p f = .ok d ∧ ShortestDecimal f d) )
    ↔ p = Schubfach.toDecimal :=
  Schubfach.correct_iff_toDecimal_proof p


/-! ## derived theorem -/

/-- For each finite float, **exactly one** decimal satisfies the
specification: the one `Schubfach.toDecimal` returns. -/
theorem shortest_decimal_exists_unique (f : Float)
    (h_fin : isFiniteBits f) :
    ∃! d : Decimal, ShortestDecimal f d :=
  Schubfach.shortest_decimal_exists_unique_proof f h_fin

end Srtfp.Spec


/-! ## Axioms -/

/--
info: 'Srtfp.Spec.correct_iff_ofDecimal' depends on axioms: [propext, Classical.choice, Float.toBits_ofBits, Quot.sound]
-/
#guard_msgs in
#print axioms Srtfp.Spec.correct_iff_ofDecimal

/--
info: 'Srtfp.Spec.correct_iff_toDecimal' depends on axioms: [propext, Classical.choice, Float.toBits_ofBits, Quot.sound]
-/
#guard_msgs in
#print axioms Srtfp.Spec.correct_iff_toDecimal

/-- The axiom's side condition, displayed for convenience: -/
example (x : UInt64) : Float.isNaNPattern x =
    (((x >>> 52) &&& 0x7FF == 0x7FF) && (x &&& 0xF_FFFF_FFFF_FFFF != 0)) := rfl

/-- The only non-standard axiom: converting non-NaN bits to `Float` and
back is the identity (the runtime canonicalises NaN payloads; see
`SrtfpTest/RuntimeAxiomProbe.lean`): -/
example : ∀ x : UInt64, Float.isNaNPattern x = false → (Float.ofBits x).toBits = x :=
  Float.toBits_ofBits

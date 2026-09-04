module
/- The correctness theorems at the runtime `Float` level.

   The same two theorems as `Srtfp/Correctness.lean`, with `Float` at the
   boundary: the reader returns `Float`s, the printer consumes them, and
   candidates range over `Float`s. Each proof is the bits-level theorem
   transported across the bit round-trip `Float.toBits_ofBits`
   (`Srtfp/Float/Model.lean`), which realizes every finite word as a
   `Float` (`Float.ofBits`) and cancels `(Float.ofBits w).toBits = w` on the
   reader's outputs. -/

public import Srtfp.Correctness
public import Srtfp.Proofs.Bits
public import Srtfp.Bridge.Clinger

@[expose] public section

open Srtfp.Compat

namespace Srtfp.Spec

open Srtfp Srtfp.Float

/-! ## Float-level vocabulary -/

/-- The exact value of a finite `Float`: `wordVal f.toBits`. -/
def floatVal (f : Float) : Rat := wordVal f.toBits

/-- The distance between a decimal's value and a float's. -/
def distF (d : Decimal) (f : Float) : Rat := |floatVal f - toRat d|

/-- `f` is THE nearest finite float to `d`, candidates ranging over `Float`s. -/
structure NearestFloat (d : Decimal) (f : Float) : Prop where
  finite : isFiniteBits f
  sign : signBit f = d.sign
  nearest : ∀ g : Float, isFiniteBits g →
      distF d f ≤ distF d g
    ∧ (floatVal g ≠ floatVal f → distF d g = distF d f → mantissaBits f % 2 = 0)

structure CorrectReaderF (p : Decimal → Float) : Prop where
  inRange : ∀ d : Decimal, |toRat d| < 2 ^ 1024 - 2 ^ 970 → NearestFloat d (p d)
  overflow : ∀ d : Decimal, 2 ^ 1024 - 2 ^ 970 ≤ |toRat d| →
    isInfBits (p d) ∧ signBit (p d) = d.sign

inductive BeatsF (f : Float) (d d' : Decimal) : Prop
  | shorter : digits d.significand < digits d'.significand → BeatsF f d d'
  | closer  : digits d'.significand = digits d.significand → distF d f < distF d' f → BeatsF f d d'
  | even    : digits d'.significand = digits d.significand → distF d f = distF d' f →
              d.significand % 2 = 0 → BeatsF f d d'

structure ShortestDecimalF (f : Float) (d : Decimal) : Prop where
  canonical : d.IsCanonical
  roundTrip : (Clinger.ofDecimal d).toBits = f.toBits
  shortest : ∀ d' : Decimal, d' ≠ d → d'.IsCanonical →
    (Clinger.ofDecimal d').toBits = f.toBits → BeatsF f d d'

structure CorrectPrinterF (p : Float → Except String Decimal) : Prop where
  nan : ∀ f : Float, isNaNBits f → p f = .error "NaN"
  inf : ∀ f : Float, isInfBits f →
    p f = .error (if signBit f then "-Infinity" else "Infinity")
  finite : ∀ f : Float, isFiniteBits f → ∃ d : Decimal, p f = .ok d ∧ ShortestDecimalF f d

/-! ## Transport lemmas -/

/-- A finite word is realized by a `Float` with exactly those bits: the
axiom's contribution to the `Float` tier. -/
private theorem exists_float_of_finite_word (v : UInt64) (h : Word.isFinite v = true) :
    ∃ g : Float, g.toBits = v :=
  ⟨Float.ofBits v, _root_.Float.toBits_ofBits v (isNaNPattern_false_of_isFinite v h)⟩

private theorem distF_eq (d : Decimal) (g : Float) : distF d g = dist d g.toBits := rfl

/-- `NearestWord` at `f.toBits` is exactly `NearestFloat`: the candidate
sets coincide across the axiom. -/
private theorem nearestFloat_iff (d : Decimal) (f : Float) :
    NearestFloat d f ↔ NearestWord d f.toBits := by
  constructor
  · intro h
    refine ⟨h.finite, h.sign, fun v hv => ?_⟩
    obtain ⟨g, hg⟩ := exists_float_of_finite_word v hv
    have := h.nearest g (by rw [isFiniteBits_word, hg]; exact hv)
    rw [distF_eq, distF_eq, hg] at this
    rwa [show floatVal g = wordVal v from by unfold floatVal; rw [hg]] at this
  · intro h
    exact ⟨h.finite, h.sign, fun g hg => h.nearest g.toBits hg⟩

private theorem beatsF_iff (f : Float) (d d' : Decimal) :
    BeatsF f d d' ↔ Beats f.toBits d d' := by
  constructor
  · rintro (h1 | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩)
    · exact .shorter h1
    · exact .closer h1 h2
    · exact .even h1 h2 h3
  · rintro (h1 | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩)
    · exact .shorter h1
    · exact .closer h1 h2
    · exact .even h1 h2 h3

/-- `ShortestDecimalF` at `f` is `ShortestDecimal` at `f.toBits`: the
round-trip clauses convert through `ofDecimal_toBits`. -/
private theorem shortestDecimalF_iff (f : Float) (d : Decimal) :
    ShortestDecimalF f d ↔ ShortestDecimal f.toBits d := by
  have hrt : ∀ c : Decimal,
      ((Clinger.ofDecimal c).toBits = f.toBits ↔ Clinger.ofDecimalBits c = f.toBits) := by
    intro c; rw [Clinger.ofDecimal_toBits]
  constructor
  · intro h
    exact ⟨h.canonical, (hrt d).mp h.roundTrip,
      fun d' hne hc hrt' => (beatsF_iff f d d').mp (h.shortest d' hne hc ((hrt d').mpr hrt'))⟩
  · intro h
    exact ⟨h.canonical, (hrt d).mpr h.roundTrip,
      fun d' hne hc hrt' => (beatsF_iff f d d').mpr (h.shortest d' hne hc ((hrt d').mp hrt'))⟩

/-! ## The reader theorem, `Float` tier -/

/-- **A function is a correct Decimal→`Float` reader iff it agrees with
`Clinger.ofDecimal` bit for bit.** Float tier of
`Srtfp.Spec.correct_iff_ofDecimal`; admits the runtime axiom. -/
theorem correct_iff_ofDecimalF (p : Decimal → Float) :
    CorrectReaderF p ↔ ∀ d : Decimal, (p d).toBits = (Clinger.ofDecimal d).toBits := by
  have hbits := correct_iff_ofDecimal (fun d => (p d).toBits)
  constructor
  · intro h d
    rw [Clinger.ofDecimal_toBits]
    exact (hbits.mp ⟨fun d' hin => (nearestFloat_iff d' (p d')).mp (h.inRange d' hin),
                      fun d' hout => h.overflow d' hout⟩) d
  · intro h
    have hb : ∀ c : Decimal, (p c).toBits = Clinger.ofDecimalBits c := by
      intro c; rw [h c, Clinger.ofDecimal_toBits]
    have hc := hbits.mpr hb
    exact ⟨fun d hin => (nearestFloat_iff d (p d)).mpr (hc.inRange d hin),
           fun d hout => hc.overflow d hout⟩

/-! ## The printer theorem, `Float` tier -/

/-- **A function is a correct `Float`→shortest-decimal printer iff it is
`Printer.toDecimal`.** Float tier of `Srtfp.Spec.correct_iff_toDecimal`;
admits the runtime axiom. -/
theorem correct_iff_toDecimalF (p : Float → Except String Decimal) :
    CorrectPrinterF p ↔ p = Printer.toDecimal := by
  have hprinter := (correct_iff_toDecimal Printer.toDecimalBits).mpr rfl
  constructor
  · intro h
    funext f
    rw [Printer.toDecimal_eq_bits]
    by_cases hN : Word.isNaN f.toBits = true
    · rw [h.nan f hN, hprinter.nan f.toBits hN]
    · by_cases hF : Word.isFinite f.toBits = true
      · obtain ⟨d, hpd, hspec⟩ := h.finite f hF
        obtain ⟨d₀, hd₀, hspec₀⟩ := hprinter.finite f.toBits hF
        obtain ⟨dstar, _, hstar⟩ := shortest_decimal_exists_unique f.toBits hF
        rw [hpd, hd₀, hstar d ((shortestDecimalF_iff f d).mp hspec), hstar d₀ hspec₀]
      · have hF' : ¬ (Word.biasedExp f.toBits < 2047) := fun hlt =>
          hF (by unfold Word.isFinite; simpa using hlt)
        have hbe : Word.biasedExp f.toBits = 2047 := by
          have hlt := word_biasedExp_lt f.toBits
          omega
        have hm : Word.mantissa f.toBits = 0 := by
          rcases Nat.eq_zero_or_pos (Word.mantissa f.toBits) with h0 | hpos
          · exact h0
          · exfalso
            apply hN
            unfold Word.isNaN
            simp [hbe]
            omega
        have hI : Word.isInf f.toBits = true := by
          unfold Word.isInf; simp [hbe, hm]
        rw [h.inf f hI, hprinter.inf f.toBits hI]; rfl
  · rintro rfl
    refine ⟨fun f hn => ?_, fun f hi => ?_, fun f hf => ?_⟩
    · rw [Printer.toDecimal_eq_bits]; exact hprinter.nan f.toBits hn
    · rw [Printer.toDecimal_eq_bits]; exact hprinter.inf f.toBits hi
    · obtain ⟨d, hd, hspec⟩ := hprinter.finite f.toBits hf
      exact ⟨d, by rw [Printer.toDecimal_eq_bits]; exact hd, (shortestDecimalF_iff f d).mpr hspec⟩

/-! ## Derived theorem, `Float` tier -/

/-- For each finite float, exactly one decimal is the shortest. -/
theorem shortest_decimal_exists_uniqueF (f : Float) (h_fin : isFiniteBits f) :
    ∃! d : Decimal, ShortestDecimalF f d := by
  obtain ⟨d, hd, huniq⟩ := shortest_decimal_exists_unique f.toBits h_fin
  exact ⟨d, (shortestDecimalF_iff f d).mpr hd,
         fun d' hd' => huniq d' ((shortestDecimalF_iff f d').mp hd')⟩

end Srtfp.Spec

/-- The round-trip's side condition, displayed for convenience: -/
example (x : UInt64) : Float.isNaNPattern x =
    (((x >>> 52) &&& 0x7FF == 0x7FF) && (x &&& 0xF_FFFF_FFFF_FFFF != 0)) := rfl

/-- The bridge to `Float`: converting non-NaN bits to `Float` and back is the
identity, a theorem over core's `Float.Model` (`Srtfp/Float/Model.lean`): -/
example : ∀ x : UInt64, Float.isNaNPattern x = false → (Float.ofBits x).toBits = x :=
  Float.toBits_ofBits

/- THE THEOREMS, at the runtime `Float` level.

   The same two correctness iffs as `Srtfp/Correctness.lean`, with the
   runtime `Float` type at the boundary: the reader returns `Float`s, the
   printer consumes them, and candidates range over `Float`s. Each proof
   is the corresponding bits-level theorem transported across the single
   restricted runtime axiom `Float.toBits_ofBits`
   (`Srtfp/Float/RuntimeAxiom.lean`): the axiom realizes every finite
   word as a `Float` (`Float.ofBits`) and cancels
   `(Float.ofBits w).toBits = w` on the reader's outputs.

   Importing this module is the opt-in for trusting the runtime contract;
   everything upstream of it is axiom-free. -/

import Srtfp.Correctness
import Srtfp.Bridge.Clinger

namespace Srtfp.Spec

open Srtfp Srtfp.Float

/-! ## Float-level vocabulary -/

/-- The exact rational value of a finite `Float` — definitionally
`wordVal f.toBits`. -/
def floatVal (f : Float) : ℚ := wordVal f.toBits

/-- **The reader specification** on `Float`s: `f` is THE nearest finite
float to `d`, candidates ranging over `Float`s. -/
def NearestFloat (d : Decimal) (f : Float) : Prop :=
    isFiniteBits f
  ∧ signBit f = d.sign
  ∧ (∀ g : Float, isFiniteBits g →
       |floatVal f - toRat d| ≤ |floatVal g - toRat d|)
  ∧ (∀ g : Float, isFiniteBits g → floatVal g ≠ floatVal f →
       |floatVal g - toRat d| = |floatVal f - toRat d| →
       mantissaBits f % 2 = 0)

/-- **The printer specification** on `Float`s. -/
def ShortestDecimalF (f : Float) (d : Decimal) : Prop :=
    d.IsCanonical
  ∧ (Clinger.ofDecimal d).toBits = f.toBits
  ∧ (∀ d' : Decimal, d' ≠ d → d'.IsCanonical →
       (Clinger.ofDecimal d').toBits = f.toBits →
         ( digits d.significand < digits d'.significand
         ∨ ( digits d'.significand = digits d.significand
           ∧ ( |toRat d - floatVal f| < |toRat d' - floatVal f|
             ∨ ( |toRat d - floatVal f| = |toRat d' - floatVal f|
               ∧ d.significand % 2 = 0 )))))

/-! ## Transport lemmas -/

/-- A finite word is realized by a `Float` with exactly those bits — the
axiom's contribution to the `Float` tier. -/
private theorem exists_float_of_finite_word (v : UInt64)
    (h : Word.isFinite v = true) :
    ∃ g : Float, g.toBits = v :=
  ⟨Float.ofBits v, _root_.Float.toBits_ofBits v (isNaNPattern_false_of_isFinite v h)⟩

/-- `NearestWord` at `f.toBits` is exactly `NearestFloat` — the candidate
sets coincide across the axiom. -/
private theorem nearestFloat_iff_nearestWord (d : Decimal) (f : Float) :
    NearestFloat d f ↔ NearestWord d f.toBits := by
  unfold NearestFloat NearestWord
  refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr ?_ ?_))
  · constructor
    · intro h v hv
      obtain ⟨g, hg⟩ := exists_float_of_finite_word v hv
      have := h g (by rw [isFiniteBits_word, hg]; exact hv)
      rwa [show floatVal g = wordVal v from by unfold floatVal; rw [hg]] at this
    · intro h g hg
      exact h g.toBits hg
  · constructor
    · intro h v hv hne heq
      obtain ⟨g, hg⟩ := exists_float_of_finite_word v hv
      refine h g (by rw [isFiniteBits_word, hg]; exact hv) ?_ ?_
      · rwa [show floatVal g = wordVal v from by unfold floatVal; rw [hg]]
      · rwa [show floatVal g = wordVal v from by unfold floatVal; rw [hg]]
    · intro h g hg hne heq
      exact h g.toBits hg hne heq

/-- `ShortestDecimalF` at `f` is `ShortestDecimal` at `f.toBits` — the
round-trip clauses convert through `ofDecimal_toBits`. -/
private theorem shortestDecimalF_iff_bits (f : Float) (d : Decimal) :
    ShortestDecimalF f d ↔ ShortestDecimal f.toBits d := by
  unfold ShortestDecimalF ShortestDecimal
  have hrt : ∀ c : Decimal,
      ((Clinger.ofDecimal c).toBits = f.toBits ↔ Clinger.ofDecimalBits c = f.toBits) := by
    intro c
    rw [Clinger.ofDecimal_toBits]
  refine and_congr Iff.rfl (and_congr (hrt d) ?_)
  constructor
  · intro h d' hne hc hrt'
    exact h d' hne hc ((hrt d').mpr hrt')
  · intro h d' hne hc hrt'
    exact h d' hne hc ((hrt d').mp hrt')

/-! ## the float parser theorem, `Float` tier -/

/-- **A function is a correct Decimal→`Float` reader iff it agrees with
`Clinger.ofDecimal` bit for bit.** Float tier of
`Srtfp.Spec.correct_iff_ofDecimal`; admits the runtime axiom. -/
theorem correct_iff_ofDecimalF (p : Decimal → Float) :
    ( ∀ d : Decimal,
        (|toRat d| < 2 ^ 1024 - 2 ^ 970 → NearestFloat d (p d))
      ∧ (2 ^ 1024 - 2 ^ 970 ≤ |toRat d| →
           isInfBits (p d) ∧ signBit (p d) = d.sign) )
    ↔ ∀ d : Decimal, (p d).toBits = (Clinger.ofDecimal d).toBits := by
  have hbits := correct_iff_ofDecimal (fun d => (p d).toBits)
  constructor
  · intro h d
    rw [Clinger.ofDecimal_toBits]
    refine (hbits.mp ?_) d
    intro d'
    refine ⟨?_, (h d').2⟩
    intro hin
    exact (nearestFloat_iff_nearestWord d' (p d')).mp ((h d').1 hin)
  · intro h d
    have hb : ∀ c : Decimal, (p c).toBits = Clinger.ofDecimalBits c := by
      intro c
      rw [h c, Clinger.ofDecimal_toBits]
    have := hbits.mpr hb d
    exact ⟨fun hin => (nearestFloat_iff_nearestWord d (p d)).mpr (this.1 hin), this.2⟩

/-! ## the float printer theorem, `Float` tier -/

/-- **A function is a correct `Float`→shortest-decimal printer iff it
is `Schubfach.toDecimal`.** Float tier of
`Srtfp.Spec.correct_iff_toDecimal`; admits the runtime axiom. -/
theorem correct_iff_toDecimalF (p : Float → Except String Decimal) :
    ( ∀ f : Float,
        (isNaNBits f → p f = .error "NaN")
      ∧ (isInfBits f →
           p f = .error (if signBit f then "-Infinity" else "Infinity"))
      ∧ (isFiniteBits f →
           ∃ d : Decimal, p f = .ok d ∧ ShortestDecimalF f d) )
    ↔ p = Schubfach.toDecimal := by
  have hprinter := (correct_iff_toDecimal Schubfach.toDecimalBits).mpr rfl
  constructor
  · intro h
    funext f
    rw [Schubfach.toDecimal_eq_bits]
    obtain ⟨hnan, hinf, hfin⟩ := h f
    obtain ⟨hnanB, hinfB, hfinB⟩ := hprinter f.toBits
    by_cases hN : Word.isNaN f.toBits = true
    · rw [hnan hN, hnanB hN]
    · by_cases hF : Word.isFinite f.toBits = true
      · obtain ⟨d, hpd, hspec⟩ := hfin hF
        obtain ⟨d₀, hd₀, hspec₀⟩ := hfinB hF
        obtain ⟨dstar, _, hstar⟩ := shortest_decimal_exists_unique f.toBits hF
        rw [hpd, hd₀, hstar d ((shortestDecimalF_iff_bits f d).mp hspec),
            hstar d₀ hspec₀]
      · have hF' : ¬ (Word.biasedExp f.toBits < 2047) := fun hlt =>
          hF (by unfold Word.isFinite; simpa using hlt)
        have hbe : Word.biasedExp f.toBits = 2047 := by
          have hlt := word_biasedExp_lt f.toBits
          omega
        have hm : Word.mantissa f.toBits = 0 := by
          by_contra hm_ne
          apply hN
          unfold Word.isNaN
          simp [hbe, hm_ne]
        have hI : Word.isInf f.toBits = true := by
          unfold Word.isInf; simp [hbe, hm]
        rw [hinf hI, hinfB hI]; rfl
  · rintro rfl f
    have hp : Schubfach.toDecimal f = Schubfach.toDecimalBits f.toBits :=
      Schubfach.toDecimal_eq_bits f
    obtain ⟨hnan, hinf, hfin⟩ := hprinter f.toBits
    refine ⟨fun hn => by rw [hp]; exact hnan hn,
            fun hi => by rw [hp]; exact hinf hi,
            fun hf => ?_⟩
    obtain ⟨d, hd, hspec⟩ := hfin hf
    exact ⟨d, by rw [hp]; exact hd, (shortestDecimalF_iff_bits f d).mpr hspec⟩

/-! ## derived theorem, `Float` tier -/

/-- For each finite float, exactly one decimal satisfies the spec. -/
theorem shortest_decimal_exists_uniqueF (f : Float)
    (h_fin : isFiniteBits f) :
    ∃! d : Decimal, ShortestDecimalF f d := by
  obtain ⟨d, hd, huniq⟩ := shortest_decimal_exists_unique f.toBits h_fin
  exact ⟨d, (shortestDecimalF_iff_bits f d).mpr hd,
         fun d' hd' => huniq d' ((shortestDecimalF_iff_bits f d').mp hd')⟩

end Srtfp.Spec

/-! ## Axioms — the standard three plus the single runtime axiom -/

/--
info: 'Srtfp.Spec.correct_iff_ofDecimalF' depends on axioms: [propext, Classical.choice, Float.toBits_ofBits, Quot.sound]
-/
#guard_msgs in
#print axioms Srtfp.Spec.correct_iff_ofDecimalF

/--
info: 'Srtfp.Spec.correct_iff_toDecimalF' depends on axioms: [propext, Classical.choice, Float.toBits_ofBits, Quot.sound]
-/
#guard_msgs in
#print axioms Srtfp.Spec.correct_iff_toDecimalF

/-- The axiom's side condition, displayed for convenience: -/
example (x : UInt64) : Float.isNaNPattern x =
    (((x >>> 52) &&& 0x7FF == 0x7FF) && (x &&& 0xF_FFFF_FFFF_FFFF != 0)) := rfl

/-- The only non-standard axiom: converting non-NaN bits to `Float` and
back is the identity (the runtime canonicalises NaN payloads; see
`SrtfpTest/RuntimeAxiomProbe.lean`): -/
example : ∀ x : UInt64, Float.isNaNPattern x = false → (Float.ofBits x).toBits = x :=
  Float.toBits_ofBits

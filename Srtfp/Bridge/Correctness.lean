module
/- The correctness theorems at the runtime `Float` level.

   The same two theorems as `Srtfp/Correctness.lean`, with `Float` at the
   boundary: the reader returns `Float`s, the printer consumes them, and
   candidates range over `Float`s. Each proof is the bits-level theorem
   transported across the bit round-trip `Float.toBits_ofBits`
   (`Srtfp/Bridge/Basic.lean`), which realizes every finite word as a
   `Float` (`Float.ofBits`). -/

public import Srtfp.Correctness
public import Srtfp.Bridge.Basic

@[expose] public section

open Srtfp.Compat

namespace Srtfp.Spec

open Srtfp
open Float.Model (UnpackedFloat)
open Float.Model.UnpackedFloat (Sign)

/-! ## Float-level vocabulary

`Float.toBits f = f.toModel.toBits`, so unpacking a `Float` is the spec's
`unpack` of its bits, definitionally. -/

/-- A `Float`, unpacked by Lean's model. -/
def unpackF (f : Float) : Float.Model.UnpackedFloat := f.toModel.unpack

theorem unpackF_eq (f : Float) : unpackF f = unpack f.toBits := rfl

/-- The exact value of a finite `Float`: `wordVal f.toBits`. -/
def floatVal (f : Float) : Rat := wordVal f.toBits

/-- The sign and integer significand of a `Float`. -/
def floatSign (f : Float) : Sign := wordSign f.toBits
def floatSig (f : Float) : Nat := wordSig f.toBits

/-- The distance between a decimal's value and a float's. -/
def distF (d : Decimal) (f : Float) : Rat := |floatVal f - toRat d|

/-- `f` is THE nearest finite float to `d`, candidates ranging over `Float`s. -/
structure NearestFloat (d : Decimal) (f : Float) : Prop where
  finite : (unpackF f).isFinite
  sign : floatSign f = d.sign
  nearest : ∀ g : Float, (unpackF g).isFinite →
      distF d f ≤ distF d g
    ∧ (floatVal g ≠ floatVal f → distF d g = distF d f → floatSig f % 2 = 0)

structure CorrectReaderF (p : Decimal → Float) : Prop where
  inRange : ∀ d : Decimal, |toRat d| < 2 ^ 1024 - 2 ^ 970 → NearestFloat d (p d)
  overflow : ∀ d : Decimal, 2 ^ 1024 - 2 ^ 970 ≤ |toRat d| →
    unpackF (p d) = .infinity d.sign

inductive BeatsF (f : Float) (d d' : Decimal) : Prop
  | shorter : digits d.significand < digits d'.significand → BeatsF f d d'
  | closer  : digits d'.significand = digits d.significand → distF d f < distF d' f → BeatsF f d d'
  | even    : digits d'.significand = digits d.significand → distF d f = distF d' f →
              d.significand % 2 = 0 → BeatsF f d d'

/-- `d` reads back to `f`'s bits under every correct `Float` reader. -/
def ReadsToF (d : Decimal) (f : Float) : Prop := ∀ p, CorrectReaderF p → (p d).toBits = f.toBits

structure ShortestDecimalF (f : Float) (d : Decimal) : Prop where
  canonical : d.IsCanonical
  roundTrip : ReadsToF d f
  shortest : ∀ d' : Decimal, d' ≠ d → d'.IsCanonical → ReadsToF d' f → BeatsF f d d'

structure CorrectPrinterF (p : Float → Except String Decimal) : Prop where
  nan : ∀ f : Float, unpackF f = .notANumber → p f = .error "NaN"
  inf : ∀ (f : Float) (s : Sign), unpackF f = .infinity s →
    p f = .error (match s with | .negative => "-Infinity" | .positive => "Infinity")
  finite : ∀ f : Float, (unpackF f).isFinite → ∃ d : Decimal, p f = .ok d ∧ ShortestDecimalF f d

/-! ## Transport lemmas -/

/-- A finite word is realized by a `Float` with exactly those bits: the bit
round-trip's contribution to the `Float` tier. -/
private theorem exists_float_of_finite_word (v : UInt64) (h : (unpack v).isFinite = true) :
    ∃ g : Float, g.toBits = v :=
  ⟨Float.ofBits v, _root_.Float.toBits_ofBits v
    (fun e => by rw [e] at h; simp [UnpackedFloat.isFinite] at h)⟩

private theorem distF_eq (d : Decimal) (g : Float) : distF d g = dist d g.toBits := rfl

/-- `NearestWord` at `f.toBits` is exactly `NearestFloat`: the candidate
sets coincide across the round-trip. -/
private theorem nearestFloat_iff (d : Decimal) (f : Float) :
    NearestFloat d f ↔ NearestWord d f.toBits := by
  constructor
  · intro h
    refine ⟨h.finite, h.sign, fun v hv => ?_⟩
    obtain ⟨g, hg⟩ := exists_float_of_finite_word v hv
    have := h.nearest g (by rw [unpackF_eq, hg]; exact hv)
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

/-! ## The reader theorem, `Float` tier -/

/-- **A function is a correct Decimal→`Float` reader iff it agrees with
`Reader.ofDecimal` bit for bit.** Float tier of
`Srtfp.Spec.correct_iff_ofDecimal`. -/
theorem correct_iff_ofDecimalF (p : Decimal → Float) :
    CorrectReaderF p ↔ ∀ d : Decimal, (p d).toBits = (Reader.ofDecimal d).toBits := by
  have hbits := correct_iff_ofDecimal (fun d => (p d).toBits)
  constructor
  · intro h d
    rw [Reader.ofDecimal_toBits]
    exact (hbits.mp ⟨fun d' hin => (nearestFloat_iff d' (p d')).mp (h.inRange d' hin),
                      fun d' hout => h.overflow d' hout⟩) d
  · intro h
    have hb : ∀ c : Decimal, (p c).toBits = Reader.ofDecimalBits c := by
      intro c; rw [h c, Reader.ofDecimal_toBits]
    have hc := hbits.mpr hb
    exact ⟨fun d hin => (nearestFloat_iff d (p d)).mpr (hc.inRange d hin),
           fun d hout => hc.overflow d hout⟩

/-- Reading back under every correct `Float` reader is reading back under
every correct word reader. -/
private theorem readsToF_iff (d : Decimal) (f : Float) : ReadsToF d f ↔ ReadsTo d f.toBits := by
  rw [Reader.readsTo_iff]
  constructor
  · intro h
    have := h Reader.ofDecimal ((correct_iff_ofDecimalF _).mpr fun _ => rfl)
    rwa [Reader.ofDecimal_toBits] at this
  · intro h p hp
    rw [(correct_iff_ofDecimalF p).mp hp d, Reader.ofDecimal_toBits, h]

/-- `ShortestDecimalF` at `f` is `ShortestDecimal` at `f.toBits`. -/
private theorem shortestDecimalF_iff (f : Float) (d : Decimal) :
    ShortestDecimalF f d ↔ ShortestDecimal f.toBits d := by
  constructor
  · intro h
    exact ⟨h.canonical, (readsToF_iff d f).mp h.roundTrip,
      fun d' hne hc hrt' => (beatsF_iff f d d').mp (h.shortest d' hne hc ((readsToF_iff d' f).mpr hrt'))⟩
  · intro h
    exact ⟨h.canonical, (readsToF_iff d f).mpr h.roundTrip,
      fun d' hne hc hrt' => (beatsF_iff f d d').mpr (h.shortest d' hne hc ((readsToF_iff d' f).mp hrt'))⟩

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
    have fin (hfin : (unpackF f).isFinite = true) : p f = Printer.toDecimalBits f.toBits := by
      obtain ⟨d, hpd, hspec⟩ := h.finite f hfin
      obtain ⟨d₀, hd₀, hspec₀⟩ := hprinter.finite f.toBits hfin
      obtain ⟨dstar, -, hstar⟩ := shortest_decimal_exists_unique f.toBits hfin
      rw [hpd, hd₀, hstar d ((shortestDecimalF_iff f d).mp hspec), hstar d₀ hspec₀]
    rcases hu : unpackF f with s | _ | s | ⟨s, m, e, hm⟩
    · rw [h.inf f s hu, hprinter.inf f.toBits s hu]; cases s <;> rfl
    · rw [h.nan f hu, hprinter.nan f.toBits hu]
    · exact fin (by rw [hu]; rfl)
    · exact fin (by rw [hu]; rfl)
  · rintro rfl
    refine ⟨fun f hn => ?_, fun f s hi => ?_, fun f hf => ?_⟩
    · rw [Printer.toDecimal_eq_bits]; exact hprinter.nan f.toBits hn
    · rw [Printer.toDecimal_eq_bits]; exact hprinter.inf f.toBits s hi
    · obtain ⟨d, hd, hspec⟩ := hprinter.finite f.toBits hf
      exact ⟨d, by rw [Printer.toDecimal_eq_bits]; exact hd, (shortestDecimalF_iff f d).mpr hspec⟩

/-! ## Derived theorem, `Float` tier -/

/-- For each finite float, exactly one decimal is the shortest. -/
theorem shortest_decimal_exists_uniqueF (f : Float) (h_fin : (unpackF f).isFinite) :
    ∃! d : Decimal, ShortestDecimalF f d := by
  obtain ⟨d, hd, huniq⟩ := shortest_decimal_exists_unique f.toBits h_fin
  exact ⟨d, (shortestDecimalF_iff f d).mpr hd,
         fun d' hd' => huniq d' ((shortestDecimalF_iff f d').mp hd')⟩

end Srtfp.Spec

/-- The bridge to `Float`: converting non-NaN bits to `Float` and back is the
identity, a theorem over core's `Float.Model` (`Srtfp/Bridge/Basic.lean`): -/
example : ∀ x : UInt64, Srtfp.Spec.unpack x ≠ .notANumber → (Float.ofBits x).toBits = x :=
  Float.toBits_ofBits

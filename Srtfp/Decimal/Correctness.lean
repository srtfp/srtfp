module
/- Decimal construction and negation, certified against the definitions in Spec.
   Normalizes specifies one canonical result, retaining either sign of zero. -/
public import Srtfp.Proofs.Decimal.Canonical

@[expose] public section

namespace Srtfp.Decimal

open Float.Model.UnpackedFloat (Sign)

/-- Normalization specifies exactly the result of the smart constructor. -/
theorem mk'_spec (sign : Sign) (sig : Nat) (exp : Int) (d : Decimal) :
    Normalizes sign sig exp d ↔ mk' sign sig exp = d := normalizes_iff sign sig exp d

/-- Every decimal has exactly the specified canonical form. -/
theorem canonical_spec (raw d : Decimal) :
    Normalizes raw.sign raw.significand raw.exponent d ↔ canonical raw = d :=
  normalizes_iff raw.sign raw.significand raw.exponent d

/-- The normalization rules uniquely determine the canonicalization function. -/
theorem correct_iff_canonical (p : Decimal → Decimal) :
    (∀ d, Normalizes d.sign d.significand d.exponent (p d)) ↔ p = canonical := by
  constructor
  · intro h
    funext d
    exact ((canonical_spec d (p d)).mp (h d)).symm
  · rintro rfl
    exact fun d => (canonical_spec d _).mpr rfl

/-- Natural-number construction normalizes the positive integer value. -/
theorem ofNat_spec (n : Nat) (d : Decimal) :
    Normalizes .positive n 0 d ↔ ofNat n = d := normalizes_iff .positive n 0 d

/-- Integer construction normalizes its sign and magnitude; zero is positive. -/
theorem ofInt_spec (i : Int) (d : Decimal) :
    Normalizes (if i < 0 then .negative else .positive) i.natAbs 0 d ↔ ofInt i = d :=
  normalizes_iff _ _ _ d

/-- Lean's scientific-literal interface normalizes mantissa × 10^(±exponent). -/
theorem ofScientific_spec (mantissa : Nat) (negativeExponent : Bool) (exponent : Nat)
    (d : Decimal) :
    Normalizes .positive mantissa (if negativeExponent then -(exponent : Int) else exponent) d ↔
      (OfScientific.ofScientific mantissa negativeExponent exponent : Decimal) = d :=
  normalizes_iff _ _ _ d

/-- The named constants have exactly these fields. -/
theorem zero_spec : zero = ⟨.positive, 0, 0⟩ := rfl
theorem one_spec : one = ⟨.positive, 1, 0⟩ := rfl

/-- Negation preserves the magnitude and reverses the sign, even at zero. -/
theorem neg_spec (d : Decimal) :
    (-d).sign = -d.sign ∧ (-d).significand = d.significand ∧
      (-d).exponent = d.exponent := ⟨rfl, rfl, rfl⟩

end Srtfp.Decimal

module
/- The text API certified against the independent grammar in Text.Spec. -/
public import Srtfp.Proofs.Text.Spec

@[expose] public section

namespace Srtfp.Text

/-- Parsing succeeds exactly for the specified strings and canonical values. -/
theorem parse_spec (opts : DecimalSyntax) (s : String) (d : Decimal) :
    parse opts s = some d ↔ Spec.Parses opts s d :=
  ⟨Proof.parse_sound, Proof.parse_complete⟩

/-- The grammar and values determine the parser uniquely, including rejection. -/
theorem correct_iff_parse (opts : DecimalSyntax) (p : String → Option Decimal) :
    (∀ s d, p s = some d ↔ Spec.Parses opts s d) ↔ p = parse opts := by
  constructor
  · intro h
    funext s
    exact Option.ext fun d => (h s d).trans (parse_spec opts s d).symm
  · rintro rfl
    exact parse_spec opts

/-- Formatting a canonical decimal produces a permitted spelling of that value. -/
theorem format_spec {fopts : FormatOptions} {popts : DecimalSyntax}
    (hcompat : fopts.CompatibleWith popts) (d : Decimal) (hcan : d.IsCanonical) :
    Spec.Parses popts (format fopts d) d :=
  (parse_spec popts _ d).mp (parse_format hcompat d hcan)

end Srtfp.Text

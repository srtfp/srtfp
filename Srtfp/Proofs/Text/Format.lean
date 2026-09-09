module
/- The formatter satisfies the independent presentation rules in Text.Spec. -/
public import Srtfp.Text
public import Srtfp.Text.Spec

@[expose] public section

namespace Srtfp.Text.Proof

private theorem positional_digits (ds : List Char) (hne : ds ≠ []) (exp : Int) :
    let point := exp + ds.length
    let D := List.replicate (-(point - 1)).toNat '0' ++ ds ++ List.replicate exp.toNat '0'
    let w := D.length - (-exp).toNat
    D.take w = (if point ≤ 0 then ['0'] else
      ds.take point.toNat ++ List.replicate (point.toNat - ds.length) '0') ∧
    D.drop w = List.replicate (-point).toNat '0' ++ ds.drop point.toNat := by
  have hlen : 0 < ds.length := List.length_pos_iff.mpr hne
  dsimp only
  by_cases he : 0 ≤ exp
  · have hleft : (-(exp + ds.length - 1)).toNat = 0 := by omega
    have hfrac : (-exp).toNat = 0 := by omega
    have hp : ¬ exp + ds.length ≤ 0 := by omega
    have hpneg : (-(exp + ds.length)).toNat = 0 := by omega
    have hplen : ds.length ≤ (exp + ds.length).toNat := by omega
    have hr : (exp + ds.length).toNat - ds.length = exp.toNat := by omega
    simp [hleft, hfrac, hp, hpneg, List.take_of_length_le hplen,
      List.drop_of_length_le hplen, hr]
    exact List.take_of_length_le (by simp)
  · have hright : exp.toNat = 0 := by omega
    by_cases hp : exp + ds.length ≤ 0
    · have hpoint : (exp + ds.length).toNat = 0 := by omega
      have hl : 1 ≤ (-(exp + ds.length - 1)).toNat := by omega
      have hw : (-(exp + ds.length - 1)).toNat + ds.length - (-exp).toNat = 1 := by omega
      have hz : (-(exp + ds.length - 1)).toNat - 1 = (-(exp + ds.length)).toNat := by omega
      simp only [hright, List.replicate_zero, List.append_nil, List.length_append,
        List.length_replicate, hw, if_pos hp, hpoint, List.drop_zero]
      rw [List.take_append_of_le_length (by simpa using hl), List.take_replicate,
        Nat.min_eq_left hl, List.replicate_one,
        List.drop_append_of_le_length (by simpa using hl), List.drop_replicate, hz]
      exact ⟨rfl, rfl⟩
    · have hleft : (-(exp + ds.length - 1)).toNat = 0 := by omega
      have hpneg : (-(exp + ds.length)).toNat = 0 := by omega
      have hw : ds.length - (-exp).toNat = (exp + ds.length).toNat := by omega
      have hr : (exp + ds.length).toNat - ds.length = 0 := by omega
      simp [hright, hleft, hpneg, hw, hp, hr]

theorem format_meets_layout (opts : FormatOptions) (d : Decimal) :
    Spec.Formats opts d (format opts d) := by
  have hlen : 1 ≤ (Nat.toDigits 10 d.significand).length := Nat.length_toDigits_pos
  unfold Spec.Formats format place
  dsimp only [natChars]
  split
  · simp [Lexeme.split, padTo, render, expChars, expDigits, natChars,
      Nat.sub_eq_zero_of_le hlen, List.append_assoc]
    rfl
  · obtain ⟨hi, hf⟩ := positional_digits (Nat.toDigits 10 d.significand)
      Nat.toDigits_ne_nil d.exponent
    have hpoint : d.exponent + (Nat.toDigits 10 d.significand).length - 1 + 1 =
        d.exponent + (Nat.toDigits 10 d.significand).length := by omega
    simp only [Lexeme.split, padTo, render, String.toList_ofList, hpoint, hi, hf,
      List.append_nil]
    rfl

end Srtfp.Text.Proof

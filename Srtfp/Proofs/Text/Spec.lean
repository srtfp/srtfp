module
/- The executable parser accepts exactly the grammar in Text.Spec. -/
public import Srtfp.Text.Spec
public import Srtfp.Proofs.Text
public import Srtfp.Proofs.Decimal
@[expose] public section
namespace Srtfp.Text.Proof
open Float.Model.UnpackedFloat (Sign)

private theorem normalizes_mk (sign : Sign) (sig : Nat) (exp : Int) :
    Spec.Normalizes sign sig exp (Decimal.mk' sign sig exp) := by
  refine ⟨Decimal.canonical_isCanonical _, ?_⟩
  by_cases h : sig = 0
  · subst sig
    exact ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
  · obtain ⟨hs, _, _, he, hv⟩ := mk_pos_props sign sig exp h
    refine ⟨hs, Or.inr ⟨((Decimal.mk' sign sig exp).exponent - exp).toNat, hv.symm, ?_⟩⟩
    omega

private theorem normalizes_iff (sign : Sign) (sig : Nat) (exp : Int) (d : Decimal) :
    Spec.Normalizes sign sig exp d ↔ Decimal.mk' sign sig exp = d := by
  constructor
  · rintro ⟨hc, hs, hzero | ⟨k, hsig, he⟩⟩
    · obtain ⟨rfl, hz⟩ := hzero
      have he : d.exponent = 0 := by
        rcases hc with h | h
        · exact h.2
        · exact False.elim (h.1 hz)
      cases d
      simp_all [Decimal.mk', Decimal.canonical]
    · rw [hsig, ← hs, show exp = d.exponent - k by omega, mk'_shift]
      exact Decimal.canonical_fixed_of_isCanonical d hc
  · rintro rfl
    exact normalizes_mk sign sig exp

private theorem lexSign_sound {allow : Bool} {cs body : List Char} {sign : Sign}
    (h : lexSign allow cs = some (sign, body)) :
    ∃ pre, Spec.SignChars allow pre sign ∧ cs = pre ++ body := by
  cases cs with
  | nil =>
    simp [lexSign] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], Or.inl rfl, rfl⟩
  | cons c cs =>
    by_cases hm : c = '-'
    · subst c
      simp [lexSign] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨['-'], rfl, rfl⟩
    · by_cases hp : c = '+'
      · subst c
        simp [lexSign] at h
        obtain ⟨ha, rfl, rfl⟩ := h
        exact ⟨['+'], Or.inr ⟨ha, rfl⟩, rfl⟩
      · simp [lexSign, hm, hp] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨[], Or.inl rfl, rfl⟩

private theorem lexSign_complete {allow : Bool} {pre body : List Char} {sign : Sign}
    (h : Spec.SignChars allow pre sign)
    (hm : body.head? ≠ some '-') (hp : body.head? ≠ some '+') :
    lexSign allow (pre ++ body) = some (sign, body) := by
  cases sign with
  | negative =>
    obtain rfl := h
    simp [lexSign]
  | positive =>
    rcases h with rfl | ⟨rfl, rfl⟩
    · simp [lexSign, hm, hp]
    · simp [lexSign]

private theorem digits_no_sign {ds : List Char} (h : Digits ds) :
    ds.head? ≠ some '-' ∧ ds.head? ≠ some '+' := by
  cases ds with
  | nil => simp
  | cons c cs =>
    have hc := h c (List.mem_cons_self ..)
    constructor <;> intro he <;> simp only [List.head?_cons, Option.some.injEq] at he <;>
      subst c <;> contradiction

private theorem lexExpTail_sound {cs : List Char} {exp : Option Int}
    (h : lexExpTail cs = some exp) : Spec.Exponent cs (exp.getD 0) := by
  cases cs with
  | nil =>
    simp [lexExpTail] at h
    subst exp
    exact Or.inl ⟨rfl, rfl⟩
  | cons marker cs =>
    simp only [lexExpTail] at h
    split at h
    next hm =>
      obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [lexExp, Option.bind_eq_some_iff] at he
      obtain ⟨⟨sign, ds⟩, hs, hv⟩ := he
      split at hv
      next hbad => contradiction
      next hgood =>
        simp at hgood
        have hv := Option.some.inj hv
        subst e
        obtain ⟨pre, hpre, rfl⟩ := lexSign_sound hs
        exact Or.inr ⟨marker, pre, sign, ds, hm, hpre, hgood.1, List.all_eq_true.mpr hgood.2, rfl, rfl⟩
    next hm => contradiction

private theorem lexExpTail_complete {cs : List Char} {e : Int}
    (h : Spec.Exponent cs e) : ∃ exp, lexExpTail cs = some exp ∧ exp.getD 0 = e := by
  rcases h with ⟨rfl, rfl⟩ | ⟨marker, pre, sign, ds, hm, hs, hne, hd, rfl, rfl⟩
  · exact ⟨none, rfl, rfl⟩
  · have hd' : Digits ds := List.all_eq_true.mp hd
    have hn := digits_no_sign hd'
    have hl := lexExp_of_sign (lexSign_complete hs hn.1 hn.2) hd' hne
    refine ⟨some _, ?_, rfl⟩
    simp only [lexExpTail, if_pos hm, hl, Option.map_some, charsVal]
    rfl

private theorem exponent_tail {cs : List Char} {e : Int} (h : Spec.Exponent cs e) : ExpTail cs := by
  rcases h with ⟨rfl, _⟩ | ⟨marker, pre, sign, ds, hm, _, _, _, rfl, _⟩
  · exact expTail_nil
  · simpa [ExpTail] using hm

private theorem lexMantissa_sound {opts : DecimalSyntax} {cs intD fracD rest : List Char}
    (h : lexMantissa opts cs = some (intD, fracD, rest)) :
    ∃ dot, Spec.Mantissa opts intD fracD dot ∧
      cs = intD ++ (if dot then '.' :: fracD else []) ++ rest := by
  dsimp only [lexMantissa] at h
  split at h
  next => contradiction
  next hI =>
    split at h
    next => contradiction
    next hlead =>
      split at h
      next hdot =>
        split at h
        next => contradiction
        next hF =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          refine ⟨true, ?_, ?_⟩
          · refine ⟨List.all_takeWhile, List.all_takeWhile, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
              simp_all <;> grind
          · obtain ⟨body, hbody⟩ := List.head?_eq_some_iff.mp hdot
            simpa [hbody, List.append_assoc] using
              (List.takeWhile_append_dropWhile (p := Char.isDigit) (l := cs)).symm
      next hdot =>
        split at h
        next => contradiction
        next hF =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          refine ⟨false, ?_, ?_⟩
          · refine ⟨List.all_takeWhile, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
              simp_all <;> grind
          · simp

private theorem lexMantissa_complete {opts : DecimalSyntax} {intD fracD rest : List Char}
    {dot : Bool} (h : Spec.Mantissa opts intD fracD dot) (hrest : ExpTail rest) :
    lexMantissa opts (intD ++ (if dot then '.' :: fracD else []) ++ rest)
      = some (intD, fracD, rest) := by
  obtain ⟨hI, hF, hne, hleadDot, htrailDot, hnoDot, hreqDot, hlead⟩ := h
  have hI' : Digits intD := List.all_eq_true.mp hI
  have hF' : Digits fracD := List.all_eq_true.mp hF
  have hlead' : ¬ (¬opts.allowLeadingZeros = true ∧ 2 ≤ intD.length ∧ intD.head? = some '0') := by
    grind
  cases dot with
  | false =>
    have hF0 := hnoDot rfl
    subst fracD
    simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil]
    simp only [lexMantissa, takeWhile_digits hI' hrest.stops, dropWhile_digits hI' hrest.stops]
    rw [if_neg (by grind), if_neg hlead', if_neg hrest.noDot, if_neg (by grind)]
  | true =>
    simp only [↓reduceIte, List.append_assoc, List.cons_append]
    simp only [lexMantissa, takeWhile_digits hI' (stops_dot _), dropWhile_digits hI' (stops_dot _),
      List.head?_cons, List.tail_cons, takeWhile_digits hF' hrest.stops, dropWhile_digits hF' hrest.stops]
    rw [if_neg (by grind), if_neg hlead', if_pos trivial, if_neg (by grind)]

private theorem mantissa_no_sign {opts : DecimalSyntax} {intD fracD rest : List Char}
    {dot : Bool} (h : Spec.Mantissa opts intD fracD dot) :
    (intD ++ (if dot then '.' :: fracD else []) ++ rest).head? ≠ some '-' ∧
    (intD ++ (if dot then '.' :: fracD else []) ++ rest).head? ≠ some '+' := by
  cases intD with
  | nil =>
    have hd : dot = true := by
      obtain ⟨_, _, hne, _, _, hnoDot, _⟩ := h
      cases dot <;> simp_all
    simp [hd]
  | cons c cs =>
    have hc := (List.all_eq_true.mp h.1) c (List.mem_cons_self ..)
    constructor <;> intro he <;> simp only [List.cons_append, List.head?_cons, Option.some.injEq] at he <;>
      subst c <;> contradiction

/-- Every successful parse has a grammar derivation and the specified canonical value. -/
theorem parse_sound {opts : DecimalSyntax} {s : String} {d : Decimal}
    (h : parse opts s = some d) : Spec.Parses opts s d := by
  obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.mp h
  simp only [lex, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at hl
  obtain ⟨⟨sign, body⟩, hs, ⟨⟨intD, fracD, rest⟩, hm, ⟨exp, he, hl⟩⟩⟩ := hl
  dsimp only at hm he
  simp only [Option.some.injEq] at hl
  subst l
  obtain ⟨pre, hpre, hbody⟩ := lexSign_sound hs
  obtain ⟨dot, hmant, hparts⟩ := lexMantissa_sound hm
  refine ⟨pre, sign, intD, fracD, dot, rest, exp.getD 0, hpre, hmant,
    lexExpTail_sound he, ?_, normalizes_mk _ _ _⟩
  rw [hbody, hparts]
  simp only [List.append_assoc]

/-- Every grammar derivation is accepted with the specified canonical value. -/
theorem parse_complete {opts : DecimalSyntax} {s : String} {d : Decimal}
    (h : Spec.Parses opts s d) : parse opts s = some d := by
  obtain ⟨pre, sign, intD, fracD, dot, rest, e, hsign, hmant, hexp, htext, hvalue⟩ := h
  obtain ⟨exp, he, heval⟩ := lexExpTail_complete hexp
  have hn := mantissa_no_sign (rest := rest) hmant
  have hs := lexSign_complete hsign hn.1 hn.2
  have hm := lexMantissa_complete hmant (exponent_tail hexp)
  have htext' : s.toList = pre ++ (intD ++ (if dot then '.' :: fracD else []) ++ rest) := by
    simpa only [List.append_assoc] using htext
  rw [parse, htext']
  simp only [lex, Option.bind_eq_bind, hs, Option.bind_some, hm, he, Option.pure_def, Option.map_some,
    Option.some.injEq, Lexeme.value, heval, charsVal]
  exact (normalizes_iff sign _ _ d).mp hvalue

end Srtfp.Text.Proof

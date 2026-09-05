module
/- Round-trip: `parse` inverts `format`, for every compatible pair of
   dialect options.

   The theorem is asymmetric by design: `parse (format d) = some d`
   holds for every canonical `d`; the reverse direction cannot hold on
   the nose (`"2."`, `"007.5"`, `"+1.5"` all parse but are never
   printed) — `parse` canonicalises through `Decimal.mk'`, which is also
   what makes value-preserving zero-padding round-trip for free.

   Following `format = render ∘ place` and `parse = value ∘ lex`
   (`Srtfp/Text.lean`), the proof is two independent halves glued by the
   well-formedness predicate `Lexeme.WF`:

     lex popts (render fopts l) = some l   for every `l` well-formed for `popts`
     (place fopts … d).value = d           for every canonical `d`

   and `place` produces well-formed lexemes whenever the printer is
   compatible with the dialect. -/

public import Srtfp.Text
public import Srtfp.Proofs.Decimal.Canonical

@[expose] public section

namespace Srtfp.Text

open Float.Model.UnpackedFloat (Sign)

/-! ## Digits -/

theorem isDigit_digitChar : ∀ d, d < 10 → (digitChar d).isDigit = true := by decide
theorem digitVal_digitChar : ∀ d, d < 10 → digitVal (digitChar d) = d := by decide
theorem digitChar_eq_zero : ∀ d, d < 10 → digitChar d = '0' → d = 0 := by decide

/-- A digit string. -/
def Digits (cs : List Char) : Prop := ∀ c ∈ cs, c.isDigit = true

theorem Digits.append {xs ys : List Char} (hx : Digits xs) (hy : Digits ys) :
    Digits (xs ++ ys) := by
  intro c hc
  rcases List.mem_append.mp hc with h | h
  · exact hx c h
  · exact hy c h

theorem Digits.take {cs : List Char} (h : Digits cs) (n : Nat) : Digits (cs.take n) :=
  fun c hc => h c (List.take_subset _ _ hc)

theorem Digits.drop {cs : List Char} (h : Digits cs) (n : Nat) : Digits (cs.drop n) :=
  fun c hc => h c (List.drop_subset _ _ hc)

theorem digits_replicate (k : Nat) : Digits (List.replicate k '0') :=
  fun c hc => by rw [List.eq_of_mem_replicate hc]; decide

theorem digits_padTo {cs : List Char} (h : Digits cs) (n : Nat) : Digits (padTo n cs) :=
  h.append (digits_replicate _)

theorem digits_natChars (n : Nat) : Digits (natChars n) := by
  induction n using natChars.induct with
  | case1 n h =>
    intro c hc
    rw [natChars, if_pos h, List.mem_singleton] at hc
    exact hc ▸ isDigit_digitChar n h
  | case2 n h ih =>
    rw [natChars, if_neg h]
    exact ih.append fun c hc => by
      rw [List.mem_singleton] at hc
      exact hc ▸ isDigit_digitChar _ (Nat.mod_lt _ (by decide))

theorem natChars_ne_nil (n : Nat) : natChars n ≠ [] := by
  rw [natChars]; split <;> simp

theorem natChars_zero : natChars 0 = ['0'] := by
  rw [natChars, if_pos (by decide)]; rfl

/-- Only zero prints with a leading `'0'`. -/
theorem natChars_head_zero (n : Nat) (rest : List Char) :
    (natChars n ++ rest).head? = some '0' → n = 0 := by
  induction n using natChars.induct generalizing rest with
  | case1 n h => simpa [natChars, h] using digitChar_eq_zero n h
  | case2 n h ih =>
    rw [natChars, if_neg h, List.append_assoc]
    intro hz
    have := ih _ hz
    omega

/-! ## `charsVal` -/

private theorem foldl_shift (cs : List Char) (a : Nat) :
    cs.foldl (fun a c => 10 * a + digitVal c) a
      = a * 10 ^ cs.length + cs.foldl (fun a c => 10 * a + digitVal c) 0 := by
  induction cs generalizing a with
  | nil => simp
  | cons c cs ih =>
    simp only [List.foldl, List.length_cons]
    rw [ih (10 * a + digitVal c), ih (10 * 0 + digitVal c)]
    grind

theorem charsVal_append (xs ys : List Char) :
    charsVal (xs ++ ys) = charsVal xs * 10 ^ ys.length + charsVal ys := by
  simp only [charsVal, List.foldl_append]
  rw [foldl_shift]

theorem charsVal_cons (c : Char) (cs : List Char) :
    charsVal (c :: cs) = digitVal c * 10 ^ cs.length + charsVal cs := by
  simpa [charsVal] using charsVal_append [c] cs

theorem charsVal_replicate (k : Nat) : charsVal (List.replicate k '0') = 0 := by
  have h0 : digitVal '0' = 0 := by decide
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, charsVal_cons, ih, h0]

theorem charsVal_natChars (n : Nat) : charsVal (natChars n) = n := by
  induction n using natChars.induct with
  | case1 n h => simp [natChars, h, charsVal, digitVal_digitChar n h]
  | case2 n h ih =>
    rw [natChars, if_neg h, charsVal_append, ih]
    simp [charsVal, digitVal_digitChar (n % 10) (Nat.mod_lt _ (by decide))]
    omega

/-! ## Canonicalisation absorbs trailing zeros -/

theorem mk'_mul_ten (s : Sign) (v : Nat) (e : Int) :
    Decimal.mk' s (v * 10) e = Decimal.mk' s v (e + 1) := by
  by_cases hv : v = 0
  · subst hv; rfl
  · have h10 : v * 10 ≠ 0 := Nat.mul_ne_zero hv (by decide)
    simp only [Decimal.mk', Decimal.canonical, if_neg hv, if_neg h10,
      Decimal.canonicaliseAux_div _ _ h10 (Nat.mul_mod_left v 10),
      Nat.mul_div_cancel v (by decide : 0 < 10)]

/-- Trailing zeros in the significand shift into the exponent: parsing
    a zero-padded rendering recovers the unpadded decimal. -/
theorem mk'_shift (s : Sign) (v : Nat) (e : Int) (k : Nat) :
    Decimal.mk' s (v * 10 ^ k) (e - k) = Decimal.mk' s v e := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.pow_succ, ← Nat.mul_assoc, mk'_mul_ten, show e - ↑(k + 1) + 1 = e - ↑k by omega, ih]

/-! ## Scanning digit runs -/

/-- `rest` does not begin with a digit. -/
def Stops (rest : List Char) : Prop := ∀ c, rest.head? = some c → c.isDigit = false

theorem stops_dot (cs : List Char) : Stops ('.' :: cs) :=
  fun c hc => by simp at hc; exact hc ▸ rfl

theorem takeWhile_digits {ds rest : List Char} (hds : Digits ds) (hrest : Stops rest) :
    (ds ++ rest).takeWhile Char.isDigit = ds := by
  rw [List.takeWhile_append_of_pos hds]
  cases rest with
  | nil => simp
  | cons c r => rw [List.takeWhile_cons_of_neg (by simpa using hrest c rfl), List.append_nil]

theorem dropWhile_digits {ds rest : List Char} (hds : Digits ds) (hrest : Stops rest) :
    (ds ++ rest).dropWhile Char.isDigit = rest := by
  rw [List.dropWhile_append_of_pos hds]
  cases rest with
  | nil => rfl
  | cons c r => exact List.dropWhile_cons_of_neg (by simpa using hrest c rfl)

/-! ## `lex` inverts `render` -/

/-- What `lex popts` accepts of the shapes `render` prints: digit runs,
    a nonempty integer part without a redundant leading zero, and a
    fraction whenever the dialect insists on the point. -/
structure Lexeme.WF (popts : DecimalSyntax) (l : Lexeme) : Prop where
  intD : Digits l.intD
  fracD : Digits l.fracD
  ne : l.intD ≠ []
  lead : 2 ≤ l.intD.length → l.intD.head? = some '0' → popts.allowLeadingZeros = true
  dot : popts.requireDot = true → l.fracD ≠ []

theorem lexSign_neg (allowPlus : Bool) (cs : List Char) :
    lexSign allowPlus ('-' :: cs) = some (.negative, cs) := by
  simp [lexSign]

theorem lexSign_plus (cs : List Char) : lexSign true ('+' :: cs) = some (.positive, cs) := by
  simp [lexSign]

theorem lexSign_digits (allowPlus : Bool) {ds : List Char} (hds : Digits ds) (hne : ds ≠ [])
    (rest : List Char) : lexSign allowPlus (ds ++ rest) = some (.positive, ds ++ rest) := by
  obtain ⟨c, ds, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hc := hds c (List.mem_cons_self ..)
  have h1 : c ≠ '-' := fun h => absurd (h ▸ hc) (by decide)
  have h2 : c ≠ '+' := fun h => absurd (h ▸ hc) (by decide)
  simp [lexSign, h1, h2]

theorem lexExp_of_sign {cs ds : List Char} {s : Sign} (h : lexSign true cs = some (s, ds))
    (hds : Digits ds) (hne : ds ≠ []) :
    lexExp cs = some (match (generalizing := false) s with
      | .negative => -(charsVal ds : Int) | .positive => charsVal ds) := by
  simp only [lexExp, h, Option.bind_some]
  rw [if_neg (fun h' => h'.elim hne fun h' => h' (List.all_eq_true.mpr hds))]
  cases s <;> rfl

/-- `T` is empty or begins with the exponent marker. -/
def ExpTail (T : List Char) : Prop := ∀ c, T.head? = some c → c = 'e' ∨ c = 'E'

theorem ExpTail.stops {T : List Char} (h : ExpTail T) : Stops T :=
  fun c hc => by rcases h c hc with rfl | rfl <;> decide

theorem ExpTail.noDot {T : List Char} (h : ExpTail T) : T.head? ≠ some '.' :=
  fun hc => by rcases h '.' hc with h | h <;> cases h

theorem expTail_nil : ExpTail [] := fun _ hc => by cases hc

theorem expTail_expChars (opts : FormatOptions) (e : Int) : ExpTail (expChars opts e) := by
  intro c hc
  rw [expChars, List.cons_append, List.head?_cons, Option.some.injEq] at hc
  subst hc
  cases opts.upperExp <;> simp

theorem digits_expDigits (n : Nat) (e : Int) : Digits (expDigits n e) :=
  (digits_replicate _).append (digits_natChars _)

theorem expDigits_ne_nil (n : Nat) (e : Int) : expDigits n e ≠ [] := by
  simp [expDigits, natChars_ne_nil]

theorem charsVal_expDigits (n : Nat) (e : Int) : charsVal (expDigits n e) = e.natAbs := by
  rw [expDigits, charsVal_append, charsVal_replicate, charsVal_natChars]; simp

theorem lexExpTail_expChars (opts : FormatOptions) (e : Int) :
    lexExpTail (expChars opts e) = some (some e) := by
  have hm : lexExpTail (expChars opts e)
      = (lexExp ((if e < 0 then ['-'] else if opts.expPlus then ['+'] else [])
          ++ expDigits opts.expMinDigits e)).map some := by
    cases hu : opts.upperExp <;> simp [expChars, lexExpTail, hu]
  have hds := digits_expDigits opts.expMinDigits e
  have hne := expDigits_ne_nil opts.expMinDigits e
  rw [hm]
  by_cases hneg : e < 0
  · rw [if_pos hneg, List.singleton_append, lexExp_of_sign (lexSign_neg _ _) hds hne,
      charsVal_expDigits]
    simp; omega
  · rw [if_neg hneg]
    by_cases hp : opts.expPlus
    · rw [if_pos hp, List.singleton_append, lexExp_of_sign (lexSign_plus _) hds hne,
        charsVal_expDigits]
      simp; omega
    · rw [if_neg hp, List.nil_append,
        lexExp_of_sign (by simpa using lexSign_digits true hds hne []) hds hne, charsVal_expDigits]
      simp; omega

theorem lexMantissa_render {popts : DecimalSyntax} {l : Lexeme} (hwf : l.WF popts)
    {T : List Char} (hT : ExpTail T) :
    lexMantissa popts (l.intD ++ ((if l.fracD = [] then [] else '.' :: l.fracD) ++ T))
      = some (l.intD, l.fracD, T) := by
  obtain ⟨hI, hF, hne, hlead, hdot⟩ := hwf
  have hlead' : ¬ (¬ popts.allowLeadingZeros = true ∧ 2 ≤ l.intD.length ∧ l.intD.head? = some '0') :=
    fun ⟨h1, h2, h3⟩ => h1 (hlead h2 h3)
  by_cases hF0 : l.fracD = []
  · rw [if_pos hF0, List.nil_append]
    simp only [lexMantissa, takeWhile_digits hI hT.stops, dropWhile_digits hI hT.stops]
    rw [if_neg (fun h => hne h.1), if_neg hlead', if_neg hT.noDot,
      if_neg (fun h => h.elim (fun h => hdot h hF0) hne), hF0]
  · rw [if_neg hF0, List.cons_append]
    simp only [lexMantissa, takeWhile_digits hI (stops_dot _), dropWhile_digits hI (stops_dot _),
      List.head?_cons, List.tail_cons, takeWhile_digits hF hT.stops, dropWhile_digits hF hT.stops]
    rw [if_neg (fun h => hne h.1), if_neg hlead', if_pos trivial, if_neg (fun h => hF0 h.1)]

theorem lex_render {popts : DecimalSyntax} {l : Lexeme} (hwf : l.WF popts) (fopts : FormatOptions) :
    lex popts (render fopts l) = some l := by
  have hsign := lexSign_digits popts.allowExplicitMantissaPlus hwf.intD hwf.ne
  obtain ⟨sign, intD, fracD, exp⟩ := l
  cases exp with
  | none =>
    have hM := lexMantissa_render hwf expTail_nil
    simp only [List.append_nil] at hM
    cases sign <;> simp [lex, render, hsign, lexSign_neg, hM, lexExpTail]
  | some e =>
    have hM := lexMantissa_render hwf (expTail_expChars fopts e)
    cases sign <;> simp [lex, render, hsign, lexSign_neg, hM, lexExpTail_expChars]

/-! ## `place` produces well-formed lexemes -/

/-- Compatibility of a printer with a dialect: if the dialect requires
    the decimal point, the printer always emits one. The only
    interaction — everything else a printer can emit (`'+'`-signed or
    zero-padded exponents, padded fractions) is accepted by every
    dialect. -/
def FormatOptions.CompatibleWith (fopts : FormatOptions) (popts : DecimalSyntax) : Prop :=
  popts.requireDot = true → 1 ≤ fopts.minFracDigits ∧ 1 ≤ fopts.sciMinFracDigits

theorem split_wf {popts : DecimalSyntax} (sign : Sign) {D : List Char} {w n : Nat} (e : Option Int)
    (hD : Digits D) (hDne : D ≠ []) (hw : 1 ≤ w)
    (hlead : 2 ≤ w → D.head? = some '0' → popts.allowLeadingZeros = true)
    (hn : popts.requireDot = true → 1 ≤ n) :
    (Lexeme.split sign D w n e).WF popts where
  intD := hD.take w
  fracD := digits_padTo (hD.drop w) n
  ne := by simp [Lexeme.split, List.take_eq_nil_iff, hDne]; omega
  lead := fun h2 h0 => by
    simp only [Lexeme.split, List.length_take] at h2
    rw [Lexeme.split, List.head?_take, if_neg (by omega)] at h0
    exact hlead (by omega) h0
  dot := fun h => by
    simp only [Lexeme.split, padTo, ne_eq, List.append_eq_nil_iff, List.drop_eq_nil_iff,
      List.replicate_eq_nil_iff, List.length_drop]
    have := hn h
    omega

theorem place_wf {fopts : FormatOptions} {popts : DecimalSyntax}
    (hcompat : fopts.CompatibleWith popts) (sign : Sign) {sig : Nat} {exp : Int}
    (hcan : Decimal.IsCanonical ⟨sign, sig, exp⟩) :
    (place fopts sign (natChars sig) exp).WF popts := by
  have hlen : 1 ≤ (natChars sig).length := List.length_pos_iff.mpr (natChars_ne_nil sig)
  have hzero : sig = 0 → exp = 0 := fun h0 => by
    rcases hcan with ⟨-, h⟩ | ⟨hne, -⟩
    · exact h
    · exact absurd h0 hne
  simp only [place]
  split
  · exact split_wf sign _ (digits_natChars sig) (natChars_ne_nil sig) (Nat.le_refl 1)
      (fun h => by omega) (fun h => (hcompat h).2)
  · refine split_wf sign _ (((digits_replicate _).append (digits_natChars _)).append (digits_replicate _))
      (by simp [natChars_ne_nil]) ?_ ?_ (fun h => (hcompat h).1)
    · simp only [List.length_append, List.length_replicate]; omega
    · intro h2 h0
      simp only [List.length_append, List.length_replicate] at h2
      by_cases hl : (-(exp + ↑(natChars sig).length - 1)).toNat = 0
      · rw [hl, List.replicate_zero, List.nil_append] at h0
        have h0' := natChars_head_zero sig _ h0
        have := hzero h0'
        have hn1 : (natChars 0).length = 1 := by rw [natChars_zero]; rfl
        subst h0'
        omega
      · exfalso; omega

/-! ## `value` inverts `place` -/

theorem value_split (sign : Sign) (D : List Char) (w n : Nat) (e : Option Int) :
    (Lexeme.split sign D w n e).value
      = Decimal.mk' sign (charsVal D) (e.getD 0 - (D.length - w : Nat)) := by
  simp only [Lexeme.value, Lexeme.split, padTo, ← List.append_assoc, List.take_append_drop,
    charsVal_append, charsVal_replicate, List.length_append, List.length_replicate,
    List.length_drop, Nat.add_zero]
  rw [show (e.getD 0 - ↑(D.length - w + (n - (D.length - w))))
      = (e.getD 0 - ↑(D.length - w)) - ↑(n - (D.length - w)) by omega]
  exact mk'_shift ..

theorem value_place (fopts : FormatOptions) {sign : Sign} {sig : Nat} {exp : Int}
    (hcan : Decimal.IsCanonical ⟨sign, sig, exp⟩) :
    (place fopts sign (natChars sig) exp).value = ⟨sign, sig, exp⟩ := by
  have hlen : 1 ≤ (natChars sig).length := List.length_pos_iff.mpr (natChars_ne_nil sig)
  have hself := Decimal.mk'_eq_self_of_isCanonical hcan
  simp only [place]
  split
  · rw [value_split, charsVal_natChars, ← hself]
    congr 1
    simp; omega
  · rw [value_split]
    simp only [charsVal_append, charsVal_replicate, charsVal_natChars, List.length_replicate,
      Nat.zero_mul, Nat.zero_add, Nat.add_zero]
    rw [← hself, ← mk'_shift sign sig exp exp.toNat]
    congr 1
    simp only [List.length_append, List.length_replicate, Option.getD_none]
    omega

/-! ## The round trip -/

/-- **Round trip.** Rendering a canonical `Decimal` with any
    `FormatOptions` and parsing it back under any compatible
    `DecimalSyntax` recovers it exactly. -/
theorem parse_format {fopts : FormatOptions} {popts : DecimalSyntax}
    (hcompat : fopts.CompatibleWith popts)
    (d : Decimal) (hcan : d.IsCanonical) :
    parse popts (format fopts d) = some d := by
  obtain ⟨sign, sig, exp⟩ := d
  rw [parse, format, String.toList_ofList, lex_render (place_wf hcompat sign hcan),
    Option.map_some, value_place fopts hcan]

/-- Whatever `parse` returns is canonical. -/
theorem parse_isCanonical {opts : DecimalSyntax} {s : String} {d : Decimal}
    (h : parse opts s = some d) : d.IsCanonical := by
  obtain ⟨l, -, rfl⟩ := Option.map_eq_some_iff.mp h
  exact Decimal.canonical_isCanonical _

/-! ## Preset instantiations

The compatibility side condition discharges by `decide` for any pair of
option literals (after unfolding `CompatibleWith` — instance synthesis
does not see through the definition). Consumers with their own
`FormatOptions` instantiate `parse_format` the same one-line way. -/

theorem parse_json_format_python (d : Decimal) (hcan : d.IsCanonical) :
    parse .jsonStrict (format .python d) = some d :=
  parse_format (by unfold FormatOptions.CompatibleWith; decide) d hcan

theorem parse_json_format_js (d : Decimal) (hcan : d.IsCanonical) :
    parse .jsonStrict (format .js d) = some d :=
  parse_format (by unfold FormatOptions.CompatibleWith; decide) d hcan

end Srtfp.Text

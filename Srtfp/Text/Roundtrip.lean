module
/- Round-trip: `parse` inverts `format`, for every compatible pair of
   dialect options.

   The theorem is asymmetric by design: `parse (format d) = some d`
   holds for every canonical `d`; the reverse direction cannot hold on
   the nose (`"2."`, `"007.5"`, `"+1.5"` all parse but are never
   printed) — `parse` canonicalises through `Decimal.mk'`, which is also
   what makes value-preserving zero-padding round-trip for free. -/

public import Srtfp.Text
public import Srtfp.Decimal.Instances

@[expose] public section

namespace Srtfp.Text

/-! ## Digit characters -/

theorem isDigitChar_digitChar {d : Nat} (h : d < 10) :
    isDigitChar (digitChar d) = true := by
  have : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 ∨ d = 8 ∨ d = 9 := by
    omega
  rcases this with h|h|h|h|h|h|h|h|h|h <;> subst h <;> decide

theorem digitVal_digitChar {d : Nat} (h : d < 10) :
    digitVal (digitChar d) = d := by
  have : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 ∨ d = 8 ∨ d = 9 := by
    omega
  rcases this with h|h|h|h|h|h|h|h|h|h <;> subst h <;> decide

theorem isDigitChar_zero : isDigitChar '0' = true := by decide

theorem not_isDigitChar_dot : isDigitChar '.' = false := by decide
theorem not_isDigitChar_e : isDigitChar 'e' = false := by decide
theorem not_isDigitChar_E : isDigitChar 'E' = false := by decide

/-! ## `natChars` -/

theorem natCharsAux_eq_append (n : Nat) (acc : List Char) :
    natCharsAux n acc = natChars n ++ acc := by
  induction n using Nat.strongRecOn generalizing acc with
  | _ n ih =>
    by_cases h : n < 10
    · rw [natCharsAux, dif_pos h]
      conv => rhs; rw [natChars, natCharsAux, dif_pos h]
      rfl
    · have hlt : n / 10 < n := Nat.div_lt_self (by omega) (by decide)
      rw [natCharsAux, dif_neg h, ih _ hlt]
      conv => rhs; rw [natChars, natCharsAux, dif_neg h, ih _ hlt]
      simp

/-- For `n ≥ 10`, the digits split as `natChars (n / 10) ++ [last]`. -/
theorem natChars_step {n : Nat} (h : ¬ n < 10) :
    natChars n = natChars (n / 10) ++ [digitChar (n % 10)] := by
  rw [natChars, natCharsAux, dif_neg h, natCharsAux_eq_append]

theorem natChars_small {n : Nat} (h : n < 10) : natChars n = [digitChar n] := by
  rw [natChars, natCharsAux, dif_pos h]

theorem natChars_all_digits (n : Nat) :
    ∀ c ∈ natChars n, isDigitChar c = true := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases h : n < 10
    · rw [natChars_small h]
      intro c hc
      rw [List.mem_singleton] at hc
      subst hc
      exact isDigitChar_digitChar h
    · rw [natChars_step h]
      intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · exact ih _ (Nat.div_lt_self (by omega) (by decide)) c hc
      · rw [List.mem_singleton] at hc
        subst hc
        exact isDigitChar_digitChar (Nat.mod_lt _ (by decide))

/-- `natChars n` is a nonempty digit string whose head is `'0'` only for
    `n = 0`. -/
theorem natChars_shape (n : Nat) :
    ∃ c cs, natChars n = c :: cs ∧ (c = '0' → n = 0) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases h : n < 10
    · refine ⟨digitChar n, [], natChars_small h, fun hc => ?_⟩
      have := digitVal_digitChar h
      rw [hc] at this
      simpa [digitVal] using this.symm
    · obtain ⟨c, cs, hsplit, hzero⟩ := ih (n / 10) (Nat.div_lt_self (by omega) (by decide))
      refine ⟨c, cs ++ [digitChar (n % 10)], ?_, fun hc => ?_⟩
      · rw [natChars_step h, hsplit]; rfl
      · have := hzero hc
        omega

theorem natChars_ne_nil (n : Nat) : natChars n ≠ [] := by
  obtain ⟨c, cs, hsplit, _⟩ := natChars_shape n
  rw [hsplit]; simp

theorem natChars_zero : natChars 0 = ['0'] := natChars_small (by decide)

/-! ## `charsVal` -/

private def valStep (a : Nat) (c : Char) : Nat := 10 * a + digitVal c

private theorem charsVal_eq_foldl (cs : List Char) : charsVal cs = cs.foldl valStep 0 := rfl

private theorem foldl_valStep_shift (cs : List Char) :
    ∀ a : Nat, cs.foldl valStep a = a * 10 ^ cs.length + cs.foldl valStep 0 := by
  induction cs with
  | nil => intro a; simp [List.foldl]
  | cons c cs ih =>
    intro a
    rw [List.foldl, List.foldl, ih (valStep a c), ih (valStep 0 c)]
    show (10 * a + digitVal c) * 10 ^ cs.length + _
        = a * 10 ^ (cs.length + 1) + ((10 * 0 + digitVal c) * 10 ^ cs.length + _)
    have : 10 ^ (cs.length + 1) = 10 ^ cs.length * 10 := Nat.pow_succ ..
    rw [this]
    generalize 10 ^ cs.length = P
    generalize cs.foldl valStep 0 = F
    have h1 : (10 * a + digitVal c) * P = a * (P * 10) + digitVal c * P := by
      rw [Nat.add_mul]
      have : 10 * a * P = a * (P * 10) := by
        rw [Nat.mul_comm 10 a, Nat.mul_assoc, Nat.mul_comm 10 P]
      rw [this]
    have h2 : (10 * 0 + digitVal c) * P = digitVal c * P := by
      rw [Nat.mul_zero, Nat.zero_add]
    omega

theorem charsVal_append (xs ys : List Char) :
    charsVal (xs ++ ys) = charsVal xs * 10 ^ ys.length + charsVal ys := by
  rw [charsVal_eq_foldl, List.foldl_append, foldl_valStep_shift,
      ← charsVal_eq_foldl, ← charsVal_eq_foldl]

theorem charsVal_replicate_zero (k : Nat) :
    charsVal (List.replicate k '0') = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, charsVal_eq_foldl, List.foldl]
    show (List.replicate k '0').foldl valStep (valStep 0 '0') = 0
    rw [foldl_valStep_shift, ← charsVal_eq_foldl, ih]
    show (10 * 0 + digitVal '0') * 10 ^ _ + 0 = 0
    simp [digitVal]

theorem charsVal_append_zeros (xs : List Char) (k : Nat) :
    charsVal (xs ++ List.replicate k '0') = charsVal xs * 10 ^ k := by
  rw [charsVal_append, charsVal_replicate_zero, List.length_replicate]
  omega

theorem charsVal_zeros_append (k : Nat) (xs : List Char) :
    charsVal (List.replicate k '0' ++ xs) = charsVal xs := by
  rw [charsVal_append, charsVal_replicate_zero]
  omega

theorem charsVal_natChars (n : Nat) : charsVal (natChars n) = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases h : n < 10
    · rw [natChars_small h]
      show (10 * 0 + digitVal (digitChar n)) = n
      rw [digitVal_digitChar h]
      omega
    · rw [natChars_step h, charsVal_append,
          ih _ (Nat.div_lt_self (by omega) (by decide))]
      show n / 10 * 10 ^ 1 + (10 * 0 + digitVal (digitChar (n % 10))) = n
      rw [digitVal_digitChar (Nat.mod_lt _ (by decide))]
      omega

/-! ## Scanning -/

theorem takeWhile_append_all {p : Char → Bool} :
    ∀ (xs : List Char), (∀ c ∈ xs, p c = true) → ∀ (ys : List Char),
      (xs ++ ys).takeWhile p = xs ++ ys.takeWhile p
  | [], _, ys => by simp
  | x :: xs, h, ys => by
    have hx : p x = true := h x (by simp)
    have ih := takeWhile_append_all xs (fun c hc => h c (by simp [hc])) ys
    simp only [List.cons_append, List.takeWhile_cons, hx, if_true, ih]

theorem dropWhile_append_all {p : Char → Bool} :
    ∀ (xs : List Char), (∀ c ∈ xs, p c = true) → ∀ (ys : List Char),
      (xs ++ ys).dropWhile p = ys.dropWhile p
  | [], _, ys => by simp
  | x :: xs, h, ys => by
    have hx : p x = true := h x (by simp)
    have ih := dropWhile_append_all xs (fun c hc => h c (by simp [hc])) ys
    simp only [List.cons_append, List.dropWhile_cons, hx, if_true, ih]

/-- A list whose head (if any) stops a digit scan and is not `'.'`. -/
def ExpTailish (cs : List Char) : Prop :=
  ∀ c, cs.head? = some c → isDigitChar c = false ∧ c ≠ '.'

theorem expTailish_nil : ExpTailish [] := by
  intro c hc; cases hc

theorem expTailish_expChars (opts : FormatOptions) (e : Int) :
    ExpTailish (expChars opts e) := by
  intro c hc
  rw [expChars] at hc
  by_cases h : opts.upperExp <;> simp [h] at hc <;> subst hc <;> exact ⟨by decide, by decide⟩

theorem takeWhile_expTailish {cs : List Char} (h : ExpTailish cs) :
    cs.takeWhile isDigitChar = [] := by
  match cs with
  | [] => rfl
  | c :: rest =>
    rw [List.takeWhile_cons, (h c rfl).1]
    simp

theorem dropWhile_expTailish {cs : List Char} (h : ExpTailish cs) :
    cs.dropWhile isDigitChar = cs := by
  match cs with
  | [] => rfl
  | c :: rest =>
    rw [List.dropWhile_cons, (h c rfl).1]
    simp

theorem takeWhile_digits {ds : List Char} (hds : ∀ c ∈ ds, isDigitChar c = true)
    {rest : List Char} (hrest : ∀ c, rest.head? = some c → isDigitChar c = false) :
    (ds ++ rest).takeWhile isDigitChar = ds := by
  have htw : rest.takeWhile isDigitChar = [] := by
    match rest with
    | [] => rfl
    | c :: r => rw [List.takeWhile_cons, hrest c rfl]; simp
  rw [takeWhile_append_all _ hds, htw, List.append_nil]

theorem dropWhile_digits {ds : List Char} (hds : ∀ c ∈ ds, isDigitChar c = true)
    {rest : List Char} (hrest : ∀ c, rest.head? = some c → isDigitChar c = false) :
    (ds ++ rest).dropWhile isDigitChar = rest := by
  have hdw : rest.dropWhile isDigitChar = rest := by
    match rest with
    | [] => rfl
    | c :: r => rw [List.dropWhile_cons, hrest c rfl]; simp
  rw [dropWhile_append_all _ hds, hdw]

theorem takeWhile_digits_all {ds : List Char} (hds : ∀ c ∈ ds, isDigitChar c = true) :
    ds.takeWhile isDigitChar = ds := by
  have := takeWhile_digits hds (rest := []) (fun c hc => by cases hc)
  simpa using this

theorem dropWhile_digits_all {ds : List Char} (hds : ∀ c ∈ ds, isDigitChar c = true) :
    ds.dropWhile isDigitChar = [] := by
  have := dropWhile_digits hds (rest := []) (fun c hc => by cases hc)
  simpa using this

/-! ## `mk'` shifting -/

private theorem ten_pow_ne_zero (k : Nat) : 10 ^ k ≠ 0 := by
  induction k with
  | zero => decide
  | succ k ih => rw [Nat.pow_succ]; exact Nat.mul_ne_zero ih (by decide)

theorem mk'_sig_zero (sign : Bool) (e : Int) :
    Decimal.mk' sign 0 e = ⟨sign, 0, 0⟩ := by
  rw [Decimal.mk', Decimal.canonical]
  simp

private theorem canonical_mul_ten (s : Bool) (v : Nat) (hv : v ≠ 0) (e : Int) :
    Decimal.canonical ⟨s, v * 10, e - 1⟩ = Decimal.canonical ⟨s, v, e⟩ := by
  have hne : v * 10 ≠ 0 := Nat.mul_ne_zero hv (by decide)
  have h10 : (v * 10) % 10 = 0 := Nat.mul_mod_left v 10
  have hdiv : v * 10 / 10 = v := by omega
  rw [Decimal.canonical, Decimal.canonical]
  show (if v * 10 = 0 then _ else _) = (if v = 0 then _ else _)
  rw [if_neg hne, if_neg hv,
      Decimal.canonicaliseAux_div _ _ hne h10, hdiv, Int.sub_add_cancel]

/-- Trailing zeros in the significand shift into the exponent under
    canonicalisation: parsing a zero-padded rendering recovers the
    unpadded decimal. -/
theorem mk'_shift (sign : Bool) (v : Nat) (e : Int) (k : Nat) :
    Decimal.mk' sign (v * 10 ^ k) (e - (k : Int)) = Decimal.mk' sign v e := by
  by_cases hv : v = 0
  · subst hv
    simp only [Nat.zero_mul]
    rw [mk'_sig_zero, mk'_sig_zero]
  · induction k with
    | zero => simp
    | succ k ih =>
      have hsig : v * 10 ^ (k + 1) = v * 10 ^ k * 10 := by rw [Nat.pow_succ, Nat.mul_assoc]
      have hexp : e - ((k + 1 : Nat) : Int) = e - (k : Nat) - 1 := by omega
      rw [Decimal.mk', hsig, hexp,
          canonical_mul_ten sign (v * 10 ^ k) (Nat.mul_ne_zero hv (ten_pow_ne_zero k)) _,
          ← Decimal.mk', ih]

/-! ## Auxiliary shapes -/

/-- A digit-headed nonempty list: zero-padding prepended to `natChars`. -/
theorem pad_natChars_shape (p m : Nat) :
    ∃ c cs, List.replicate p '0' ++ natChars m = c :: cs ∧ isDigitChar c = true := by
  match p with
  | 0 =>
    obtain ⟨c, cs, hsplit, _⟩ := natChars_shape m
    refine ⟨c, cs, by simpa using hsplit, ?_⟩
    exact natChars_all_digits m c (by rw [hsplit]; exact List.mem_cons_self ..)
  | p + 1 =>
    exact ⟨'0', List.replicate p '0' ++ natChars m, by rw [List.replicate_succ]; rfl,
      isDigitChar_zero⟩

private theorem ne_of_digit {c : Char} (h : isDigitChar c = true) {x : Char}
    (hx : isDigitChar x = false) : c ≠ x := by
  intro he
  rw [he, hx] at h
  cases h

/-! ## `parseExpTail` -/

theorem parseExpDigits_run {rest : List Char} (hds : ∀ c ∈ rest, isDigitChar c = true)
    (hne : rest ≠ []) (neg : Bool) :
    parseExpDigits neg rest
      = some (if neg then -(charsVal rest : Int) else (charsVal rest : Int)) := by
  simp only [parseExpDigits, takeWhile_digits_all hds, dropWhile_digits_all hds]
  rw [if_neg (by simp [List.isEmpty_iff, hne])]

theorem parseExpTail_expChars (opts : FormatOptions) (e : Int) :
    parseExpTail (expChars opts e) = some e := by
  have hdigits : ∀ c ∈ List.replicate (opts.expMinDigits - (natChars e.natAbs).length) '0' ++ natChars e.natAbs, isDigitChar c = true := by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · rw [List.eq_of_mem_replicate hc]; exact isDigitChar_zero
    · exact natChars_all_digits _ c hc
  have hval : charsVal (List.replicate (opts.expMinDigits - (natChars e.natAbs).length) '0' ++ natChars e.natAbs) = e.natAbs := by
    rw [charsVal_zeros_append, charsVal_natChars]
  obtain ⟨c0, cs0, hshape, hc0⟩ :=
    pad_natChars_shape (opts.expMinDigits - (natChars e.natAbs).length) e.natAbs
  have hne : List.replicate (opts.expMinDigits - (natChars e.natAbs).length) '0'
      ++ natChars e.natAbs ≠ [] := by rw [hshape]; simp
  rw [expChars, parseExpTail]
  rw [if_neg (by intro h; cases h)]
  rw [if_pos (by by_cases h : opts.upperExp <;> simp [h])]
  simp only [List.cons_append, List.tail_cons]
  by_cases hneg : e < 0
  · rw [if_pos hneg]
    simp only [List.cons_append, List.nil_append, List.head?_cons, List.tail_cons, if_true]
    rw [parseExpDigits_run hdigits hne true, hval, if_pos rfl]
    congr 1
    omega
  · rw [if_neg hneg]
    by_cases hplus : opts.expPlus
    · rw [if_pos hplus]
      simp only [List.cons_append, List.nil_append, List.head?_cons, List.tail_cons,
        if_neg (by decide : ¬ ((some '+' : Option Char) = some '-')), if_true]
      rw [parseExpDigits_run hdigits hne false, hval, if_neg (by decide)]
      congr 1
      omega
    · rw [if_neg hplus]
      simp only [List.nil_append]
      rw [hshape]
      simp only [List.head?_cons, Option.some.injEq,
        eq_false (ne_of_digit hc0 (by decide : isDigitChar '-' = false)),
        eq_false (ne_of_digit hc0 (by decide : isDigitChar '+' = false)),
        if_false]
      rw [← hshape, parseExpDigits_run hdigits hne false, hval, if_neg (by decide)]
      congr 1
      omega

/-! ## `parseMantissa` -/

/-- Guard bundle: the integer part is a nonempty digit string that
    passes the leading-zero rule. -/
structure IntPartOk (opts : DecimalSyntax) (I : List Char) : Prop where
  digits : ∀ c ∈ I, isDigitChar c = true
  ne : I ≠ []
  noLeadZero : ¬ (¬ opts.allowLeadingZeros = true ∧ 2 ≤ I.length ∧ I.head? = some '0')

private theorem dot_stops (rest : List Char) :
    ∀ c, ('.' :: rest).head? = some c → isDigitChar c = false :=
  fun c hc => by injection hc with hc; rw [← hc]; decide

theorem parseMantissa_dot {opts : DecimalSyntax} {I F T : List Char}
    (hI : IntPartOk opts I)
    (hF : ∀ c ∈ F, isDigitChar c = true) (hFne : F ≠ [])
    (hT : ExpTailish T) :
    parseMantissa opts (I ++ '.' :: (F ++ T)) = some (I, F, T) := by
  simp only [parseMantissa]
  rw [takeWhile_digits hI.digits (dot_stops _), dropWhile_digits hI.digits (dot_stops _)]
  rw [if_neg (by simp [hI.ne]), if_neg (fun h => hI.noLeadZero ⟨h.1, h.2⟩)]
  rw [if_pos (show ('.' :: (F ++ T)).head? = some '.' from rfl)]
  simp only [List.tail_cons]
  simp only [takeWhile_digits hF (fun c hc => (hT c hc).1),
      dropWhile_digits hF (fun c hc => (hT c hc).1)]
  rw [if_neg (by simp [List.isEmpty_iff, hFne]),
      if_neg (by simp [List.isEmpty_iff, hFne])]

theorem parseMantissa_nodot {opts : DecimalSyntax} {I T : List Char}
    (hI : IntPartOk opts I)
    (hT : ExpTailish T)
    (hdot : opts.requireDot = false) :
    parseMantissa opts (I ++ T) = some (I, [], T) := by
  simp only [parseMantissa]
  rw [takeWhile_digits hI.digits (fun c hc => (hT c hc).1),
      dropWhile_digits hI.digits (fun c hc => (hT c hc).1)]
  rw [if_neg (by simp [hI.ne]), if_neg (fun h => hI.noLeadZero ⟨h.1, h.2⟩)]
  rw [if_neg (fun h => ((hT _ h).2 rfl)),
      if_neg (by simp [hdot, List.isEmpty_iff, hI.ne])]

/-! ## `parseMag` -/

theorem parseMag_dot {opts : DecimalSyntax} {I F : List Char} {sign : Bool}
    {T : List Char} {e : Int}
    (hI : IntPartOk opts I)
    (hF : ∀ c ∈ F, isDigitChar c = true) (hFne : F ≠ [])
    (hT : ExpTailish T) (hTe : parseExpTail T = some e) :
    parseMag opts sign (I ++ '.' :: (F ++ T))
      = some (Decimal.mk' sign (charsVal (I ++ F)) (e - F.length)) := by
  rw [parseMag, parseMantissa_dot hI hF hFne hT]
  show (parseExpTail T).map _ = _
  rw [hTe]
  rfl

theorem parseMag_nodot {opts : DecimalSyntax} {I : List Char} {sign : Bool}
    {T : List Char} {e : Int}
    (hI : IntPartOk opts I)
    (hT : ExpTailish T) (hTe : parseExpTail T = some e)
    (hdot : opts.requireDot = false) :
    parseMag opts sign (I ++ T)
      = some (Decimal.mk' sign (charsVal I) e) := by
  rw [parseMag, parseMantissa_nodot hI hT hdot]
  show (parseExpTail T).map _ = _
  rw [hTe]
  show some (Decimal.mk' sign (charsVal (I ++ [])) (e - ↑(List.length []))) = _
  rw [List.append_nil]
  simp

/-! ## `dotFrac` -/

theorem parseExpTail_nil : parseExpTail [] = some 0 := rfl

theorem dotFrac_eq_dot {minFrac : Nat} {frac : List Char}
    (h : frac ++ List.replicate (minFrac - frac.length) '0' ≠ []) :
    dotFrac minFrac frac
      = '.' :: (frac ++ List.replicate (minFrac - frac.length) '0') := by
  simp only [dotFrac]
  rw [if_neg (by simp [List.isEmpty_iff, h])]

theorem dotFrac_eq_nil {minFrac : Nat} {frac : List Char}
    (h : frac ++ List.replicate (minFrac - frac.length) '0' = []) :
    dotFrac minFrac frac = [] := by
  simp only [dotFrac]
  rw [if_pos (by simp [List.isEmpty_iff, h])]

/-! ## The round-trip -/

/-- Compatibility of a printer with a dialect: if the dialect requires
    the decimal point, the printer always emits one. The only
    interaction — everything else a printer can emit (`'+'`-signed or
    zero-padded exponents, padded fractions) is accepted by every
    dialect. -/
def FormatOptions.CompatibleWith (fopts : FormatOptions) (popts : DecimalSyntax) : Prop :=
  popts.requireDot = true → 1 ≤ fopts.minFracDigits ∧ 1 ≤ fopts.sciMinFracDigits

private theorem intPartOk_pad {popts : DecimalSyntax} {sig Z : Nat}
    (hz : sig = 0 → Z = 0) :
    IntPartOk popts (natChars sig ++ List.replicate Z '0') := by
  obtain ⟨c0, cs0, hshape, hc0z⟩ := natChars_shape sig
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact natChars_all_digits sig c hc
    · rw [List.eq_of_mem_replicate hc]; exact isDigitChar_zero
  · rw [hshape]; simp
  · rintro ⟨-, hlen2, hhead⟩
    rw [hshape] at hhead
    simp only [List.cons_append, List.head?_cons, Option.some.injEq] at hhead
    have hsig0 : sig = 0 := hc0z hhead
    have hZ : Z = 0 := hz hsig0
    subst hsig0; subst hZ
    rw [natChars_zero] at hlen2
    simp at hlen2

private theorem intPartOk_zero {popts : DecimalSyntax} : IntPartOk popts ['0'] := by
  refine ⟨?_, by simp, ?_⟩
  · intro c hc
    rw [List.mem_singleton] at hc
    subst hc
    exact isDigitChar_zero
  · rintro ⟨-, hlen2, -⟩
    simp at hlen2

private theorem intPartOk_take {popts : DecimalSyntax} {sig w : Nat}
    (hsig : sig ≠ 0) (hw : 1 ≤ w) :
    IntPartOk popts ((natChars sig).take w) := by
  obtain ⟨c0, cs0, hshape, hc0z⟩ := natChars_shape sig
  obtain ⟨m, rfl⟩ : ∃ m, w = m + 1 := ⟨w - 1, by omega⟩
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    exact natChars_all_digits sig c (List.take_subset _ _ hc)
  · rw [hshape, List.take_succ_cons]; simp
  · rintro ⟨-, -, hhead⟩
    rw [hshape, List.take_succ_cons] at hhead
    simp only [List.head?_cons, Option.some.injEq] at hhead
    exact hsig (hc0z hhead)

private theorem replicate_ne_nil {k : Nat} (hk : 1 ≤ k) :
    List.replicate k '0' ≠ [] := by
  intro h
  have := congrArg List.length h
  simp at this
  omega

private theorem charsVal_zero_cons (X : List Char) :
    charsVal ('0' :: X) = charsVal X := by
  have : ('0' :: X) = ['0'] ++ X := rfl
  rw [this, charsVal_append]
  have : charsVal ['0'] = 0 := by decide
  rw [this]
  omega

/-- The core round trip at the magnitude level: parsing back a rendered
    canonical `(sig, exp)` recovers it exactly. -/
theorem parseMag_formatMag {fopts : FormatOptions} {popts : DecimalSyntax}
    (hcompat : fopts.CompatibleWith popts)
    (s : Bool) {sig : Nat} {exp : Int}
    (hcan : Decimal.IsCanonical ⟨s, sig, exp⟩) :
    parseMag popts s (formatMag fopts (natChars sig) exp) = some ⟨s, sig, exp⟩ := by
  obtain ⟨c0, cs0, hshape, hc0z⟩ := natChars_shape sig
  have hdig := natChars_all_digits sig
  have hn : (natChars sig).length = cs0.length + 1 := by rw [hshape]; rfl
  have hval : charsVal (natChars sig) = sig := charsVal_natChars sig
  have hzero_exp : sig = 0 → exp = 0 := by
    intro h0
    rcases hcan with ⟨-, h⟩ | ⟨hne, -⟩
    · exact h
    · exact absurd h0 hne
  have hself := Srtfp.Decimal.mk'_eq_self_of_isCanonical (sign := s) hcan
  have hzeros : ∀ (k : Nat), ∀ c ∈ List.replicate k '0', isDigitChar c = true := by
    intro k c hc
    rw [List.eq_of_mem_replicate hc]
    exact isDigitChar_zero
  simp only [formatMag]
  by_cases hsci : fopts.mode.scientificAt (exp + ↑(natChars sig).length - 1) = true
  · -- Scientific: `d₀[.frac]e<pointExp>`.
    rw [if_pos hsci]
    have htake1 : (natChars sig).take 1 = [c0] := by
      rw [hshape, List.take_succ_cons, List.take_zero]
    have hdrop1 : (natChars sig).drop 1 = cs0 := by
      rw [hshape, List.drop_succ_cons, List.drop_zero]
    rw [htake1, hdrop1]
    have hI : IntPartOk popts [c0] := by
      refine ⟨?_, by simp, ?_⟩
      · intro c hc
        rw [List.mem_singleton] at hc
        rw [hc]
        exact hdig c0 (by rw [hshape]; exact List.mem_cons_self ..)
      · rintro ⟨-, hlen2, -⟩
        simp at hlen2
    have hTail := expTailish_expChars fopts (exp + ↑(natChars sig).length - 1)
    have hTe := parseExpTail_expChars fopts (exp + ↑(natChars sig).length - 1)
    by_cases hFe : cs0 ++ List.replicate (fopts.sciMinFracDigits - cs0.length) '0' = []
    · -- No fraction, no dot: `d₀e<pe>`.
      obtain ⟨hcs0, -⟩ : cs0 = [] ∧ True := by
        cases cs0 with
        | nil => exact ⟨rfl, trivial⟩
        | cons a l => simp at hFe
      have hrd : popts.requireDot = false := by
        cases h : popts.requireDot with
        | false => rfl
        | true =>
          exfalso
          have hmf := (hcompat h).2
          subst hcs0
          exact replicate_ne_nil (by simpa using hmf) (by simpa using hFe)
      rw [dotFrac_eq_nil hFe]
      simp only [List.append_nil]
      rw [parseMag_nodot hI hTail hTe hrd]
      have hv : charsVal [c0] = sig := by
        rw [show ([c0] : List Char) = natChars sig from by rw [hshape, hcs0]]
        exact hval
      have hpe : exp + ↑(natChars sig).length - 1 = exp := by
        subst hcs0
        simp at hn
        omega
      rw [hv, hpe, hself]
    · -- Fraction present: `d₀.frac e<pe>`.
      rw [dotFrac_eq_dot hFe]
      have hassoc : ([c0] ++ ('.' :: (cs0 ++ List.replicate (fopts.sciMinFracDigits - cs0.length) '0'))
            ++ expChars fopts (exp + ↑(natChars sig).length - 1))
          = [c0] ++ '.' :: ((cs0 ++ List.replicate (fopts.sciMinFracDigits - cs0.length) '0')
            ++ expChars fopts (exp + ↑(natChars sig).length - 1)) := by
        simp
      have hFdig : ∀ c ∈ cs0 ++ List.replicate (fopts.sciMinFracDigits - cs0.length) '0',
          isDigitChar c = true := by
        intro c hc
        rcases List.mem_append.mp hc with hc | hc
        · exact hdig c (by rw [hshape]; exact List.mem_cons_of_mem _ hc)
        · exact hzeros _ c hc
      rw [hassoc, parseMag_dot hI hFdig hFe hTail hTe]
      have hv : charsVal ([c0] ++ (cs0 ++ List.replicate (fopts.sciMinFracDigits - cs0.length) '0'))
          = sig * 10 ^ (fopts.sciMinFracDigits - cs0.length) := by
        rw [show [c0] ++ (cs0 ++ List.replicate (fopts.sciMinFracDigits - cs0.length) '0')
              = (c0 :: cs0) ++ List.replicate (fopts.sciMinFracDigits - cs0.length) '0' from by simp,
            charsVal_append_zeros, ← hshape, hval]
      have hlen : ((cs0 ++ List.replicate (fopts.sciMinFracDigits - cs0.length) '0').length : Int)
          = ↑cs0.length + ↑(fopts.sciMinFracDigits - cs0.length) := by
        simp [List.length_append]
      have he : exp + ↑(natChars sig).length - 1
            - ↑(cs0 ++ List.replicate (fopts.sciMinFracDigits - cs0.length) '0').length
          = exp - ↑(fopts.sciMinFracDigits - cs0.length) := by
        rw [hlen, hn]
        push_cast
        omega
      rw [hv, he, mk'_shift, hself]
  · rw [if_neg hsci]
    by_cases hpos : (0 : Int) ≤ exp
    · -- Positional, integral: `digits0…0[.0…0]`.
      rw [if_pos hpos]
      have hIok : IntPartOk popts (natChars sig ++ List.replicate exp.toNat '0') :=
        intPartOk_pad (fun h0 => by rw [hzero_exp h0]; rfl)
      have hIv : charsVal (natChars sig ++ List.replicate exp.toNat '0')
          = sig * 10 ^ exp.toNat := by
        rw [charsVal_append_zeros, hval]
      by_cases hmf : fopts.minFracDigits = 0
      · have hrd : popts.requireDot = false := by
          cases h : popts.requireDot with
          | false => rfl
          | true => exact absurd (hcompat h).1 (by omega)
        rw [dotFrac_eq_nil (by simp [hmf]),
            parseMag_nodot hIok expTailish_nil parseExpTail_nil hrd, hIv]
        rw [show (0 : Int) = exp - ↑exp.toNat from by omega, mk'_shift, hself]
      · have hFne : ([] : List Char) ++ List.replicate (fopts.minFracDigits - ([] : List Char).length) '0' ≠ [] := by
          simp only [List.nil_append, List.length_nil, Nat.sub_zero]
          exact replicate_ne_nil (by omega)
        rw [dotFrac_eq_dot hFne]
        simp only [List.nil_append, List.length_nil, Nat.sub_zero]
        have hassoc : (natChars sig ++ List.replicate exp.toNat '0')
              ++ '.' :: List.replicate fopts.minFracDigits '0'
            = (natChars sig ++ List.replicate exp.toNat '0')
              ++ '.' :: (List.replicate fopts.minFracDigits '0' ++ []) := by
          simp
        rw [hassoc, parseMag_dot hIok (hzeros _)
              (replicate_ne_nil (by omega)) expTailish_nil parseExpTail_nil]
        rw [charsVal_append_zeros, hIv, List.length_replicate]
        rw [mk'_shift, show (0 : Int) = exp - ↑exp.toNat from by omega, mk'_shift, hself]
    · -- Negative exponent: sub-one or split.
      rw [if_neg hpos]
      by_cases hsub : (↑(natChars sig).length : Int) + exp ≤ 0
      · -- `0.0…0digits`
        rw [if_pos hsub]
        have hzInt : (((-(↑(natChars sig).length + exp)).toNat : Int))
            = -(↑(natChars sig).length + exp) := Int.toNat_of_nonneg (by omega)
        have hFraw_ne : List.replicate (-(↑(natChars sig).length + exp)).toNat '0'
            ++ natChars sig ≠ [] := by
          intro h
          have := congrArg List.length h
          simp [hn] at this
        have hFne : (List.replicate (-(↑(natChars sig).length + exp)).toNat '0' ++ natChars sig)
            ++ List.replicate (fopts.minFracDigits
              - (List.replicate (-(↑(natChars sig).length + exp)).toNat '0'
                  ++ natChars sig).length) '0' ≠ [] := by
          intro h
          rcases List.append_eq_nil_iff.mp h with ⟨h1, -⟩
          exact hFraw_ne h1
        rw [dotFrac_eq_dot hFne]
        have hFdig : ∀ c ∈ (List.replicate (-(↑(natChars sig).length + exp)).toNat '0'
              ++ natChars sig)
            ++ List.replicate (fopts.minFracDigits
              - (List.replicate (-(↑(natChars sig).length + exp)).toNat '0'
                  ++ natChars sig).length) '0', isDigitChar c = true := by
          intro c hc
          rcases List.mem_append.mp hc with hc | hc
          · rcases List.mem_append.mp hc with hc | hc
            · exact hzeros _ c hc
            · exact hdig c hc
          · exact hzeros _ c hc
        have hassoc : ('0' :: ('.' :: ((List.replicate (-(↑(natChars sig).length + exp)).toNat '0'
              ++ natChars sig)
            ++ List.replicate (fopts.minFracDigits
              - (List.replicate (-(↑(natChars sig).length + exp)).toNat '0'
                  ++ natChars sig).length) '0')))
            = ['0'] ++ '.' :: (((List.replicate (-(↑(natChars sig).length + exp)).toNat '0'
              ++ natChars sig)
            ++ List.replicate (fopts.minFracDigits
              - (List.replicate (-(↑(natChars sig).length + exp)).toNat '0'
                  ++ natChars sig).length) '0') ++ []) := by
          simp
        rw [hassoc, parseMag_dot intPartOk_zero hFdig hFne expTailish_nil parseExpTail_nil]
        have hv : charsVal (['0'] ++ ((List.replicate (-(↑(natChars sig).length + exp)).toNat '0'
              ++ natChars sig)
            ++ List.replicate (fopts.minFracDigits
              - (List.replicate (-(↑(natChars sig).length + exp)).toNat '0'
                  ++ natChars sig).length) '0'))
            = sig * 10 ^ (fopts.minFracDigits
              - (List.replicate (-(↑(natChars sig).length + exp)).toNat '0'
                  ++ natChars sig).length) := by
          rw [show (['0'] : List Char) ++ ((List.replicate (-(↑(natChars sig).length + exp)).toNat '0'
                ++ natChars sig)
              ++ List.replicate (fopts.minFracDigits
                - (List.replicate (-(↑(natChars sig).length + exp)).toNat '0'
                    ++ natChars sig).length) '0')
              = '0' :: (List.replicate (-(↑(natChars sig).length + exp)).toNat '0'
                ++ (natChars sig
                  ++ List.replicate (fopts.minFracDigits
                    - (List.replicate (-(↑(natChars sig).length + exp)).toNat '0'
                        ++ natChars sig).length) '0')) from by simp,
              charsVal_zero_cons, charsVal_zeros_append, charsVal_append_zeros, hval]
        rw [hv]
        have he : (0 : Int) - ↑((List.replicate (-(↑(natChars sig).length + exp)).toNat '0'
              ++ natChars sig)
            ++ List.replicate (fopts.minFracDigits
              - (List.replicate (-(↑(natChars sig).length + exp)).toNat '0'
                  ++ natChars sig).length) '0').length
            = exp - ↑(fopts.minFracDigits
              - (List.replicate (-(↑(natChars sig).length + exp)).toNat '0'
                  ++ natChars sig).length) := by
          simp only [List.length_append, List.length_replicate]
          push_cast
          omega
        rw [he, mk'_shift, hself]
      · -- `int.frac`
        rw [if_neg hsub]
        have hsig0 : sig ≠ 0 := by
          intro h0
          rw [hzero_exp h0] at hpos
          exact hpos (by omega)
        have hwInt : (((↑(natChars sig).length + exp).toNat : Int))
            = ↑(natChars sig).length + exp := Int.toNat_of_nonneg (by omega)
        have hw1 : 1 ≤ (↑(natChars sig).length + exp).toNat := by omega
        have hwlt : (↑(natChars sig).length + exp).toNat < (natChars sig).length := by omega
        have hdroplen : ((natChars sig).drop (↑(natChars sig).length + exp).toNat).length
            = (natChars sig).length - (↑(natChars sig).length + exp).toNat := by
          simp [List.length_drop]
        have hdropne : (natChars sig).drop (↑(natChars sig).length + exp).toNat ≠ [] := by
          intro h
          have := congrArg List.length h
          rw [hdroplen] at this
          simp at this
          omega
        have hFne : (natChars sig).drop (↑(natChars sig).length + exp).toNat
            ++ List.replicate (fopts.minFracDigits
              - ((natChars sig).drop (↑(natChars sig).length + exp).toNat).length) '0' ≠ [] := by
          intro h
          rcases List.append_eq_nil_iff.mp h with ⟨h1, -⟩
          exact hdropne h1
        have hFdig : ∀ c ∈ (natChars sig).drop (↑(natChars sig).length + exp).toNat
            ++ List.replicate (fopts.minFracDigits
              - ((natChars sig).drop (↑(natChars sig).length + exp).toNat).length) '0',
            isDigitChar c = true := by
          intro c hc
          rcases List.mem_append.mp hc with hc | hc
          · exact hdig c (List.drop_subset _ _ hc)
          · exact hzeros _ c hc
        rw [dotFrac_eq_dot hFne]
        have hassoc : ((natChars sig).take (↑(natChars sig).length + exp).toNat
              ++ '.' :: ((natChars sig).drop (↑(natChars sig).length + exp).toNat
                ++ List.replicate (fopts.minFracDigits
                  - ((natChars sig).drop (↑(natChars sig).length + exp).toNat).length) '0'))
            = (natChars sig).take (↑(natChars sig).length + exp).toNat
              ++ '.' :: (((natChars sig).drop (↑(natChars sig).length + exp).toNat
                ++ List.replicate (fopts.minFracDigits
                  - ((natChars sig).drop (↑(natChars sig).length + exp).toNat).length) '0') ++ []) := by
          simp
        rw [hassoc, parseMag_dot (intPartOk_take hsig0 hw1) hFdig hFne
              expTailish_nil parseExpTail_nil]
        have hv : charsVal ((natChars sig).take (↑(natChars sig).length + exp).toNat
              ++ ((natChars sig).drop (↑(natChars sig).length + exp).toNat
                ++ List.replicate (fopts.minFracDigits
                  - ((natChars sig).drop (↑(natChars sig).length + exp).toNat).length) '0'))
            = sig * 10 ^ (fopts.minFracDigits
                  - ((natChars sig).drop (↑(natChars sig).length + exp).toNat).length) := by
          rw [← List.append_assoc, List.take_append_drop, charsVal_append_zeros, hval]
        rw [hv]
        have he : (0 : Int) - ↑((natChars sig).drop (↑(natChars sig).length + exp).toNat
              ++ List.replicate (fopts.minFracDigits
                - ((natChars sig).drop (↑(natChars sig).length + exp).toNat).length) '0').length
            = exp - ↑(fopts.minFracDigits
                - ((natChars sig).drop (↑(natChars sig).length + exp).toNat).length) := by
          simp only [List.length_append, List.length_replicate, hdroplen]
          push_cast
          omega
        rw [he, mk'_shift, hself]

/-- Whatever `formatMag` emits starts with a digit — in particular never
    with a sign character, so the sign layer of `parseChars` passes
    through untouched. -/
theorem formatMag_head_digit (fopts : FormatOptions) {sig : Nat} (exp : Int) :
    ∀ c, (formatMag fopts (natChars sig) exp).head? = some c → isDigitChar c = true := by
  obtain ⟨c0, cs0, hshape, -⟩ := natChars_shape sig
  have hc0 : isDigitChar c0 = true :=
    natChars_all_digits sig c0 (by rw [hshape]; exact List.mem_cons_self ..)
  simp only [formatMag]
  by_cases hsci : fopts.mode.scientificAt (exp + ↑(natChars sig).length - 1) = true
  · rw [if_pos hsci, hshape, List.take_succ_cons, List.take_zero]
    simp only [List.cons_append, List.nil_append, List.head?_cons]
    intro c hc
    injection hc with hc
    rw [← hc]
    exact hc0
  · rw [if_neg hsci]
    by_cases hpos : (0 : Int) ≤ exp
    · rw [if_pos hpos, hshape]
      simp only [List.cons_append, List.head?_cons]
      intro c hc
      injection hc with hc
      rw [← hc]
      exact hc0
    · rw [if_neg hpos]
      by_cases hsub : (↑(natChars sig).length : Int) + exp ≤ 0
      · rw [if_pos hsub]
        simp only [List.head?_cons]
        intro c hc
        injection hc with hc
        rw [← hc]
        exact isDigitChar_zero
      · rw [if_neg hsub]
        obtain ⟨m, hm⟩ : ∃ m, (↑(natChars sig).length + exp).toNat = m + 1 :=
          ⟨(↑(natChars sig).length + exp).toNat - 1, by omega⟩
        rw [hm, hshape, List.take_succ_cons]
        simp only [List.cons_append, List.head?_cons]
        intro c hc
        injection hc with hc
        rw [← hc]
        exact hc0

/-- **Round trip (character level).** Rendering a canonical `Decimal`
    with any `FormatOptions` and parsing it back under any compatible
    `DecimalSyntax` recovers it exactly. -/
theorem parseChars_formatChars {fopts : FormatOptions} {popts : DecimalSyntax}
    (hcompat : fopts.CompatibleWith popts)
    (d : Decimal) (hcan : d.IsCanonical) :
    parseChars popts (formatChars fopts d) = some d := by
  obtain ⟨s, sig, exp⟩ := d
  cases s with
  | true =>
    have h1 : formatChars fopts ⟨true, sig, exp⟩
        = '-' :: formatMag fopts (natChars sig) exp := by
      rw [formatChars]
      rfl
    rw [h1, parseChars,
        if_pos (show ('-' :: formatMag fopts (natChars sig) exp).head? = some '-' from rfl)]
    simp only [List.tail_cons]
    exact parseMag_formatMag hcompat true hcan
  | false =>
    have h1 : formatChars fopts ⟨false, sig, exp⟩
        = formatMag fopts (natChars sig) exp := by
      rw [formatChars]
      rfl
    have hhead := formatMag_head_digit fopts (sig := sig) exp
    rw [h1, parseChars,
        if_neg (fun h => by have := hhead '-' h; exact absurd this (by decide)),
        if_neg (fun h => by have := hhead '+' h; exact absurd this (by decide))]
    exact parseMag_formatMag hcompat false hcan

/-- **Round trip (`String` level).** -/
theorem parse_format {fopts : FormatOptions} {popts : DecimalSyntax}
    (hcompat : fopts.CompatibleWith popts)
    (d : Decimal) (hcan : d.IsCanonical) :
    parse popts (format fopts d) = some d := by
  rw [parse, format, String.toList_ofList]
  exact parseChars_formatChars hcompat d hcan

/-! ## Parse outputs are canonical -/

theorem parseMag_isCanonical {opts : DecimalSyntax} {sign : Bool} {cs : List Char}
    {d : Decimal} (h : parseMag opts sign cs = some d) : d.IsCanonical := by
  rw [parseMag] at h
  cases hm : parseMantissa opts cs with
  | none => rw [hm] at h; cases h
  | some x =>
    obtain ⟨intD, fracD, rest⟩ := x
    rw [hm] at h
    cases he : parseExpTail rest with
    | none => simp [he] at h
    | some e =>
      simp [he] at h
      rw [← h, Decimal.mk']
      exact Srtfp.Decimal.canonical_isCanonical _

theorem parse_isCanonical {opts : DecimalSyntax} {s : String} {d : Decimal}
    (h : parse opts s = some d) : d.IsCanonical := by
  rw [parse, parseChars] at h
  by_cases h1 : s.toList.head? = some '-'
  · rw [if_pos h1] at h
    exact parseMag_isCanonical h
  · rw [if_neg h1] at h
    by_cases h2 : s.toList.head? = some '+'
    · rw [if_pos h2] at h
      by_cases h3 : opts.allowExplicitMantissaPlus = true
      · rw [if_pos h3] at h
        exact parseMag_isCanonical h
      · rw [if_neg h3] at h
        cases h
    · rw [if_neg h2] at h
      exact parseMag_isCanonical h

/-! ## Preset instantiations

The compatibility side condition discharges by `decide` for every
shipped preset pair; these name the ones consumers actually cite. -/

theorem parse_mlir_format_veir (d : Decimal) (hcan : d.IsCanonical) :
    parse .mlir (format .veir d) = some d :=
  parse_format (by unfold FormatOptions.CompatibleWith; decide) d hcan

theorem parse_json_format_veir (d : Decimal) (hcan : d.IsCanonical) :
    parse .jsonStrict (format .veir d) = some d :=
  parse_format (by unfold FormatOptions.CompatibleWith; decide) d hcan

theorem parse_json_format_python (d : Decimal) (hcan : d.IsCanonical) :
    parse .jsonStrict (format .python d) = some d :=
  parse_format (by unfold FormatOptions.CompatibleWith; decide) d hcan

theorem parse_json_format_js (d : Decimal) (hcan : d.IsCanonical) :
    parse .jsonStrict (format .js d) = some d :=
  parse_format (by unfold FormatOptions.CompatibleWith; decide) d hcan

theorem parse_yamlCore_format_veir (d : Decimal) (hcan : d.IsCanonical) :
    parse .yamlCore (format .veir d) = some d :=
  parse_format (by unfold FormatOptions.CompatibleWith; decide) d hcan

end Srtfp.Text

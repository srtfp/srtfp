module
/- Word algebra for `Srtfp.Float.Word`: field bounds and the packing
   round-trip. Pure `UInt64` arithmetic about the definitions in
   `Srtfp/Float/Bits.lean`; consumed by the proof stack and the `Float`
   bridge. -/

public import Srtfp.Perf.Bits

@[expose] public section

namespace Srtfp.Float

/-! ## Word algebra: field bounds and packing round-trip

The `(signBit, biasedExp, mantissa)` projections of `Word.pack` recover
the inputs when the fields are in range (`biasedExp < 2048`,
`mantissa < 2^52`). The decomposition is pure `UInt64` algebra: the three
fields occupy disjoint bit ranges, so the assembling `|||`s are additions
(`or_or_eq_add`), and each projection is a plain div/mod fact closed by
`omega`. No axioms beyond the kernel's are involved. -/

/-- Or of the three disjoint IEEE-754 binary64 bit fields (sign at bit 63,
biased exponent at bits 62..52, mantissa at bits 51..0) is addition. -/
theorem or_or_eq_add {s' b mm : Nat} (_hs' : s' ≤ 1) (hb : b < 2048)
    (hm : mm < 4503599627370496) :
    2 ^ 63 * s' ||| b * 2 ^ 52 ||| mm = 2 ^ 63 * s' + b * 2 ^ 52 + mm := by
  have hbm : b * 2 ^ 52 < 2 ^ 63 := by omega
  rw [← Nat.two_pow_add_eq_or_of_lt hbm s']
  have h2 : 2 ^ 63 * s' + b * 2 ^ 52 = 2 ^ 52 * (2 ^ 11 * s' + b) := by omega
  rw [h2, ← Nat.two_pow_add_eq_or_of_lt (show mm < 2 ^ 52 by omega) (2 ^ 11 * s' + b)]

/-- `or_or_eq_add` with the field summands in arbitrary syntactic shape,
convenient for rewriting. -/
theorem or_or_eq_add' {s b mm : Nat} (hs : s = 0 ∨ s = 2 ^ 63)
    (hb : ∃ b', b' < 2048 ∧ b = b' * 2 ^ 52) (hm : mm < 2 ^ 52) :
    s ||| b ||| mm = s + b + mm := by
  obtain ⟨b', hb', rfl⟩ := hb
  rcases hs with rfl | rfl
  · have := or_or_eq_add (s' := 0) (by omega) hb' (by omega)
    simpa using this
  · have := or_or_eq_add (s' := 1) (by omega) hb' (by omega)
    simpa using this

/-- `toNat` of the word assembled by `Word.pack`: with in-range fields it is
the plain sum `2^63·sign + biasedExp·2^52 + mantissa`. -/
theorem pack_toNat (sign : Bool) (biasedExp mantissa : Nat)
    (h_be : biasedExp < 2048) (h_m : mantissa < 2 ^ 52) :
    (Word.pack sign biasedExp mantissa).toNat
      = 2 ^ 63 * (if sign then 1 else 0) + biasedExp * 2 ^ 52 + mantissa := by
  unfold Word.pack
  have h_be_tn : (UInt64.ofNat biasedExp).toNat = biasedExp :=
    Nat.mod_eq_of_lt (by omega)
  have h_m_tn : (UInt64.ofNat mantissa).toNat = mantissa :=
    Nat.mod_eq_of_lt (by omega)
  have h1 : ((if sign = true then (1 : UInt64) <<< 63 else 0)).toNat
      = 2 ^ 63 * (if sign then 1 else 0) := by
    cases sign <;> simp
  have h2 : ((UInt64.ofNat biasedExp &&& 2047) <<< 52).toNat = biasedExp * 2 ^ 52 := by
    rw [UInt64.toNat_shiftLeft, UInt64.toNat_and, h_be_tn]
    rw [show ((2047 : UInt64)).toNat = 2 ^ 11 - 1 by decide]
    rw [Nat.and_two_pow_sub_one_of_lt_two_pow (by omega)]
    rw [show ((52 : UInt64)).toNat % 64 = 52 by decide]
    rw [Nat.shiftLeft_eq]
    exact Nat.mod_eq_of_lt (by omega)
  have h3 : (UInt64.ofNat mantissa &&& 4503599627370495).toNat = mantissa := by
    rw [UInt64.toNat_and, h_m_tn]
    rw [show ((4503599627370495 : UInt64)).toNat = 2 ^ 52 - 1 by decide]
    exact Nat.and_two_pow_sub_one_of_lt_two_pow (by omega)
  rw [UInt64.toNat_or, UInt64.toNat_or, h1, h2, h3]
  exact or_or_eq_add (by cases sign <;> simp) h_be (by omega)

/-- The biased-exponent field of the word assembled by `Word.pack`:
`Word.biasedExp (pack sign biasedExp mantissa) = biasedExp`. Pure
`UInt64`/`Nat` arithmetic over `pack_toNat`. -/
theorem pack_biasedExp (sign : Bool) (biasedExp mantissa : Nat)
    (h_be : biasedExp < 2048) (h_m : mantissa < 2 ^ 52) :
    Word.biasedExp (Word.pack sign biasedExp mantissa) = biasedExp := by
  have hw := pack_toNat sign biasedExp mantissa h_be h_m
  unfold Word.biasedExp
  rw [UInt64.toNat_and, UInt64.toNat_shiftRight, hw]
  rw [show ((2047 : UInt64)).toNat = 2 ^ 11 - 1 by decide]
  rw [show ((52 : UInt64)).toNat % 64 = 52 by decide]
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  cases sign <;> simp <;> omega

/-- The mantissa field of the word assembled by `Word.pack`:
`Word.mantissa (pack sign biasedExp mantissa) = mantissa`. Pure
`UInt64`/`Nat` arithmetic over `pack_toNat`. -/
theorem pack_mantissa (sign : Bool) (biasedExp mantissa : Nat)
    (h_be : biasedExp < 2048) (h_m : mantissa < 2 ^ 52) :
    Word.mantissa (Word.pack sign biasedExp mantissa) = mantissa := by
  have hw := pack_toNat sign biasedExp mantissa h_be h_m
  unfold Word.mantissa
  rw [UInt64.toNat_and, hw]
  rw [show ((4503599627370495 : UInt64)).toNat = 2 ^ 52 - 1 by decide]
  rw [Nat.and_two_pow_sub_one_eq_mod]
  cases sign <;> simp <;> omega

/-- Projection round-trip of `Word.pack` — no NaN side condition needed at
the word level (that condition exists only to discharge the runtime
axiom's domain restriction on the `Float` side). -/
theorem pack_proj (sign : Bool) (biasedExp : Nat) (mantissa : Nat)
    (h_be : biasedExp < 2048) (h_m : mantissa < 2 ^ 52) :
    Word.signBit (Word.pack sign biasedExp mantissa) = sign ∧
    Word.biasedExp (Word.pack sign biasedExp mantissa) = biasedExp ∧
    Word.mantissa (Word.pack sign biasedExp mantissa) = mantissa := by
  refine ⟨?_, pack_biasedExp sign biasedExp mantissa h_be h_m,
          pack_mantissa sign biasedExp mantissa h_be h_m⟩
  have hw := pack_toNat sign biasedExp mantissa h_be h_m
  unfold Word.signBit
  have hs : ((Word.pack sign biasedExp mantissa) >>> 63).toNat
      = ((if sign = true then (1 : UInt64) else 0)).toNat := by
    rw [UInt64.toNat_shiftRight, hw]
    rw [show ((63 : UInt64)).toNat % 64 = 63 by decide]
    rw [Nat.shiftRight_eq_div_pow]
    cases sign <;> simp <;> omega
  rw [UInt64.toNat_inj.mp hs]
  cases sign <;> decide

/-- The word assembled by `Word.pack` is never a NaN pattern when `h_nan`
rules out the `biasedExp = 2047 ∧ mantissa ≠ 0` combination. This is the
side condition the round-trip `Float.toBits_ofBits` demands, so every
caller re-encoding bit fields via `fromBits` must supply it. -/
theorem pack_isNaNPattern_false (sign : Bool) (biasedExp mantissa : Nat)
    (h_be : biasedExp < 2048) (h_m : mantissa < 2 ^ 52)
    (h_nan : biasedExp = 2047 → mantissa = 0) :
    _root_.Float.isNaNPattern (Word.pack sign biasedExp mantissa) = false := by
  unfold _root_.Float.isNaNPattern
  have hbe := pack_biasedExp sign biasedExp mantissa h_be h_m
  have hmt := pack_mantissa sign biasedExp mantissa h_be h_m
  unfold Word.biasedExp at hbe
  unfold Word.mantissa at hmt
  by_cases h : biasedExp = 2047
  · have hm0 := h_nan h
    have hbe_eq : (Word.pack sign biasedExp mantissa &&& 4503599627370495) = 0 := by
      rw [← UInt64.toNat_inj, hmt, hm0]
      decide
    rw [hbe_eq]
    simp
  · have hbe_ne : (Word.pack sign biasedExp mantissa >>> 52 &&& 2047) ≠ 2047 := by
      intro hcontra
      apply h
      have := congrArg UInt64.toNat hcontra
      rw [hbe] at this
      simpa using this
    simp [hbe_ne]

/-- `Word.isNaN` coincides with the runtime axiom's side-condition
predicate `Float.isNaNPattern`. -/
theorem word_isNaN_eq_isNaNPattern (w : UInt64) :
    Word.isNaN w = _root_.Float.isNaNPattern w := by
  unfold Word.isNaN Word.biasedExp Word.mantissa _root_.Float.isNaNPattern
  congr 1
  · rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq, beq_iff_eq]
    rw [show (2047 : Nat) = (2047 : UInt64).toNat from rfl, UInt64.toNat_inj]
  · rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq, bne_iff_ne, ne_eq]
    rw [show (0 : Nat) = (0 : UInt64).toNat from rfl, UInt64.toNat_inj]

/-- Finite words are not NaN patterns. -/
theorem word_isNaN_false_of_isFinite (w : UInt64) (h : Word.isFinite w = true) :
    Word.isNaN w = false := by
  unfold Word.isFinite at h
  unfold Word.isNaN
  have : ¬ Word.biasedExp w = 2047 := by
    simp only [decide_eq_true_eq] at h; omega
  simp [this]

/-- Finite words satisfy the runtime axiom's side condition. -/
theorem isNaNPattern_false_of_isFinite (w : UInt64) (h : Word.isFinite w = true) :
    _root_.Float.isNaNPattern w = false := by
  rw [← word_isNaN_eq_isNaNPattern]
  exact word_isNaN_false_of_isFinite w h

/-- `Word.biasedExp` is always in range `[0, 2048)`: it is an 11-bit field
mask, bounded regardless of the word. -/
theorem word_biasedExp_lt (w : UInt64) : Word.biasedExp w < 2048 := by
  unfold Word.biasedExp
  rw [UInt64.toNat_and]
  have hmask : ((0x7FF : UInt64).toNat) = 2047 := by decide
  rw [hmask]
  have := @Nat.and_le_right (w >>> 52).toNat 2047
  omega

/-- `Word.mantissa` is always in range `[0, 2^52)`: it is a 52-bit field
mask, bounded regardless of the word. -/
theorem word_mantissa_lt (w : UInt64) : Word.mantissa w < 2 ^ 52 := by
  unfold Word.mantissa
  rw [UInt64.toNat_and]
  have hmask : ((0x000F_FFFF_FFFF_FFFF : UInt64).toNat) = 4503599627370495 := by decide
  rw [hmask]
  have hle : w.toNat &&& 4503599627370495 ≤ 4503599627370495 := Nat.and_le_right
  have hpow : (2 : Nat) ^ 52 = 4503599627370496 := by decide
  omega

/-! ## Decoding

`Word.decode` of a packed word, and a word from its decoding. -/

/-- The three fields reassemble the word (pure `UInt64` algebra). -/
theorem pack_decode_eq (w : UInt64) :
    Word.pack (Word.signBit w) (Word.biasedExp w) (Word.mantissa w) = w := by
  unfold Word.pack Word.signBit Word.biasedExp Word.mantissa
  -- Goal: (signBit branch ||| biasedExp shifted ||| mantissa masked) = w.
  -- Pure UInt64 fact: OR of disjoint bit-field projections recovers W.
  generalize w = W
  -- Reduce the .toNat in biasedExpBits and mantissaBits casts.
  show (if decide (W >>> 63 ≠ 0) = true then (1 : UInt64) <<< 63 else 0) |||
       (UInt64.ofNat (((W >>> 52) &&& 0x7FF).toNat) &&& 0x7FF) <<< 52 |||
       UInt64.ofNat ((W &&& 0x000F_FFFF_FFFF_FFFF).toNat) &&& 0x000F_FFFF_FFFF_FFFF = W
  -- UInt64.ofNat ∘ UInt64.toNat = id on `< 2^64` values; all here are.
  have h1 : UInt64.ofNat (((W >>> 52) &&& 0x7FF).toNat) = (W >>> 52) &&& 0x7FF :=
    UInt64.toNat_inj.1 (Nat.mod_eq_of_lt (UInt64.toNat_lt _))
  have h2 : UInt64.ofNat ((W &&& 0x000F_FFFF_FFFF_FFFF).toNat) = W &&& 0x000F_FFFF_FFFF_FFFF :=
    UInt64.toNat_inj.1 (Nat.mod_eq_of_lt (UInt64.toNat_lt _))
  rw [h1, h2]
  -- Compare at the Nat level, where each field is a div/mod expression.
  rw [← UInt64.toNat_inj, UInt64.toNat_or, UInt64.toNat_or]
  have ha : W.toNat < 2 ^ 64 := UInt64.toNat_lt _
  -- biased-exponent field value
  have hbe : (((W >>> 52 &&& 2047) &&& 2047) <<< 52).toNat
      = (W.toNat / 2 ^ 52 % 2048) * 2 ^ 52 := by
    rw [UInt64.toNat_shiftLeft, UInt64.toNat_and, UInt64.toNat_and, UInt64.toNat_shiftRight,
        show ((52 : UInt64)).toNat % 64 = 52 by decide,
        show ((2047 : UInt64)).toNat = 2 ^ 11 - 1 by decide,
        Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod,
        Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  -- mantissa field value
  have hmnt : ((W &&& 4503599627370495) &&& 4503599627370495).toNat = W.toNat % 2 ^ 52 := by
    rw [UInt64.toNat_and, UInt64.toNat_and,
        show ((4503599627370495 : UInt64)).toNat = 2 ^ 52 - 1 by decide,
        Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod]
    omega
  rw [hbe, hmnt]
  by_cases hsgn : W >>> 63 = 0
  · have hz : W.toNat / 2 ^ 63 = 0 := by
      have := congrArg UInt64.toNat hsgn
      rwa [UInt64.toNat_shiftRight, show ((63 : UInt64)).toNat % 64 = 63 by decide,
           Nat.shiftRight_eq_div_pow] at this
    simp only [hsgn, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, if_false]
    rw [or_or_eq_add' (Or.inl (by decide)) ⟨_, by omega, rfl⟩ (by omega),
        show ((0 : UInt64)).toNat = 0 by decide]
    omega
  · have hz : W.toNat / 2 ^ 63 = 1 := by
      have h0 : (W >>> 63).toNat ≠ 0 := fun h => hsgn (UInt64.toNat_inj.1 (by simpa using h))
      rw [UInt64.toNat_shiftRight, show ((63 : UInt64)).toNat % 64 = 63 by decide,
          Nat.shiftRight_eq_div_pow] at h0
      omega
    simp only [hsgn, ne_eq, not_false_eq_true, decide_true, if_true]
    rw [show ((1 : UInt64) <<< 63).toNat = 2 ^ 63 by decide]
    rw [or_or_eq_add' (Or.inr rfl) ⟨_, by omega, rfl⟩ (by omega)]
    omega

theorem signBit_eq_decode_sign (w : UInt64) : Word.signBit w = (Word.decode w).sign := by
  unfold Word.decode
  by_cases he : Word.biasedExp w = 0 <;> simp [he]

/-- The mantissa field has the parity of the integer significand. -/
theorem mantissa_mod_two (w : UInt64) : Word.mantissa w % 2 = (Word.decode w).m % 2 := by
  unfold Word.decode
  by_cases he : Word.biasedExp w = 0 <;> simp [he] <;> omega

theorem isFinite_pack (sign : Bool) {biasedExp mantissa : Nat}
    (h_be : biasedExp < 2047) (h_m : mantissa < 2 ^ 52) :
    Word.isFinite (Word.pack sign biasedExp mantissa) = true := by
  unfold Word.isFinite
  rw [pack_biasedExp sign biasedExp mantissa (by omega) h_m]
  simpa using h_be

theorem decode_pack (sign : Bool) {biasedExp mantissa : Nat}
    (h_be : biasedExp < 2048) (h_m : mantissa < 2 ^ 52) :
    Word.decode (Word.pack sign biasedExp mantissa) =
      if biasedExp = 0 then ⟨sign, mantissa, -1074⟩
      else ⟨sign, mantissa + 2 ^ 52, (biasedExp : Int) - 1075⟩ := by
  obtain ⟨hs, hb, hmn⟩ := pack_proj sign biasedExp mantissa h_be h_m
  unfold Word.decode
  rw [hs, hb, hmn]
  by_cases he : biasedExp = 0
  · simp [he]
  · simp only [he, if_false, Nat.shiftLeft_eq, Decoded.mk.injEq, true_and]
    omega

/-- A word's fields, from its decoding. -/
theorem fields_of_decode (w : UInt64) :
    Word.biasedExp w = (if (Word.decode w).m < 2 ^ 52 then 0 else ((Word.decode w).q + 1075).toNat)
    ∧ Word.mantissa w = (if (Word.decode w).m < 2 ^ 52 then (Word.decode w).m
                          else (Word.decode w).m - 2 ^ 52) := by
  have hm := word_mantissa_lt w
  unfold Word.decode
  by_cases he : Word.biasedExp w = 0
  · simp only [he, if_true]
    rw [if_pos hm, if_pos hm]; exact ⟨rfl, rfl⟩
  · simp only [he, if_false, Nat.shiftLeft_eq]
    rw [if_neg (by omega), if_neg (by omega)]
    constructor
    · omega
    · omega

/-- Words with the same decoding are the same word. -/
theorem eq_of_decode_eq {w w' : UInt64} (h : Word.decode w = Word.decode w') : w = w' := by
  obtain ⟨hb, hm⟩ := fields_of_decode w
  obtain ⟨hb', hm'⟩ := fields_of_decode w'
  rw [← pack_decode_eq w, ← pack_decode_eq w', signBit_eq_decode_sign, signBit_eq_decode_sign,
    hb, hm, hb', hm', h]

end Srtfp.Float

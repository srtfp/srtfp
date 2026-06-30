/- IEEE-754 binary64 runtime axiom.

   `Float.toBits` and `Float.ofBits` are `@[extern]` runtime functions
   implemented by the Lean compiler against the host platform's IEEE-754
   binary64 representation. The naive inverse identity

     ∀ x : UInt64, (Float.ofBits x).toBits = x

   does *not* hold at every `x`: `SrtfpTest/RuntimeAxiomProbe.lean` empirically
   demonstrates that the runtime canonicalises NaN payloads — every NaN bit
   pattern `x` (biased exponent all-ones, mantissa nonzero) round-trips to
   the single canonical quiet-NaN pattern `0x7FF8000000000000`, not to `x`
   itself — while every non-NaN pattern (`isNaNPattern x = false`) round-trips
   exactly. The axiom below is restricted to that non-NaN domain, where it
   holds by the implementation contract: `Float.ofBits` simply
   `reinterpret_cast`s the 64 bits into the host's binary64 register, and
   `Float.toBits` is the reverse. This restricted identity still cannot be
   derived in pure Lean 4 because the Float type itself is opaque.

   This file isolates that single non-derivable identity as an audited
   axiom. The bit-field round-trip helper `fromBits_proj` is a theorem
   proven by elementary `Nat` arithmetic over the round-tripped UInt64
   word (no extra axioms), modulo the same non-NaN side condition. -/

import Srtfp.Numeric.Float.Bits

namespace Float

/-- A `UInt64` bit pattern is a NaN pattern iff its biased exponent field
    (bits 62..52) is all-ones (`0x7FF`) and its mantissa field (bits 51..0)
    is nonzero. See `SrtfpTest/RuntimeAxiomProbe.lean` for the empirical
    justification that the runtime's `toBits_ofBits` round-trip fails
    exactly on this set (NaN payloads are canonicalised away). -/
def isNaNPattern (x : UInt64) : Bool :=
  ((x >>> 52) &&& 0x7FF == 0x7FF) && (x &&& 0xF_FFFF_FFFF_FFFF != 0)

/-- IEEE-754 binary64 bit round-trip, restricted to non-NaN bit patterns.
    Lean's `Float.toBits` and `Float.ofBits` are `@[extern]` runtime
    functions; this identity holds by the implementation but is not
    derivable in pure Lean 4. Taken on trust from the IEEE-754
    specification and Lean's runtime contract — and, on the NaN patterns
    excluded here, is empirically *false* (the runtime canonicalises NaN
    payloads to a single quiet NaN on the `ofBits` side); see
    `SrtfpTest/RuntimeAxiomProbe.lean`. -/
axiom toBits_ofBits : ∀ x : UInt64, isNaNPattern x = false → (Float.ofBits x).toBits = x

end Float

/-! ## Bit-field round-trip helper

The `(signBit, biasedExpBits, mantissaBits)` projections of
`fromBits sign biasedExp mantissa` reduce to `(sign, biasedExp, mantissa)`
when the input bit fields are in range (biasedExp < 2048, mantissa < 2^52).
The decomposition is pure `UInt64` algebra: the three fields occupy
disjoint bit ranges, so the assembling `|||`s are additions
(`or_or_eq_add`), and each projection is a plain div/mod fact closed by
`omega`. No axioms beyond the kernel's are involved. -/

namespace PP.Numeric.Float

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

/-- `toNat` of the word assembled by `fromBits`: with in-range fields it is
the plain sum `2^63·sign + biasedExp·2^52 + mantissa`. -/
private theorem word_toNat (sign : Bool) (biasedExp mantissa : Nat)
    (h_be : biasedExp < 2048) (h_m : mantissa < 2 ^ 52) :
    ((if sign = true then (1 : UInt64) <<< 63 else 0) |||
      (UInt64.ofNat biasedExp &&& 2047) <<< 52 |||
      UInt64.ofNat mantissa &&& 4503599627370495).toNat
      = 2 ^ 63 * (if sign then 1 else 0) + biasedExp * 2 ^ 52 + mantissa := by
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

/-- The biased-exponent field of the word assembled by `fromBits`'s inputs
(before `Float.ofBits` is applied): `(word >>> 52 &&& 0x7FF).toNat =
biasedExp`. Pure `UInt64`/`Nat` arithmetic over `word_toNat`, independent
of any Float-level axiom. Shared by `fromBits_proj` and
`word_isNaNPattern_false`. -/
private theorem word_biasedExp_toNat (sign : Bool) (biasedExp mantissa : Nat)
    (h_be : biasedExp < 2048) (h_m : mantissa < 2 ^ 52) :
    (((if sign = true then (1 : UInt64) <<< 63 else 0) |||
        (UInt64.ofNat biasedExp &&& 2047) <<< 52 |||
        UInt64.ofNat mantissa &&& 4503599627370495) >>> 52 &&& 2047).toNat
      = biasedExp := by
  have hw := word_toNat sign biasedExp mantissa h_be h_m
  rw [UInt64.toNat_and, UInt64.toNat_shiftRight, hw]
  rw [show ((2047 : UInt64)).toNat = 2 ^ 11 - 1 by decide]
  rw [show ((52 : UInt64)).toNat % 64 = 52 by decide]
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  cases sign <;> simp <;> omega

/-- The mantissa field of the word assembled by `fromBits`'s inputs (before
`Float.ofBits` is applied): `(word &&& 0x000F_FFFF_FFFF_FFFF).toNat =
mantissa`. Pure `UInt64`/`Nat` arithmetic over `word_toNat`, independent of
any Float-level axiom. Shared by `fromBits_proj` and
`word_isNaNPattern_false`. -/
private theorem word_mantissa_toNat (sign : Bool) (biasedExp mantissa : Nat)
    (h_be : biasedExp < 2048) (h_m : mantissa < 2 ^ 52) :
    (((if sign = true then (1 : UInt64) <<< 63 else 0) |||
        (UInt64.ofNat biasedExp &&& 2047) <<< 52 |||
        UInt64.ofNat mantissa &&& 4503599627370495) &&& 4503599627370495).toNat
      = mantissa := by
  have hw := word_toNat sign biasedExp mantissa h_be h_m
  rw [UInt64.toNat_and, hw]
  rw [show ((4503599627370495 : UInt64)).toNat = 2 ^ 52 - 1 by decide]
  rw [Nat.and_two_pow_sub_one_eq_mod]
  cases sign <;> simp <;> omega

/-- `biasedExpBits` is always in range `[0, 2048)`: it is a 11-bit field
mask, so bounded regardless of whether `f` is finite. -/
theorem biasedExpBits_lt (f : _root_.Float) : biasedExpBits f < 2048 := by
  unfold biasedExpBits
  rw [UInt64.toNat_and]
  have hmask : ((0x7FF : UInt64).toNat) = 2047 := by decide
  rw [hmask]
  have := @Nat.and_le_right (f.toBits >>> 52).toNat 2047
  omega

/-- `mantissaBits` is always in range `[0, 2^52)`: it is a 52-bit field
mask, so bounded regardless of whether `f` is finite. -/
theorem mantissaBits_lt (f : _root_.Float) : mantissaBits f < 2 ^ 52 := by
  unfold mantissaBits
  rw [UInt64.toNat_and]
  have hmask : ((0x000F_FFFF_FFFF_FFFF : UInt64).toNat) = 4503599627370495 := by decide
  rw [hmask]
  have hle : f.toBits.toNat &&& 4503599627370495 ≤ 4503599627370495 := Nat.and_le_right
  have hpow : (2 : Nat) ^ 52 = 4503599627370496 := by decide
  omega

/-- The word assembled by `fromBits`'s inputs is never a NaN pattern when
`h_nan` rules out the `biasedExp = 2047 ∧ mantissa ≠ 0` combination. This is
the side condition the restricted `Float.toBits_ofBits` axiom demands, so
`fromBits_proj` (and every other caller re-encoding bit fields via
`fromBits`) must supply it. -/
theorem word_isNaNPattern_false (sign : Bool) (biasedExp mantissa : Nat)
    (h_be : biasedExp < 2048) (h_m : mantissa < 2 ^ 52)
    (h_nan : biasedExp = 2047 → mantissa = 0) :
    _root_.Float.isNaNPattern
      ((if sign = true then (1 : UInt64) <<< 63 else 0) |||
        (UInt64.ofNat biasedExp &&& 2047) <<< 52 |||
        UInt64.ofNat mantissa &&& 4503599627370495) = false := by
  unfold _root_.Float.isNaNPattern
  have hbe := word_biasedExp_toNat sign biasedExp mantissa h_be h_m
  have hmt := word_mantissa_toNat sign biasedExp mantissa h_be h_m
  by_cases h : biasedExp = 2047
  · have hm0 := h_nan h
    have hbe_eq :
        (((if sign = true then (1 : UInt64) <<< 63 else 0) |||
            (UInt64.ofNat biasedExp &&& 2047) <<< 52 |||
            UInt64.ofNat mantissa &&& 4503599627370495) &&& 4503599627370495) = 0 := by
      rw [← UInt64.toNat_inj, hmt, hm0]
      decide
    rw [hbe_eq]
    simp
  · have hbe_ne :
        (((if sign = true then (1 : UInt64) <<< 63 else 0) |||
            (UInt64.ofNat biasedExp &&& 2047) <<< 52 |||
            UInt64.ofNat mantissa &&& 4503599627370495) >>> 52 &&& 2047) ≠ 2047 := by
      intro hcontra
      apply h
      have := congrArg UInt64.toNat hcontra
      rw [hbe] at this
      simpa using this
    simp [hbe_ne]

/-- Round-trip of `fromBits` through `(signBit, biasedExpBits,
mantissaBits)`. When `biasedExp < 2048`, `mantissa < 2^52`, and the pair
does not encode a NaN payload (`biasedExp = 2047 → mantissa = 0`), the
bit-field projections recover the input. Proven by reducing each
projection to `Nat` div/mod arithmetic over `fromBits`'s output word
(`word_toNat`) and discharging with `omega`; the NaN side condition
discharges the restricted `toBits_ofBits` axiom via
`word_isNaNPattern_false`. -/
theorem fromBits_proj (sign : Bool) (biasedExp : Nat) (mantissa : Nat)
    (h_be : biasedExp < 2048) (h_m : mantissa < 2 ^ 52)
    (h_nan : biasedExp = 2047 → mantissa = 0) :
    signBit (fromBits sign biasedExp mantissa) = sign ∧
    biasedExpBits (fromBits sign biasedExp mantissa) = biasedExp ∧
    mantissaBits (fromBits sign biasedExp mantissa) = mantissa := by
  unfold signBit biasedExpBits mantissaBits fromBits
  rw [_root_.Float.toBits_ofBits _ (word_isNaNPattern_false sign biasedExp mantissa h_be h_m h_nan)]
  have hw := word_toNat sign biasedExp mantissa h_be h_m
  refine ⟨?_, ?_, ?_⟩
  · -- sign-bit projection: decide (w >>> 63 ≠ 0) = sign
    have hs : (((if sign = true then (1 : UInt64) <<< 63 else 0) |||
        (UInt64.ofNat biasedExp &&& 2047) <<< 52 |||
        UInt64.ofNat mantissa &&& 4503599627370495) >>> 63).toNat
        = ((if sign = true then (1 : UInt64) else 0)).toNat := by
      rw [UInt64.toNat_shiftRight, hw]
      rw [show ((63 : UInt64)).toNat % 64 = 63 by decide]
      rw [Nat.shiftRight_eq_div_pow]
      cases sign <;> simp <;> omega
    rw [UInt64.toNat_inj.mp hs]
    cases sign <;> decide
  · -- biased-exponent projection
    rw [UInt64.toNat_and, UInt64.toNat_shiftRight, hw]
    rw [show ((2047 : UInt64)).toNat = 2 ^ 11 - 1 by decide]
    rw [show ((52 : UInt64)).toNat % 64 = 52 by decide]
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
    cases sign <;> simp <;> omega
  · -- mantissa projection
    rw [UInt64.toNat_and, hw]
    rw [show ((4503599627370495 : UInt64)).toNat = 2 ^ 52 - 1 by decide]
    rw [Nat.and_two_pow_sub_one_eq_mod]
    cases sign <;> simp <;> omega

/-- Convenience wrapper: `(fromBits sign biasedExp mantissa).toBits` is
never a NaN pattern, when the fields are in range and don't encode a NaN
payload. Combines the restricted `Float.toBits_ofBits` axiom (via
`word_isNaNPattern_false`) with the resulting bits being exactly the
assembled word. -/
theorem fromBits_toBits_isNaNPattern_false (sign : Bool) (biasedExp mantissa : Nat)
    (h_be : biasedExp < 2048) (h_m : mantissa < 2 ^ 52)
    (h_nan : biasedExp = 2047 → mantissa = 0) :
    _root_.Float.isNaNPattern (fromBits sign biasedExp mantissa).toBits = false := by
  unfold fromBits
  have h_side := word_isNaNPattern_false sign biasedExp mantissa h_be h_m h_nan
  rw [_root_.Float.toBits_ofBits _ h_side]
  exact h_side

end PP.Numeric.Float

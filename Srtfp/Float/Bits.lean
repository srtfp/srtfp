/- IEEE-754 binary64 bit-level decomposition.

   This file has two layers:

   1. **Word layer** (`Srtfp.Float.Word`): pure `UInt64` functions — field
      extraction (sign / biased exponent / mantissa), the decoded
      "integer significand × power-of-two" form, the NaN/Inf/finite
      pattern predicates, and field packing — plus their algebra
      (projection round-trips, field bounds). Everything here is
      axiom-free: no `Float` value is ever consulted.

   2. **Float layer**: the same names on `Float`, each a one-line
      composition of the word layer with `Float.toBits` / `Float.ofBits`.

   For a finite binary64 word `w`:

     value = (-1)^sign × m × 2^q

   where:
     - `sign` is the top bit
     - `biasedExp` is the next 11 bits, `0 ≤ biasedExp ≤ 2047`
     - `mantissa` is the bottom 52 bits, `0 ≤ mantissa < 2^52`
     - The integer significand `m` and binary exponent `q` are derived as:
         * Normal (`1 ≤ biasedExp ≤ 2046`):
             m = 2^52 + mantissa         (∈ [2^52, 2^53))
             q = biasedExp - 1023 - 52   (∈ [-1074, 971])
         * Subnormal / zero (`biasedExp = 0`):
             m = mantissa                (∈ [0, 2^52))
             q = -1074

   NaN and Infinity (`biasedExp = 2047`) are exposed via pattern
   predicates and are otherwise out of scope for the decomposition. -/

import Srtfp.Decimal

/-- A `UInt64` bit pattern is a NaN pattern iff its biased exponent field
    (bits 62..52) is all-ones (`0x7FF`) and its mantissa field (bits 51..0)
    is nonzero. See `SrtfpTest/RuntimeAxiomProbe.lean` for the empirical
    justification that the runtime's `toBits_ofBits` round-trip fails
    exactly on this set (NaN payloads are canonicalised away); the
    restricted axiom in `Srtfp/Float/RuntimeAxiom.lean` uses this predicate
    as its side condition. -/
def Float.isNaNPattern (x : UInt64) : Bool :=
  ((x >>> 52) &&& 0x7FF == 0x7FF) && (x &&& 0xF_FFFF_FFFF_FFFF != 0)

namespace Srtfp.Float

/-- Decomposed finite binary64 value:
    `value = (if sign then -1 else 1) * m * 2^q`.
    For zero, `m = 0` and `q = -1074` (the subnormal-zero convention). -/
structure Decoded where
  sign : Bool
  /-- Integer significand. For normals, `m ∈ [2^52, 2^53)`. For subnormals,
      `m ∈ [0, 2^52)`. -/
  m : Nat
  /-- Binary exponent. `q ∈ [-1074, 971]` over the finite domain. -/
  q : Int
  deriving Repr, DecidableEq, Inhabited

/-! ## Word layer: pure `UInt64` bit-field algebra -/

namespace Word

/-- The sign bit of a binary64 word (bit 63). -/
def signBit (w : UInt64) : Bool :=
  (w >>> 63) ≠ 0

/-- The 11-bit biased exponent of a binary64 word (bits 62..52).
    Range `[0, 2047]`. -/
def biasedExp (w : UInt64) : Nat :=
  ((w >>> 52) &&& 0x7FF).toNat

/-- The 52-bit mantissa field of a binary64 word (bits 51..0).
    Range `[0, 2^52)`. For *normal* numbers this is the fractional part of
    the significand (the leading `1` is implicit); for *subnormals* it is
    the significand. -/
def mantissa (w : UInt64) : Nat :=
  (w &&& 0x000F_FFFF_FFFF_FFFF).toNat

/-- Decode a binary64 word into `(sign, m, q)`. The result is meaningful
    only for finite patterns; for NaN / Infinity the fields are returned
    uninterpreted. -/
def decode (w : UInt64) : Decoded :=
  let s := signBit w
  let e := biasedExp w
  let mb := mantissa w
  if e = 0 then
    -- Subnormal or zero.
    ⟨s, mb, -1074⟩
  else
    -- Normal. Restore the implicit leading 1.
    ⟨s, mb + (1 <<< 52), (e : Int) - 1023 - 52⟩

/-- `w` is a NaN pattern: `biasedExp = 2047` and `mantissa ≠ 0`.
    Same predicate as `Float.isNaNPattern`, phrased via the field readers
    (see `isNaN_eq_isNaNPattern`). -/
def isNaN (w : UInt64) : Bool :=
  biasedExp w = 2047 && mantissa w ≠ 0

/-- `w` is a `±∞` pattern: `biasedExp = 2047` and `mantissa = 0`. -/
def isInf (w : UInt64) : Bool :=
  biasedExp w = 2047 && mantissa w = 0

/-- `w` is a finite pattern: `biasedExp < 2047`. -/
def isFinite (w : UInt64) : Bool :=
  biasedExp w < 2047

/-- Assemble a binary64 word from raw bit fields. Inverse of the
    `(signBit, biasedExp, mantissa)` triple (see `pack_proj`). -/
def pack (sign : Bool) (biasedExp mantissa : Nat) : UInt64 :=
  (if sign then (1 : UInt64) <<< 63 else 0)
    ||| (UInt64.ofNat biasedExp &&& 0x7FF) <<< 52
    ||| (UInt64.ofNat mantissa &&& 0x000F_FFFF_FFFF_FFFF)

end Word

/-! ## Float layer

Each function is *definitionally* the corresponding word-layer function
applied to `f.toBits` (see the `rfl` bridge lemmas below), but the bodies
are spelled out directly so that existing proofs unfolding them see the
raw bit expressions. -/

/-- The sign bit of a `Float` (bit 63). -/
def signBit (f : _root_.Float) : Bool :=
  (f.toBits >>> 63) ≠ 0

/-- The 11-bit biased exponent of a `Float` (bits 62..52). Range `[0, 2047]`. -/
def biasedExpBits (f : _root_.Float) : Nat :=
  ((f.toBits >>> 52) &&& 0x7FF).toNat

/-- The 52-bit mantissa field of a `Float` (bits 51..0). Range `[0, 2^52)`.
    For *normal* numbers this is the fractional part of the significand (the
    leading `1` is implicit); for *subnormals* it is the significand. -/
def mantissaBits (f : _root_.Float) : Nat :=
  (f.toBits &&& 0x000F_FFFF_FFFF_FFFF).toNat

/-- Decode a `Float` into `(sign, m, q)`. The result is meaningful only for
    finite Floats; for NaN / Infinity the fields are returned uninterpreted. -/
def decode (f : _root_.Float) : Decoded :=
  let s := signBit f
  let e := biasedExpBits f
  let mb := mantissaBits f
  if e = 0 then
    -- Subnormal or zero.
    ⟨s, mb, -1074⟩
  else
    -- Normal. Restore the implicit leading 1.
    ⟨s, mb + (1 <<< 52), (e : Int) - 1023 - 52⟩

/-- `f` is NaN if `biasedExp = 2047` and `mantissaBits ≠ 0`. -/
def isNaNBits (f : _root_.Float) : Bool :=
  biasedExpBits f = 2047 && mantissaBits f ≠ 0

/-- `f` is `+∞` or `-∞` if `biasedExp = 2047` and `mantissaBits = 0`. -/
def isInfBits (f : _root_.Float) : Bool :=
  biasedExpBits f = 2047 && mantissaBits f = 0

/-- `f` is finite if `biasedExp < 2047`. -/
def isFiniteBits (f : _root_.Float) : Bool :=
  biasedExpBits f < 2047

/-- Reassemble a `Float` from raw bit fields. Inverse of the
    `(signBit, biasedExpBits, mantissaBits)` triple. -/
def fromBits (sign : Bool) (biasedExp : Nat) (mantissa : Nat) : _root_.Float :=
  let s : UInt64 := if sign then (1 : UInt64) <<< 63 else 0
  let e : UInt64 := (UInt64.ofNat biasedExp &&& 0x7FF) <<< 52
  let mPart : UInt64 := UInt64.ofNat mantissa &&& 0x000F_FFFF_FFFF_FFFF
  _root_.Float.ofBits (s ||| e ||| mPart)

/-! ## Bridges: the Float layer is the word layer at `f.toBits`

All are `rfl`: the two layers are definitionally equal, so bits-level
theorems about `Word.*` transport to `Float`-level statements (and back)
by rewriting with these. -/

theorem signBit_word (f : _root_.Float) : signBit f = Word.signBit f.toBits := rfl
theorem biasedExpBits_word (f : _root_.Float) :
    biasedExpBits f = Word.biasedExp f.toBits := rfl
theorem mantissaBits_word (f : _root_.Float) :
    mantissaBits f = Word.mantissa f.toBits := rfl
theorem decode_word (f : _root_.Float) : decode f = Word.decode f.toBits := rfl
theorem isNaNBits_word (f : _root_.Float) : isNaNBits f = Word.isNaN f.toBits := rfl
theorem isInfBits_word (f : _root_.Float) : isInfBits f = Word.isInf f.toBits := rfl
theorem isFiniteBits_word (f : _root_.Float) :
    isFiniteBits f = Word.isFinite f.toBits := rfl
theorem fromBits_word (sign : Bool) (biasedExp mantissa : Nat) :
    fromBits sign biasedExp mantissa
      = _root_.Float.ofBits (Word.pack sign biasedExp mantissa) := rfl

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
side condition the restricted `Float.toBits_ofBits` axiom demands, so every
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

/-- `biasedExpBits` is always in range `[0, 2048)`. -/
theorem biasedExpBits_lt (f : _root_.Float) : biasedExpBits f < 2048 :=
  word_biasedExp_lt f.toBits

/-- `mantissaBits` is always in range `[0, 2^52)`. -/
theorem mantissaBits_lt (f : _root_.Float) : mantissaBits f < 2 ^ 52 :=
  word_mantissa_lt f.toBits

end Srtfp.Float

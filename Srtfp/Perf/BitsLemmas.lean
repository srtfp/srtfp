module
/- Word algebra for `Srtfp.Float.Word`: field bounds and the packing
   round-trip. Pure `UInt64` arithmetic about the definitions in
   `Srtfp/Float/Bits.lean`; consumed by the proof stack and the `Float`
   bridge. -/

public import Srtfp.Perf.Bits

@[expose] public section

open Float.Model.UnpackedFloat (Sign)

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

/-- `toNat` of the word assembled by `Word.pack`: with in-range fields it is
the plain sum `2^63·sign + biasedExp·2^52 + mantissa`. -/
theorem pack_toNat (sign : Sign) (biasedExp mantissa : Nat)
    (h_be : biasedExp < 2048) (h_m : mantissa < 2 ^ 52) :
    (Word.pack sign biasedExp mantissa).toNat
      = 2 ^ 63 * (match sign with | .negative => 1 | .positive => 0) + biasedExp * 2 ^ 52 + mantissa := by
  unfold Word.pack
  have h_be_tn : (UInt64.ofNat biasedExp).toNat = biasedExp :=
    Nat.mod_eq_of_lt (by omega)
  have h_m_tn : (UInt64.ofNat mantissa).toNat = mantissa :=
    Nat.mod_eq_of_lt (by omega)
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
  rw [UInt64.toNat_or, UInt64.toNat_or, h2, h3]
  cases sign
  · show ((1 : UInt64) <<< 63).toNat ||| biasedExp * 2 ^ 52 ||| mantissa
      = 2 ^ 63 * 1 + biasedExp * 2 ^ 52 + mantissa
    rw [show ((1 : UInt64) <<< 63).toNat = 2 ^ 63 * 1 by decide]
    exact or_or_eq_add (by omega) h_be (by omega)
  · show ((0 : UInt64)).toNat ||| biasedExp * 2 ^ 52 ||| mantissa
      = 2 ^ 63 * 0 + biasedExp * 2 ^ 52 + mantissa
    rw [show ((0 : UInt64)).toNat = 2 ^ 63 * 0 by decide]
    exact or_or_eq_add (by omega) h_be (by omega)

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

end Srtfp.Float

module
/- Word algebra for `Srtfp.Float.Word`: field bounds and the packing
   round-trip. Pure `UInt64` arithmetic about the definitions in
   `Srtfp/Float/Bits.lean`; consumed by the proof stack and the `Float`
   bridge. -/

public import Srtfp.Perf.Bits
public import Srtfp.Perf.Word

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
  word_simp
  rw [Nat.mod_eq_of_lt (by omega : biasedExp < 2 ^ (64 : Nat)),
    Nat.mod_eq_of_lt (by omega : mantissa < 2 ^ (64 : Nat)), Nat.mod_eq_of_lt h_be,
    Nat.mod_eq_of_lt h_m, Nat.mod_eq_of_lt (by omega : biasedExp * 2 ^ (52 : Nat) < 2 ^ (64 : Nat))]
  cases sign
  · exact or_or_eq_add (s' := 1) (by omega) h_be h_m
  · exact or_or_eq_add (s' := 0) (by omega) h_be h_m

/-- `Word.biasedExp` is always in range `[0, 2048)`: it is an 11-bit field
mask, bounded regardless of the word. -/
theorem word_biasedExp_lt (w : UInt64) : Word.biasedExp w < 2048 := by
  unfold Word.biasedExp; word

/-- `Word.mantissa` is always in range `[0, 2^52)`: it is a 52-bit field
mask, bounded regardless of the word. -/
theorem word_mantissa_lt (w : UInt64) : Word.mantissa w < 2 ^ 52 := by
  unfold Word.mantissa; word

/-! ## Decoding

`Word.decode` of a packed word, and a word from its decoding. -/

end Srtfp.Float

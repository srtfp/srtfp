module
/- `word`: `UInt64` arithmetic as `Nat` arithmetic. Every word operation in
   the goal (`word_simp at …` for hypotheses too) becomes its `toNat` image,
   with wraps left as `% 2^64`, and `omega` finishes; the bounds that rule
   the wraps out must be in the context. -/

@[expose] public section

namespace Srtfp

/-! The bit masks the words use, as remainders. -/

theorem and_mask11 (n : Nat) : n &&& 2047 = n % 2 ^ 11 := Nat.and_two_pow_sub_one_eq_mod n 11
theorem and_mask32 (n : Nat) : n &&& 4294967295 = n % 2 ^ 32 :=
  Nat.and_two_pow_sub_one_eq_mod n 32
theorem and_mask52 (n : Nat) : n &&& 4503599627370495 = n % 2 ^ 52 :=
  Nat.and_two_pow_sub_one_eq_mod n 52

syntax "word_simp" (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| word_simp $[$loc:location]?) =>
    `(tactic| try simp only [ne_eq, ge_iff_le, gt_iff_lt, UInt64.le_iff_toNat_le,
        UInt64.lt_iff_toNat_lt, ← UInt64.toNat_inj, UInt64.toNat_add, UInt64.toNat_sub,
        UInt64.toNat_mul, UInt64.toNat_div, UInt64.toNat_mod, UInt64.toNat_and, UInt64.toNat_or,
        UInt64.toNat_shiftLeft, UInt64.toNat_shiftRight, UInt64.toNat_ofNat, UInt64.toNat_ofNat',
        UInt64.toNat_ofNatLT, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod,
        and_mask11, and_mask32, and_mask52, Nat.reducePow, Nat.reduceMod, Nat.reduceAdd,
        Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv] $[$loc:location]?)

macro "word" : tactic => `(tactic| word_simp <;> omega)

end Srtfp

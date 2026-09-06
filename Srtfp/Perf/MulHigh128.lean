module
/- The high word of a 64×64-bit product, `⌊a·b / 2^64⌋`, by the schoolbook
   split into 32-bit halves (Knuth's Algorithm M). Used by the printer's F8
   (`Perf/Schubfach/Product.lean`) and the reader's Eisel–Lemire kernel. -/

public import Srtfp.Perf.Word

@[expose] public section

namespace Srtfp.Schubfach

/-- High 64 bits of the unsigned product `a · b`. -/
@[inline]
def mulHi64 (a b : UInt64) : UInt64 :=
  let m   : UInt64 := 0xFFFFFFFF
  let aLo : UInt64 := a &&& m
  let aHi : UInt64 := a >>> 32
  let bLo : UInt64 := b &&& m
  let bHi : UInt64 := b >>> 32
  let ll   : UInt64 := aLo * bLo
  let mid1 : UInt64 := aLo * bHi + (ll >>> 32)
  let mid2 : UInt64 := aHi * bLo + (mid1 &&& m)
  aHi * bHi + (mid1 >>> 32) + (mid2 >>> 32)

theorem mulHi64_toNat_eq (a b : UInt64) :
    (mulHi64 a b).toNat = a.toNat * b.toNat / 2 ^ 64 := by
  unfold mulHi64
  simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_and, UInt64.toNat_shiftRight,
    show (0xFFFFFFFF : UInt64).toNat = 2 ^ 32 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.shiftRight_eq_div_pow, show (32 : UInt64).toNat % 64 = 32 from rfl, -Nat.reducePow]
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  generalize a.toNat = A at *
  generalize b.toNat = B at *
  -- the halves
  have hA := Nat.div_add_mod A (2 ^ 32)
  have hB := Nat.div_add_mod B (2 ^ 32)
  have haL := Nat.mod_lt A (by decide : 0 < 2 ^ 32)
  have hbL := Nat.mod_lt B (by decide : 0 < 2 ^ 32)
  generalize A / 2 ^ 32 = aH at *
  generalize A % 2 ^ 32 = aL at *
  generalize B / 2 ^ 32 = bH at *
  generalize B % 2 ^ 32 = bL at *
  have haH : aH < 2 ^ 32 := by omega
  have hbH : bH < 2 ^ 32 := by omega
  -- the four partial products as atoms
  have hAB : A * B = aH * bH * 2 ^ 64 + (aL * bH + aH * bL) * 2 ^ 32 + aL * bL := by
    rw [← hA, ← hB]; grind
  have p0 := Nat.mul_le_mul (Nat.le_of_lt_succ haL) (Nat.le_of_lt_succ hbL)
  have p1 := Nat.mul_le_mul (Nat.le_of_lt_succ haL) (Nat.le_of_lt_succ hbH)
  have p2 := Nat.mul_le_mul (Nat.le_of_lt_succ haH) (Nat.le_of_lt_succ hbL)
  have p3 := Nat.mul_le_mul (Nat.le_of_lt_succ haH) (Nat.le_of_lt_succ hbH)
  generalize aL * bL = P0 at *
  generalize aL * bH = P1 at *
  generalize aH * bL = P2 at *
  generalize aH * bH = P3 at *
  generalize A * B = P at *
  -- no word wraps: every intermediate is below `2^64`
  rw [Nat.mod_eq_of_lt (by omega : P0 < 2 ^ 64), Nat.mod_eq_of_lt (by omega : P1 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : P2 < 2 ^ 64), Nat.mod_eq_of_lt (by omega : P3 < 2 ^ 64)]
  rw [Nat.mod_eq_of_lt (by omega : P1 + P0 / 2 ^ 32 < 2 ^ 64)]
  rw [Nat.mod_eq_of_lt (by omega : P2 + (P1 + P0 / 2 ^ 32) % 2 ^ 32 < 2 ^ 64)]
  omega

end Srtfp.Schubfach

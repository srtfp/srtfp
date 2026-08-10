/- 128-bit unsigned multiply-high kernel for the Schubfach multiply-shift
   inner loop (Phase 3 of the UInt64 refinement).

   Computes `⌊a · g / 2⁶⁴⌋` for `a : UInt64` and `g = (gHi : UInt64) ‖ (gLo : UInt64)`
   (a 128-bit unsigned represented as a pair).  The result is the high
   64 bits of the 128-bit product `a · g`, treated as a 192-bit value.

   This is the workhorse used by `cmpScaledMixed_fast2` / `shiftedSig_fast2`
   to evaluate `⌊a · 2^q · 10^{-k}⌋` once a fixed-precision approximation
   of `10^{-k}` has been precomputed (Schubfach §9.8).

   ## Specification

   The mathematical spec is in `Nat`:

   ```
   mulHigh128Spec a gHi gLo
     = (a.toNat * (gHi.toNat * 2⁶⁴ + gLo.toNat)) / 2⁶⁴
   ```

   The actual implementation (`mulHigh128`) returns the low 64 bits of
   `mulHigh128Spec`, i.e. the result modulo 2⁶⁴.  `mulHigh128_toNat`
   proves this equivalence.

   In the Schubfach use, the spec value is constrained (by the dynamic
   range of `a` and the precomputed `g`) to fit in 64 bits, so callers
   can treat `mulHigh128` as exact.

-/

namespace Srtfp.Schubfach

/-! ## 64×64 → 128 unsigned multiply-high

`mulHi64 a b` returns the high 64 bits of the product `a · b` (the low
64 bits would be just `a * b` under wraparound).  Standard schoolbook
algorithm: split each 64-bit operand into two 32-bit halves and combine
the four 64-bit partial products. -/

/-- High 64 bits of the unsigned product `a · b`.  Standard Knuth
    Algorithm M (schoolbook 32-bit splits with carry propagation).
    `(mulHi64 a b).toNat = (a.toNat * b.toNat) / 2⁶⁴`
    (proved by `mulHi64_toNat`). -/
@[inline]
def mulHi64 (a b : UInt64) : UInt64 :=
  let m   : UInt64 := 0xFFFFFFFF
  let aLo : UInt64 := a &&& m
  let aHi : UInt64 := a >>> 32
  let bLo : UInt64 := b &&& m
  let bHi : UInt64 := b >>> 32
  let ll   : UInt64 := aLo * bLo             -- 64 bits, fits
  -- mid1 = aLo·bHi + (ll >>> 32); ≤ (2³²-1)² + 2³²-1 < 2⁶⁴ so no overflow.
  let mid1 : UInt64 := aLo * bHi + (ll >>> 32)
  -- mid2 = aHi·bLo + (mid1 &&& m); both summands < 2⁶⁴ and result still < 2⁶⁴
  let mid2 : UInt64 := aHi * bLo + (mid1 &&& m)
  aHi * bHi + (mid1 >>> 32) + (mid2 >>> 32)

/-! ## 64 × 128 → high 64 multiply-shift

`mulHigh128 a gHi gLo` returns `⌊a · ((gHi ‖ gLo)) / 2⁶⁴⌋ mod 2⁶⁴`,
i.e. the second-highest 64 bits of the 192-bit product `a · g`.

Decomposition:

```
a · g = a · (gHi · 2⁶⁴ + gLo)
      = (a · gHi) · 2⁶⁴ + a · gLo
```

The high 64 bits (of the 128-bit cut at 2⁶⁴):

```
⌊a · g / 2⁶⁴⌋ = a · gHi + ⌊a · gLo / 2⁶⁴⌋
              = a · gHi + mulHi64 a gLo
```

Implementation drops the upper 64 of `a · gHi` (UInt64 multiply wraps),
which is precisely the second-highest-64-bits cut we want. -/

/-- High 64 bits of `⌊a · g / 2⁶⁴⌋` where `g = gHi · 2⁶⁴ + gLo`.  See module
    docstring for the Nat spec. -/
@[inline]
def mulHigh128 (a gHi gLo : UInt64) : UInt64 :=
  a * gHi + mulHi64 a gLo

/-! ## Nat-level specification

The `mulHigh128Spec` Nat function captures the exact mathematical
quantity we care about.  `mulHigh128_toNat` proves equivalence (mod 2⁶⁴). -/

/-- Mathematical specification: `(a · g) / 2⁶⁴` in `Nat`. -/
def mulHigh128Spec (a gHi gLo : UInt64) : Nat :=
  (a.toNat * (gHi.toNat * 2 ^ 64 + gLo.toNat)) / 2 ^ 64

/-- Auxiliary spec for `mulHi64`. -/
def mulHi64Spec (a b : UInt64) : Nat :=
  (a.toNat * b.toNat) / 2 ^ 64

/-! ## Nat-level mirror

`mulHi64Nat` is a Nat-only mirror of the schoolbook computation in
`mulHi64`.  Each intermediate stage is guaranteed `< 2⁶⁴`, so it is the
shape `mulHi64` would have without UInt64 wraparound.  The proof of
`mulHi64Nat = (· * · / 2⁶⁴)` is a pure algebraic exercise. -/

/-- Nat mirror of `mulHi64` — exact 32-bit schoolbook split, no overflow. -/
def mulHi64Nat (α β : Nat) : Nat :=
  let αL := α % 2 ^ 32
  let αH := α / 2 ^ 32
  let βL := β % 2 ^ 32
  let βH := β / 2 ^ 32
  let ll   := αL * βL
  let mid1 := αL * βH + ll / 2 ^ 32
  let mid2 := αH * βL + mid1 % 2 ^ 32
  αH * βH + mid1 / 2 ^ 32 + mid2 / 2 ^ 32

/-- The Nat mirror equals `α · β / 2⁶⁴`. -/
theorem mulHi64Nat_eq (α β : Nat) (hα : α < 2 ^ 64) (hβ : β < 2 ^ 64) :
    mulHi64Nat α β = α * β / 2 ^ 64 := by
  have h264' : (2 : Nat) ^ 64 = 2 ^ 32 * 2 ^ 32 := by decide
  have hαL : α % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
  have hβL : β % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
  have hαH : α / 2 ^ 32 < 2 ^ 32 := by
    apply Nat.div_lt_of_lt_mul; rw [← h264']; exact hα
  have hβH : β / 2 ^ 32 < 2 ^ 32 := by
    apply Nat.div_lt_of_lt_mul; rw [← h264']; exact hβ
  have hα_split : α = α / 2 ^ 32 * 2 ^ 32 + α % 2 ^ 32 := by
    have := Nat.div_add_mod α (2 ^ 32); omega
  have hβ_split : β = β / 2 ^ 32 * 2 ^ 32 + β % 2 ^ 32 := by
    have := Nat.div_add_mod β (2 ^ 32); omega
  -- Stage the key abbreviations so we can talk about them.
  let αL := α % 2 ^ 32
  let αH := α / 2 ^ 32
  let βL := β % 2 ^ 32
  let βH := β / 2 ^ 32
  let ll := αL * βL
  let mid1 := αL * βH + ll / 2 ^ 32
  let mid2 := αH * βL + mid1 % 2 ^ 32
  show αH * βH + mid1 / 2 ^ 32 + mid2 / 2 ^ 32 = α * β / 2 ^ 64
  have hll_mod : ll % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
  have hmid2_mod : mid2 % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
  have h_tail : (mid2 % 2 ^ 32) * 2 ^ 32 + ll % 2 ^ 32 < 2 ^ 64 := by
    have h1 : (mid2 % 2 ^ 32) * 2 ^ 32 ≤ (2 ^ 32 - 1) * 2 ^ 32 := by
      apply Nat.mul_le_mul_right; omega
    have hX : (2 : Nat) ^ 32 - 1 = 4294967295 := by decide
    omega
  -- α · β = αH·βH·2⁶⁴ + (αH·βL + αL·βH)·2³² + αL·βL.
  have hexpand : α * β = αH * βH * 2 ^ 64 + (αH * βL + αL * βH) * 2 ^ 32 + αL * βL := by
    show α * β = (α/2^32) * (β/2^32) * 2 ^ 64
               + ((α/2^32) * (β % 2^32) + (α % 2^32) * (β/2^32)) * 2 ^ 32
               + (α % 2^32) * (β % 2^32)
    conv => lhs; rw [hα_split, hβ_split]
    rw [show (2 : Nat) ^ 64 = 2 ^ 32 * 2 ^ 32 from by decide]
    grind
  -- Reduce α · β / 2⁶⁴.
  rw [hexpand]
  rw [show αH * βH * 2 ^ 64 + (αH * βL + αL * βH) * 2 ^ 32 + αL * βL
       = ((αH * βL + αL * βH) * 2 ^ 32 + αL * βL) + 2 ^ 64 * (αH * βH) from by grind]
  rw [Nat.add_mul_div_left _ _ (by decide : 0 < 2 ^ 64)]
  -- Goal: αH·βH + mid1/2³² + mid2/2³² = ((αH·βL + αL·βH)·2³² + αL·βL)/2⁶⁴ + αH·βH
  -- Subtract αH·βH from both sides via omega-style cancellation.
  rw [show αH * βH + mid1 / 2 ^ 32 + mid2 / 2 ^ 32
       = (mid1 / 2 ^ 32 + mid2 / 2 ^ 32) + αH * βH from by grind]
  congr 1
  -- Now show: mid1/2³² + mid2/2³² = ((αH·βL + αL·βH)·2³² + αL·βL)/2⁶⁴
  have hll_split : ll = (ll / 2 ^ 32) * 2 ^ 32 + ll % 2 ^ 32 := by
    have := Nat.div_add_mod ll (2 ^ 32); omega
  have hmid1_split : mid1 = (mid1 / 2 ^ 32) * 2 ^ 32 + mid1 % 2 ^ 32 := by
    have := Nat.div_add_mod mid1 (2 ^ 32); omega
  have hmid2_split : mid2 = (mid2 / 2 ^ 32) * 2 ^ 32 + mid2 % 2 ^ 32 := by
    have := Nat.div_add_mod mid2 (2 ^ 32); omega
  have hmid1_def : mid1 = αL * βH + ll / 2 ^ 32 := rfl
  have hmid2_def : mid2 = αH * βL + mid1 % 2 ^ 32 := rfl
  have hll_def : ll = αL * βL := rfl
  have hR_eq :
      (αH * βL + αL * βH) * 2 ^ 32 + αL * βL
        = (mid1 / 2 ^ 32 + mid2 / 2 ^ 32) * 2 ^ 64
          + ((mid2 % 2 ^ 32) * 2 ^ 32 + ll % 2 ^ 32) := by
    grind
  rw [hR_eq]
  -- Goal: mid1/2³² + mid2/2³² = ((mid1/2³² + mid2/2³²)·2⁶⁴ + tail)/2⁶⁴
  rw [Nat.add_comm ((mid1 / 2 ^ 32 + mid2 / 2 ^ 32) * 2 ^ 64) _,
      Nat.add_mul_div_right _ _ (by decide : 0 < 2 ^ 64)]
  rw [Nat.div_eq_of_lt h_tail]
  grind

/-! ## UInt64 to Nat mirror

The actual `mulHi64` (UInt64 algorithm) is observationally the Nat
mirror.  All intermediates are overflow-free, so the UInt64 mod-2⁶⁴
collapses to identity. -/

private theorem nat_and_2_32 (x : Nat) : x &&& 4294967295 = x % 2 ^ 32 := by
  rw [show (4294967295 : Nat) = 2 ^ 32 - 1 from by decide,
      Nat.and_two_pow_sub_one_eq_mod]

private theorem nat_shiftRight_32 (x : Nat) : x >>> 32 = x / 2 ^ 32 :=
  Nat.shiftRight_eq_div_pow x 32

/-- The schoolbook UInt64 algorithm matches the Nat mirror. -/
theorem mulHi64_toNat (a b : UInt64) :
    (mulHi64 a b).toNat = mulHi64Nat a.toNat b.toNat := by
  unfold mulHi64 mulHi64Nat
  -- Establish bounds.
  have hα : a.toNat < 2 ^ 64 := a.toNat_lt
  have hβ : b.toNat < 2 ^ 64 := b.toNat_lt
  have hαL : a.toNat % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
  have hβL : b.toNat % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
  have h264 : (2 : Nat) ^ 64 = 2 ^ 32 * 2 ^ 32 := by decide
  have hαH : a.toNat / 2 ^ 32 < 2 ^ 32 := by
    apply Nat.div_lt_of_lt_mul; rw [← h264]; exact hα
  have hβH : b.toNat / 2 ^ 32 < 2 ^ 32 := by
    apply Nat.div_lt_of_lt_mul; rw [← h264]; exact hβ
  let αL := a.toNat % 2 ^ 32
  let αH := a.toNat / 2 ^ 32
  let βL := b.toNat % 2 ^ 32
  let βH := b.toNat / 2 ^ 32
  have hll : αL * βL < 2 ^ 64 := by
    have : αL * βL ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := by
      apply Nat.mul_le_mul <;> omega
    have hX : (2 : Nat) ^ 32 - 1 = 4294967295 := by decide
    omega
  have hlh : αL * βH < 2 ^ 64 := by
    have : αL * βH ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := by
      apply Nat.mul_le_mul <;> omega
    have hX : (2 : Nat) ^ 32 - 1 = 4294967295 := by decide
    omega
  have hhl : αH * βL < 2 ^ 64 := by
    have : αH * βL ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := by
      apply Nat.mul_le_mul <;> omega
    have hX : (2 : Nat) ^ 32 - 1 = 4294967295 := by decide
    omega
  have hhh : αH * βH < 2 ^ 64 := by
    have : αH * βH ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := by
      apply Nat.mul_le_mul <;> omega
    have hX : (2 : Nat) ^ 32 - 1 = 4294967295 := by decide
    omega
  have hll_div : αL * βL / 2 ^ 32 < 2 ^ 32 := by
    apply Nat.div_lt_of_lt_mul; rw [← h264]; exact hll
  let ll := αL * βL
  let mid1 := αL * βH + ll / 2 ^ 32
  have hmid1 : mid1 < 2 ^ 64 := by
    show αL * βH + ll / 2 ^ 32 < 2 ^ 64
    have h1 : αL * βH ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := by
      apply Nat.mul_le_mul <;> omega
    have hX : (2 : Nat) ^ 32 - 1 = 4294967295 := by decide
    omega
  have hmid1_mod : mid1 % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
  have hmid1_div : mid1 / 2 ^ 32 < 2 ^ 32 := by
    apply Nat.div_lt_of_lt_mul; rw [← h264]; exact hmid1
  let mid2 := αH * βL + mid1 % 2 ^ 32
  have hmid2 : mid2 < 2 ^ 64 := by
    show αH * βL + mid1 % 2 ^ 32 < 2 ^ 64
    have h1 : αH * βL ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := by
      apply Nat.mul_le_mul <;> omega
    have hX : (2 : Nat) ^ 32 - 1 = 4294967295 := by decide
    omega
  have hmid2_div : mid2 / 2 ^ 32 < 2 ^ 32 := by
    apply Nat.div_lt_of_lt_mul; rw [← h264]; exact hmid2
  have hfinal : αH * βH + mid1 / 2 ^ 32 + mid2 / 2 ^ 32 < 2 ^ 64 := by
    have h1 : αH * βH ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := by
      apply Nat.mul_le_mul <;> omega
    have hX : (2 : Nat) ^ 32 - 1 = 4294967295 := by decide
    omega
  -- Reduce all UInt64 ops to Nat.
  simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_and,
             UInt64.toNat_shiftRight, UInt64.toNat_ofNat]
  -- Normalize shift constants and AND with 0xFFFFFFFF.
  have h32mod_2 : (32 % 2 ^ 64 % 64 : Nat) = 32 := by decide
  have h_and_mod : ((4294967295 : Nat) % 2 ^ 64) = 4294967295 := by decide
  simp only [h32mod_2, h_and_mod, nat_shiftRight_32, nat_and_2_32]
  -- Discharge the remaining `mod 2^64`s using the overflow-free bounds.
  have hhh_mid1_div : αH * βH + mid1 / 2 ^ 32 < 2 ^ 64 := by
    have h1 : αH * βH ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := by
      apply Nat.mul_le_mul <;> omega
    have hX : (2 : Nat) ^ 32 - 1 = 4294967295 := by decide
    omega
  rw [Nat.mod_eq_of_lt hll]
  rw [Nat.mod_eq_of_lt hlh]
  rw [Nat.mod_eq_of_lt hmid1]
  rw [Nat.mod_eq_of_lt hhl]
  rw [Nat.mod_eq_of_lt hmid2]
  rw [Nat.mod_eq_of_lt hhh]
  rw [Nat.mod_eq_of_lt hhh_mid1_div]
  rw [Nat.mod_eq_of_lt hfinal]

/-- The actual UInt64 high-multiply is the divided product (when it fits). -/
theorem mulHi64_toNat_eq (a b : UInt64) :
    (mulHi64 a b).toNat = a.toNat * b.toNat / 2 ^ 64 := by
  rw [mulHi64_toNat, mulHi64Nat_eq _ _ a.toNat_lt b.toNat_lt]

/-! ## Correctness of `mulHigh128`

The full 64×128 → high-64 cut equals `(a · g) / 2⁶⁴ mod 2⁶⁴` where
`g = gHi · 2⁶⁴ + gLo`. -/

/-- `mulHigh128 a gHi gLo` returns `mulHigh128Spec mod 2⁶⁴`. -/
theorem mulHigh128_toNat (a gHi gLo : UInt64) :
    (mulHigh128 a gHi gLo).toNat = mulHigh128Spec a gHi gLo % 2 ^ 64 := by
  unfold mulHigh128 mulHigh128Spec
  -- a * gHi + mulHi64 a gLo, reduced to Nat:
  --   (a · gHi mod 2⁶⁴ + mulHi64 a gLo mod 2⁶⁴) mod 2⁶⁴
  -- = (a · gHi + (a · gLo) / 2⁶⁴) mod 2⁶⁴.
  -- And: (a · (gHi · 2⁶⁴ + gLo)) / 2⁶⁴ = a · gHi + (a · gLo) / 2⁶⁴.
  simp only [UInt64.toNat_add, UInt64.toNat_mul, mulHi64_toNat_eq]
  -- Goal: (a.toNat * gHi.toNat % 2 ^ 64 + a.toNat * gLo.toNat / 2 ^ 64 % 2 ^ 64) % 2 ^ 64
  --     = (a.toNat * (gHi.toNat * 2 ^ 64 + gLo.toNat)) / 2 ^ 64 % 2 ^ 64
  -- Rewrite the RHS: a·(gHi·2⁶⁴ + gLo) / 2⁶⁴ = a·gHi + a·gLo/2⁶⁴.
  have h_expand : a.toNat * (gHi.toNat * 2 ^ 64 + gLo.toNat)
      = a.toNat * gLo.toNat + 2 ^ 64 * (a.toNat * gHi.toNat) := by grind
  rw [h_expand, Nat.add_mul_div_left _ _ (by decide : 0 < 2 ^ 64)]
  rw [Nat.add_comm (a.toNat * gLo.toNat / 2 ^ 64)]
  conv => rhs; rw [Nat.add_mod]
  simp

end Srtfp.Schubfach

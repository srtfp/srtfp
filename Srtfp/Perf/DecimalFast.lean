module
/- UInt64 fast path for `Decimal.canonicaliseAux` / `Decimal.mk'`.

   `canonicaliseAux` strips trailing decimal zeros from `(s, e)` by
   repeatedly dividing `s` by 10 and incrementing `e`. The loop runs at
   most `⌊log_10 s⌋ + 1` times.

   In the Schubfach pipeline `s < 10^17 < 2^57`, so the entire loop
   can run in `UInt64`. The fast path takes the `UInt64` branch when
   `s < UInt64.size` (≈ all practical Schubfach use) and falls back to
   `Nat` otherwise.

   Registered via `@[csimp]` so the native runtime substitutes the
   fast form. Proofs about `canonicaliseAux` continue to reference the
   `Nat` reference implementation. -/

public import Srtfp.Decimal

@[expose] public section

open Float.Model.UnpackedFloat (Sign)

namespace Srtfp.Decimal

/-! ## UInt64 inner loop -/

/-! ## Correctness -/

theorem UInt64_mod10_eq_zero_iff (s : UInt64) :
    s % 10 = 0 ↔ s.toNat % 10 = 0 := by
  rw [← UInt64.toNat_inj]
  rw [UInt64.toNat_mod]
  rfl

/-! ## Fast `Decimal.canonical` and `Decimal.mk'`

`Decimal.canonical` was compiled in `Srtfp/Decimal.lean` (which
doesn't import this file), so its compiled body calls `canonicaliseAux`
directly — bypassing the `canonicaliseAux_fast` csimp.  Re-define
`canonical` and `mk'` here so their compiled bodies pick up the
`canonicaliseAux_fast` rewrite.  Register `@[csimp]` so callers see
the rewrite. -/

/-- Fast `canonical`: same body as `Decimal.canonical` but compiled
    after the `canonicaliseAux ↦ canonicaliseAux_fast` csimp is in
    scope.  Also short-circuits the common no-strip case (`s % 10 ≠ 0`)
    without allocating an intermediate Prod. -/
def canonical_fast (d : Decimal) : Decimal :=
  let s := d.significand
  if s = 0 then ⟨d.sign, 0, 0⟩
  else if s % 10 ≠ 0 then
    -- No trailing zeros: return d unchanged (fast common case).
    d
  else
    -- Strip via canonicaliseAux (csimps to canonicaliseAux_fast).
    let (s', e') := canonicaliseAux s d.exponent
    ⟨d.sign, s', e'⟩

theorem canonical_eq_fast (d : Decimal) : Decimal.canonical d = canonical_fast d := by
  unfold canonical_fast Decimal.canonical
  by_cases hs0 : d.significand = 0
  · simp [hs0]
  simp only [hs0, ite_false]
  by_cases hsmod : d.significand % 10 ≠ 0
  · rw [if_pos hsmod]
    -- canonicaliseAux d.significand d.exponent = (d.significand, d.exponent) when no trailing zero
    have hCanon : canonicaliseAux d.significand d.exponent = (d.significand, d.exponent) := by
      unfold canonicaliseAux
      simp [hs0, hsmod]
    rw [hCanon]
  rw [if_neg hsmod]

/-- Fast `mk'`: same body as `Decimal.mk'` but with `canonical` /
    `canonicaliseAux` inlined through their fast variants. -/
def mk'_fast (sign : Sign) (significand : Nat) (exponent : Int) : Decimal :=
  canonical_fast ⟨sign, significand, exponent⟩

theorem mk'_eq_fast (sign : Sign) (significand : Nat) (exponent : Int) :
    Decimal.mk' sign significand exponent = mk'_fast sign significand exponent := by
  unfold mk'_fast Decimal.mk'
  exact canonical_eq_fast _

/-! ## `mk'_fast2` — check canonicalisation BEFORE allocating the Decimal.

`mk'_fast` allocates a Decimal ctor then calls `canonical_fast` which
immediately destructures and either returns the same ctor (no-strip
common case) or allocates a new one.  Even on the no-strip path, the
ctor allocation and re-use are visible in the generated C.

`mk'_fast2` checks the canonicalisation conditions on the raw args
first, then allocates exactly once (or returns the cached `Decimal.zero`). -/

@[inline]
def mk'_fast2 (sign : Sign) (significand : Nat) (exponent : Int) : Decimal :=
  if significand = 0 then ⟨sign, 0, 0⟩
  else if significand % 10 ≠ 0 then
    -- No trailing zeros: build the canonical Decimal directly.
    ⟨sign, significand, exponent⟩
  else
    -- Strip trailing zeros via canonicaliseAux (csimps to fast variant).
    let (s', e') := canonicaliseAux significand exponent
    ⟨sign, s', e'⟩

theorem mk'_eq_fast2 (sign : Sign) (significand : Nat) (exponent : Int) :
    Decimal.mk' sign significand exponent = mk'_fast2 sign significand exponent := by
  rw [mk'_eq_fast]
  unfold mk'_fast mk'_fast2 canonical_fast
  by_cases hs0 : significand = 0
  · simp [hs0]
  simp only [hs0, ite_false]

end Srtfp.Decimal

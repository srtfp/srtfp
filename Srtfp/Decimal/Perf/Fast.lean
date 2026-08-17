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

import Srtfp.Decimal

namespace Srtfp.Decimal

/-! ## UInt64 inner loop -/

/-- Strip trailing zeros from `(s, e)` using `UInt64` arithmetic.
    `fuel = 64` suffices: each iteration at least halves `s`, and
    `s < 2^64` ⇒ ≤ 64 iterations.
    The `s = 0` branch resets `e` to `0` (matches the `Nat` reference). -/
def canonicaliseAuxU64 : Nat → UInt64 → Int → UInt64 × Int
  | 0, s, e => if s = 0 then (0, 0) else (s, e)
  | fuel + 1, s, e =>
    if s = 0 then (0, 0)
    else if s % 10 = 0 then canonicaliseAuxU64 fuel (s / 10) (e + 1)
    else (s, e)

/-- Fast variant of `canonicaliseAux`: dispatch on whether the input
    fits in `UInt64`. The `UInt64` branch terminates in ≤ 20 iterations
    (we allocate 64 fuel — runtime cost negligible, proof simpler).

    The common case in practice is "no trailing zeros to strip": `s = 0`
    (the shortcut returns `(0, 0)` directly) or `s % 10 ≠ 0` (we return
    `(s, e)` directly).  We check these in `Nat` before paying for the
    `Nat ↔ UInt64` round-trip. -/
def canonicaliseAux_fast (s : Nat) (e : Int) : Nat × Int :=
  -- Common-case shortcut: 0 iterations of the strip loop.
  if s = 0 then (0, 0)
  else if s % 10 ≠ 0 then (s, e)
  else if _h : s < UInt64.size then
    let p := canonicaliseAuxU64 64 (UInt64.ofNat s) e
    (p.1.toNat, p.2)
  else
    canonicaliseAux s e

/-! ## Correctness -/

private theorem UInt64_eq_zero_iff (s : UInt64) : s = 0 ↔ s.toNat = 0 := by
  constructor
  · intro h; rw [h]; rfl
  · intro h
    rw [← UInt64.toNat_inj, h]; rfl

private theorem UInt64_mod10_eq_zero_iff (s : UInt64) :
    s % 10 = 0 ↔ s.toNat % 10 = 0 := by
  rw [← UInt64.toNat_inj]
  rw [UInt64.toNat_mod]
  rfl

/-- The `UInt64` loop matches the `Nat` loop on `(toNat, e)`,
    provided fuel suffices. -/
private theorem canonicaliseAuxU64_eq
    (fuel : Nat) (s : UInt64) (e : Int) (hbound : s.toNat ≤ 2^fuel) :
    let p := canonicaliseAuxU64 fuel s e
    (p.1.toNat, p.2) = canonicaliseAux s.toNat e := by
  induction fuel generalizing s e with
  | zero =>
    have h1 : s.toNat ≤ 1 := by simpa using hbound
    unfold canonicaliseAuxU64 canonicaliseAux
    by_cases hs0 : s = 0
    · have hs0n : s.toNat = 0 := (UInt64_eq_zero_iff s).mp hs0
      simp [hs0]
    · have hs0n : s.toNat ≠ 0 := fun h => hs0 ((UInt64_eq_zero_iff s).mpr h)
      have hs1 : s.toNat = 1 := by omega
      have hsmod : s.toNat % 10 ≠ 0 := by rw [hs1]; decide
      simp [hs0, hs0n, hsmod]
  | succ n ih =>
    unfold canonicaliseAuxU64 canonicaliseAux
    by_cases hs0 : s = 0
    · have hs0n : s.toNat = 0 := (UInt64_eq_zero_iff s).mp hs0
      simp [hs0]
    · have hs0n : s.toNat ≠ 0 := fun h => hs0 ((UInt64_eq_zero_iff s).mpr h)
      by_cases hmod : s % 10 = 0
      · have hmodNat : s.toNat % 10 = 0 := (UInt64_mod10_eq_zero_iff s).mp hmod
        have hdiv : (s / 10).toNat = s.toNat / 10 := UInt64.toNat_div s 10
        have hbound_dec : (s / 10).toNat ≤ 2^n := by
          rw [hdiv]
          have h_div_le : s.toNat / 10 ≤ s.toNat / 2 :=
            Nat.div_le_div_left (by decide) (by decide)
          have h_div2 : s.toNat / 2 ≤ 2^n := by
            have : s.toNat ≤ 2 * 2^n := by
              have h2p : 2^(n+1) = 2 * 2^n := by grind
              omega
            omega
          omega
        simp only [hs0, hmod, hs0n, hmodNat, if_false, if_true]
        have := ih (s / 10) (e + 1) hbound_dec
        rw [hdiv] at this
        exact this
      · have hmodNat : s.toNat % 10 ≠ 0 := fun h => hmod ((UInt64_mod10_eq_zero_iff s).mpr h)
        simp [hs0, hs0n, hmod, hmodNat]

theorem canonicaliseAux_eq_fast (s : Nat) (e : Int) :
    canonicaliseAux s e = canonicaliseAux_fast s e := by
  unfold canonicaliseAux_fast
  -- Shortcut: s = 0
  by_cases hs0 : s = 0
  · rw [if_pos hs0]
    unfold canonicaliseAux
    simp [hs0]
  rw [if_neg hs0]
  -- Shortcut: s % 10 ≠ 0 → 0 iterations
  by_cases hsmod_ne : s % 10 ≠ 0
  · rw [if_pos hsmod_ne]
    unfold canonicaliseAux
    simp [hs0, hsmod_ne]
  have hsmod_ne : s % 10 = 0 := by omega
  rw [if_neg (by simp [hsmod_ne])]
  -- Main path: dispatch on UInt64 fit
  split
  · rename_i h
    have h_toNat : (UInt64.ofNat s).toNat = s :=
      UInt64.toNat_ofNat_of_lt' h
    have h_bound : (UInt64.ofNat s).toNat ≤ 2^64 := by
      rw [h_toNat]
      have hsize : UInt64.size = 2^64 := by decide
      have : s < UInt64.size := h
      omega
    have key := canonicaliseAuxU64_eq 64 (UInt64.ofNat s) e h_bound
    simp only at key
    rw [h_toNat] at key
    rw [← key]
  · rfl

@[csimp]
theorem canonicaliseAux_eq_fast_csimp :
    @canonicaliseAux = @canonicaliseAux_fast := by
  funext s e
  exact canonicaliseAux_eq_fast s e

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

@[csimp]
theorem canonical_eq_fast_csimp : @Decimal.canonical = @canonical_fast := by
  funext d
  exact canonical_eq_fast d

/-- Fast `mk'`: same body as `Decimal.mk'` but with `canonical` /
    `canonicaliseAux` inlined through their fast variants. -/
def mk'_fast (sign : Bool) (significand : Nat) (exponent : Int) : Decimal :=
  canonical_fast ⟨sign, significand, exponent⟩

theorem mk'_eq_fast (sign : Bool) (significand : Nat) (exponent : Int) :
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
def mk'_fast2 (sign : Bool) (significand : Nat) (exponent : Int) : Decimal :=
  if significand = 0 then ⟨sign, 0, 0⟩
  else if significand % 10 ≠ 0 then
    -- No trailing zeros: build the canonical Decimal directly.
    ⟨sign, significand, exponent⟩
  else
    -- Strip trailing zeros via canonicaliseAux (csimps to fast variant).
    let (s', e') := canonicaliseAux significand exponent
    ⟨sign, s', e'⟩

theorem mk'_eq_fast2 (sign : Bool) (significand : Nat) (exponent : Int) :
    Decimal.mk' sign significand exponent = mk'_fast2 sign significand exponent := by
  rw [mk'_eq_fast]
  unfold mk'_fast mk'_fast2 canonical_fast
  by_cases hs0 : significand = 0
  · simp [hs0]
  simp only [hs0, ite_false]

@[csimp]
theorem mk'_eq_fast2_csimp : @Decimal.mk' = @mk'_fast2 := by
  funext sign sig exp
  exact mk'_eq_fast2 sign sig exp

end Srtfp.Decimal

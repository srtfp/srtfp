module
/- Table-driven refinements of the two reference kernels
   `Schubfach.cmpScaledMixed` and `Schubfach.shiftedSig`.

   The reference forms clear denominators with `Nat.pow` and compare or
   divide big `Nat`s (operands up to ~1100 bits). Two refinements, each
   a total function equal to its reference on every input:

     - `_fast`:  the same arithmetic with `2^n` / `10^n` fetched from the
                 tables in `Pow10Table.lean` (`pow2Lookup_eq` /
                 `pow10Lookup_eq` make the equalities one-liners here);
     - `_fast2`: Schubfach's fixed-precision multiply-shift (§9.6–9.8).
                 A 128-bit ceiling approximation `G = ⌈10^k · 2^h⌉` from
                 `Pow10Table128.lean` turns `b · 10^k` into one 64×128
                 multiply, and the comparison / floor is taken on 192-bit
                 `UInt64` triples. Inputs outside the envelope the proof
                 covers fall back to `_fast`, which keeps the function
                 total and exact.

   The `_fast2` equalities need the table-precision argument; they are
   proven in `Kernel128.lean`, which also registers both as `@[csimp]`
   so natively compiled code runs the `UInt64` kernels. -/

public import Srtfp.Perf.Schubfach
public import Srtfp.Perf.MulHigh128
public import Srtfp.Perf.Pow10Table
public import Srtfp.Perf.Pow10Table128

@[expose] public section

namespace Srtfp.Schubfach

/-! ## Table lookups in place of `Nat.pow` -/

/-- Memoized variant of `cmpScaledMixed`: `2^n` and `10^n` are looked up
    from precomputed tables (with fallback) instead of recomputed.
    Functionally identical to `cmpScaledMixed`. -/
def cmpScaledMixed_fast (a : Int) (q : Int) (b : Int) (k : Int) : Int :=
  let qPos : Nat := if q ≥ 0 then q.toNat else 0
  let qNeg : Nat := if q < 0 then (-q).toNat else 0
  let kPos : Nat := if k ≥ 0 then k.toNat else 0
  let kNeg : Nat := if k < 0 then (-k).toNat else 0
  let lhs : Int := a * (pow2Lookup qPos : Int) * (pow10Lookup kNeg : Int)
  let rhs : Int := b * (pow10Lookup kPos : Int) * (pow2Lookup qNeg : Int)
  if lhs < rhs then -1 else if lhs = rhs then 0 else 1

theorem cmpScaledMixed_eq_fast (a : Int) (q : Int) (b : Int) (k : Int) :
    cmpScaledMixed a q b k = cmpScaledMixed_fast a q b k := by
  unfold cmpScaledMixed cmpScaledMixed_fast
  simp only [pow2Lookup_eq, pow10Lookup_eq]
  push_cast
  rfl

/-- Memoized variant of `shiftedSig`: `2^n` and `10^n` are looked up from
    precomputed tables (with fallback) instead of recomputed. -/
def shiftedSig_fast (m : Nat) (q : Int) (k : Int) : Nat :=
  let qPos : Nat := if q ≥ 0 then q.toNat else 0
  let qNeg : Nat := if q < 0 then (-q).toNat else 0
  let kPos : Nat := if k ≥ 0 then k.toNat else 0
  let kNeg : Nat := if k < 0 then (-k).toNat else 0
  (m * pow2Lookup qPos * pow10Lookup kNeg) / (pow2Lookup qNeg * pow10Lookup kPos)

/-- Functional equivalence of the fast variant. Holds for **all** inputs
    (the lookups fall back to `Nat.pow` outside the tabulated range), so
    no range hypothesis is needed. -/
theorem shiftedSig_eq_fast (m : Nat) (q k : Int) :
    shiftedSig m q k = shiftedSig_fast m q k := by
  unfold shiftedSig shiftedSig_fast
  simp only [pow2Lookup_eq, pow10Lookup_eq]

/-! ## `cmpScaledMixed` by multiply-shift

`cmpScaledMixed_fast2` compares `L = a · 2^{q+h}` (a shift) against
`R = b · G` (one 64×128 multiply), both as 192-bit `(hi, mid, lo)`
triples of `UInt64`. For the `(q, k)` pairs `kOfMQ` produces,
`q + h ∈ [124, 134]`, so nothing here needs a `Nat`.

Because `G` over-approximates `10^k · 2^h` by less than 1, the strict
verdicts are exact whenever `L` is more than `b` away from `R`:
`L > R` gives `+1`, `L + b ≤ R` gives `-1`. In the remaining window
`R - b < L ≤ R` the function defers to `cmpScaledMixed_fast`. -/

/-- `(hi₁, mid₁, lo₁) > (hi₂, mid₂, lo₂)` as unsigned 192-bit. -/
@[inline]
def gt192 (hi₁ mid₁ lo₁ hi₂ mid₂ lo₂ : UInt64) : Bool :=
  if hi₁ ≠ hi₂ then hi₁ > hi₂
  else if mid₁ ≠ mid₂ then mid₁ > mid₂
  else lo₁ > lo₂

/-- `(hi₁, mid₁, lo₁) ≤ (hi₂, mid₂, lo₂)` as unsigned 192-bit. -/
@[inline]
def le192 (hi₁ mid₁ lo₁ hi₂ mid₂ lo₂ : UInt64) : Bool :=
  if hi₁ ≠ hi₂ then hi₁ < hi₂
  else if mid₁ ≠ mid₂ then mid₁ < mid₂
  else lo₁ ≤ lo₂

/-- Add a 64-bit value to a 192-bit `(hi, mid, lo)` triple.  Returns the
    new `(hi, mid, lo)` triple.  Overflow (i.e. the carry into bit 192)
    is silently dropped, which is fine for our use because `a · 2^{q+h}`
    and `b · G + b` both fit in well under 192 bits. -/
@[inline]
def add192_64 (hi mid lo : UInt64) (x : UInt64) : UInt64 × UInt64 × UInt64 :=
  let lo' := lo + x
  let c0 : UInt64 := if lo' < lo then 1 else 0
  let mid' := mid + c0
  let c1 : UInt64 := if c0 = 1 ∧ mid' < mid then 1 else 0
  let hi' := hi + c1
  (hi', mid', lo')

/-- Multiply-shift refinement of `cmpScaledMixed` using pure UInt64
    arithmetic on the fast path.  The 128-bit pow10 table is consulted to
    obtain `(gHi, gLo, h)`; we then compute the 192-bit values
    `R = b · (gHi · 2^64 + gLo)` and `L = a · 2^{q+h}` directly as triples
    of UInt64s, avoiding `Nat` allocation entirely.

    Functionally equivalent to `cmpScaledMixed` for the inputs Schubfach
    actually produces (binary64 mantissa range, `kOfMQ`-derived `k`).
    The strict-verdict branches return values that match the true sign of
    `a · 2^q - b · 10^k`; an ambiguous fallback defers to the exact slow
    path so the function is total. -/
def cmpScaledMixed_fast2 (a : Int) (q : Int) (b : Int) (k : Int) : Int :=
  -- The kernel handles `a, b` representable as UInt64 with `k` in the
  -- tabulated binary64 range; everything else degrades to the exact
  -- table-lookup path.
  if a < 0 ∨ b < 0 then cmpScaledMixed_fast a q b k
  -- The strict-verdict `-1` branch uses the bound `b·g - b < b·10^k·2^h`,
  -- which only holds when `b > 0`.  When `b = 0`, fall back to the
  -- exact path (it returns immediately: 0 < 0 vs 0 = 0).  In
  -- production this branch never fires (Schubfach's `b` is always ≥ 1),
  -- but the equivalence is stated for all inputs, so the check is needed.
  else if b = 0 then cmpScaledMixed_fast a q b k
  else if a ≥ (1 <<< 60 : Int) ∨ b ≥ (1 <<< 60 : Int) then
    -- Defensive: `a, b` exceed binary64 mantissa scale; fall back.
    cmpScaledMixed_fast a q b k
  else if k < pow10Table128_kMin ∨ k > pow10Table128_kMax then
    cmpScaledMixed_fast a q b k
  else
    let (gHi, gLo, h) := pow10Lookup128 k
    let qPlusH : Int := q + h
    -- The Schubfach table is tuned so `q+h ∈ [124, 134]` for k = kOfMQ.
    if qPlusH < 64 ∨ qPlusH ≥ 192 then cmpScaledMixed_fast a q b k
    else
      -- a, b fit in UInt64 by guard above
      let aU : UInt64 := UInt64.ofNat a.toNat
      let bU : UInt64 := UInt64.ofNat b.toNat
      -- Compute R = b · (gHi · 2^64 + gLo) as a 192-bit (hi, mid, lo) triple.
      let rLo  : UInt64 := bU * gLo
      let rLoH : UInt64 := mulHi64 bU gLo
      let rHi  : UInt64 := bU * gHi
      let rHiH : UInt64 := mulHi64 bU gHi
      -- R = (rHiH·2^64 + rHi)·2^64 + (rLoH·2^64 + rLo)
      --   = rHiH·2^128 + rHi·2^64 + rLoH·2^64 + rLo
      --   = rHiH·2^128 + (rHi + rLoH)·2^64 + rLo  [w/ possible carry]
      let midSum : UInt64 := rHi + rLoH
      let midCarry : UInt64 := if midSum < rHi then 1 else 0
      let r192_hi  : UInt64 := rHiH + midCarry
      let r192_mid : UInt64 := midSum
      let r192_lo  : UInt64 := rLo
      -- The hi-branch shift `aU <<< s64` requires `aU < 2^(64-s64)` to
      -- avoid silent UInt64 overflow.  With the `a < 2^60` guard above,
      -- this holds for `s64 ≤ 4`, i.e., `qPlusH ≤ 132`.  Schubfach's
      -- actual `q+h` for binary64 is in `[124, 134]`; for `qPlusH ∈
      -- {133, 134}` we fall back to the exact path.  (In production
      -- this is rare: only `m ≥ 2^58` triggers the upper end of the
      -- range, and even then the fallback is correct.)
      if qPlusH > 132 then cmpScaledMixed_fast a q b k
      else
      -- Compute L = a · 2^{q+h} as 192-bit (l_hi, l_mid, l_lo).
      let s : UInt64 := UInt64.ofNat qPlusH.toNat   -- in [64, 132]
      let l192 : UInt64 × UInt64 × UInt64 :=
        if s < 64 then
          (0, mulHi64 aU (1 <<< s), aU <<< s)
        else if s < 128 then
          let s64 := s - 64
          if s64 = 0 then (0, aU, 0)
          else (aU >>> (64 - s64), aU <<< s64, 0)
        else  -- 128 ≤ s ≤ 132 ⇒ s64 ∈ [0, 4]
          let s64 := s - 128
          if s64 = 0 then (aU, 0, 0)
          else (aU <<< s64, 0, 0)  -- aU < 2^60 < 2^(64-s64), no overflow
      let (l_hi, l_mid, l_lo) := l192
      -- Strict verdicts:
      --   • L > R       ⇒  +1                      (skip computing L+b)
      --   • L + b ≤ R   ⇒  -1
      --   • otherwise   ⇒  ambiguous, defer to slow path
      if gt192 l_hi l_mid l_lo r192_hi r192_mid r192_lo then 1
      else
        let (lpb_hi, lpb_mid, lpb_lo) := add192_64 l_hi l_mid l_lo bU
        if le192 lpb_hi lpb_mid lpb_lo r192_hi r192_mid r192_lo then -1
      else cmpScaledMixed_fast a q b k

/-! ## `shiftedSig` by multiply-shift

`shiftedSig_fast2` evaluates `⌊m · 2^q · 10^{-k}⌋` as
`⌊m · G · 2^{q-h}⌋` with `G` the 128-bit table entry for `10^{-k}`:
one 64×128 → 192 multiply, a right shift, and the low word. The
guards keep the kernel inside the regime where that floor provably
equals the reference floor (`shiftedSig_floor_safe` in
`KernelCorrectness.lean`); everything else falls back to
`shiftedSig_fast`. -/

/-- Multiply-shift refinement of `shiftedSig`.  Uses the 128-bit pow10
    table at index `-k` so `m · 2^q · 10^{-k} ≈ m · G · 2^{q - h}`.

    Safe-regime guard `B = 2^qNeg · 10^kPos < 2^64`: outside it the
    floor of the UInt64 kernel is not known to match the reference
    floor, so the kernel falls back. -/
def shiftedSig_fast2 (m : Nat) (q : Int) (k : Int) : Nat :=
  -- Fast path: m fits in UInt64, the -k lookup is in range, and the
  -- final shift is non-positive and fits in [0, 192).
  if m ≥ (1 <<< 60 : Nat) then shiftedSig_fast m q k
  else
    let kLookup : Int := -k
    if kLookup < pow10Table128_kMin ∨ kLookup > pow10Table128_kMax then
      shiftedSig_fast m q k
    else
      let (gHi, gLo, h) := pow10Lookup128 kLookup
      let shiftAmt : Int := h - q   -- shift = -(q - h); shift right by this many bits
      -- We require `shiftAmt ≥ 124` so that `(m · G) / 2^shiftAmt < 2^64`
      -- (`m < 2^60`, `G < 2^128` ⇒ `m · G < 2^188`).  Without this lower
      -- guard the kernel's UInt64 output would silently truncate the spec.
      if shiftAmt < 124 ∨ shiftAmt ≥ 192 then shiftedSig_fast m q k
      else
        -- Safe-regime guard: `B = 2^qNeg · 10^kPos < 2^64` combined with
        -- `m < 2^60` and `s ≥ 124` gives `m · B < 2^124 ≤ 2^s`.  In that
        -- regime the UInt64 kernel floor provably equals the spec floor
        -- via `shiftedSig_floor_safe`.  Outside the regime (very large
        -- denormals or extreme exponents) we fall back to the exact
        -- `shiftedSig_fast` so the function remains a total refinement.
        let qNeg : Nat := if q < 0 then (-q).toNat else 0
        let kPos : Nat := if k ≥ 0 then k.toNat else 0
        let B : Nat := 2 ^ qNeg * 10 ^ kPos
        if B ≥ (1 <<< 64 : Nat) then shiftedSig_fast m q k
        else
        let mU : UInt64 := UInt64.ofNat m
        -- Compute R = m · (gHi · 2^64 + gLo) as a 192-bit (rHi, rMid, rLo) triple.
        let pLo  : UInt64 := mU * gLo
        let pLoH : UInt64 := mulHi64 mU gLo
        let pHi  : UInt64 := mU * gHi
        let pHiH : UInt64 := mulHi64 mU gHi
        let midSum   : UInt64 := pHi + pLoH
        let midCarry : UInt64 := if midSum < pHi then 1 else 0
        let rHi  : UInt64 := pHiH + midCarry
        let rMid : UInt64 := midSum
        let rLo  : UInt64 := pLo
        -- Shift right by `shiftAmt` bits; extract the lower 64 bits of the result.
        let s : UInt64 := UInt64.ofNat shiftAmt.toNat
        let resU : UInt64 :=
          if s < 64 then
            -- Result low 64 = (rLo >> s) | (rMid << (64-s)), with care for s=0.
            if s = 0 then rLo
            else (rLo >>> s) ||| (rMid <<< (64 - s))
          else if s < 128 then
            let s64 := s - 64
            if s64 = 0 then rMid
            else (rMid >>> s64) ||| (rHi <<< (64 - s64))
          else  -- 128 ≤ s < 192
            let s64 := s - 128
            rHi >>> s64
        resU.toNat

end Srtfp.Schubfach

/- Schubfach printer — Float → Decimal.

   Full implementation of the Schubfach algorithm (Giulietti, 2021):
   `~/acs/project/research/Schubfach-Giulietti-2021.pdf`. Produces the
   round-trip-shortest decimal representation of any binary64 input.

   Round-trip correctness (`Schubfach.toDecimal` followed by Clinger's
   decimal-to-float yields the original `Float`) and cross-scale
   minimality (Schubfach §6) are proven; the multiply-shift error bound
   (§9.6–9.8) is mechanised in `Perf/Kernel192Correctness.lean`.

   Pieces of the pipeline:

     - `PP/Numeric/Float/Bits.lean` — bit-level decomposition of a
       `Float` into `Decoded { sign, m, q }`.
     - This file — magic-constant R14/R15 approximations of
       `⌊log_10(2^q)⌋` and `⌊log_10(3/4 · 2^q)⌋`, the reference
       multiply-shift kernel, and `Schubfach.toDecimal` proper.
     - `Pow10Table.lean` / `Pow10Table128.lean` — precomputed pow-tables.
     - `KernelCorrectness.lean` — sandwich lemmas + correctness theory.
     - `Perf/` — verified runtime fast paths (csimp). Removing
       `Perf/` leaves the reference impl intact (~6× slower).

   ## Correctness

   The single user-facing theorem is `PP.Numeric.Spec.correct_iff_toDecimal`
   in `PP/Proofs/Numeric/Correctness.lean`. It states: for any finite,
   nonzero binary64 float `f`, `Schubfach.toDecimal f` is the unique
   canonical `Decimal` satisfying (1) round-trip via Clinger, (2) shortest
   digit count, and (3) the closer-to-`f` tie-breaking rule (with
   round-half-to-even on exact midpoints). NaN/Infinity yield `.error`;
   ±0 yields the canonical zero Decimal.

   The proof composes the following sub-milestones (all proven, axiom-clean,
   zero `sorry`):

     - M3.8.1 (`R14R15.lean`)             — magic-constant correctness
     - M3.8.2 (`RoundingInterval.lean`)   — `R_v` rounding interval
     - M3.8.3 (`K.lean`)                  — `kOfMQ` correctness
     - M3.8.4 (`ShiftedSig.lean`)         — `shiftedSig` correctness
     - M3.8.5 (`PickNearer.lean`)         — tie-breaker correctness
     - M3.8.6 (`Shorter.lean`)            — shorter-form selection
     - M3.8.7 (`ToDecimal.lean`)          — `toDecimal` output in `R_v`
     - M3.8.8 (`Shortest.lean`)           — K+1 minimality pigeonhole
     - M3.8.9 (`Minimal.lean`)            — full cross-scale minimality
     - Round-trip (`RoundTrip.lean`)      — `Clinger ∘ Schubfach = id` -/

import Srtfp.Numeric.Decimal
import Srtfp.Numeric.Decimal.Perf.Fast
import Srtfp.Numeric.Float.Bits
import Srtfp.Numeric.Schubfach.MulHigh128
import Srtfp.Numeric.Schubfach.Pow10Table
import Srtfp.Numeric.Schubfach.Pow10Table128

namespace PP.Numeric.Schubfach

open PP.Numeric.Float

/-! ## §9.1 magic-constant approximations of floor-log

These give exact integer values within proven ranges (Schubfach R14/R15).
Binary64's full `q ∈ [-1074, 971]` is comfortably inside both. -/

/-- The shift exponent `Q` from Schubfach R14/R15. Both `floorLog10Pow2` and
    `floorLog10ThreeQuartersPow2` use the same shift width for D = 10. -/
def shiftQ : Nat := 41

/-- `⌊2^41 · log_10(2)⌋`. Magic constant from Schubfach R14 / R15. -/
def constC : Int := 661971961083

/-- `⌊2^41 · log_10(3/4)⌋`. Magic constant from Schubfach R14. -/
def constA : Int := -274743187321

/-- `⌊log_10(2^e)⌋` via R15. Valid for `e ∈ [-6432162, 6432162]`. -/
@[inline]
def floorLog10Pow2 (e : Int) : Int :=
  Int.fdiv (e * constC) (2 ^ shiftQ)

/-- `⌊log_10(3/4 · 2^e)⌋` via R14. Valid for `e ∈ [-3606689, 3150619]`. -/
@[inline]
def floorLog10ThreeQuartersPow2 (e : Int) : Int :=
  Int.fdiv (e * constC + constA) (2 ^ shiftQ)

/-! ## §5 spacing classification

The rounding interval `R_v` has *regular* spacing (width `2^q`) except when
`v` is a normal number whose significand is exactly `2^{P-1}` and whose
binary exponent is strictly above `Q_min`. In that one case `v`'s predecessor
is closer than its successor, so `R_v` has width `3·2^q/4` (Schubfach §5,
eq. (2) / Result 11 setup). -/

/-- For binary64: precision `P = 53`, so the boundary mantissa is `2^{P-1} = 2^52`. -/
def minNormalSignificand : Nat := 1 <<< 52

/-- For binary64: minimum binary exponent `Q_min = -1074`. -/
def minBinaryExp : Int := -1074

/-- `true` iff `(m, q)` represents a value with irregular `R_v` spacing
    (`m = 2^{P-1} ∧ q > Q_min`). -/
def isIrregular (m : Nat) (q : Int) : Bool :=
  m = minNormalSignificand && q > minBinaryExp

/-! ## Schubfach k

`k = ⌊log_D(‖R_v‖)⌋` from R10, computed as either `⌊log_10(2^q)⌋` (regular)
or `⌊log_10(3/4 · 2^q)⌋` (irregular). -/

/-- Compute Schubfach's `k` from the decoded `(m, q)` of a finite Float. -/
def kOfMQ (m : Nat) (q : Int) : Int :=
  if isIrregular m q then
    floorLog10ThreeQuartersPow2 q
  else
    floorLog10Pow2 q

/-- Compute Schubfach's `k` directly from a `Float`. The result is meaningful
    only for finite values; NaN / Infinity should be filtered upstream. -/
def kOfFloat (f : _root_.Float) : Int :=
  let d := decode f
  kOfMQ d.m d.q

/-! ## M3.3+ Multiply-shift and tie-breaking

The reference Schubfach implementation uses a precomputed table of 18-digit
approximations to `10^{-k}` (§9.8) to bound the multiply-shift step to
fixed-precision integer arithmetic.  Our pipeline lands this in stages:

  - **Stage 1** (`cmpScaledMixed` / `shiftedSig`, this file): direct
    `Nat` arithmetic.  Operand sizes stay below ~1100 bits, slow at
    runtime but trivially correct.
  - **Stage 2** (`cmpScaledMixed_fast` / `shiftedSig_fast`,
    `Pow10Table.lean` + `@[csimp]`): replace `Nat.pow` with O(1) array
    lookups.  ~34 % faster.
  - **Stage 3** (`MulHigh128.lean`, infrastructure): proven 64×128 →
    high-64 multiply-shift kernel.  Not yet wired into
    `cmpScaledMixed` — the remaining work is the 128-bit pow10 table
    and the comparator using `mulHigh128`. -/

/-- Compare `a · 2^q` vs `b · 10^k` as rationals; returns `-1`, `0`, `1`.
    Implemented by clearing both denominators with the common factor
    `2^{max(-q,0)} · 10^{max(-k,0)}`. -/
def cmpScaledMixed (a : Int) (q : Int) (b : Int) (k : Int) : Int :=
  let qPos : Nat := if q ≥ 0 then q.toNat else 0
  let qNeg : Nat := if q < 0 then (-q).toNat else 0
  let kPos : Nat := if k ≥ 0 then k.toNat else 0
  let kNeg : Nat := if k < 0 then (-k).toNat else 0
  -- a · 2^q vs b · 10^k
  -- ↔ a · 2^{max(q,0)} · 10^{max(-k,0)} vs b · 10^{max(k,0)} · 2^{max(-q,0)}
  let lhs : Int := a * (2 ^ qPos : Int) * (10 ^ kNeg : Int)
  let rhs : Int := b * (10 ^ kPos : Int) * (2 ^ qNeg : Int)
  if lhs < rhs then -1 else if lhs = rhs then 0 else 1

/-- `⌊m · 2^q · 10^{-k}⌋` as a `Nat`. Used to compute `s` in Schubfach. -/
def shiftedSig (m : Nat) (q : Int) (k : Int) : Nat :=
  let qPos : Nat := if q ≥ 0 then q.toNat else 0
  let qNeg : Nat := if q < 0 then (-q).toNat else 0
  let kPos : Nat := if k ≥ 0 then k.toNat else 0
  let kNeg : Nat := if k < 0 then (-k).toNat else 0
  -- m · 2^q · 10^{-k} = (m · 2^{max(q,0)} · 10^{max(-k,0)}) / (2^{max(-q,0)} · 10^{max(k,0)})
  (m * 2 ^ qPos * 10 ^ kNeg) / (2 ^ qNeg * 10 ^ kPos)

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

/-! ## Phase 3 runtime refinement of `cmpScaledMixed`

`cmpScaledMixed_fast2` evaluates `b · 10^k` via the precomputed 128-bit
table (`Pow10Table128.lean`) and a single big-Nat multiply by a 128-bit
constant `G`, then compares against `a · 2^{q+h}` (a shift) instead of
materialising the full `a · 2^|q| · 10^|k|` product.

The table stores `G = ⌈10^k · 2^h⌉ ∈ [2^127, 2^128)` per `k`.  For the
inputs `kOfMQ m q` produces, `q + h ∈ [124, 134]`, so both `a · 2^{q+h}`
and `b · G` are short Nats (≤ ~200 bits), avoiding the ~1100-bit GMP
multiplication of the Phase 2 path.

Because `G` over-approximates `10^k · 2^h` by at most 1 (ceiling), the
unscaled comparison reaches a strict verdict whenever
`L = a · 2^{q+h}` is at distance > `b` from `R = b · G` on either side.
For inputs in the small "ambiguous" window `R - b < L ≤ R`, the
function falls back to `cmpScaledMixed_fast` (the Phase 2 path), which
is provably exact.

The dispatch keeps `cmpScaledMixed_fast2` operationally equivalent to
`cmpScaledMixed` on every input.  Proving this rigorously requires the
Schubfach §9.6–9.8 error bound (relating the shifted Nat comparison to
the scaled-rational comparison via the 2^{-127} table-precision
guarantee); we whitelist it as an axiom and prove it on paper, leaving
the fully mechanised version for a follow-up. -/

/-- Compare two 192-bit unsigned values represented as `(hi, mid, lo)`
    UInt64 triples.  Returns `-1`, `0`, or `1`. -/
@[inline]
def cmp192 (hi₁ mid₁ lo₁ hi₂ mid₂ lo₂ : UInt64) : Int :=
  if hi₁ < hi₂ then -1
  else if hi₁ > hi₂ then 1
  else if mid₁ < mid₂ then -1
  else if mid₁ > mid₂ then 1
  else if lo₁ < lo₂ then -1
  else if lo₁ > lo₂ then 1
  else 0

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
  -- Phase-3 fast path only handles `a, b` representable as UInt64 with
  -- `k` in the tabulated binary64 range; everything else degrades to
  -- the exact Phase-2 path.
  if a < 0 ∨ b < 0 then cmpScaledMixed_fast a q b k
  -- The strict-verdict `-1` branch uses the bound `b·g - b < b·10^k·2^h`,
  -- which only holds when `b > 0`.  When `b = 0`, fall back to the
  -- exact path (it returns immediately: 0 < 0 vs 0 = 0).  In
  -- production this branch never fires (Schubfach's `b` is always ≥ 1),
  -- but the axiom is universal so the check is necessary for soundness.
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
      -- R = (rHiH, rHi, 0) << 64 + (rLoH, rLo, 0) wait no
      -- R = (rHi · 2^64 + rLo's hi · 2^0) shift; let me re-derive
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

/- Schubfach §9.6–9.8 multiply-shift correctness, specialised to our
   ceiling-rounded 128-bit table.  The 192-bit product `b · G` deviates
   from `b · 10^k · 2^h` by at most `b`, and the strict-verdict
   decision intervals (`L + b ≤ R` for `-1`, `L > R` for `+1`) carve
   out the cases where the rounding error cannot flip the sign.  In
   the small "ambiguous" interval the function defers to
   `cmpScaledMixed_fast`, so the overall result matches the
   fixed-precision Phase-2 comparison.

   The full mechanised proof is in `PP/Numeric/Schubfach/KernelCorrectness.lean`
   (theorem `cmpScaledMixed_eq_fast2`).  The `@[csimp]` registration
   also lives there. -/

/-! ## Phase 1 runtime refinement of `shiftedSig`

`shiftedSig` recomputes `2^|q|` and `10^|k|` from scratch on each call.
For binary64 inputs `|q| ≤ 1074` and `|k| ≤ 324`, both powers are
tabulated in `PP.Numeric.Schubfach.Pow10Table` and looked up in O(1).

`shiftedSig_fast` is observationally equal to `shiftedSig` (proven via
`pow2Lookup_eq` / `pow10Lookup_eq`) and registered as a `@[csimp]`
replacement so the native-compiled runtime uses the table lookup.

Microbenchmark (`lake exe benchShiftedSig`, 23-value binary64 set,
median of 5 × 2000 iterations, native compilation):

  - baseline (`shiftedSig`, no csimp)   : 627 ns/call
  - tabulated (`shiftedSig_fast`)       : 412 ns/call  (≈34% speedup)

Note: in **interpreted** runs (`#eval` / `lake env lean`) the table
lookup is slower than `Nat.pow` (interpreter overhead per `Array.getD`).
The `@[csimp]` rewrite only kicks in for natively-compiled code paths
(via `lake build` / `lake exe`), which is what production use exercises.

A full UInt64 multiply-shift refinement (eliminating the GMP `Nat`
multiply itself) is Phase 2; that requires proving the multiply-shift
correctness theorem (floor/ceiling reasoning, likely Mathlib-style
analytic infrastructure). -/

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

theorem shiftedSig_eq_fast_thm : @shiftedSig = @shiftedSig_fast := by
  funext m q k
  exact shiftedSig_eq_fast m q k

/-! ## Phase 3 runtime refinement of `shiftedSig`

`shiftedSig_fast2` evaluates `⌊m · 2^q · 10^{-k}⌋` directly in UInt64
arithmetic, using the 128-bit pow10 table (consulted at index `-k`).
For binary64 inputs the shifted product fits in a single UInt64, so the
entire computation is one 64×128 → 192 multiply, a right-shift, and an
extraction — no `Nat` allocations on the hot path.

Functionally identical to `shiftedSig` for binary64 inputs; falls back
to `shiftedSig_fast` whenever the operands escape the fast envelope. -/

/-- Multiply-shift refinement of `shiftedSig`.  Uses the 128-bit pow10
    table at index `-k` so `m · 2^q · 10^{-k} ≈ m · G · 2^{q - h}`.

    Safe-regime guard `B < 2^64`: when `qNeg ≥ 64` or `kPos ≥ 20`,
    `B = 2^qNeg · 10^kPos ≥ 2^64`, falls outside the regime where the
    floor of the UInt64 kernel provably matches the spec floor.  We
    short-circuit on `qNeg + 4·kPos ≥ 64` to avoid materialising large
    `B` values; the equivalent rigorous check is `2 ^ qNeg * 10 ^ kPos
    < 2 ^ 64`, which we use in the proof. -/
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

/- Schubfach §9 multiply-shift correctness for `shiftedSig`: the
   ceiling-rounded 128-bit pow10 table provides enough precision that
   `⌊m · G · 2^{q-h}⌋` matches `⌊m · 2^q · 10^{-k}⌋` for binary64
   inputs.

   The full mechanised proof is in `PP/Numeric/Schubfach/KernelCorrectness.lean`
   (theorem `shiftedSig_eq_fast2`).  The `@[csimp]` registration
   also lives there. -/

/-- Test whether `u = s · 10^k` lies in the rounding interval `R_v` for the
    value `v = m · 2^q`. Endpoint inclusion follows roundTiesToEven (both
    endpoints included iff `m` is even, else both excluded). -/
def inRoundingInterval (s : Nat) (k : Int) (m : Nat) (q : Int) (irregular : Bool) : Bool :=
  -- Endpoints scaled by 4:
  --   regular:   4 · v_ℓ = (4m - 2) · 2^q,  4 · v_r = (4m + 2) · 2^q
  --   irregular: 4 · v_ℓ = (4m - 1) · 2^q,  4 · v_r = (4m + 2) · 2^q
  let m4 : Int := 4 * (m : Int)
  let leftN : Int := if irregular then m4 - 1 else m4 - 2
  let rightN : Int := m4 + 2
  let s4 : Int := 4 * (s : Int)
  let cmpL := cmpScaledMixed leftN q s4 k     -- 4·v_ℓ vs 4·u
  let cmpR := cmpScaledMixed rightN q s4 k    -- 4·v_r vs 4·u
  let cEven := m % 2 = 0
  -- u > v_ℓ (strict) or u = v_ℓ ∧ c even
  let leftOK := cmpL < 0 || (cmpL = 0 && cEven)
  -- u < v_r (strict) or u = v_r ∧ c even
  let rightOK := cmpR > 0 || (cmpR = 0 && cEven)
  leftOK && rightOK

/-- Tie-break between adjacent candidates `s · 10^k` and `(s+1) · 10^k`
    when both (or neither) sit inside `R_v`. Returns the chosen significand
    (either `s` or `s+1`); the caller pairs it with `k + Δk`. -/
def pickNearer (s : Nat) (k : Int) (m : Nat) (q : Int) : Nat :=
  let irregular := isIrregular m q
  let uIn := inRoundingInterval s k m q irregular
  let wIn := inRoundingInterval (s + 1) k m q irregular
  if uIn && !wIn then s
  else if !uIn && wIn then s + 1
  else
    -- Both in R_v (or neither — but neither can't happen by Schubfach R11).
    -- Compare v - u and w - v via 2v ⋚ u + w ↔ 2m · 2^q ⋚ (2s+1) · 10^k.
    -- v - u < w - v ↔ 2v < u + w ↔ v below midpoint ↔ v closer to u.
    let cmp := cmpScaledMixed (2 * (m : Int)) q (2 * (s : Int) + 1) k
    if cmp < 0 then s            -- 2v < u + w, so v closer to u (= s · 10^k)
    else if cmp > 0 then s + 1   -- 2v > u + w, so v closer to w
    else if s % 2 = 0 then s     -- tie, prefer even significand
    else s + 1

/-- Schubfach's "shortest decimal" (variant F1, `M = 1`) for a finite,
    non-zero, unsigned value `v = m · 2^q`. Returns `(sig, exp)` such that
    `v ≈ sig · 10^exp` is the shortest decimal that rounds back to `v`;
    this output is NOT yet stripped of trailing zeros (the caller passes
    it through `Decimal.mk'`). With `M = 1` the §8.2.1 tiny-value
    adjustment is unnecessary. -/
def shortestUnsigned (m : Nat) (q : Int) : Nat × Int :=
  let irregular := isIrregular m q
  let k := kOfMQ m q
  let s := shiftedSig m q k
  -- Try the shorter (length-N-1) form when `s` has at least 2 digits.
  if s ≥ 10 then
    let kHigh := k + 1
    let sHigh := s / 10
    let uIn := inRoundingInterval sHigh kHigh m q irregular
    let wIn := inRoundingInterval (sHigh + 1) kHigh m q irregular
    if uIn then (sHigh, kHigh)
    else if wIn then (sHigh + 1, kHigh)
    else (pickNearer s k m q, k)
  else
    (pickNearer s k m q, k)

/-! ## §8.3 fast path

When `-P < q < 0` and `v ∈ ℤ`, Schubfach skips the multiply-shift entirely
and returns `v / 2^{-q}` directly (R13). We don't bother — the Nat pipeline
handles it. -/

/-! ## Float → Decimal

Top-level entry point. Returns `Except` so callers can refuse NaN / Infinity
(which have no `Decimal` representation under this biparser). -/

/-- Render a finite `Float` as its shortest round-trip `Decimal`. Returns
    `.error _` for NaN and Infinity. -/
def toDecimal (f : _root_.Float) : Except String Decimal :=
  if isNaNBits f then
    .error "NaN"
  else if isInfBits f then
    .error (if signBit f then "-Infinity" else "Infinity")
  else
    let d := decode f
    if d.m = 0 then .ok ⟨d.sign, 0, 0⟩
    else
      let (sig, exp) := shortestUnsigned d.m d.q
      .ok (Decimal.mk' d.sign sig exp)

end PP.Numeric.Schubfach

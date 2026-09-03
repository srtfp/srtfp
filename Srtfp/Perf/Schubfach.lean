module
/- Schubfach printer — binary64 word → shortest round-trip `Decimal`.

   The reference implementation of the Schubfach algorithm (Raffaello
   Giulietti, "The Schubfach way to render doubles", 2021), variant F1
   with `M = 1`: for every finite, non-zero binary64 value it returns
   the decimal with the fewest significant digits that reads back to
   the same value, choosing the closer candidate (ties to even) when
   several are equally short.

   Everything is unbounded `Nat`/`Int` arithmetic; the only concession
   to speed is Schubfach's magic-constant floor-log (R14/R15), which the
   paper proves exact on the binary64 range. The `Perf/` tier replaces
   the two big-number kernels (`cmpScaledMixed`, `shiftedSig`) with
   fixed-width `UInt64` code proven equal to them; this file never
   depends on it.

   Pipeline:

     - `Srtfp/Float/Bits.lean` — decode a word into `(sign, m, q)` with
       value `(-1)^sign · m · 2^q`.
     - This file — `k` from the floor-log, the candidate significand
       `s = ⌊m · 2^q · 10^{-k}⌋`, the rounding-interval test, the
       shorter-form attempt, and the tie-break.
     - `Srtfp/Decimal.lean` — `Decimal.mk'` strips trailing zeros.

   The specification is `Srtfp/Correctness.lean`; the proofs are under
   `Srtfp/Proofs/Schubfach/`. -/

public import Srtfp.Decimal
public import Srtfp.Float.Bits
public import Srtfp.Proofs.Clinger.NatIntervalDefs

@[expose] public section

namespace Srtfp.Schubfach

open Srtfp.Float

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

/-! ## Schubfach k

`k = ⌊log_D(‖R_v‖)⌋` from R10, computed as either `⌊log_10(2^q)⌋` (regular)
or `⌊log_10(3/4 · 2^q)⌋` (irregular). -/

/-- Compute Schubfach's `k` from the decoded `(m, q)` of a finite Float. -/
def kOfMQ (m : Nat) (q : Int) : Int :=
  if isIrregular m q then
    floorLog10ThreeQuartersPow2 q
  else
    floorLog10Pow2 q

/-! ## Exact rational comparison and floor

Schubfach compares candidates `s · 10^k` against the endpoints of the
rounding interval and computes `⌊m · 2^q · 10^{-k}⌋`. Both are done here
exactly, by clearing denominators with the common factor
`2^{max(-q,0)} · 10^{max(-k,0)}` and computing in `Nat`. -/

/-- `⌊m · 2^q · 10^{-k}⌋` as a `Nat`. Used to compute `s` in Schubfach. -/
def shiftedSig (m : Nat) (q : Int) (k : Int) : Nat :=
  let qPos : Nat := if q ≥ 0 then q.toNat else 0
  let qNeg : Nat := if q < 0 then (-q).toNat else 0
  let kPos : Nat := if k ≥ 0 then k.toNat else 0
  let kNeg : Nat := if k < 0 then (-k).toNat else 0
  -- m · 2^q · 10^{-k} = (m · 2^{max(q,0)} · 10^{max(-k,0)}) / (2^{max(-q,0)} · 10^{max(k,0)})
  (m * 2 ^ qPos * 10 ^ kNeg) / (2 ^ qNeg * 10 ^ kPos)

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

/-! ## Word → Decimal

Top-level entry point. Returns `Except` so callers can refuse NaN / Infinity
(which have no `Decimal` representation). -/

/-- Render a binary64 *bit pattern* as its shortest round-trip `Decimal`,
    or `.error _` for NaN and Infinity. A pure function of the word, never
    consulting a runtime `Float`. -/
def toDecimalBits (w : UInt64) : Except String Decimal :=
  if Word.isNaN w then
    .error "NaN"
  else if Word.isInf w then
    .error (if Word.signBit w then "-Infinity" else "Infinity")
  else
    let d := Word.decode w
    if d.m = 0 then .ok ⟨d.sign, 0, 0⟩
    else
      let (sig, exp) := shortestUnsigned d.m d.q
      .ok (Decimal.mk' d.sign sig exp)

/-- Render a `Float` as its shortest round-trip `Decimal`, or `.error _`
    for NaN and Infinity. -/
def toDecimal (f : _root_.Float) : Except String Decimal :=
  toDecimalBits f.toBits

theorem toDecimal_eq_bits (f : _root_.Float) : toDecimal f = toDecimalBits f.toBits := rfl

end Srtfp.Schubfach

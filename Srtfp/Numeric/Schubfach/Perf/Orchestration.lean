/- Orchestration-layer perf refactor for Schubfach `toDecimal`.

   `shortestUnsigned m q` makes 4–7 calls to `cmpScaledMixed` and one
   call to `shiftedSig`, all sharing the same `(q, k)`.  Each of these
   independently looks up the 128-bit `pow10` table and re-derives the
   shift exponent `h`, the safe-regime denominator `B = 2^qNeg · 10^kPos`,
   and `qPlusH = q + h` / `shiftAmt = h - q`.

   This file hoists those `(q, k)`-only precomputations by introducing
   per-call-site flat-argument fast paths that the compiler can
   scalar-replace, then re-implements `shortestUnsigned_packed` so the
   precomputation happens exactly once per top-level call.

   The packed variants are *byte-identical* (up to inlined lookups) to
   their `_fast2` counterparts; equivalence theorems below close the
   round-trip, and `@[csimp]` registers `shortestUnsigned_packed` as
   the runtime implementation.
-/
import Srtfp.Numeric.Schubfach
import Srtfp.Numeric.Schubfach.KernelCorrectness
import Srtfp.Numeric.Schubfach.Perf.Kernel128
import Srtfp.Numeric.Schubfach.Perf.KernelR20

namespace PP.Numeric.Schubfach

/-! ## Packed `cmpScaledMixed`

`cmpScaledMixed_packed` mirrors `cmpScaledMixed_fast2`'s body byte-for-byte,
but the four `(q, k)`-only inputs `(gHi, gLo, h, qPlusH)` are supplied as
explicit arguments instead of being recomputed.  When called with the
values that `cmpScaledMixed_fast2` would have derived from `(q, k)`, this
function is observationally identical. -/

/-- Packed comparator: same body as `cmpScaledMixed_fast2`, but with the
    `(q, k)`-only precomputations (`gHi`, `gLo`, `q + h`) supplied
    as direct arguments.  `q` and `k` are still needed for the fallback
    branch that delegates to `cmpScaledMixed_fast`. -/
def cmpScaledMixed_packed
    (q : Int) (k : Int)
    (gHi : UInt64) (gLo : UInt64) (qPlusH : Int)
    (a b : Int) : Int :=
  if a < 0 ∨ b < 0 then cmpScaledMixed_fast a q b k
  else if b = 0 then cmpScaledMixed_fast a q b k
  else if a ≥ (1 <<< 60 : Int) ∨ b ≥ (1 <<< 60 : Int) then
    cmpScaledMixed_fast a q b k
  else if k < pow10Table128_kMin ∨ k > pow10Table128_kMax then
    cmpScaledMixed_fast a q b k
  else
    if qPlusH < 64 ∨ qPlusH ≥ 192 then cmpScaledMixed_fast a q b k
    else
      let aU : UInt64 := UInt64.ofNat a.toNat
      let bU : UInt64 := UInt64.ofNat b.toNat
      let rLo  : UInt64 := bU * gLo
      let rLoH : UInt64 := mulHi64 bU gLo
      let rHi  : UInt64 := bU * gHi
      let rHiH : UInt64 := mulHi64 bU gHi
      let midSum : UInt64 := rHi + rLoH
      let midCarry : UInt64 := if midSum < rHi then 1 else 0
      let r192_hi  : UInt64 := rHiH + midCarry
      let r192_mid : UInt64 := midSum
      let r192_lo  : UInt64 := rLo
      if qPlusH > 132 then cmpScaledMixed_fast a q b k
      else
        let s : UInt64 := UInt64.ofNat qPlusH.toNat
        let l192 : UInt64 × UInt64 × UInt64 :=
          if s < 64 then
            (0, mulHi64 aU (1 <<< s), aU <<< s)
          else if s < 128 then
            let s64 := s - 64
            if s64 = 0 then (0, aU, 0)
            else (aU >>> (64 - s64), aU <<< s64, 0)
          else
            let s64 := s - 128
            if s64 = 0 then (aU, 0, 0)
            else (aU <<< s64, 0, 0)
        let (l_hi, l_mid, l_lo) := l192
        if gt192 l_hi l_mid l_lo r192_hi r192_mid r192_lo then 1
        else
          let (lpb_hi, lpb_mid, lpb_lo) := add192_64 l_hi l_mid l_lo bU
          if le192 lpb_hi lpb_mid lpb_lo r192_hi r192_mid r192_lo then -1
        else cmpScaledMixed_fast a q b k


/-- When the four precomputed values match `pow10Lookup128 k` (and its
    derived `qPlusH`), the packed comparator equals `cmpScaledMixed_fast2`. -/
theorem cmpScaledMixed_packed_eq_fast2 (a q b k : Int) :
    cmpScaledMixed_packed q k (pow10Lookup128 k).1 (pow10Lookup128 k).2.1
        (q + (pow10Lookup128 k).2.2) a b
      = cmpScaledMixed_fast2 a q b k := by
  unfold cmpScaledMixed_packed cmpScaledMixed_fast2
  rfl

/-- Round-trip: when the precomputed inputs match `pow10Lookup128 k`,
    `cmpScaledMixed_packed` equals the spec `cmpScaledMixed`. -/
theorem cmpScaledMixed_packed_eq (a q b k : Int) :
    cmpScaledMixed_packed q k (pow10Lookup128 k).1 (pow10Lookup128 k).2.1
        (q + (pow10Lookup128 k).2.2) a b
      = cmpScaledMixed a q b k := by
  rw [cmpScaledMixed_packed_eq_fast2, ← cmpScaledMixed_eq_fast2]

/-! ## Packed `inRoundingInterval` / `pickNearer` / `shortestUnsigned`

The original `B < 2^64`-guarded packed `shiftedSig` kernel
(`shiftedSig_packed` + its lemmas) lived here; with R20 it is superseded
by the widened `shiftedSig_packed_w` (`Perf/KernelR20.lean`) and the
unreachable original is preserved in `Perf/dead/PackedB64.lean`. -/

/-- Packed rounding-interval test.  Takes the four cmp-side precomputed
    values directly. -/
def inRoundingInterval_packed
    (q : Int) (k : Int)
    (gHi : UInt64) (gLo : UInt64) (qPlusH : Int)
    (s : Nat) (m : Nat) (irregular : Bool) : Bool :=
  let m4 : Int := 4 * (m : Int)
  let leftN : Int := if irregular then m4 - 1 else m4 - 2
  let rightN : Int := m4 + 2
  let s4 : Int := 4 * (s : Int)
  let cmpL := cmpScaledMixed_packed q k gHi gLo qPlusH leftN s4
  let cmpR := cmpScaledMixed_packed q k gHi gLo qPlusH rightN s4
  let cEven := m % 2 = 0
  let leftOK := cmpL < 0 || (cmpL = 0 && cEven)
  let rightOK := cmpR > 0 || (cmpR = 0 && cEven)
  leftOK && rightOK

theorem inRoundingInterval_packed_eq (s : Nat) (m : Nat) (q k : Int)
    (irregular : Bool) :
    inRoundingInterval_packed q k (pow10Lookup128 k).1 (pow10Lookup128 k).2.1
        (q + (pow10Lookup128 k).2.2) s m irregular
      = inRoundingInterval s k m q irregular := by
  unfold inRoundingInterval_packed inRoundingInterval
  simp only [cmpScaledMixed_packed_eq]




/-- Packed tie-breaker. -/
def pickNearer_packed
    (q : Int) (k : Int)
    (gHi : UInt64) (gLo : UInt64) (qPlusH : Int)
    (s : Nat) (m : Nat) : Nat :=
  let irregular := isIrregular m q
  let uIn := inRoundingInterval_packed q k gHi gLo qPlusH s m irregular
  let wIn := inRoundingInterval_packed q k gHi gLo qPlusH (s + 1) m irregular
  if uIn && !wIn then s
  else if !uIn && wIn then s + 1
  else
    let cmp := cmpScaledMixed_packed q k gHi gLo qPlusH
                (2 * (m : Int)) (2 * (s : Int) + 1)
    if cmp < 0 then s
    else if cmp > 0 then s + 1
    else if s % 2 = 0 then s
    else s + 1

theorem pickNearer_packed_eq (s : Nat) (m : Nat) (q k : Int) :
    pickNearer_packed q k (pow10Lookup128 k).1 (pow10Lookup128 k).2.1
        (q + (pow10Lookup128 k).2.2) s m
      = pickNearer s k m q := by
  unfold pickNearer_packed pickNearer
  simp only [inRoundingInterval_packed_eq, cmpScaledMixed_packed_eq]

/-- Fused `shortestUnsigned`: does each `(q, k)`-only precomputation
    exactly once and threads the results through the inner calls. -/
def shortestUnsigned_packed (m : Nat) (q : Int) : Nat × Int :=
  let irregular := isIrregular m q
  let k := kOfMQ m q
  -- shiftedSig-side precomputation (uses pow10Lookup128 at index -k).
  let sigTuple := pow10Lookup128 (-k)
  let sigGHi := sigTuple.1
  let sigGLo := sigTuple.2.1
  let sigH := sigTuple.2.2
  let sigShiftAmt : Int := sigH - q
  -- Binary64-domain dispatch: every real decode satisfies
  -- `0 < m < 2^53` and `-1074 ≤ q ≤ 971`, so the widened UInt64 kernel
  -- (`shiftedSig_packed_w`) is correct (R20: no `B < 2^64` guard) and is
  -- taken for the *entire* binary64 range.  Inputs outside the domain
  -- (never produced by `decode`) fall back to the exact spec, which keeps
  -- the `@[csimp]` equivalence universal.
  let s :=
    if 0 < m ∧ m < 2 ^ 53 ∧ -1074 ≤ q ∧ q ≤ 971 then
      shiftedSig_packed_w q k sigGHi sigGLo sigShiftAmt m
    else
      shiftedSig m q k
  -- cmpScaledMixed-side precomputation (at index k or k+1).
  if s ≥ 10 then
    let kHigh : Int := k + 1
    -- The kHigh ctx is used for the two top-level inRoundingInterval
    -- checks.  If both fail we fall back to pickNearer at the original `k`.
    let cmpTupleH := pow10Lookup128 kHigh
    let cmpHGHi := cmpTupleH.1
    let cmpHGLo := cmpTupleH.2.1
    let cmpHH := cmpTupleH.2.2
    let cmpHQPlusH : Int := q + cmpHH
    let sHigh := s / 10
    let uIn := inRoundingInterval_packed q kHigh cmpHGHi cmpHGLo cmpHQPlusH
                  sHigh m irregular
    let wIn := inRoundingInterval_packed q kHigh cmpHGHi cmpHGLo cmpHQPlusH
                  (sHigh + 1) m irregular
    if uIn then (sHigh, kHigh)
    else if wIn then (sHigh + 1, kHigh)
    else
      let cmpTuple := pow10Lookup128 k
      let cmpGHi := cmpTuple.1
      let cmpGLo := cmpTuple.2.1
      let cmpH := cmpTuple.2.2
      let cmpQPlusH : Int := q + cmpH
      (pickNearer_packed q k cmpGHi cmpGLo cmpQPlusH s m, k)
  else
    let cmpTuple := pow10Lookup128 k
    let cmpGHi := cmpTuple.1
    let cmpGLo := cmpTuple.2.1
    let cmpH := cmpTuple.2.2
    let cmpQPlusH : Int := q + cmpH
    (pickNearer_packed q k cmpGHi cmpGLo cmpQPlusH s m, k)

theorem shortestUnsigned_packed_eq (m : Nat) (q : Int) :
    shortestUnsigned_packed m q = shortestUnsigned m q := by
  unfold shortestUnsigned_packed shortestUnsigned
  -- Side-condition: the binary64-domain check decides shiftedSig dispatch.
  -- For real decodes the widened kernel is exact (R20); outside the domain
  -- the spec is used directly.  Both branches equal `shiftedSig m q k`.
  have hS : (if 0 < m ∧ m < 2 ^ 53 ∧ -1074 ≤ q ∧ q ≤ 971 then
              shiftedSig_packed_w q (kOfMQ m q) (pow10Lookup128 (-(kOfMQ m q))).1
                (pow10Lookup128 (-(kOfMQ m q))).2.1
                ((pow10Lookup128 (-(kOfMQ m q))).2.2 - q) m
            else
              shiftedSig m q (kOfMQ m q)) = shiftedSig m q (kOfMQ m q) := by
    by_cases hbin : 0 < m ∧ m < 2 ^ 53 ∧ -1074 ≤ q ∧ q ≤ 971
    · rw [if_pos hbin]
      obtain ⟨hm, hm53, hq_lo, hq_hi⟩ := hbin
      exact shiftedSig_packed_w_eq_binary64 m q hm hm53 hq_lo hq_hi
    · rw [if_neg hbin]
  simp only [hS, inRoundingInterval_packed_eq, pickNearer_packed_eq]

-- Superseded registration: `shortestUnsigned_eq_v3_csimp` (Uint64Bridge.lean)
-- is the live @[csimp].
theorem shortestUnsigned_eq_packed_csimp :
    @shortestUnsigned = @shortestUnsigned_packed := by
  funext m q
  exact (shortestUnsigned_packed_eq m q).symm

/-! ## Fused `toDecimal`

`toDecimal` is defined upstream in `Schubfach.lean`, before the
csimp registrations in this file are in scope.  As a result, its
compiled body calls `shortestUnsigned` (the spec) directly, bypassing
the runtime-faster `shortestUnsigned_packed`.

`toDecimal_packed` is a syntactic copy of `toDecimal` defined *here*
(inside Orchestration), so its compilation picks up the packed
csimp rewrites and the inner `shortestUnsigned` call goes through
`shortestUnsigned_packed`.  We register a `@[csimp]` so callers
that import this module see `toDecimal` rewritten to `toDecimal_packed`. -/

open PP.Numeric.Float in
/-- Fused `Float → Decimal`: identical body to `toDecimal` but compiled
    after the packed csimps are in scope, so the inner `shortestUnsigned`
    call goes through `shortestUnsigned_packed`. -/
def toDecimal_packed (f : _root_.Float) : Except String Decimal :=
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

theorem toDecimal_packed_eq (f : _root_.Float) :
    toDecimal_packed f = toDecimal f := by
  unfold toDecimal_packed toDecimal
  rfl

-- Superseded registration: `toDecimal_eq_v7_csimp` (KernelV6.lean) is the live @[csimp].
theorem toDecimal_eq_packed_csimp : @toDecimal = @toDecimal_packed := by
  funext f
  exact (toDecimal_packed_eq f).symm

end PP.Numeric.Schubfach

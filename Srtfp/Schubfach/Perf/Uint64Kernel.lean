/- All-UInt64 fast-path kernels for Schubfach's `toDecimal` inner loop.

The `_packed` kernels in `Orchestration.lean` already use UInt64 inside
their fast path, but their **arguments** are still `Int`/`Nat`, which
forces the Lean compiler to box them at each function-call boundary
even though the actual values fit comfortably in machine words.  Each
`cmpScaledMixed_packed` call therefore round-trips `a, b, q, k, qPlusH`
through boxed (heap-allocated, GMP-sized) `Int` objects.

This file mirrors the `_packed` kernels with `_u64` variants whose
arguments and intermediates are all `UInt64`.  Preconditions
(`a, b < 2^60`, `qPlusH ∈ [64, 132]`, `m < 2^53`, `s ≤ m·2^{q+h}/2^h`,
etc.) are now caller-enforced — the kernels themselves perform no
guards.

The chain bottoms out at `shortestUnsigned_v2`, which is the new
top-level orchestration; for inputs in the binary64 regime it stays
entirely on the UInt64 path.  Out-of-regime inputs (which never arise
from `decode : Float → Decoded`, since binary64 fixes
`m ≤ 2^53`, `q ∈ [-1074, 971]`) delegate to the existing
`shortestUnsigned_packed` for total correctness.
-/
import Srtfp.Schubfach
import Srtfp.Schubfach.Perf.Orchestration
import Srtfp.Tactics

namespace Srtfp.Schubfach

/-! ## Pure-UInt64 comparator

`cmpScaledMixed_u64` returns the ternary verdict as an `Int` (`+1` = GT,
`-1` = LT, `0` = ambiguous).  The caller is responsible for handling
the ambiguous case (`0`) by falling back to the slow path.  Note that
`cmpScaledMixed` itself can return `0` (EQ), but the strict-verdict
kernel here returns `0` ONLY when ambiguous; true EQ flows through the
slow-path fallback.

`@[inline]` lets clang see the constants at the call site so the boxed-
`Int` return collapses (the consumer just compares `< 0`, `= 0`, etc.). -/

/-- Helper to compute the L triple `(l_hi, l_mid, l_lo)` from `aU` and
    the shift `s = qPlusH8`. -/
@[inline]
def cmpScaledMixed_u64_L
    (aU : UInt64) (s : UInt64) : UInt64 × UInt64 × UInt64 :=
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

/-- Inner helper: the post-destructure body of `cmpScaledMixed_u64_slow`,
    factored as a function of the destructured L triple components and
    the R triple components.  Both `_u64_slow` and `_u64` reduce to a
    call to this helper, making leaf-irrelevance proofs structural. -/
@[inline]
def cmpScaledMixed_u64_inner
    (l_hi l_mid l_lo : UInt64)
    (r192_hi r192_mid r192_lo : UInt64)
    (bU : UInt64) (slow : Int) : Int :=
  if gt192 l_hi l_mid l_lo r192_hi r192_mid r192_lo then 1
  else
    let (lpb_hi, lpb_mid, lpb_lo) := add192_64 l_hi l_mid l_lo bU
    if le192 lpb_hi lpb_mid lpb_lo r192_hi r192_mid r192_lo then -1
    else slow

/-- Generic UInt64 kernel: same body as `cmpScaledMixed_fast2`'s strict-
    verdict branch, parameterised over the ambiguous-leaf value.
    Factored through `cmpScaledMixed_u64_inner` (the post-destructure
    body) so leaf-irrelevance proofs are straightforward.

    Caller preconditions:
      - `gHi, gLo` come from `pow10Lookup128 k` for valid `k`.
      - `qPlusH8 = UInt64.ofNat (q + h).toNat` with `q+h ∈ [64, 132]`.
      - `aU, bU` are the UInt64 representations of `a, b ∈ [0, 2^60)`
        with `bU > 0` (i.e. `b ≠ 0`). -/
@[inline]
def cmpScaledMixed_u64_slow
    (gHi gLo : UInt64) (qPlusH8 : UInt64)
    (aU bU : UInt64) (slow : Int) : Int :=
  let rLo  : UInt64 := bU * gLo
  let rLoH : UInt64 := mulHi64 bU gLo
  let rHi  : UInt64 := bU * gHi
  let rHiH : UInt64 := mulHi64 bU gHi
  let midSum   : UInt64 := rHi + rLoH
  let midCarry : UInt64 := if midSum < rHi then 1 else 0
  let r192_hi  : UInt64 := rHiH + midCarry
  let r192_mid : UInt64 := midSum
  let r192_lo  : UInt64 := rLo
  let (l_hi, l_mid, l_lo) := cmpScaledMixed_u64_L aU qPlusH8
  cmpScaledMixed_u64_inner l_hi l_mid l_lo r192_hi r192_mid r192_lo bU slow

/-- Strict-verdict-only UInt64 kernel: returns `0` for the ambiguous
    case so the caller can dispatch lazily.  Same body as
    `cmpScaledMixed_u64_slow ... 0`. -/
@[inline]
def cmpScaledMixed_u64
    (gHi gLo : UInt64) (qPlusH8 : UInt64)
    (aU bU : UInt64) : Int :=
  cmpScaledMixed_u64_slow gHi gLo qPlusH8 aU bU 0

/-- `cmpScaledMixed_packed`'s fast-path body is structurally identical
    to `cmpScaledMixed_u64_slow` with the supplied slow leaf.  This
    equivalence is byte-for-byte: `rfl` closes it after discharging
    the precondition guards. -/
theorem cmpScaledMixed_packed_eq_u64_slow
    (q k : Int) (gHi gLo : UInt64) (qPlusH : Int)
    (a b : Int)
    (ha_nn : 0 ≤ a) (hb_nn : 0 ≤ b)
    (hb_pos : b ≠ 0)
    (ha_lt : a < (1 <<< 60 : Int)) (hb_lt : b < (1 <<< 60 : Int))
    (hk_lo : pow10Table128_kMin ≤ k) (hk_hi : k ≤ pow10Table128_kMax)
    (hqh_lo : 64 ≤ qPlusH) (hqh_hi : qPlusH ≤ 132) :
    cmpScaledMixed_packed q k gHi gLo qPlusH a b =
      cmpScaledMixed_u64_slow gHi gLo (UInt64.ofNat qPlusH.toNat)
        (UInt64.ofNat a.toNat) (UInt64.ofNat b.toNat)
        (cmpScaledMixed_fast a q b k) := by
  unfold cmpScaledMixed_packed cmpScaledMixed_u64_slow
    cmpScaledMixed_u64_L cmpScaledMixed_u64_inner
  rw [if_neg (by push_neg; exact ⟨ha_nn, hb_nn⟩)]
  rw [if_neg hb_pos]
  rw [if_neg (by push_neg; exact ⟨ha_lt, hb_lt⟩)]
  rw [if_neg (by push_neg; exact ⟨hk_lo, hk_hi⟩)]
  rw [if_neg (by omega : ¬(qPlusH < 64 ∨ qPlusH ≥ 192))]
  rw [if_neg (by omega : ¬(qPlusH > 132))]


/-! ## Pure-UInt64 `inRoundingInterval`

Two `cmpScaledMixed_u64` calls share `R = bU·G`; only `aU` differs.
Both call sites supply UInt64 args directly.  The ambiguous fallback
(`v = 0`) is dispatched at the caller level, where the `Int`-typed
spec args are already in scope.

Returns:
  - `(false, true)` / `(true, false)` / `(false, false)` / `(true, true)`
    if both cmps gave strict verdicts.  Combine these per
    `inRoundingInterval`'s formula.
  - `none` if either cmp was ambiguous; caller falls back to
    `inRoundingInterval_packed`. -/

/-- Try the rounding-interval test with the UInt64 kernel.  Returns
    `some result` if both cmps got strict verdicts; `none` if either
    was ambiguous (caller must use the slow path). -/
@[inline]
def inRoundingInterval_u64_opt
    (gHi gLo : UInt64) (qPlusH8 : UInt64)
    (sU mU : UInt64) (irregular : Bool) : Option Bool :=
  let m4 : UInt64 := mU <<< 2
  let leftU : UInt64 := if irregular then m4 - 1 else m4 - 2
  let rightU : UInt64 := m4 + 2
  let s4U : UInt64 := sU <<< 2
  let cmpL := cmpScaledMixed_u64 gHi gLo qPlusH8 leftU s4U
  if cmpL = 0 then none
  else
    let cmpR := cmpScaledMixed_u64 gHi gLo qPlusH8 rightU s4U
    if cmpR = 0 then none
    else
      -- Both strict: cmpL, cmpR ∈ {-1, +1}.  Even-tie branch never fires.
      let leftOK := cmpL < 0
      let rightOK := cmpR > 0
      some (leftOK && rightOK)

/-! ## Pair `inRoundingInterval`: share `R = b·G` across both cmps.

The two `cmpScaledMixed_u64` calls inside `inRoundingInterval_u64_opt`
share `b = 4s`, `gHi`, `gLo`, `qPlusH8`; only `a` (`leftU` vs `rightU`)
differs.  The `R` triple (rHi, rMid, rLo) computed from `b·G` is
identical across both calls.

`inRoundingInterval_u64_packed` computes R once, then does both
verdict-checks against the shared R triple.  Returns a packed
`UInt8` verdict to avoid `Option Bool` heap allocation:
  - `0` — ambiguous (either cmp was ambig); caller falls back
  - `1` — false (`u ∉ R_v`)
  - `2` — true (`u ∈ R_v`)
The encoding lets the caller decide via `v == 2` / `v == 0`
without unpacking nested ctors. -/

/-- Sentinel for "ambiguous (defer to slow path)". -/
@[inline]
def inRoundingInterval_u8_AMBIG : UInt8 := 0

/-- Sentinel for "interval test = false". -/
@[inline]
def inRoundingInterval_u8_FALSE : UInt8 := 1

/-- Sentinel for "interval test = true". -/
@[inline]
def inRoundingInterval_u8_TRUE : UInt8 := 2

/-- Verdict-from-precomputed-R helper.  Given a precomputed
    `(r192_hi, r192_mid, r192_lo)` and `bU`, returns 0 for ambig,
    +1 for GT (L > R), -1 for LT (L+b ≤ R), as an `Int8`-like value
    packed into `UInt64` (`0`, `1`, `0xFF_FF_FF_FF_FF_FF_FF_FF`). -/
@[inline]
def cmpVerdict_u64_inner
    (l_hi l_mid l_lo : UInt64)
    (r192_hi r192_mid r192_lo : UInt64)
    (bU : UInt64) : Int :=
  if gt192 l_hi l_mid l_lo r192_hi r192_mid r192_lo then 1
  else
    let (lpb_hi, lpb_mid, lpb_lo) := add192_64 l_hi l_mid l_lo bU
    if le192 lpb_hi lpb_mid lpb_lo r192_hi r192_mid r192_lo then -1
    else 0

/-- Packed `inRoundingInterval`: shares the R triple between the two
    cmps.  Returns a `UInt8` sentinel (see `inRoundingInterval_u8_*`). -/
@[inline]
def inRoundingInterval_u64_packed_u8
    (gHi gLo : UInt64) (qPlusH8 : UInt64)
    (sU mU : UInt64) (irregular : Bool) : UInt8 :=
  let m4 : UInt64 := mU <<< 2
  let leftU : UInt64 := if irregular then m4 - 1 else m4 - 2
  let rightU : UInt64 := m4 + 2
  let s4U : UInt64 := sU <<< 2
  -- R = s4U · G, computed once and shared across both verdict checks.
  let rLo  : UInt64 := s4U * gLo
  let rLoH : UInt64 := mulHi64 s4U gLo
  let rHi  : UInt64 := s4U * gHi
  let rHiH : UInt64 := mulHi64 s4U gHi
  let midSum   : UInt64 := rHi + rLoH
  let midCarry : UInt64 := if midSum < rHi then 1 else 0
  let r192_hi  : UInt64 := rHiH + midCarry
  let r192_mid : UInt64 := midSum
  let r192_lo  : UInt64 := rLo
  -- Left verdict.
  let (l_hi_L, l_mid_L, l_lo_L) := cmpScaledMixed_u64_L leftU qPlusH8
  let cmpL := cmpVerdict_u64_inner l_hi_L l_mid_L l_lo_L r192_hi r192_mid r192_lo s4U
  if cmpL = 0 then inRoundingInterval_u8_AMBIG
  else
    -- Right verdict.
    let (l_hi_R, l_mid_R, l_lo_R) := cmpScaledMixed_u64_L rightU qPlusH8
    let cmpR := cmpVerdict_u64_inner l_hi_R l_mid_R l_lo_R r192_hi r192_mid r192_lo s4U
    if cmpR = 0 then inRoundingInterval_u8_AMBIG
    else
      -- Both strict: result is (cmpL < 0) && (cmpR > 0).
      if cmpL < 0 && cmpR > 0 then inRoundingInterval_u8_TRUE
      else inRoundingInterval_u8_FALSE

/-- Internal: a single `cmpScaledMixed_u64 gHi gLo qPlusH8 aU bU` equals
    `cmpVerdict_u64_inner (L_triple) (R_triple) bU` with R derived from
    `bU * G`.  Used to identify the two `cmpScaledMixed_u64` calls
    inside `inRoundingInterval_u64_opt` with the corresponding
    `cmpVerdict_u64_inner` calls in `inRoundingInterval_u64_packed_u8`. -/
theorem cmpScaledMixed_u64_eq_cmpVerdict
    (gHi gLo : UInt64) (qPlusH8 : UInt64) (aU bU : UInt64) :
    cmpScaledMixed_u64 gHi gLo qPlusH8 aU bU =
      cmpVerdict_u64_inner (cmpScaledMixed_u64_L aU qPlusH8).1
        (cmpScaledMixed_u64_L aU qPlusH8).2.1
        (cmpScaledMixed_u64_L aU qPlusH8).2.2
        (mulHi64 bU gHi + (if bU * gHi + mulHi64 bU gLo < bU * gHi then 1 else 0))
        (bU * gHi + mulHi64 bU gLo)
        (bU * gLo) bU := by
  unfold cmpScaledMixed_u64 cmpScaledMixed_u64_slow cmpScaledMixed_u64_inner
    cmpVerdict_u64_inner
  obtain ⟨l_hi, l_mid_lo⟩ := cmpScaledMixed_u64_L aU qPlusH8
  obtain ⟨l_mid, l_lo⟩ := l_mid_lo
  rfl

/-- Equivalence: the packed-u8 version agrees with `inRoundingInterval_u64_opt`. -/
theorem inRoundingInterval_u64_packed_u8_eq
    (gHi gLo : UInt64) (qPlusH8 : UInt64)
    (sU mU : UInt64) (irregular : Bool) :
    inRoundingInterval_u64_packed_u8 gHi gLo qPlusH8 sU mU irregular =
      (match inRoundingInterval_u64_opt gHi gLo qPlusH8 sU mU irregular with
       | none => inRoundingInterval_u8_AMBIG
       | some true => inRoundingInterval_u8_TRUE
       | some false => inRoundingInterval_u8_FALSE) := by
  unfold inRoundingInterval_u64_packed_u8 inRoundingInterval_u64_opt
  -- Bridge: rewrite each `cmpScaledMixed_u64` on RHS to `cmpVerdict_u64_inner`.
  simp only [cmpScaledMixed_u64_eq_cmpVerdict]
  -- Destructure L triples.
  obtain ⟨l_hi_L, l_mid_L, l_lo_L⟩ := cmpScaledMixed_u64_L
    (if irregular then mU <<< 2 - 1 else mU <<< 2 - 2) qPlusH8
  obtain ⟨l_hi_R, l_mid_R, l_lo_R⟩ := cmpScaledMixed_u64_L (mU <<< 2 + 2) qPlusH8
  -- Generalise R triple (shared between the two branches).
  set s4U : UInt64 := sU <<< 2 with hs4U
  set rHi  : UInt64 := s4U * gHi
  set rLoH : UInt64 := mulHi64 s4U gLo
  set rHiH : UInt64 := mulHi64 s4U gHi
  set midSum   : UInt64 := rHi + rLoH
  set midCarry : UInt64 := if midSum < rHi then 1 else 0
  set r192_hi  : UInt64 := rHiH + midCarry
  set r192_mid : UInt64 := midSum
  set r192_lo  : UInt64 := s4U * gLo
  set cmpL : Int :=
    cmpVerdict_u64_inner l_hi_L l_mid_L l_lo_L r192_hi r192_mid r192_lo s4U
  set cmpR : Int :=
    cmpVerdict_u64_inner l_hi_R l_mid_R l_lo_R r192_hi r192_mid r192_lo s4U
  by_cases hL0 : cmpL = 0
  · simp [hL0, inRoundingInterval_u8_AMBIG]
  · simp only [hL0, if_false]
    by_cases hR0 : cmpR = 0
    · simp [hR0, inRoundingInterval_u8_AMBIG]
    · simp only [hR0, if_false]
      by_cases hLn : cmpL < 0
      · by_cases hRp : cmpR > 0
        · simp [hLn, hRp, inRoundingInterval_u8_TRUE]
        · simp [hLn, hRp, inRoundingInterval_u8_FALSE]
      · by_cases hRp : cmpR > 0
        · simp [hLn, hRp, inRoundingInterval_u8_FALSE]
        · simp [hLn, hRp, inRoundingInterval_u8_FALSE]

/-! ## `inRoundingInterval` via `_u64_slow` (proof-friendly path).

`inRoundingInterval_u64_slow` is the structural counterpart of
`inRoundingInterval_packed`: it calls `cmpScaledMixed_u64_slow` with
the supplied slow leaves and returns a `Bool` matching the spec
formula.  Useful for the equivalence proof: byte-identical to
`inRoundingInterval_packed`'s body when slow leaves come from
`cmpScaledMixed_fast`. -/


/-- Leaf-independence of the inner body: when the kernel produces a
    strict verdict (non-zero on the `slow=0` instance), it produces the
    same value for any slow leaf. -/
theorem cmpScaledMixed_u64_inner_strict_eq
    (l_hi l_mid l_lo : UInt64)
    (r192_hi r192_mid r192_lo : UInt64)
    (bU : UInt64) (slow : Int)
    (hstrict : cmpScaledMixed_u64_inner l_hi l_mid l_lo r192_hi r192_mid r192_lo bU 0 ≠ 0) :
    cmpScaledMixed_u64_inner l_hi l_mid l_lo r192_hi r192_mid r192_lo bU slow
      = cmpScaledMixed_u64_inner l_hi l_mid l_lo r192_hi r192_mid r192_lo bU 0 := by
  unfold cmpScaledMixed_u64_inner at *
  -- Now the if-chain is at top level (no `let` destructuring needed:
  -- l_hi, l_mid, l_lo are direct args).
  by_cases hgt : gt192 l_hi l_mid l_lo r192_hi r192_mid r192_lo = true
  · simp [hgt]
  · simp only [hgt] at hstrict ⊢
    -- Generalize add192_64 so the `let (lpb_hi, ...) := ...` is handled.
    generalize (add192_64 l_hi l_mid l_lo bU) = LpB at hstrict ⊢
    obtain ⟨lpb_hi, lpb_mid, lpb_lo⟩ := LpB
    by_cases hle : le192 lpb_hi lpb_mid lpb_lo r192_hi r192_mid r192_lo = true
    · simp [hle]
    · simp [hle] at hstrict

/-- The branch form: `_u64_inner ... slow = if _u64_inner ... 0 = 0 then slow else _u64_inner ... 0`. -/
theorem cmpScaledMixed_u64_inner_eq_branch
    (l_hi l_mid l_lo : UInt64)
    (r192_hi r192_mid r192_lo : UInt64)
    (bU : UInt64) (slow : Int) :
    cmpScaledMixed_u64_inner l_hi l_mid l_lo r192_hi r192_mid r192_lo bU slow
      = (let v := cmpScaledMixed_u64_inner l_hi l_mid l_lo r192_hi r192_mid r192_lo bU 0
         if v = 0 then slow else v) := by
  by_cases h : cmpScaledMixed_u64_inner l_hi l_mid l_lo r192_hi r192_mid r192_lo bU 0 = 0
  · simp only [h]
    -- LHS: same body with `slow` instead of `0`; given the slow=0 result is 0,
    -- the strict branches didn't fire, so the LHS returns slow.
    unfold cmpScaledMixed_u64_inner at *
    by_cases hgt : gt192 l_hi l_mid l_lo r192_hi r192_mid r192_lo = true
    · simp [hgt] at h
    · simp only [hgt] at h ⊢
      generalize hLpB : (add192_64 l_hi l_mid l_lo bU) = LpB at h ⊢
      obtain ⟨lpb_hi, lpb_mid, lpb_lo⟩ := LpB
      by_cases hle : le192 lpb_hi lpb_mid lpb_lo r192_hi r192_mid r192_lo = true
      · simp [hle] at h
      · simp [hle]
  · simp only [h, if_false]
    exact cmpScaledMixed_u64_inner_strict_eq _ _ _ _ _ _ _ _ h

/-- The branch form for `_u64_slow`: equals `if _u64 = 0 then slow else _u64`. -/
theorem cmpScaledMixed_u64_slow_eq_branch
    (gHi gLo : UInt64) (qPlusH8 : UInt64) (aU bU : UInt64) (slow : Int) :
    cmpScaledMixed_u64_slow gHi gLo qPlusH8 aU bU slow =
      (let v := cmpScaledMixed_u64 gHi gLo qPlusH8 aU bU
       if v = 0 then slow else v) := by
  show cmpScaledMixed_u64_slow gHi gLo qPlusH8 aU bU slow =
       (if cmpScaledMixed_u64_slow gHi gLo qPlusH8 aU bU 0 = 0
        then slow
        else cmpScaledMixed_u64_slow gHi gLo qPlusH8 aU bU 0)
  unfold cmpScaledMixed_u64_slow
  exact cmpScaledMixed_u64_inner_eq_branch _ _ _ _ _ _ _ _

/-- `cmpScaledMixed_packed`'s fast-path value via the `_u64` sentinel-0
    dispatch.  Combines `_packed_eq_u64_slow` with `_slow_eq_branch`. -/
theorem cmpScaledMixed_packed_eq_u64_branch
    (q k : Int) (gHi gLo : UInt64) (qPlusH : Int)
    (a b : Int)
    (ha_nn : 0 ≤ a) (hb_nn : 0 ≤ b)
    (hb_pos : b ≠ 0)
    (ha_lt : a < (1 <<< 60 : Int)) (hb_lt : b < (1 <<< 60 : Int))
    (hk_lo : pow10Table128_kMin ≤ k) (hk_hi : k ≤ pow10Table128_kMax)
    (hqh_lo : 64 ≤ qPlusH) (hqh_hi : qPlusH ≤ 132) :
    cmpScaledMixed_packed q k gHi gLo qPlusH a b =
      (let v := cmpScaledMixed_u64 gHi gLo (UInt64.ofNat qPlusH.toNat)
                  (UInt64.ofNat a.toNat) (UInt64.ofNat b.toNat)
       if v = 0 then cmpScaledMixed_fast a q b k else v) := by
  rw [cmpScaledMixed_packed_eq_u64_slow _ _ _ _ _ _ _ ha_nn hb_nn hb_pos
        ha_lt hb_lt hk_lo hk_hi hqh_lo hqh_hi]
  exact cmpScaledMixed_u64_slow_eq_branch _ _ _ _ _ _

/-- All-UInt64 rounding-interval test with explicit slow-path leaves.
    The result matches `inRoundingInterval_packed` byte-for-byte
    when the slow leaves are the corresponding `cmpScaledMixed_fast`
    calls and the UInt64 args are the corresponding conversions. -/
@[inline]
def inRoundingInterval_u64_slow
    (gHi gLo : UInt64) (qPlusH8 : UInt64)
    (sU mU : UInt64) (irregular : Bool)
    (slowL slowR : Int) : Bool :=
  let m4 : UInt64 := mU <<< 2
  let leftU : UInt64 := if irregular then m4 - 1 else m4 - 2
  let rightU : UInt64 := m4 + 2
  let s4U : UInt64 := sU <<< 2
  let cmpL := cmpScaledMixed_u64_slow gHi gLo qPlusH8 leftU s4U slowL
  let cmpR := cmpScaledMixed_u64_slow gHi gLo qPlusH8 rightU s4U slowR
  let cEven := mU &&& 1 = 0
  let leftOK := cmpL < 0 || (cmpL = 0 && cEven)
  let rightOK := cmpR > 0 || (cmpR = 0 && cEven)
  leftOK && rightOK


/-! ## Pure-UInt64 `pickNearer` -/

/-- Try the pick-nearer with the UInt64 kernel.  Returns `some` if all
    intermediate cmps had strict verdicts; `none` otherwise.

    Uses `inRoundingInterval_u64_packed_u8` (UInt8 sentinel) internally
    to avoid two `Option Bool` heap allocations per call. -/
@[inline]
def pickNearer_u64_opt
    (gHi gLo : UInt64) (qPlusH8 : UInt64)
    (sU mU : UInt64) (irregular : Bool) : Option UInt64 :=
  let uV := inRoundingInterval_u64_packed_u8 gHi gLo qPlusH8 sU mU irregular
  if uV = inRoundingInterval_u8_AMBIG then none
  else
    let wV := inRoundingInterval_u64_packed_u8 gHi gLo qPlusH8 (sU + 1) mU irregular
    if wV = inRoundingInterval_u8_AMBIG then none
    else
      -- Both strict: decode the booleans.
      let uIn : Bool := uV = inRoundingInterval_u8_TRUE
      let wIn : Bool := wV = inRoundingInterval_u8_TRUE
      if uIn && !wIn then some sU
      else if !uIn && wIn then some (sU + 1)
      else
        -- Compare 2m·2^q vs (2s+1)·10^k.
        let twoM : UInt64 := mU <<< 1
        let twoSp1 : UInt64 := (sU <<< 1) + 1
        let cmp := cmpScaledMixed_u64 gHi gLo qPlusH8 twoM twoSp1
        if cmp = 0 then none
        else if cmp < 0 then some sU
        else if cmp > 0 then some (sU + 1)
        else if mU &&& 1 = 0 then some sU
        else some (sU + 1)

/-! ## Pure-UInt64 `shortestUnsigned`

The orchestration: takes spec `(m, q)`, pre-converts to UInt64, calls
the `_u64_opt` helpers.  If any kernel signals ambiguity (or any
precondition fails), defers to the `_packed` slow path.

Preconditions for the fast path:
  - `m < 2^53` (binary64 mantissa bound — always holds post-`decode`)
  - `q ∈ [-1074, 971]` (binary64 exponent bound)
  - `k = kOfMQ m q ∈ [-308, 308]` (binary64 decimal exponent range)
  - `s = shiftedSig m q k < 2^57` (Schubfach §9 output bound)
  - `q + h ∈ [64, 132]` for the table's `h` at index `k` or `k+1`

Falling out of any guard simply uses `shortestUnsigned_packed`. -/

/-! ## kOfMQ_fast — UInt64 arithmetic for the Schubfach k computation.

`floorLog10Pow2 e = Int.fdiv (e * constC) (2^41)` runs in boxed `Int`
(GMP).  For binary64 inputs `e ∈ [-1074, 971]`, the product `e * C`
fits in `Int64` (max ~7.1e14 < 2^63), and the floor-by-power-of-2 is
an arithmetic right shift on a 2's-complement value.

We compute the entire thing in `UInt64` with 2's-complement-style
arithmetic.  Conversion to/from `Int` is handled by biasing `e` by
`1074` (so the input is non-negative) and computing
`(e_unsigned * C - 1074 * C) >>> 41` with sign-aware shift. -/

/-- Arithmetic right shift by 41 on a 2's-complement-style `UInt64`.
    For non-negative `x` (high bit clear) this is `x >>> 41`; for
    negative `x` (high bit set), fills the top 41 bits with 1s. -/
@[inline]
def asrUInt64_41 (x : UInt64) : UInt64 :=
  let lo := x >>> 41
  -- 0xFFFFFFFFFFE00000: top 23 bits set (mask for sign-extend on right shift by 41).
  let signMask : UInt64 := 0xFFFFFFFFFFE00000
  if x &&& 0x8000000000000000 = 0 then lo
  else lo ||| signMask

/-- Convert a 2's-complement-style `UInt64` (bit pattern of an `Int64`)
    back to `Int`.  Positive values (high bit clear) map directly via
    `toNat`.  Negative values bypass the `(x.toNat : Int) - 2^64` chain
    (which materialises a big Nat ≈ 2^64): compute `|x|` via 2's
    complement negation (`(~x) + 1`), then negate as `Int`.  Since `|x|`
    is small for our floor-log use case, the resulting Nat stays in the
    inline-Nat fast path. -/
@[inline]
def int64_uint64_toInt (x : UInt64) : Int :=
  if x &&& 0x8000000000000000 = 0 then (x.toNat : Int)
  else -((((~~~ x) + 1).toNat : Int))

/-- Encodes `constC` as a UInt64 (fits in 40 bits). -/
@[inline]
def constC_u64 : UInt64 := 661971961083

/-- Encodes `1074 * constC` as a UInt64 (used as the bias offset).
    `1074 * 661971961083 = 710957886203142`, fits in 50 bits. -/
@[inline]
def bias1074constC_u64 : UInt64 := 710957886203142

/-- Encodes `1074 * constC - constA` (irregular bias).
    `1074 * 661971961083 - (-274743187321) = 711232629390463`. -/
@[inline]
def bias1074constC_minus_constA_u64 : UInt64 := 711232629390463

/-- Fast `floorLog10Pow2 e` for `e ∈ [-1074, 971]` using UInt64 arithmetic.
    Falls back to the spec for out-of-range inputs. -/
@[inline]
def floorLog10Pow2_fast (e : Int) : Int :=
  if e < (-1074 : Int) ∨ e > 971 then floorLog10Pow2 e
  else
    -- Bias: e' = e + 1074, in [0, 2045].
    let eU : UInt64 := UInt64.ofNat (e + 1074).toNat
    let prodU : UInt64 := eU * constC_u64                  -- ≤ 2045 * C < 2^51
    let signedDiffU : UInt64 := prodU - bias1074constC_u64 -- 2's complement
    int64_uint64_toInt (asrUInt64_41 signedDiffU)

/-- Fast `floorLog10ThreeQuartersPow2 e` for `e ∈ [-1074, 971]` using
    UInt64 arithmetic.  Computes `(e*C + A) >>> 41` (floor) via the
    bias trick: result = (e'*C - 1074*C + A) >>> 41
                       = (e'*C - (1074*C - A)) >>> 41.
    Falls back to spec for out-of-range. -/
@[inline]
def floorLog10ThreeQuartersPow2_fast (e : Int) : Int :=
  if e < (-1074 : Int) ∨ e > 971 then floorLog10ThreeQuartersPow2 e
  else
    -- Bias: e' = e + 1074.
    let eU : UInt64 := UInt64.ofNat (e + 1074).toNat
    let prodU : UInt64 := eU * constC_u64
    let signedDiffU : UInt64 := prodU - bias1074constC_minus_constA_u64
    int64_uint64_toInt (asrUInt64_41 signedDiffU)

/-- Fast `kOfMQ` for binary64 inputs (`q ∈ [-1074, 971]`).  Uses the
    UInt64 floor-log fast paths.  For out-of-range inputs, the
    underlying functions delegate to the spec. -/
@[inline]
def kOfMQ_fast (m : Nat) (q : Int) : Int :=
  if isIrregular m q then
    floorLog10ThreeQuartersPow2_fast q
  else
    floorLog10Pow2_fast q

/-! ## Correctness proofs for the `_fast` floor-log helpers.

Proof strategy: out-of-range delegates to the spec by construction;
in-range is a finite domain (2046 values of `e ∈ [-1074, 971]`).  We
use `decide +kernel` to discharge the universally-quantified equality
on this finite range; kernel reduction keeps the proof axiom-free (no
`Lean.ofReduceBool` / `Lean.trustCompiler`). -/

/-- Bool-valued bulk check for `floorLog10Pow2_fast = floorLog10Pow2` on
    `e ∈ [-1074, 971]`.  Reformulated as a Bool to avoid the deep
    `Fin.all_iff` recursion when the elaborator tries to handle a
    universal over `Fin 2046`. -/
private def floorLog10Pow2_check : Bool :=
  (List.range 2046).all fun i =>
    decide (floorLog10Pow2_fast (-1074 + (i : Int)) =
      floorLog10Pow2 (-1074 + (i : Int)))

private theorem floorLog10Pow2_check_true : floorLog10Pow2_check = true := by
  decide +kernel

private theorem floorLog10Pow2_fast_bounded
    (i : Nat) (hi : i < 2046) :
    floorLog10Pow2_fast (-1074 + (i : Int)) =
      floorLog10Pow2 (-1074 + (i : Int)) := by
  have hbulk : floorLog10Pow2_check = true := floorLog10Pow2_check_true
  unfold floorLog10Pow2_check at hbulk
  rw [List.all_eq_true] at hbulk
  have hi_mem : i ∈ List.range 2046 := List.mem_range.mpr hi
  have := hbulk i hi_mem
  exact decide_eq_true_iff.mp this

/-- Bool-valued bulk check for the 3/4-variant. -/
private def floorLog10ThreeQuartersPow2_check : Bool :=
  (List.range 2046).all fun i =>
    decide (floorLog10ThreeQuartersPow2_fast (-1074 + (i : Int)) =
      floorLog10ThreeQuartersPow2 (-1074 + (i : Int)))

private theorem floorLog10ThreeQuartersPow2_check_true :
    floorLog10ThreeQuartersPow2_check = true := by decide +kernel

private theorem floorLog10ThreeQuartersPow2_fast_bounded
    (i : Nat) (hi : i < 2046) :
    floorLog10ThreeQuartersPow2_fast (-1074 + (i : Int)) =
      floorLog10ThreeQuartersPow2 (-1074 + (i : Int)) := by
  have hbulk : floorLog10ThreeQuartersPow2_check = true :=
    floorLog10ThreeQuartersPow2_check_true
  unfold floorLog10ThreeQuartersPow2_check at hbulk
  rw [List.all_eq_true] at hbulk
  have hi_mem : i ∈ List.range 2046 := List.mem_range.mpr hi
  have := hbulk i hi_mem
  exact decide_eq_true_iff.mp this

theorem floorLog10Pow2_fast_eq (e : Int) :
    floorLog10Pow2_fast e = floorLog10Pow2 e := by
  by_cases hOOR : e < (-1074 : Int) ∨ e > 971
  · -- Out-of-range: fast delegates to spec.
    unfold floorLog10Pow2_fast
    rw [if_pos hOOR]
  · push_neg at hOOR
    obtain ⟨he_lo, he_hi⟩ := hOOR
    set i : Nat := (e + 1074).toNat with hi_def
    have hi_lt : i < 2046 := by simp [hi_def]; omega
    have he_eq : e = -1074 + (i : Int) := by simp [hi_def]; omega
    rw [he_eq]
    exact floorLog10Pow2_fast_bounded i hi_lt

theorem floorLog10ThreeQuartersPow2_fast_eq (e : Int) :
    floorLog10ThreeQuartersPow2_fast e = floorLog10ThreeQuartersPow2 e := by
  by_cases hOOR : e < (-1074 : Int) ∨ e > 971
  · unfold floorLog10ThreeQuartersPow2_fast
    rw [if_pos hOOR]
  · push_neg at hOOR
    obtain ⟨he_lo, he_hi⟩ := hOOR
    set i : Nat := (e + 1074).toNat with hi_def
    have hi_lt : i < 2046 := by simp [hi_def]; omega
    have he_eq : e = -1074 + (i : Int) := by simp [hi_def]; omega
    rw [he_eq]
    exact floorLog10ThreeQuartersPow2_fast_bounded i hi_lt

/-- Correctness of `kOfMQ_fast`. -/
theorem kOfMQ_fast_eq (m : Nat) (q : Int) :
    kOfMQ_fast m q = kOfMQ m q := by
  unfold kOfMQ_fast kOfMQ
  by_cases h : isIrregular m q = true
  · simp [h, floorLog10ThreeQuartersPow2_fast_eq]
  · simp [h, floorLog10Pow2_fast_eq]

/-- Csimp: route `kOfMQ` to `kOfMQ_fast` at runtime.  External callers
    (decode pipelines, debugging) benefit; the orchestrated v2 path
    inlines `kOfMQ_fast` directly. -/
@[csimp]
theorem kOfMQ_eq_fast_csimp : @kOfMQ = @kOfMQ_fast := by
  funext m q
  exact (kOfMQ_fast_eq m q).symm

@[csimp]
theorem floorLog10Pow2_eq_fast_csimp : @floorLog10Pow2 = @floorLog10Pow2_fast := by
  funext e
  exact (floorLog10Pow2_fast_eq e).symm

@[csimp]
theorem floorLog10ThreeQuartersPow2_eq_fast_csimp :
    @floorLog10ThreeQuartersPow2 = @floorLog10ThreeQuartersPow2_fast := by
  funext e
  exact (floorLog10ThreeQuartersPow2_fast_eq e).symm

/-- Binary64-domain-dispatched `shiftedSig`: when `(m, q)` is a real
    decode (`0 < m < 2^53`, `-1074 ≤ q ≤ 971`) and `k = kOfMQ m q`, the
    widened UInt64 kernel `shiftedSig_packed_w` applies for the *entire*
    binary64 range (R20: no `B < 2^64` accuracy guard).  Out-of-domain
    inputs (never produced by `decode`) fall back to the exact spec
    `shiftedSig`, keeping the `@[csimp]` equivalence universal. -/
@[inline]
def shiftedSig_v2 (m : Nat) (q : Int) (k : Int) : Nat :=
  let sigTuple := pow10Lookup128 (-k)
  let sigGHi := sigTuple.1
  let sigGLo := sigTuple.2.1
  let sigH := sigTuple.2.2
  let sigShiftAmt : Int := sigH - q
  if 0 < m ∧ m < 2 ^ 53 ∧ -1074 ≤ q ∧ q ≤ 971 ∧ k = kOfMQ m q then
    shiftedSig_packed_w q k sigGHi sigGLo sigShiftAmt m
  else
    shiftedSig m q k

/-! ## Pure-UInt64 `shiftedSig` kernel.

Variant of `shiftedSig_packed` that takes all args pre-converted to
`UInt64` and returns `UInt64`, skipping the four boxed-Int/Nat guards
that the orchestration has already established.

Caller preconditions (for the result to match `shiftedSig m q k`):
- `m < 2^60` (well within binary64's `m ≤ 2^53` bound)
- `mU = UInt64.ofNat m`
- `gHi, gLo = pow10Lookup128 (-k)` with `k ∈ [-kMax, kMax]`
- `shiftAmtU = UInt64.ofNat shiftAmt.toNat` with `shiftAmt = h - q ∈ [124, 192)`

The shift branches collapse for `shiftAmtU ∈ [128, 192)`: only the `>= 128`
arm runs.  However `shiftAmt` can also be `124, 125, 126, 127` (just below
128), so we still need the middle arm.  We keep the full branch structure
to match the spec under all valid inputs. -/
@[inline]
def shiftedSig_u64_kernel
    (mU : UInt64) (gHi gLo : UInt64) (shiftAmtU : UInt64) : UInt64 :=
  let pLo  : UInt64 := mU * gLo
  let pLoH : UInt64 := mulHi64 mU gLo
  let pHi  : UInt64 := mU * gHi
  let pHiH : UInt64 := mulHi64 mU gHi
  let midSum   : UInt64 := pHi + pLoH
  let midCarry : UInt64 := if midSum < pHi then 1 else 0
  let rHi  : UInt64 := pHiH + midCarry
  let rMid : UInt64 := midSum
  let rLo  : UInt64 := pLo
  if shiftAmtU < 64 then
    if shiftAmtU = 0 then rLo
    else (rLo >>> shiftAmtU) ||| (rMid <<< (64 - shiftAmtU))
  else if shiftAmtU < 128 then
    let s64 := shiftAmtU - 64
    if s64 = 0 then rMid
    else (rMid >>> s64) ||| (rHi <<< (64 - s64))
  else
    let s64 := shiftAmtU - 128
    rHi >>> s64

/-- The pure UInt64 kernel agrees with the *widened* packed kernel
    `shiftedSig_packed_w` under the same width preconditions — with NO
    `B < 2^64` guard. -/
theorem shiftedSig_u64_kernel_eq_packed_w
    (q k : Int) (m : Nat) (gHi gLo : UInt64) (shiftAmt : Int)
    (hm : m < (1 <<< 60 : Nat))
    (hk_lo : pow10Table128_kMin ≤ -k) (hk_hi : -k ≤ pow10Table128_kMax)
    (hsh_lo : 124 ≤ shiftAmt) (hsh_hi : shiftAmt < 192) :
    shiftedSig_u64_kernel (UInt64.ofNat m) gHi gLo
        (UInt64.ofNat shiftAmt.toNat)
      = UInt64.ofNat (shiftedSig_packed_w q k gHi gLo shiftAmt m) := by
  unfold shiftedSig_u64_kernel shiftedSig_packed_w
  rw [if_neg (by omega : ¬ m ≥ (1 <<< 60 : Nat))]
  rw [if_neg (by push_neg; constructor <;> omega
                : ¬ ((-k : Int) < pow10Table128_kMin ∨ (-k : Int) > pow10Table128_kMax))]
  rw [if_neg (by push_neg; constructor <;> omega
                : ¬ (shiftAmt < 124 ∨ shiftAmt ≥ 192))]
  rw [UInt64.ofNat_toNat]

/-- v3: same as v2 but uses the pure-UInt64 kernel.  Avoids boxed `Int`
    guard checks for `m < 2^60`, `kLookup` range, `shiftAmt` range, and
    `B < 2^64`, on the fast path.  Falls back to the spec for out-of-regime.

    Caller still passes `(m : Nat) (q k : Int)` so the type matches `shiftedSig`. -/
@[inline]
def shiftedSig_v3 (m : Nat) (q : Int) (k : Int) : Nat :=
  let sigTuple := pow10Lookup128 (-k)
  let sigGHi := sigTuple.1
  let sigGLo := sigTuple.2.1
  let sigH := sigTuple.2.2
  let sigShiftAmt : Int := sigH - q
  -- Width guards (structural; never fire on real binary64): m < 2^60,
  -- k in table range, shiftAmt ∈ [124, 192).  The final guard is the
  -- binary64-domain check `0<m<2^53 ∧ -1074≤q≤971 ∧ k = kOfMQ m q`; on it
  -- the widened R20 kernel is correct over the *entire* range (no B<2^64).
  if _h_m : m ≥ (1 <<< 60 : Nat) then shiftedSig m q k
  else if _h_k_lo : (-k : Int) < pow10Table128_kMin then shiftedSig m q k
  else if _h_k_hi : (-k : Int) > pow10Table128_kMax then shiftedSig m q k
  else if _h_s_lo : sigShiftAmt < 124 then shiftedSig m q k
  else if _h_s_hi : sigShiftAmt ≥ 192 then shiftedSig m q k
  else if _h_dom : 0 < m ∧ m < 2 ^ 53 ∧ -1074 ≤ q ∧ q ≤ 971 ∧ k = kOfMQ m q then
    -- All preconditions hold; use the pure-UInt64 kernel.
    let mU : UInt64 := UInt64.ofNat m
    let shiftAmtU : UInt64 := UInt64.ofNat sigShiftAmt.toNat
    (shiftedSig_u64_kernel mU sigGHi sigGLo shiftAmtU).toNat
  else
    shiftedSig m q k

theorem shiftedSig_v3_eq (m : Nat) (q k : Int) :
    shiftedSig_v3 m q k = shiftedSig m q k := by
  -- We use shiftedSig_v2_eq as the spec, then identify v3 with v2 on the fast path.
  unfold shiftedSig_v3
  by_cases h_m : m ≥ (1 <<< 60 : Nat)
  · rw [dif_pos h_m]
  rw [dif_neg h_m]
  by_cases h_k_lo : (-k : Int) < pow10Table128_kMin
  · rw [dif_pos h_k_lo]
  rw [dif_neg h_k_lo]
  by_cases h_k_hi : (-k : Int) > pow10Table128_kMax
  · rw [dif_pos h_k_hi]
  rw [dif_neg h_k_hi]
  by_cases h_s_lo : ((pow10Lookup128 (-k)).2.2 - q) < 124
  · rw [dif_pos h_s_lo]
  rw [dif_neg h_s_lo]
  by_cases h_s_hi : ((pow10Lookup128 (-k)).2.2 - q) ≥ 192
  · rw [dif_pos h_s_hi]
  rw [dif_neg h_s_hi]
  by_cases h_dom : 0 < m ∧ m < 2 ^ 53 ∧ -1074 ≤ q ∧ q ≤ 971 ∧ k = kOfMQ m q
  · rw [dif_pos h_dom]
    push_neg at h_m h_k_lo h_k_hi h_s_lo h_s_hi
    obtain ⟨hm0, hm53, hq_lo, hq_hi, hk⟩ := h_dom
    show (shiftedSig_u64_kernel (UInt64.ofNat m) _ _
            (UInt64.ofNat ((pow10Lookup128 (-k)).2.2 - q).toNat)).toNat
          = shiftedSig m q k
    -- Bridge the pure UInt64 kernel to the widened packed kernel (no B<2^64).
    have h_kernel := shiftedSig_u64_kernel_eq_packed_w q k m
                       (pow10Lookup128 (-k)).1 (pow10Lookup128 (-k)).2.1
                       ((pow10Lookup128 (-k)).2.2 - q)
                       h_m h_k_lo h_k_hi (by omega) (by omega)
    rw [h_kernel]
    -- The widened packed result fits in UInt64 (fast branch returns a UInt64).
    have hlt : shiftedSig_packed_w q k (pow10Lookup128 (-k)).1 (pow10Lookup128 (-k)).2.1
                 ((pow10Lookup128 (-k)).2.2 - q) m < (1 <<< 64 : Nat) := by
      unfold shiftedSig_packed_w
      rw [if_neg (by omega : ¬ m ≥ (1 <<< 60 : Nat))]
      rw [if_neg (by push_neg; constructor <;> omega
                    : ¬ ((-k : Int) < pow10Table128_kMin ∨ (-k : Int) > pow10Table128_kMax))]
      rw [if_neg (by push_neg; constructor <;> omega
                    : ¬ (((pow10Lookup128 (-k)).2.2 - q) < 124 ∨
                         ((pow10Lookup128 (-k)).2.2 - q) ≥ 192))]
      exact UInt64.toNat_lt _
    rw [UInt64.toNat_ofNat']
    rw [Nat.mod_eq_of_lt (by show _ < 2 ^ 64; omega)]
    -- Close via the R20 widened round-trip.
    subst hk
    exact shiftedSig_packed_w_eq_binary64 m q hm0 hm53 hq_lo hq_hi
  · rw [dif_neg h_dom]

theorem shiftedSig_v2_eq (m : Nat) (q k : Int) :
    shiftedSig_v2 m q k = shiftedSig m q k := by
  unfold shiftedSig_v2
  by_cases hbin : 0 < m ∧ m < 2 ^ 53 ∧ -1074 ≤ q ∧ q ≤ 971 ∧ k = kOfMQ m q
  · rw [if_pos hbin]
    obtain ⟨hm, hm53, hq_lo, hq_hi, hk⟩ := hbin
    subst hk
    exact shiftedSig_packed_w_eq_binary64 m q hm hm53 hq_lo hq_hi
  · rw [if_neg hbin]

/-- Runtime substitution: `shiftedSig_v2` is compiled as `shiftedSig_v3`.
    Both have the same spec (`= shiftedSig`); v3 skips boxed-Int guards. -/
@[csimp]
theorem shiftedSig_v2_eq_v3_csimp :
    @shiftedSig_v2 = @shiftedSig_v3 := by
  funext m q k
  rw [shiftedSig_v2_eq, ← shiftedSig_v3_eq]

/-- All-UInt64 fast path for `shortestUnsigned`.  Returns `none` if any
    precondition or kernel guard fails (caller falls back to
    `shortestUnsigned_packed`).

    Uses `inRoundingInterval_u64_packed_u8` (UInt8 sentinel) at the
    two kHigh callsites to avoid `Option Bool` heap allocation. -/
@[inline]
def shortestUnsigned_u64_opt (m : Nat) (q : Int) : Option (Nat × Int) :=
  -- Defensive: only proceed for inputs in the binary64 fast regime.
  if _h_m : m ≥ (1 <<< 53 : Nat) then none
  else if _h_q_lo : q < (-1074 : Int) then none
  else if _h_q_hi : q > 971 then none
  else
    let irregular := isIrregular m q
    let k := kOfMQ_fast m q
    -- Defensive: ensure k and k+1 are inside the pow10 table range,
    -- required for the cmpScaledMixed_packed bridge precondition.
    if _h_k_lo : k < pow10Table128_kMin then none
    else if _h_k_hi : k + 1 > pow10Table128_kMax then none
    else
    -- Compute s = shiftedSig m q k via the B-cheap-check dispatch,
    -- avoiding the giant-Nat allocation that `shiftedSig_fast2` does
    -- on every call.  v3 additionally uses a pure-UInt64 kernel that
    -- skips the four boxed-Int guards inside `shiftedSig_packed`.
    -- Identical value to `shiftedSig m q k`.
    let s := shiftedSig_v3 m q k
    if _h_s : s ≥ (1 <<< 57 : Nat) then none  -- defensive
    else
      let sU : UInt64 := UInt64.ofNat s
      let mU : UInt64 := UInt64.ofNat m
      if s ≥ 10 then
        let kHigh : Int := k + 1
        let cmpTupleH := pow10Lookup128 kHigh
        let cmpHGHi := cmpTupleH.1
        let cmpHGLo := cmpTupleH.2.1
        let cmpHH := cmpTupleH.2.2
        let cmpHQPlusH : Int := q + cmpHH
        if _h_qh_lo : cmpHQPlusH < 64 then none
        else if _h_qh_hi : cmpHQPlusH > 132 then none
        else
          let cmpHQPlusH8 : UInt64 := UInt64.ofNat cmpHQPlusH.toNat
          let sHighU : UInt64 := sU / 10
          -- u8-packed inRoundingInterval: shares R = 4·s·G between the
          -- two cmps inside; returns UInt8 sentinel (no Option boxing).
          let uV := inRoundingInterval_u64_packed_u8 cmpHGHi cmpHGLo cmpHQPlusH8
                      sHighU mU irregular
          if uV = inRoundingInterval_u8_AMBIG then none
          else if uV = inRoundingInterval_u8_TRUE then some (sHighU.toNat, kHigh)
          else
            let wV := inRoundingInterval_u64_packed_u8 cmpHGHi cmpHGLo cmpHQPlusH8
                        (sHighU + 1) mU irregular
            if wV = inRoundingInterval_u8_AMBIG then none
            else if wV = inRoundingInterval_u8_TRUE then some ((sHighU + 1).toNat, kHigh)
            else
              -- Fall through to pickNearer at k.
              let cmpTuple := pow10Lookup128 k
              let cmpGHi := cmpTuple.1
              let cmpGLo := cmpTuple.2.1
              let cmpH := cmpTuple.2.2
              let cmpQPlusH : Int := q + cmpH
              if _h_qh2_lo : cmpQPlusH < 64 then none
              else if _h_qh2_hi : cmpQPlusH > 132 then none
              else
                let cmpQPlusH8 : UInt64 := UInt64.ofNat cmpQPlusH.toNat
                match pickNearer_u64_opt cmpGHi cmpGLo cmpQPlusH8 sU mU irregular with
                | none => none
                | some chosen => some (chosen.toNat, k)
      else if _h_s1 : s = 0 then none  -- bridge precondition: b = 4s ≠ 0
      else
        -- s < 10: only the pickNearer-at-k path.
        let cmpTuple := pow10Lookup128 k
        let cmpGHi := cmpTuple.1
        let cmpGLo := cmpTuple.2.1
        let cmpH := cmpTuple.2.2
        let cmpQPlusH : Int := q + cmpH
        if _h_qh2_lo : cmpQPlusH < 64 then none
        else if _h_qh2_hi : cmpQPlusH > 132 then none
        else
          let cmpQPlusH8 : UInt64 := UInt64.ofNat cmpQPlusH.toNat
          match pickNearer_u64_opt cmpGHi cmpGLo cmpQPlusH8 sU mU irregular with
          | none => none
          | some chosen => some (chosen.toNat, k)

/-- Top-level: try the all-UInt64 fast path, fall back to `_packed`. -/
@[inline]
def shortestUnsigned_v2 (m : Nat) (q : Int) : Nat × Int :=
  match shortestUnsigned_u64_opt m q with
  | some v => v
  | none => shortestUnsigned_packed m q

/-! ## v2 of the UInt64 fast path: returns `UInt64` significand directly.

`shortestUnsigned_u64_opt` does a `Nat ↔ UInt64` round-trip on the
significand `s`: `shiftedSig_v3` computes a UInt64 internally then
`.toNat`s, and the caller immediately `UInt64.ofNat`-converts back.
Worse, the defensive guard `s ≥ (1 <<< 57 : Nat)` runs in boxed `Nat`.

This v2 family bypasses both round-trips: it computes `sU : UInt64`
directly via `shiftedSig_u64_kernel`, runs all guards in `UInt64`, and
returns `Option (UInt64 × Int)`.  The caller (`shortestUnsigned_v3`)
does the final `.toNat` once at the boundary.

The outer guards are the same as `shortestUnsigned_u64_opt`; the
inner-fast-path guards (`m < 2^60`, `shiftAmt ∈ [124, 192)`, B-check)
are added explicitly so the kernel runs only when its preconditions
are met (the outer `m < 2^53` implies `m < 2^60` but the kernel proof
needs the latter).  Falls back to `shortestUnsigned_packed` on any
guard failure (via the wrapper). -/
@[inline]
def shortestUnsigned_u64_opt_v2 (m : Nat) (q : Int) : Option (UInt64 × Int) :=
  if _h_m : m ≥ (1 <<< 53 : Nat) then none
  else if _h_q_lo : q < (-1074 : Int) then none
  else if _h_q_hi : q > 971 then none
  else
    let irregular := isIrregular m q
    let k := kOfMQ_fast m q
    if _h_k_lo : k < pow10Table128_kMin then none
    else if _h_k_hi : k + 1 > pow10Table128_kMax then none
    else
      -- Use shiftedSig_v3 which has its own internal guards and a Nat
      -- fallback.  This means if the cheap-B check fails (e.g. subnormals),
      -- shiftedSig_v3 falls back to the slow Nat path, but we KEEP going
      -- in the UInt64 fast path for inRoundingInterval / pickNearer.
      -- This matches v1's behaviour and avoids hard-fallback to _packed.
      let s := shiftedSig_v3 m q k
      if _h_s : s ≥ (1 <<< 57 : Nat) then none  -- defensive
      else
        let sU : UInt64 := UInt64.ofNat s
        let mU : UInt64 := UInt64.ofNat m
        if sU ≥ (10 : UInt64) then
          let kHigh : Int := k + 1
          let cmpTupleH := pow10Lookup128 kHigh
          let cmpHGHi := cmpTupleH.1
          let cmpHGLo := cmpTupleH.2.1
          let cmpHH := cmpTupleH.2.2
          let cmpHQPlusH : Int := q + cmpHH
          if _h_qh_lo : cmpHQPlusH < 64 then none
          else if _h_qh_hi : cmpHQPlusH > 132 then none
          else
            let cmpHQPlusH8 : UInt64 := UInt64.ofNat cmpHQPlusH.toNat
            let sHighU : UInt64 := sU / 10
            let uV := inRoundingInterval_u64_packed_u8 cmpHGHi cmpHGLo cmpHQPlusH8
                        sHighU mU irregular
            if uV = inRoundingInterval_u8_AMBIG then none
            else if uV = inRoundingInterval_u8_TRUE then some (sHighU, kHigh)
            else
              let wV := inRoundingInterval_u64_packed_u8 cmpHGHi cmpHGLo cmpHQPlusH8
                          (sHighU + 1) mU irregular
              if wV = inRoundingInterval_u8_AMBIG then none
              else if wV = inRoundingInterval_u8_TRUE then some (sHighU + 1, kHigh)
              else
                let cmpTuple := pow10Lookup128 k
                let cmpGHi := cmpTuple.1
                let cmpGLo := cmpTuple.2.1
                let cmpH := cmpTuple.2.2
                let cmpQPlusH : Int := q + cmpH
                if _h_qh2_lo : cmpQPlusH < 64 then none
                else if _h_qh2_hi : cmpQPlusH > 132 then none
                else
                  let cmpQPlusH8 : UInt64 := UInt64.ofNat cmpQPlusH.toNat
                  match pickNearer_u64_opt cmpGHi cmpGLo cmpQPlusH8 sU mU irregular with
                  | none => none
                  | some chosen => some (chosen, k)
        else if _h_s1 : sU = 0 then none
        else
          let cmpTuple := pow10Lookup128 k
          let cmpGHi := cmpTuple.1
          let cmpGLo := cmpTuple.2.1
          let cmpH := cmpTuple.2.2
          let cmpQPlusH : Int := q + cmpH
          if _h_qh2_lo : cmpQPlusH < 64 then none
          else if _h_qh2_hi : cmpQPlusH > 132 then none
          else
            let cmpQPlusH8 : UInt64 := UInt64.ofNat cmpQPlusH.toNat
            match pickNearer_u64_opt cmpGHi cmpGLo cmpQPlusH8 sU mU irregular with
            | none => none
            | some chosen => some (chosen, k)

/-- v3 top-level: UInt64-throughout fast path with `.toNat` at the
    boundary.  Falls back to `_packed` on any guard failure. -/
@[inline]
def shortestUnsigned_v3 (m : Nat) (q : Int) : Nat × Int :=
  match shortestUnsigned_u64_opt_v2 m q with
  | some (sU, k) => (sU.toNat, k)
  | none => shortestUnsigned_packed m q

/-- Bridge: the `inRoundingInterval_u64_packed_u8` if-chain inside
    `shortestUnsigned_u64_opt` is equivalent to matching on
    `inRoundingInterval_u64_opt`.  Used by the bridge proof so the
    pre-existing `inRoundingInterval_u64_opt_some_eq_packed` machinery
    can still be applied. -/
theorem packed_u8_dispatch_eq_opt_match
    {α : Type} (gHi gLo qPlusH8 sU mU : UInt64) (irregular : Bool)
    (rNone rTrue rFalse : α) :
    (let v := inRoundingInterval_u64_packed_u8 gHi gLo qPlusH8 sU mU irregular
     if v = inRoundingInterval_u8_AMBIG then rNone
     else if v = inRoundingInterval_u8_TRUE then rTrue
     else rFalse) =
    (match inRoundingInterval_u64_opt gHi gLo qPlusH8 sU mU irregular with
     | none => rNone
     | some true => rTrue
     | some false => rFalse) := by
  rw [show inRoundingInterval_u64_packed_u8 gHi gLo qPlusH8 sU mU irregular =
        (match inRoundingInterval_u64_opt gHi gLo qPlusH8 sU mU irregular with
         | none => inRoundingInterval_u8_AMBIG
         | some true => inRoundingInterval_u8_TRUE
         | some false => inRoundingInterval_u8_FALSE) from
        inRoundingInterval_u64_packed_u8_eq _ _ _ _ _ _]
  cases inRoundingInterval_u64_opt gHi gLo qPlusH8 sU mU irregular with
  | none => simp [inRoundingInterval_u8_AMBIG]
  | some b =>
    cases b
    · simp [inRoundingInterval_u8_AMBIG, inRoundingInterval_u8_TRUE,
            inRoundingInterval_u8_FALSE]
    · simp [inRoundingInterval_u8_AMBIG, inRoundingInterval_u8_TRUE]

end Srtfp.Schubfach

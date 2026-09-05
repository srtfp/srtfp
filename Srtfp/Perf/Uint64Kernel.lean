module
/- The all-`UInt64` comparator behind the live kernels: `cmpScaledMixed`
   with the 128-bit table product and strict `gt192` / `le192` verdicts
   (`0` when the product is not decisive), the `UInt64` floor-log and `k`
   forms, and the `UInt64` arithmetic identities the kernel proofs use
   under binary64 size bounds. -/
public import Srtfp.Perf.Schubfach
public import Srtfp.Perf.Orchestration
public import Srtfp.Perf.Tactics

@[expose] public section

namespace Srtfp.Schubfach

/-! ## Pure-UInt64 comparator

`cmpScaledMixed_u64` returns the ternary verdict as an `Int` (`+1` = GT,
`-1` = LT, `0` = ambiguous). The caller handles the ambiguous case by
falling back. `cmpScaledMixed` itself can return `0` (EQ); the strict
kernel returns `0` ONLY when ambiguous, so a true EQ reaches the fallback. -/

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

/-! ## `UInt64` identities under binary64 size bounds

For `m ≤ 2^53` and `s < 10^17 < 2^57`, the shifts and small-constant
additions the kernels do are overflow-free. -/

/-- `x <<< 2 = 4 * x` as UInt64 (always — wraparound matches both sides). -/
theorem uint64_shiftLeft_2 (x : UInt64) : x <<< 2 = 4 * x := by
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_shiftLeft, UInt64.toNat_mul]
  have h2 : ((2 : UInt64).toNat % 64) = 2 := by decide
  have h4 : ((4 : UInt64).toNat) = 4 := by decide
  rw [h2, h4]
  simp [Nat.shiftLeft_eq, Nat.mul_comm]

/-- `x <<< 1 = 2 * x` as UInt64. -/
theorem uint64_shiftLeft_1 (x : UInt64) : x <<< 1 = 2 * x := by
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_shiftLeft, UInt64.toNat_mul]
  have h1 : ((1 : UInt64).toNat % 64) = 1 := by decide
  have h2 : ((2 : UInt64).toNat) = 2 := by decide
  rw [h1, h2]
  simp [Nat.shiftLeft_eq, Nat.mul_comm]

/-- For `m ≥ 1`, `(4·m - 2 : Int).toNat = 4*m - 2`. -/
theorem toNat_4m_sub_2_eq {m : Nat} (hm_pos : m ≥ 1) :
    (4 * (m : Int) - 2).toNat = 4 * m - 2 := by
  omega

/-- For `m ≥ 1`, `(4·m - 1 : Int).toNat = 4*m - 1`. -/
theorem toNat_4m_sub_1_eq {m : Nat} (hm_pos : m ≥ 1) :
    (4 * (m : Int) - 1).toNat = 4 * m - 1 := by
  omega

/-- `(4·m + 2 : Int).toNat = 4*m + 2`. -/
theorem toNat_4m_add_2_eq (m : Nat) : (4 * (m : Int) + 2).toNat = 4 * m + 2 := by
  omega

/-- `(4·s : Int).toNat = 4*s`. -/
theorem toNat_4s_eq (s : Nat) : (4 * (s : Int)).toNat = 4 * s := by omega

/-- `(2·m : Int).toNat = 2*m`. -/
theorem toNat_2m_eq (m : Nat) : (2 * (m : Int)).toNat = 2 * m := by omega

/-- `(2·s + 1 : Int).toNat = 2*s + 1`. -/
theorem toNat_2s_add_1_eq (s : Nat) : (2 * (s : Int) + 1).toNat = 2 * s + 1 := by omega

/-- `UInt64.ofNat (4m - 2) = (UInt64.ofNat m) <<< 2 - 2` when `m ≥ 1`. -/
theorem ofNat_4m_sub_2 {m : Nat} (hm_pos : m ≥ 1) :
    UInt64.ofNat (4 * m - 2) = (UInt64.ofNat m) <<< 2 - 2 := by
  rw [uint64_shiftLeft_2]
  have h1 : 4 * m = (4 * m - 2) + 2 := by omega
  have h2 : UInt64.ofNat (4 * m) = UInt64.ofNat (4 * m - 2) + UInt64.ofNat 2 := by
    conv => lhs; rw [h1]
    rw [UInt64.ofNat_add]
  rw [UInt64.ofNat_mul] at h2
  have h3 : (UInt64.ofNat 4 : UInt64) = 4 := rfl
  have h4 : (UInt64.ofNat 2 : UInt64) = 2 := rfl
  rw [h3, h4] at h2
  -- h2 : 4 * UInt64.ofNat m = UInt64.ofNat (4 * m - 2) + 2
  -- Goal: UInt64.ofNat (4 * m - 2) = 4 * UInt64.ofNat m - 2
  rw [h2]
  -- Goal: UInt64.ofNat (4 * m - 2) = UInt64.ofNat (4 * m - 2) + 2 - 2
  -- Use BitVec underlying grind structure: (x + 2) - 2 = x.
  apply UInt64.toBitVec_inj.mp
  simp []

/-- `UInt64.ofNat (4m - 1) = (UInt64.ofNat m) <<< 2 - 1` when `m ≥ 1`. -/
theorem ofNat_4m_sub_1 {m : Nat} (hm_pos : m ≥ 1) :
    UInt64.ofNat (4 * m - 1) = (UInt64.ofNat m) <<< 2 - 1 := by
  rw [uint64_shiftLeft_2]
  have h1 : 4 * m = (4 * m - 1) + 1 := by omega
  have h2 : UInt64.ofNat (4 * m) = UInt64.ofNat (4 * m - 1) + UInt64.ofNat 1 := by
    conv => lhs; rw [h1]
    rw [UInt64.ofNat_add]
  rw [UInt64.ofNat_mul] at h2
  have h3 : (UInt64.ofNat 4 : UInt64) = 4 := rfl
  have h4 : (UInt64.ofNat 1 : UInt64) = 1 := rfl
  rw [h3, h4] at h2
  rw [h2]
  apply UInt64.toBitVec_inj.mp
  simp []

/-- `UInt64.ofNat (4m + 2) = (UInt64.ofNat m) <<< 2 + 2`. -/
theorem ofNat_4m_add_2 (m : Nat) :
    UInt64.ofNat (4 * m + 2) = (UInt64.ofNat m) <<< 2 + 2 := by
  rw [uint64_shiftLeft_2]
  rw [UInt64.ofNat_add, UInt64.ofNat_mul]
  rfl

/-- `UInt64.ofNat (4s) = (UInt64.ofNat s) <<< 2`. -/
theorem ofNat_4s (s : Nat) :
    UInt64.ofNat (4 * s) = (UInt64.ofNat s) <<< 2 := by
  rw [uint64_shiftLeft_2, UInt64.ofNat_mul]
  rfl

/-- `UInt64.ofNat (2m) = (UInt64.ofNat m) <<< 1`. -/
theorem ofNat_2m (m : Nat) :
    UInt64.ofNat (2 * m) = (UInt64.ofNat m) <<< 1 := by
  rw [uint64_shiftLeft_1, UInt64.ofNat_mul]
  rfl

/-- `UInt64.ofNat (2s + 1) = (UInt64.ofNat s) <<< 1 + 1`. -/
theorem ofNat_2s_add_1 (s : Nat) :
    UInt64.ofNat (2 * s + 1) = (UInt64.ofNat s) <<< 1 + 1 := by
  rw [uint64_shiftLeft_1, UInt64.ofNat_add, UInt64.ofNat_mul]
  rfl

/-- Strict-verdict version: when the UInt64 kernel returns a nonzero value,
    `cmpScaledMixed_packed` agrees with it.  Stated under the same
    preconditions as `cmpScaledMixed_packed_eq_u64_branch`. -/
theorem cmpScaledMixed_packed_eq_u64_of_strict
    (q k : Int) (gHi gLo : UInt64) (qPlusH : Int)
    (a b : Int)
    (ha_nn : 0 ≤ a) (hb_nn : 0 ≤ b)
    (hb_pos : b ≠ 0)
    (ha_lt : a < (1 <<< 60 : Int)) (hb_lt : b < (1 <<< 60 : Int))
    (hk_lo : pow10Table128_kMin ≤ k) (hk_hi : k ≤ pow10Table128_kMax)
    (hqh_lo : 64 ≤ qPlusH) (hqh_hi : qPlusH ≤ 132)
    (hstrict : cmpScaledMixed_u64 gHi gLo (UInt64.ofNat qPlusH.toNat)
                  (UInt64.ofNat a.toNat) (UInt64.ofNat b.toNat) ≠ 0) :
    cmpScaledMixed_packed q k gHi gLo qPlusH a b =
      cmpScaledMixed_u64 gHi gLo (UInt64.ofNat qPlusH.toNat)
        (UInt64.ofNat a.toNat) (UInt64.ofNat b.toNat) := by
  rw [cmpScaledMixed_packed_eq_u64_branch _ _ _ _ _ _ _ ha_nn hb_nn hb_pos
        ha_lt hb_lt hk_lo hk_hi hqh_lo hqh_hi]
  simp only [if_neg hstrict]

/-- Helper: `UInt64.ofNat (s + 1) = UInt64.ofNat s + 1`. -/
theorem ofNat_succ (s : Nat) :
    UInt64.ofNat (s + 1) = UInt64.ofNat s + 1 := by
  rw [UInt64.ofNat_add]; rfl

/-- `(UInt64.ofNat s).toNat = s` when `s < 2^64`. -/
theorem toNat_sU_eq {s : Nat} (hs_lt : s < (1 <<< 58 : Nat)) :
    (UInt64.ofNat s).toNat = s := by
  rw [UInt64.toNat_ofNat']
  apply Nat.mod_eq_of_lt
  have h64 : (1 <<< 58 : Nat) < (2 ^ 64 : Nat) := by decide
  omega

/-- `UInt64.ofNat (s/10) = UInt64.ofNat s / 10` when `s < 2^57`. -/
theorem uint64_div_10 {s : Nat} (hs : s < (1 <<< 57 : Nat)) :
    UInt64.ofNat s / 10 = UInt64.ofNat (s / 10) := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_div]
  simp only [UInt64.toNat_ofNat']
  have h10 : ((10 : UInt64).toNat) = 10 := by decide
  rw [h10]
  have hs64 : s < 2^64 := by
    have : (1 <<< 57 : Nat) < 2^64 := by decide
    omega
  rw [Nat.mod_eq_of_lt hs64]
  have h10_lt : s / 10 < 2^64 := by
    have : s / 10 ≤ s := Nat.div_le_self _ _
    omega
  rw [Nat.mod_eq_of_lt h10_lt]

/-- For `n < 2^64`, `(UInt64.ofNat n).toNat = n`. -/
theorem toNat_ofNat_bounded {n : Nat} (h : n < 2^64) :
    (UInt64.ofNat n).toNat = n := by
  rw [UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt h

/-- UInt64 / Nat comparison: `sU ≥ 10 ↔ sU.toNat ≥ 10`. -/
theorem uint64_ge_10 (sU : UInt64) :
    sU ≥ (10 : UInt64) ↔ sU.toNat ≥ 10 := by
  constructor
  · intro h
    exact UInt64.le_iff_toNat_le.mp h
  · intro h
    exact UInt64.le_iff_toNat_le.mpr h

/-- UInt64 / Nat equality: `sU = 0 ↔ sU.toNat = 0`. -/
theorem uint64_eq_0 (sU : UInt64) :
    sU = 0 ↔ sU.toNat = 0 := by
  constructor
  · intro h; rw [h]; rfl
  · intro h
    rw [← UInt64.toNat_inj, h]; rfl

end Srtfp.Schubfach

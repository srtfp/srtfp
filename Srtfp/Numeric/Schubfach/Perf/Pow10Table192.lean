/- 192-bit power-of-10 table for the Schubfach multiply-shift kernel.

   For each `k ∈ [-324, 324]`, the table stores a 192-bit unsigned
   approximation of `10^k`:

       g_k · 2^{-h_k} ≈ 10^k        with relative error < 2^{-191}

   where `g_k = gHi_k · 2^128 + gMid_k · 2^64 + gLo_k`,
   `gHi_k, gMid_k, gLo_k : UInt64`, and `h_k : Int` is the binary scaling
   exponent.

   This wider table (vs the 128-bit `pow10Table128`) eliminates the
   slow-path fallback for subnormals (e.g. `5e-324`) and very-large
   floats (e.g. `1.8e308`), where the 128-bit precision is too tight
   for the kernel guards to pass.  The 192-bit kernel uses one more
   64-bit multiply but stays on the fast path universally.

   Entry layout matches `pow10Table128`:
     - Index `i ∈ [0, 649)` corresponds to `k = -324 + i`.
     - Each entry is `(gHi, gMid, gLo, h)` with `g = ⌈10^k · 2^h⌉`,
       normalized so `g ∈ [2^191, 2^192)`.

   The table is generated at compile time by the in-file generator
   `genPow10Entry192` (a pure `Nat`/`Int` transliteration of the
   construction; see its docstring), spliced as an `Array` literal by the
   `genPow10Table192%` elaborator.  Verified by `tableInv192`
   (`native_decide`).  Note `h192 = h128 + 64` for every entry (precision
   gain of exactly 64 bits).
-/

import Lean

namespace PP.Numeric.Schubfach

set_option maxRecDepth 16384

/-- The smallest tabulated `k`. -/
def pow10Table192_kMin : Int := -324

/-- The largest tabulated `k`. -/
def pow10Table192_kMax : Int := 324

/-- Number of entries in the table. -/
def pow10Table192_size : Nat := 649

/-! ## Compile-time table generator

The table is generated at elaboration time by `genPow10Table192` below and
spliced in as an `Array` literal (see `pow10Table192`).  This in-Lean
generator replaces the former external `tools/gen_pow10_192.py`. -/

/-- `⌈a / b⌉` for `b > 0`. -/
@[inline] def ceilDiv (a b : Nat) : Nat := (a + b - 1) / b

/-- Generate the 192-bit pow10 entry `(gHi, gMid, gLo, h)` for decimal
    exponent `k`, where `g = gHi·2^128 + gMid·2^64 + gLo` is the smallest
    192-bit number with `g·2^{-h} ≥ 10^k` and `g ∈ [2^191, 2^192)`.

    Construction (`prec = 192`):
    * For `k ≥ 0`: `h = (prec-1) - ⌊log₂(10^k)⌋`.  If `h ≥ 0`,
      `g = 10^k · 2^h` exactly; otherwise `g = ⌈10^k / 2^{-h}⌉`.
    * For `k < 0`: `h = prec + ⌊log₂(10^{-k})⌋` and `g = ⌈2^h / 10^{-k}⌉`;
      if this overshoots (`g ≥ 2^prec`), decrement `h` by one and recompute.

    `Nat.log2 n = ⌊log₂ n⌋` for `n ≥ 1`, so `Nat.log2 (10^…)` is the bit
    length minus one.  This is a pure `Nat`/`Int` bignum transliteration of
    the former Python reference generator; it runs at compile time only. -/
def genPow10Entry192 (k : Int) : UInt64 × UInt64 × UInt64 × Int :=
  let prec : Nat := 192
  let gh : Nat × Int :=
    if k ≥ 0 then
      let tenK : Nat := 10 ^ k.toNat
      let l2 : Int := (Nat.log2 tenK : Int)        -- ⌊log₂(10^k)⌋
      let h : Int := ((prec : Int) - 1) - l2
      if h ≥ 0 then
        (tenK <<< h.toNat, h)                       -- exact shift
      else
        (ceilDiv tenK (2 ^ (-h).toNat), h)
    else
      let tenNegK : Nat := 10 ^ (-k).toNat
      let l2 : Nat := Nat.log2 tenNegK
      let h0 : Int := ((prec : Int) - 1) + (l2 : Int) + 1
      let g0 : Nat := ceilDiv (2 ^ h0.toNat) tenNegK
      if g0 ≥ 2 ^ prec then
        let h1 : Int := h0 - 1
        (ceilDiv (2 ^ h1.toNat) tenNegK, h1)
      else
        (g0, h0)
  let g := gh.1
  let h := gh.2
  let mask64 : Nat := 2 ^ 64 - 1
  let gLo : UInt64 := UInt64.ofNat (g &&& mask64)
  let gMid : UInt64 := UInt64.ofNat ((g >>> 64) &&& mask64)
  let gHi : UInt64 := UInt64.ofNat ((g >>> 128) &&& mask64)
  (gHi, gMid, gLo, h)

/-- The full table as a function: map `genPow10Entry192` over the index
    range `i ∈ [0, 649)`, i.e. `k = pow10Table192_kMin + i ∈ [-324, 324]`. -/
def genPow10Table192 : Array (UInt64 × UInt64 × UInt64 × Int) :=
  (Array.range pow10Table192_size).map fun i =>
    genPow10Entry192 (pow10Table192_kMin + (i : Nat))

open Lean Elab Term Meta in
/-- Run the compiled `genPow10Table192` at elaboration time (via the
    `unsafe` `evalExpr`, which interprets compiled meta-level code). -/
unsafe def evalGenPow10Table192Unsafe : MetaM (Array (UInt64 × UInt64 × UInt64 × Int)) :=
  evalExpr (Array (UInt64 × UInt64 × UInt64 × Int))
    (ToExpr.toTypeExpr (Array (UInt64 × UInt64 × UInt64 × Int)))
    (mkConst ``genPow10Table192)

open Lean Elab Term Meta in
/-- Compile-time term elaborator: evaluates `genPow10Table192` in `MetaM`
    (running the compiled generator at elaboration time) and emits the
    result as an `Array` *literal* via `ToExpr`.  The produced term is
    `List.toArray [(…), …]` — exactly what the surface syntax `#[…]`
    desugars to — so the C backend compiles it as constant data with no
    runtime/startup computation. -/
elab "genPow10Table192%" : term => do
  let table ← unsafe evalGenPow10Table192Unsafe
  return ToExpr.toExpr table

/-- Raw 192-bit pow10 entries `(gHi, gMid, gLo, h)` for `k ∈ [-324, 324]`,
    indexed by `(k - pow10Table192_kMin).toNat`.

    The body is produced at elaboration time by `genPow10Table192%`, which
    splices in an `Array` literal (`List.toArray [...]`).  After elaboration
    this is constant data identical to a hand-written `#[...]`. -/
def pow10Table192 : Array (UInt64 × UInt64 × UInt64 × Int) := genPow10Table192%

/-- Default fallback entry, used for out-of-range `k`.  The fallback is
    safe but useless: lookups outside `[kMin, kMax]` shouldn't happen for
    binary64 inputs, but we still want a total function. -/
def pow10Table192_default : UInt64 × UInt64 × UInt64 × Int := (0, 0, 0, 0)

/-- Lookup `(gHi, gMid, gLo, h)` for the given decimal exponent `k`.
    Returns `pow10Table192_default` if `k` is outside `[kMin, kMax]`. -/
@[inline]
def pow10Lookup192 (k : Int) : UInt64 × UInt64 × UInt64 × Int :=
  if k < pow10Table192_kMin then pow10Table192_default
  else
    -- Index relative to `pow10Table192_kMin = -324`; out-of-upper-range
    -- is caught by `Array.getD`.
    let i : Nat := (k + 324).toNat
    pow10Table192.getD i pow10Table192_default

end PP.Numeric.Schubfach

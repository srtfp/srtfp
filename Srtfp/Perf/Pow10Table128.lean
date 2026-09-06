module
/- The 128-bit power-of-ten table of the fast reader (`ReadFast.lean`).

   For each `k ∈ [-324, 324]` the entry `(gHi, gLo, h)` is the 128-bit
   ceiling approximation of `10^k`:

       g = gHi · 2^64 + gLo = ⌈10^k · 2^h⌉,   2^127 ≤ g < 2^128,

   so `g · 2^{-h} ∈ [10^k, 10^k + 2^{-h})`, the invariant the reader's
   proof consumes (`pow10Lookup128_invariant`,
   `Srtfp/Perf/TableInvariant.lean`). The magnitude (the multiply) and
   the scaling (the shift) evaluate `b · 10^k` as a 192-bit product and a
   power-of-two shift. The table is computed once, when the module loads. -/

@[expose] public section

namespace Srtfp.Schubfach

/-- `10^k · 2^h` as a quotient of naturals, `pow10Num k h / pow10Den k h`
    (`Int.toNat` clips a negative exponent to zero). -/
def pow10Num (k h : Int) : Nat := 10 ^ k.toNat * 2 ^ h.toNat

def pow10Den (k h : Int) : Nat := 10 ^ (-k).toNat * 2 ^ (-h).toNat

/-- `⌈10^k · 2^h⌉`. -/
def pow10Ceil (k h : Int) : Nat := (pow10Num k h + pow10Den k h - 1) / pow10Den k h

/-- The exponent `h` with `2^127 ≤ 10^k · 2^h < 2^128`, i.e. `127 - ⌊log₂ 10^k⌋`. -/
def pow10Shift (k : Int) : Int :=
  if k ≥ 0 then 127 - (Nat.log2 (10 ^ k.toNat) : Int)
  else 128 + (Nat.log2 (10 ^ (-k).toNat) : Int)

/-- The entry for `k`: the two words of `⌈10^k · 2^h⌉` and `h`. That the
    ceiling is a 128-bit number for every tabulated `k` is checked by
    kernel evaluation (`ceilFits`, `Srtfp/Perf/TableInvariant.lean`). -/
def pow10Entry (k : Int) : UInt64 × UInt64 × Int :=
  let h := pow10Shift k
  let g := pow10Ceil k h
  (UInt64.ofNat (g >>> 64), UInt64.ofNat g, h)

/-- The smallest tabulated `k`.  Indexing convention: index `i` corresponds
    to `k = pow10Table128_kMin + i`. -/
def pow10Table128_kMin : Int := -324

/-- The largest tabulated `k`. -/
def pow10Table128_kMax : Int := 324

/-- The entries `(gHi, gLo, h)` for `k ∈ [-324, 324]`, indexed by
    `(k - pow10Table128_kMin).toNat`. -/
def pow10Table128 : Array (UInt64 × UInt64 × Int) :=
  (Array.range 649).map fun i : Nat => pow10Entry (↑i - 324)

/-- Default fallback entry, used for out-of-range `k`.  The fallback is
    safe but useless: lookups outside `[kMin, kMax]` shouldn't happen for
    binary64 inputs, but we still want a total function. -/
def pow10Table128_default : UInt64 × UInt64 × Int := (0, 0, 0)

/-- Lookup `(gHi, gLo, h)` for the given decimal exponent `k`.  Returns
    `pow10Table128_default` if `k` is outside `[kMin, kMax]`. -/
@[inline]
def pow10Lookup128 (k : Int) : UInt64 × UInt64 × Int :=
  if k < pow10Table128_kMin then pow10Table128_default
  else
    -- Index relative to `pow10Table128_kMin = -324`; out-of-upper-range
    -- is caught by `Array.getD`.
    let i : Nat := (k + 324).toNat
    pow10Table128.getD i pow10Table128_default

end Srtfp.Schubfach

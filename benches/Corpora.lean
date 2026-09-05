/- The three benchmark corpora, built at load time from a fixed seed.

   Every harness derives its inputs from this module: the Lean benches
   import it, and `lake exe genCorpora` (`benches/GenCorpora.lean`) writes
   the same bit patterns to `benches/corpora/<name>.u64` (one decimal
   IEEE-754 word per line) for the C++, Python and Java harnesses.
   `run.sh` cross-checks the checksums, so all four see identical inputs.

   - `adversarial`: every finite value of the Ryu test suite
     (`SrtfpTest/Ryu.lean`), hand-picked edge cases, ulp neighbours of
     powers of two, and the `0.1 + 0.2` family.
   - `nice`: a stratified model of JSON/API payloads (counts, currency,
     coordinates, timestamps, computed values).
   - `uniform`: random finite binary64 words (uniform sign, biased
     exponent in `[0, 2046]` and mantissa; the zero word is skipped). -/
import Std.Data.HashSet
import SrtfpTest.Ryu

namespace Corpora

/-! ## A tiny deterministic generator (SplitMix64) -/

structure Rng where
  state : UInt64

def Rng.next (r : Rng) : UInt64 × Rng :=
  let s := r.state + 0x9E3779B97F4A7C15
  let z := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31), ⟨s⟩)

/-- Uniform in `[lo, hi]` (the modulo bias is irrelevant at these ranges). -/
def Rng.int (r : Rng) (lo hi : Int) : Int × Rng :=
  let (u, r) := r.next
  (lo + (u.toNat % (hi - lo + 1).toNat : Nat), r)

/-- Uniform in `[0, 1)`, 53 random bits. -/
def Rng.unit (r : Rng) : Float × Rng :=
  let (u, r) := r.next
  ((u >>> 11).toFloat / 9007199254740992.0, r)

/-- Fisher–Yates shuffle. -/
def Rng.shuffle (r : Rng) (xs : Array Float) : Array Float × Rng := Id.run do
  let mut xs := xs
  let mut r := r
  for i in [1:xs.size] do
    let j := xs.size - i
    let (k, r') := r.int 0 j
    r := r'
    xs := xs.swapIfInBounds j k.toNat
  return (xs, r)

/-- Change the seed to draw a fresh random corpus. -/
def seed : UInt64 := 0xCCAA0ACB57FB88C0

/-! ## `nice` -/

/-- 45% small integers in `[0, 10000]`, 20% two-decimal fixed point in
    `[0.01, 1e5]`, 10% coordinates in `[-180, 180]` with 4–6 decimals,
    10% epoch seconds in `[1e9, 2e9]` (half with milliseconds), 15%
    computed values `m · 10^e` with `m ∈ [1, 10)`, `e ∈ [-6, 6]`; shuffled. -/
def nice : Array Float := Id.run do
  let n := 1024
  let mut r : Rng := ⟨seed ^^^ 0x4E696365⟩
  let mut out : Array Float := #[]
  for _ in [0:n * 45 / 100] do
    let (k, r') := r.int 0 10000
    r := r'
    out := out.push (Float.ofInt k)
  for _ in [0:n * 20 / 100] do
    let (cents, r') := r.int 1 10000000
    r := r'
    out := out.push (Float.ofInt cents / 100.0)
  for _ in [0:n * 10 / 100] do
    let (d, r') := r.int 4 6
    let scale : Int := 10 ^ d.toNat
    let (raw, r'') := r'.int (-180 * scale) (180 * scale)
    r := r''
    out := out.push (Float.ofInt raw / Float.ofInt scale)
  for i in [0:n * 10 / 100] do
    let (secs, r') := r.int 1000000000 2000000000
    r := r'
    if i % 2 == 0 then
      out := out.push (Float.ofInt secs)
    else
      let (ms, r') := r.int 0 999
      r := r'
      out := out.push (Float.ofInt secs + Float.ofInt ms / 1000.0)
  while out.size < n do
    let (u, r') := r.unit
    let (e, r'') := r'.int (-6) 6
    r := r''
    out := out.push ((1.0 + 8.9999 * u) * Float.pow 10.0 (Float.ofInt e))
  return (r.shuffle out).1

/-! ## `uniform` -/

def uniform : Array Float := Id.run do
  let mut r : Rng := ⟨seed ^^^ 0x556E6966⟩
  let mut out : Array Float := #[]
  while out.size < 1024 do
    let (u, r') := r.next
    let (e, r'') := r'.int 0 2046
    r := r''
    let mantissa := u &&& 0x000F_FFFF_FFFF_FFFF
    if !(e == 0 && mantissa == 0) then
      out := out.push (Float.ofBits ((u >>> 63 <<< 63) ||| (UInt64.ofNat e.toNat <<< 52) ||| mantissa))
  return out

/-! ## `adversarial` -/

open Srtfp.Tests.Ryu in
/-- Every value of the Ryu suite, in suite order. -/
def ryuSuite : Array Float :=
  (#[d2sBasic, d2sSwitchToSubnormal, d2sMinAndMax, d2sLotsOfTrailingZeros, d2sRegression,
     d2sLooksLikePow5, d2sOutputLength, d2sMinMaxShift, d2sSmallIntegers,
     f2sBasic, f2sSwitchToSubnormal, f2sMinAndMax, f2sBoundaryRoundEven,
     f2sExactValueRoundEven, f2sLotsOfTrailingZeros, f2sRegression, f2sLooksLikePow5,
     f2sOutputLength, d2sExactTies].flatten).map (·.2.1)

/-- The word with the given biased exponent and mantissa (positive). -/
def word (biasedExp mantissa : UInt64) : Float := Float.ofBits ((biasedExp <<< 52) ||| mantissa)

/-- `p`, and its two ulp neighbours. -/
def ulpNeighbours (p : Float) : Array Float :=
  #[p, Float.ofBits (p.toBits - 1), Float.ofBits (p.toBits + 1)]

def handPicked : Array Float :=
  -- the original 23
  #[0.0, 1.0, -1.0, 0.1, 1.5, 2.5, 3.5, 4.5,
    1.234567890123456e-10, 6.123456789012345e15,
    1.7976931348623157e308, 5e-324, 2.2250738585072014e-308,
    9.999999999999998e+22, 1.7976931348623155e308,
    12345.6789, -0.0001, 1e-100, 1e+100,
    3.141592653589793, 2.718281828459045,
    1.0000000000000002, 0.30000000000000004,
    -- Ryu / Schubfach hand-curated edge cases
    Float.ofBits 0x7FEFFFFFFFFFFFFF, Float.ofBits 0x0000000000000001,
    2.9802322387695312e-8, -2.109808898695963e16,
    4.940656e-318, 1.18575755e-316, 2.989102097996e-312,
    9.0608011534336e15, 4.708356024711512e18, 9.409340012568248e18,
    1.2345678,
    Float.ofBits 0x4830F0CF064DD592, Float.ofBits 0x4840F0CF064DD592, Float.ofBits 0x4850F0CF064DD592,
    -- output-length digit progression
    1.2, 1.23, 1.234, 1.2345, 1.23456, 1.234567, 1.23456789,
    1.234567895, 1.2345678901, 1.23456789012, 1.234567890123,
    1.2345678901234, 1.23456789012345, 1.234567890123456,
    1.2345678901234567,
    -- the 2^32 neighbourhood
    4.294967294, 4.294967295, 4.294967296, 4.294967297, 4.294967298,
    -- min/max shifts
    word 4 0, word 6 0xFFFFFFFFFFFFF, word 41 0, word 40 0xFFFFFFFFFFFFF,
    word 1077 0, word 1076 0xFFFFFFFFFFFFF, word 307 0, word 306 0xFFFFFFFFFFFFF,
    word 934 0x000FA7161A4D6E0C,
    -- the 2^53 boundary
    9007199254740991.0, 9007199254740992.0,
    -- powers of ten
    1e1, 1e2, 1e3, 1e4, 1e5, 1e6, 1e7, 1e8, 1e9, 1e10, 1e11, 1e12, 1e13, 1e14, 1e15,
    -- the largest power of two below 10^(i+1)
    8.0, 64.0, 512.0, 8192.0, 65536.0, 524288.0, 8388608.0,
    67108864.0, 536870912.0, 8589934592.0]
  -- ulp boundaries around powers of two
  ++ (#[-10, -2, -1, 0, 1, 2, 3, 4, 10, 20, 50, 100, 200, 1000] : Array Int).flatMap
       (fun k => ulpNeighbours (Float.pow 2.0 (Float.ofInt k)))
  -- the 0.1 + 0.2 family
  ++ #[0.1 + 0.2, 0.1 * 3, 0.3, 0.7 - 0.4, 1.0 / 3.0, 2.0 / 3.0]
  -- tiny but not subnormal, and the largest subnormal
  ++ #[Float.ofBits 0x0010000000000000, Float.ofBits 0x0010000000000001,
       Float.ofBits 0x000FFFFFFFFFFFFF]

/-- Finite values only, first occurrence of each bit pattern kept. -/
def dedupe (xs : Array Float) : Array Float := Id.run do
  let mut seen : Std.HashSet UInt64 := {}
  let mut out : Array Float := #[]
  for f in xs do
    let u := f.toBits
    if (u >>> 52) &&& 0x7FF != 0x7FF && !seen.contains u then
      seen := seen.insert u
      out := out.push f
  return out

def adversarial : Array Float := dedupe (ryuSuite ++ handPicked)

end Corpora

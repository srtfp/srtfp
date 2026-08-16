/- Hand-curated Ryu edge case tests, ported from `ulfjack/ryu`.

   Source files:
     - `ryu/Tests/conformance/d2s_test.cc` (double-precision, binary64) — primary
     - `ryu/Tests/conformance/f2s_test.cc` (single-precision, binary32) — adapted

   ## Comparison model

   We compare structurally on `(sign, significand, exponent)` after Schubfach
   canonicalisation, NOT on Ryu's textual rendering (e.g., "1.234E-3"). Our
   `Decimal` and Ryu's string both encode the same shortest round-trip
   decimal; format-level differences are not relevant.

   Each Ryu string is hand-converted as:
     "<digits-before-point>.<digits-after-point>E<exp>"
       → ⟨sign, sig := <digits>, exp := <exp> − count(digits-after-point)⟩
     "<sig>E<exp>"  → ⟨sign, sig, exp⟩ directly.

   ## Signed zero

   `-0.0` is preserved as the canonical negative zero `⟨true, 0, 0⟩`,
   matching Ryu's "-0E0" exactly (no divergence).

   ## f2s notes

   Every f32 value is exactly representable as f64, but f32-shortest and
   f64-shortest decimals differ in general (the f32-shortest is shorter
   when the f32 value has wider rounding tolerance). Lean's standard
   library exposes `Float32` with `Float32.ofBits` and `Float32.toFloat`;
   we widen each f32 to f64 and run our (f64) Schubfach. Expected outputs
   are therefore the **f64-shortest decimal of the widened value**, not
   Ryu's f32-shortest string. Cases that coincide (small integers, exact
   binary fractions, powers of 2) match Ryu literally; cases that differ
   are commented inline with both Ryu's f32 string and our f64 value. -/

import SrtfpTest.Spec
import Srtfp.Schubfach
import Srtfp.Schubfach.Perf.StringFast
import Srtfp.Clinger

namespace Srtfp.Tests.Ryu

open SrtfpSpec Srtfp

/-! ## Helpers -/

/-- Maximum f32 mantissa (`2^53 − 1`), used by Ryu's `ieeeParts2Double`. -/
private def maxMantissa : UInt64 := ((1 : UInt64) <<< 53) - 1

/-- Assemble a binary64 from `(sign, ieeeExponent, ieeeMantissa)`, mirroring
    Ryu's `ieeeParts2Double` helper. -/
private def ieeeParts2Double (sign : Bool) (ieeeExp : UInt64) (mantissa : UInt64) : Float :=
  let s : UInt64 := if sign then (1 : UInt64) <<< 63 else 0
  Float.ofBits (s ||| (ieeeExp <<< 52) ||| mantissa)

/-- Widen an `f32` bit pattern to `Float` for testing via our (f64) Schubfach. -/
private def f32ToFloat (bits : UInt32) : Float := (Float32.ofBits bits).toFloat

/-! ## Test infrastructure

A test case is `(description, input Float, expected Decimal)`. Each group is
an `Array` of cases; `runGroup` lifts a group into a `TestSeq`. -/

/-- Equality on `Except String Decimal` (mirrors the local instance in
    `Tests/Main.lean`). We compare both the `.ok` and `.error` branches by their
    payload. -/
private def exceptEq (a b : Except String Decimal) : Bool :=
  match a, b with
  | .ok x, .ok y => x == y
  | .error x, .error y => x == y
  | _, _ => false

abbrev Case := String × Float × Decimal

/-- Run a single case. -/
def runCase (groupName : String) (c : Case) : TestSeq :=
  let (desc, input, expected) := c
  test s!"{groupName}: {desc}" (exceptEq (Schubfach.toDecimal input) (.ok expected))

/-- Run an entire group, flattening to a single `TestSeq`. -/
def runGroup (groupName : String) (cases : Array Case) : TestSeq :=
  cases.foldl (init := TestSeq.done) (fun acc c => acc ++ runCase groupName c)

/-! ## d2s — binary64 cases (faithful port from `d2s_test.cc`) -/

/-- `D2sTest.Basic`. -/
def d2sBasic : Array Case := #[
  ("0.0",         0.0,           ⟨false, 0, 0⟩),
  ("-0.0",       -0.0,           ⟨true, 0, 0⟩),
  ("1.0",         1.0,           ⟨false, 1, 0⟩),
  ("-1.0",       -1.0,           ⟨true,  1, 0⟩)
  -- NaN, +Inf, -Inf yield `.error _`; skipped (no Decimal representation).
]

/-- `D2sTest.SwitchToSubnormal`. -/
def d2sSwitchToSubnormal : Array Case := #[
  ("2.2250738585072014E-308", 2.2250738585072014e-308, ⟨false, 22250738585072014, -324⟩)
]

/-- `D2sTest.MinAndMax`. -/
def d2sMinAndMax : Array Case := #[
  ("1.7976931348623157E308 (max finite)",
    Float.ofBits 0x7fefffffffffffff, ⟨false, 17976931348623157, 292⟩),
  ("5E-324 (min subnormal)",
    Float.ofBits 1, ⟨false, 5, -324⟩)
]

/-- `D2sTest.LotsOfTrailingZeros`. -/
def d2sLotsOfTrailingZeros : Array Case := #[
  ("2.9802322387695312E-8", 2.98023223876953125e-8, ⟨false, 29802322387695312, -24⟩)
]

/-- `D2sTest.Regression`. -/
def d2sRegression : Array Case := #[
  ("-2.109808898695963E16",  -2.109808898695963e16,
    ⟨true, 2109808898695963, 1⟩),
  ("4.940656E-318",           4.940656e-318,
    ⟨false, 4940656, -324⟩),
  ("1.18575755E-316",         1.18575755e-316,
    ⟨false, 118575755, -324⟩),
  ("2.989102097996E-312",     2.989102097996e-312,
    ⟨false, 2989102097996, -324⟩),
  ("9.0608011534336E15",      9.0608011534336e15,
    ⟨false, 90608011534336, 2⟩),
  ("4.708356024711512E18",    4.708356024711512e18,
    ⟨false, 4708356024711512, 3⟩),
  ("9.409340012568248E18",    9.409340012568248e18,
    ⟨false, 9409340012568248, 3⟩),
  ("1.2345678E0",             1.2345678,
    ⟨false, 12345678, -7⟩)
]

/-- `D2sTest.LooksLikePow5`. Corner case where `q = 22`. -/
def d2sLooksLikePow5 : Array Case := #[
  ("5.764607523034235E39",
    Float.ofBits 0x4830F0CF064DD592, ⟨false, 5764607523034235, 24⟩),
  ("1.152921504606847E40",
    Float.ofBits 0x4840F0CF064DD592, ⟨false, 1152921504606847, 25⟩),
  ("2.305843009213694E40",
    Float.ofBits 0x4850F0CF064DD592, ⟨false, 2305843009213694, 25⟩)
]

/-- `D2sTest.OutputLength`. Tests every output length from 1 to 17 digits. -/
def d2sOutputLength : Array Case := #[
  ("1.2E0",                 1.2,                  ⟨false, 12, -1⟩),
  ("1.23E0",                1.23,                 ⟨false, 123, -2⟩),
  ("1.234E0",               1.234,                ⟨false, 1234, -3⟩),
  ("1.2345E0",              1.2345,               ⟨false, 12345, -4⟩),
  ("1.23456E0",             1.23456,              ⟨false, 123456, -5⟩),
  ("1.234567E0",            1.234567,             ⟨false, 1234567, -6⟩),
  -- "1.2345678E0" lives in Regression (Ryu duplicates).
  ("1.23456789E0",          1.23456789,           ⟨false, 123456789, -8⟩),
  ("1.234567895E0",         1.234567895,          ⟨false, 1234567895, -9⟩),
  ("1.2345678901E0",        1.2345678901,         ⟨false, 12345678901, -10⟩),
  ("1.23456789012E0",       1.23456789012,        ⟨false, 123456789012, -11⟩),
  ("1.234567890123E0",      1.234567890123,       ⟨false, 1234567890123, -12⟩),
  ("1.2345678901234E0",     1.2345678901234,      ⟨false, 12345678901234, -13⟩),
  ("1.23456789012345E0",    1.23456789012345,     ⟨false, 123456789012345, -14⟩),
  ("1.234567890123456E0",   1.234567890123456,    ⟨false, 1234567890123456, -15⟩),
  ("1.2345678901234567E0",  1.2345678901234567,   ⟨false, 12345678901234567, -16⟩),
  -- 32-bit chunking boundary (2^32 ± small).
  ("4.294967294E0 (2^32 − 2)", 4.294967294,       ⟨false, 4294967294, -9⟩),
  ("4.294967295E0 (2^32 − 1)", 4.294967295,       ⟨false, 4294967295, -9⟩),
  ("4.294967296E0 (2^32)",     4.294967296,       ⟨false, 4294967296, -9⟩),
  ("4.294967297E0 (2^32 + 1)", 4.294967297,       ⟨false, 4294967297, -9⟩),
  ("4.294967298E0 (2^32 + 2)", 4.294967298,       ⟨false, 4294967298, -9⟩)
]

/-- `D2sTest.MinMaxShift`. Boundary cases for the multiply-shift step. -/
def d2sMinMaxShift : Array Case := #[
  ("1.7800590868057611E-307",
    ieeeParts2Double false 4 0,         ⟨false, 17800590868057611, -323⟩),
  ("2.8480945388892175E-306",
    ieeeParts2Double false 6 maxMantissa, ⟨false, 28480945388892175, -322⟩),
  ("2.446494580089078E-296",
    ieeeParts2Double false 41 0,        ⟨false, 2446494580089078, -311⟩),
  ("4.8929891601781557E-296",
    ieeeParts2Double false 40 maxMantissa, ⟨false, 48929891601781557, -312⟩),
  ("1.8014398509481984E16",
    ieeeParts2Double false 1077 0,      ⟨false, 18014398509481984, 0⟩),
  ("3.6028797018963964E16",
    ieeeParts2Double false 1076 maxMantissa, ⟨false, 36028797018963964, 0⟩),
  ("2.900835519859558E-216",
    ieeeParts2Double false 307 0,       ⟨false, 2900835519859558, -231⟩),
  ("5.801671039719115E-216",
    ieeeParts2Double false 306 maxMantissa, ⟨false, 5801671039719115, -231⟩),
  ("3.196104012172126E-27 (issue #19e44d1)",
    ieeeParts2Double false 934 0x000FA7161A4D6E0C, ⟨false, 3196104012172126, -42⟩)
]

/-- `D2sTest.SmallIntegers`. Most cases duplicate `OutputLength`; we keep
    only the distinct ones (`2^53 − 1`, `2^53`, powers of 10, 10^15 + 10^i,
    and largest power of 2 below 10^(i+1)). -/
def d2sSmallIntegers : Array Case := #[
  ("9.007199254740991E15 (2^53 − 1)",
    9007199254740991.0, ⟨false, 9007199254740991, 0⟩),
  ("9.007199254740992E15 (2^53)",
    9007199254740992.0, ⟨false, 9007199254740992, 0⟩),
  -- The Ne-significand forms 1.2eN, 1.23eN, ... are mathematically equal to
  -- the OutputLength entries (multiplication by a power of 10 = exponent
  -- bump) and produce the same canonical Decimal, so we don't re-test them.
  -- 10^i
  ("1E1",   1.0e+1,   ⟨false, 1, 1⟩),
  ("1E2",   1.0e+2,   ⟨false, 1, 2⟩),
  ("1E3",   1.0e+3,   ⟨false, 1, 3⟩),
  ("1E4",   1.0e+4,   ⟨false, 1, 4⟩),
  ("1E5",   1.0e+5,   ⟨false, 1, 5⟩),
  ("1E6",   1.0e+6,   ⟨false, 1, 6⟩),
  ("1E7",   1.0e+7,   ⟨false, 1, 7⟩),
  ("1E8",   1.0e+8,   ⟨false, 1, 8⟩),
  ("1E9",   1.0e+9,   ⟨false, 1, 9⟩),
  ("1E10",  1.0e+10,  ⟨false, 1, 10⟩),
  ("1E11",  1.0e+11,  ⟨false, 1, 11⟩),
  ("1E12",  1.0e+12,  ⟨false, 1, 12⟩),
  ("1E13",  1.0e+13,  ⟨false, 1, 13⟩),
  ("1E14",  1.0e+14,  ⟨false, 1, 14⟩),
  ("1E15",  1.0e+15,  ⟨false, 1, 15⟩),
  -- 10^15 + 10^i (trailing-zero stripping should produce the indicated sig).
  ("1.000000000000001E15", 1.0e+15 + 1.0e+0,  ⟨false, 1000000000000001, 0⟩),
  ("1.00000000000001E15",  1.0e+15 + 1.0e+1,  ⟨false, 100000000000001, 1⟩),
  ("1.0000000000001E15",   1.0e+15 + 1.0e+2,  ⟨false, 10000000000001, 2⟩),
  ("1.000000000001E15",    1.0e+15 + 1.0e+3,  ⟨false, 1000000000001, 3⟩),
  ("1.00000000001E15",     1.0e+15 + 1.0e+4,  ⟨false, 100000000001, 4⟩),
  ("1.0000000001E15",      1.0e+15 + 1.0e+5,  ⟨false, 10000000001, 5⟩),
  ("1.000000001E15",       1.0e+15 + 1.0e+6,  ⟨false, 1000000001, 6⟩),
  ("1.00000001E15",        1.0e+15 + 1.0e+7,  ⟨false, 100000001, 7⟩),
  ("1.0000001E15",         1.0e+15 + 1.0e+8,  ⟨false, 10000001, 8⟩),
  ("1.000001E15",          1.0e+15 + 1.0e+9,  ⟨false, 1000001, 9⟩),
  ("1.00001E15",           1.0e+15 + 1.0e+10, ⟨false, 100001, 10⟩),
  ("1.0001E15",            1.0e+15 + 1.0e+11, ⟨false, 10001, 11⟩),
  ("1.001E15",             1.0e+15 + 1.0e+12, ⟨false, 1001, 12⟩),
  ("1.01E15",              1.0e+15 + 1.0e+13, ⟨false, 101, 13⟩),
  ("1.1E15",               1.0e+15 + 1.0e+14, ⟨false, 11, 14⟩),
  -- Largest power of 2 ≤ 10^(i+1).
  ("8E0",                 8.0,                 ⟨false, 8, 0⟩),
  ("6.4E1",               64.0,                ⟨false, 64, 0⟩),
  ("5.12E2",              512.0,               ⟨false, 512, 0⟩),
  ("8.192E3",             8192.0,              ⟨false, 8192, 0⟩),
  ("6.5536E4",            65536.0,             ⟨false, 65536, 0⟩),
  ("5.24288E5",           524288.0,            ⟨false, 524288, 0⟩),
  ("8.388608E6",          8388608.0,           ⟨false, 8388608, 0⟩),
  ("6.7108864E7",         67108864.0,          ⟨false, 67108864, 0⟩),
  ("5.36870912E8",        536870912.0,         ⟨false, 536870912, 0⟩),
  ("8.589934592E9",       8589934592.0,        ⟨false, 8589934592, 0⟩),
  ("6.8719476736E10",     68719476736.0,       ⟨false, 68719476736, 0⟩),
  ("5.49755813888E11",    549755813888.0,      ⟨false, 549755813888, 0⟩),
  ("8.796093022208E12",   8796093022208.0,     ⟨false, 8796093022208, 0⟩),
  ("7.0368744177664E13",  70368744177664.0,    ⟨false, 70368744177664, 0⟩),
  ("5.62949953421312E14", 562949953421312.0,   ⟨false, 562949953421312, 0⟩),
  -- 9.007199254740992E15 (2^53) covered above.
  -- 1000 × the above (exponents shift by 3 — Decimal canonicalisation strips
  -- trailing zeros, leaving the same sig with exp + 3).
  ("8E3",                 8.0e+3,              ⟨false, 8, 3⟩),
  ("6.4E4",               64.0e+3,             ⟨false, 64, 3⟩),
  ("5.12E5",              512.0e+3,            ⟨false, 512, 3⟩),
  ("8.192E6",             8192.0e+3,           ⟨false, 8192, 3⟩),
  ("6.5536E7",            65536.0e+3,          ⟨false, 65536, 3⟩),
  ("5.24288E8",           524288.0e+3,         ⟨false, 524288, 3⟩),
  ("8.388608E9",          8388608.0e+3,        ⟨false, 8388608, 3⟩),
  ("6.7108864E10",        67108864.0e+3,       ⟨false, 67108864, 3⟩),
  ("5.36870912E11",       536870912.0e+3,      ⟨false, 536870912, 3⟩),
  ("8.589934592E12",      8589934592.0e+3,     ⟨false, 8589934592, 3⟩),
  ("6.8719476736E13",     68719476736.0e+3,    ⟨false, 68719476736, 3⟩),
  ("5.49755813888E14",    549755813888.0e+3,   ⟨false, 549755813888, 3⟩),
  ("8.796093022208E15",   8796093022208.0e+3,  ⟨false, 8796093022208, 3⟩)
]

/-! ## f2s — binary32 cases (widened to f64 then run through d2s)

These tests apply our f64 Schubfach to the f64-widened f32 value. The
expected outputs are the f64-shortest decimals — NOT Ryu's f32-shortest
strings. Where they coincide (small integers, exact binary fractions),
Ryu's string appears in the description; where they diverge, the
description lists both Ryu's f32 string and our f64 result.

Without an f32 Schubfach implementation in this project, these tests
exercise the same `Schubfach.toDecimal` as d2s — they're useful as
extra coverage of bit patterns Ryu's authors selected, but they do
NOT validate f32 round-tripping per se. -/

/-- `F2sTest.Basic`. -/
def f2sBasic : Array Case := #[
  ("0.0f",       f32ToFloat 0,            ⟨false, 0, 0⟩),
  ("-0.0f",      f32ToFloat 0x80000000,   ⟨true, 0, 0⟩),
  ("1.0f",       (1.0 : Float32).toFloat, ⟨false, 1, 0⟩),
  ("-1.0f",      (-1.0 : Float32).toFloat, ⟨true, 1, 0⟩)
]

/-- `F2sTest.SwitchToSubnormal`. Ryu f32 "1.1754944E-38"; widened f64
    Schubfach produces the longer f64-shortest. -/
def f2sSwitchToSubnormal : Array Case := #[
  ("1.1754944E-38f (Ryu f32: 1.1754944E-38; f64-shortest: 1.1754943508222875E-38)",
    (1.1754944e-38 : Float32).toFloat, ⟨false, 11754943508222875, -54⟩)
]

/-- `F2sTest.MinAndMax`. Ryu's "1E-45" tests the smallest f32 subnormal
    (`Float32.ofBits 1` = `2^-149`). Widened to f64, this is exact and
    our Schubfach produces the f64-shortest, which is `1401298464324817e-60`
    — definitely not Ryu's "1E-45". -/
def f2sMinAndMax : Array Case := #[
  ("3.4028235E38f (Ryu) → 3.4028234663852886E38 (f64-shortest)",
    f32ToFloat 0x7f7fffff, ⟨false, 34028234663852886, 22⟩),
  ("1E-45f (Ryu) → 1.401298464324817E-45 (f64-shortest of f32's 2^-149)",
    f32ToFloat 1, ⟨false, 1401298464324817, -60⟩)
]

/-- `F2sTest.BoundaryRoundEven`. Ryu's expected strings test that f32 picks
    the even-mantissa boundary; f64 sees a non-boundary value so produces
    the full f64-shortest of the widened f32. -/
def f2sBoundaryRoundEven : Array Case := #[
  ("3.355445E7f (Ryu) → 3.3554448E7 (widened, sig 33554448)",
    (3.355445e7 : Float32).toFloat, ⟨false, 33554448, 0⟩),
  ("9E9f (Ryu) → 8.999999488E9 (widened)",
    (8.999999e9 : Float32).toFloat, ⟨false, 8999999488, 0⟩),
  ("3.436672E10f (Ryu) → 3.4366717952E10 (widened)",
    (3.4366717e10 : Float32).toFloat, ⟨false, 34366717952, 0⟩)
]

/-- `F2sTest.ExactValueRoundEven`. These f32-shortest values may match f64. -/
def f2sExactValueRoundEven : Array Case := #[
  ("3.0540412E5f (Ryu) → 3.05404125E5 (widened, sig 305404125)",
    (3.0540412e5 : Float32).toFloat, ⟨false, 305404125, -3⟩),
  ("8.0990312E3f (Ryu) → 8.09903125E3 (widened, sig 809903125)",
    (8.0990312e3 : Float32).toFloat, ⟨false, 809903125, -5⟩)
]

/-- `F2sTest.LotsOfTrailingZeros`. Each of these is an exact binary fraction
    in f32 (significand bits `00111001100…0`); the *f32-shortest* trims the
    trailing zeros of the decimal expansion. Our f64-shortest of the same
    value keeps more digits. -/
def f2sLotsOfTrailingZeros : Array Case := #[
  ("2.4414062E-4f (Ryu) → 2.44140625E-4 (widened; sig 244140625)",
    (2.4414062e-4 : Float32).toFloat, ⟨false, 244140625, -12⟩),
  ("2.4414062E-3f (Ryu) → 2.44140625E-3 (widened; sig 244140625)",
    (2.4414062e-3 : Float32).toFloat, ⟨false, 244140625, -11⟩),
  ("4.3945312E-3f (Ryu) → 4.39453125E-3 (widened; sig 439453125)",
    (4.3945312e-3 : Float32).toFloat, ⟨false, 439453125, -11⟩),
  ("6.3476562E-3f (Ryu) → 6.34765625E-3 (widened; sig 634765625)",
    (6.3476562e-3 : Float32).toFloat, ⟨false, 634765625, -11⟩)
]

/-! ### `F2sTest.Regression`

These all diverge from Ryu's f32-shortest. We document each. Expected
values were computed empirically with our `Schubfach.toDecimal` on the
widened f32 (skipping the platform-conditional MSVC variant). -/

/-- `F2sTest.Regression`. Empirical f64-shortest values noted alongside
    Ryu's f32-shortest in each description. -/
def f2sRegression : Array Case := #[
  ("4.7223665E21f (Ryu) → 4.722366482869645E21 (widened)",
    (4.7223665e21 : Float32).toFloat, ⟨false, 4722366482869645, 6⟩),
  ("8388608.0f (2^23; matches Ryu 8.388608E6)",
    (8388608.0 : Float32).toFloat, ⟨false, 8388608, 0⟩),
  ("1.6777216E7f (2^24; matches Ryu 1.6777216E7)",
    (1.6777216e7 : Float32).toFloat, ⟨false, 16777216, 0⟩),
  ("3.3554436E7f (Ryu) → 3.3554436E7 (sig 33554436)",
    (3.3554436e7 : Float32).toFloat, ⟨false, 33554436, 0⟩),
  ("6.7131496E7f (Ryu) → 6.7131496E7 (sig 67131496)",
    (6.7131496e7 : Float32).toFloat, ⟨false, 67131496, 0⟩),
  ("1.9310392E-38f (Ryu) → 1.93103917...E-38 (widened)",
    (1.9310392e-38 : Float32).toFloat, ⟨false, 1931039170064928, -53⟩),
  ("-2.47E-43f (Ryu, smaller-than-min-normal subnormal)",
    (-2.47e-43 : Float32).toFloat, ⟨true, 2466285297211678, -58⟩),
  ("1.993244E-38f (Ryu) → 1.99324393...E-38 (widened)",
    (1.993244e-38 : Float32).toFloat, ⟨false, 1993243929935078, -53⟩),
  ("4.1039004E3f (4103.9003) → 4.103900390625E3 (widened)",
    (4103.9003 : Float32).toFloat, ⟨false, 4103900390625, -9⟩),
  ("5.3399997E9f → 5.339999744E9 (widened, sig 5339999744)",
    (5.3399997e9 : Float32).toFloat, ⟨false, 5339999744, 0⟩),
  ("6.0898E-39f → 6.08979930...E-39 (widened)",
    (6.0898e-39 : Float32).toFloat, ⟨false, 6089799300022862, -54⟩),
  ("0.0010310042f → 1.03100424166...E-3 (widened)",
    (0.0010310042 : Float32).toFloat, ⟨false, 1031004241667688, -18⟩),
  ("2.8823261E17f → 2.8823260953...E17 (widened)",
    (2.8823261e17 : Float32).toFloat, ⟨false, 28823260953470566, 1⟩),
  -- Ryu's "7.038531E-26" non-MSVC case (`7.038531E-26f` literal).
  ("7.038531E-26f → 7.03853069...E-26 (widened)",
    (7.038531e-26 : Float32).toFloat, ⟨false, 7038530691851209, -41⟩),
  ("9.2234038E17f → 9.223403785...E17 (widened)",
    (9.2234038e17 : Float32).toFloat, ⟨false, 9223403785253028, 2⟩),
  ("6.7108872E7f → 6.7108872E7 (sig 67108872)",
    (6.7108872e7 : Float32).toFloat, ⟨false, 67108872, 0⟩),
  ("1.0E-44f (Ryu \"1E-44\") → 9.80908925...E-45 (widened)",
    (1.0e-44 : Float32).toFloat, ⟨false, 980908925027372, -59⟩),
  ("2.816025E14f → 2.81602483552256E14 (widened)",
    (2.816025e14 : Float32).toFloat, ⟨false, 281602483552256, 0⟩),
  ("9.223372E18f → 9.223372036854776E18 (widened)",
    (9.223372e18 : Float32).toFloat, ⟨false, 9223372036854776, 3⟩),
  ("1.5846085E29f → 1.5846085850...E29 (widened)",
    (1.5846085e29 : Float32).toFloat, ⟨false, 15846085850035223, 13⟩),
  ("1.1811161E19f → 1.18111606...E19 (widened)",
    (1.1811161e19 : Float32).toFloat, ⟨false, 11811160613755814, 3⟩),
  ("5.368709E18f → 5.368709120E18 (widened, sig 536870912 × 10^10)",
    (5.368709e18 : Float32).toFloat, ⟨false, 536870912, 10⟩),
  ("4.6143165E18f → 4.61431659999...E18 (widened)",
    (4.6143165e18 : Float32).toFloat, ⟨false, 4614316599996842, 3⟩),
  ("0.007812537f → 7.81253725...E-3 (widened)",
    (0.007812537 : Float32).toFloat, ⟨false, 7812537252902985, -18⟩),
  ("1.4E-45f (Ryu \"1E-45\", min subnormal) → 1.401298464324817E-45 (widened)",
    (1.4e-45 : Float32).toFloat, ⟨false, 1401298464324817, -60⟩),
  ("1.18697724E20f → 1.18697724999...E20 (widened)",
    (1.18697724e20 : Float32).toFloat, ⟨false, 11869772499999995, 4⟩),
  ("1.00014165E-36f → 1.00014164555...E-36 (widened)",
    (1.00014165e-36 : Float32).toFloat, ⟨false, 10001416455567406, -52⟩),
  ("200.0f (matches Ryu \"2E2\")",
    (200.0 : Float32).toFloat, ⟨false, 2, 2⟩),
  ("3.3554432E7f (2^25; matches Ryu \"3.3554432E7\")",
    (3.3554432e7 : Float32).toFloat, ⟨false, 33554432, 0⟩)
]

/-- `F2sTest.LooksLikePow5`. Ryu's f32 strings; widened f64 may differ. -/
def f2sLooksLikePow5 : Array Case := #[
  ("6.7108864E17f → f64-shortest of widened",
    f32ToFloat 0x5D1502F9, ⟨false, 67108864, 10⟩),
  ("1.3421773E18f → f64-shortest of widened",
    f32ToFloat 0x5D9502F9, ⟨false, 134217728, 10⟩),
  ("2.6843546E18f → f64-shortest of widened",
    f32ToFloat 0x5E1502F9, ⟨false, 268435456, 10⟩)
]

/-- `F2sTest.OutputLength`. -/
def f2sOutputLength : Array Case := #[
  ("1.2f (Ryu \"1.2E0\") → 1.2000000476837158 (widened)",
    (1.2 : Float32).toFloat, ⟨false, 12000000476837158, -16⟩),
  ("1.23f (Ryu \"1.23E0\") → 1.2300000190734863 (widened)",
    (1.23 : Float32).toFloat, ⟨false, 12300000190734863, -16⟩),
  ("1.234f → 1.2339999675750732 (widened)",
    (1.234 : Float32).toFloat, ⟨false, 12339999675750732, -16⟩),
  ("1.2345f → 1.2345000505447388 (widened)",
    (1.2345 : Float32).toFloat, ⟨false, 12345000505447388, -16⟩),
  ("1.23456f → 1.2345600128173828 (widened)",
    (1.23456 : Float32).toFloat, ⟨false, 12345600128173828, -16⟩),
  ("1.234567f → 1.2345670461654663 (widened)",
    (1.234567 : Float32).toFloat, ⟨false, 12345670461654663, -16⟩),
  ("1.2345678f → 1.234567761...E0 (widened)",
    (1.2345678 : Float32).toFloat, ⟨false, 12345677614212036, -16⟩),
  ("1.23456735E-36f → 1.234567354...E-36 (widened)",
    (1.23456735e-36 : Float32).toFloat, ⟨false, 1234567354359712, -51⟩)
]

/-! ## Exact same-length ties (round-half-to-even)

`v = (2⁵²+1)·2⁻² = 1125899906842624.25` (bits `0x4310000000000001`) is the
smallest double with a genuine shortest-decimal tie: both 17-digit decimals
`…24.2` and `…24.3` round-trip and are exactly `1/20` from `v`. The
ties-to-even clause of `Schubfach.IsSpecOutput` selects the even `…242`;
this is the witness that the clause is not vacuous (any odd-mantissa double
with `q = -2` exhibits the same tie). -/

/-- The even pick at the canonical tie witness (and a sibling with the
mantissa bumped by 2: `…24.75`, tie between `…247`/`…248` → even `…248`). -/
def d2sExactTies : Array Case := #[
  ("(2^52+1)*2^-2 tie → even ...242",
    Float.ofBits 0x4310000000000001, ⟨false, 11258999068426242, -1⟩),
  ("(2^52+3)*2^-2 tie → even ...248",
    Float.ofBits 0x4310000000000003, ⟨false, 11258999068426248, -1⟩)]

/-- Both tie partners round-trip: the rejected odd neighbour `…243e-1`
also reads back to the same bits — only the even rule separates them. -/
def tiePartnerRoundTrips : TestSeq :=
  test "tie partner 11258999068426243e-1 also reads back to 0x4310000000000001"
    ((Clinger.ofDecimal ⟨false, 11258999068426243, -1⟩).toBits
      == (0x4310000000000001 : UInt64))

/-- `intToStrRef` (the ++-spelled exponent-emit reference in StringFast)
is byte-identical to `toString : Int → String`, including the Int64
extremes and beyond-64-bit magnitudes. -/
def intToStrRefAgrees : TestSeq :=
  test "intToStrRef = toString on samples incl. Int64 extremes"
    (([0, 1, -1, 9, -9, 10, -10, 42, -324, 292, 1000, -1000,
       9223372036854775807, -9223372036854775808,
       18446744073709551621, -18446744073709551621] : List Int).all
      (fun e => Schubfach.intToStrRef e == toString e))

/-! ## Test runner

`ryuTests` aggregates every group. Add new groups here. -/

/-- All Ryu-derived edge case tests. -/
def ryuTests : TestSeq :=
  -- d2s
  runGroup "d2s Basic" d2sBasic ++
  runGroup "d2s ExactTies" d2sExactTies ++
  tiePartnerRoundTrips ++
  intToStrRefAgrees ++
  runGroup "d2s SwitchToSubnormal" d2sSwitchToSubnormal ++
  runGroup "d2s MinAndMax" d2sMinAndMax ++
  runGroup "d2s LotsOfTrailingZeros" d2sLotsOfTrailingZeros ++
  runGroup "d2s Regression" d2sRegression ++
  runGroup "d2s LooksLikePow5" d2sLooksLikePow5 ++
  runGroup "d2s OutputLength" d2sOutputLength ++
  runGroup "d2s MinMaxShift" d2sMinMaxShift ++
  runGroup "d2s SmallIntegers" d2sSmallIntegers ++
  -- f2s (widened; many adapted, see header)
  runGroup "f2s Basic" f2sBasic ++
  runGroup "f2s SwitchToSubnormal" f2sSwitchToSubnormal ++
  runGroup "f2s MinAndMax" f2sMinAndMax ++
  runGroup "f2s BoundaryRoundEven" f2sBoundaryRoundEven ++
  runGroup "f2s ExactValueRoundEven" f2sExactValueRoundEven ++
  runGroup "f2s LotsOfTrailingZeros" f2sLotsOfTrailingZeros ++
  runGroup "f2s Regression" f2sRegression ++
  runGroup "f2s LooksLikePow5" f2sLooksLikePow5 ++
  runGroup "f2s OutputLength" f2sOutputLength

end Srtfp.Tests.Ryu

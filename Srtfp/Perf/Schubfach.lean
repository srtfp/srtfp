module
/- The constants and the exponent `k` of the Schubfach algorithm (Raffaello
   Giulietti, "The Schubfach way to render doubles", 2021) for binary64: the
   spacing classification of §5 and `k = ⌊log₁₀ ‖R_v‖⌋` of R10 through the
   magic constants of R14/R15. The algorithm, its proof and the word-level
   kernel are under `Perf/Schubfach/`. -/

public import Srtfp.Decimal

@[expose] public section

namespace Srtfp.Schubfach

/-- For binary64: precision `P = 53`, so the boundary mantissa is `2^{P-1} = 2^52`. -/
def minNormalSignificand : Nat := 1 <<< 52

/-- For binary64: minimum binary exponent `Q_min = -1074`. -/
def minBinaryExp : Int := -1074

/-- `true` iff `(m, q)` represents a value with irregular `R_v` spacing
    (`m = 2^{P-1} ∧ q > Q_min`, §5). -/
def isIrregular (m : Nat) (q : Int) : Bool :=
  m = minNormalSignificand && q > minBinaryExp

/-! ## §9.1 magic-constant approximations of floor-log

These give exact integer values within proven ranges (R14/R15).
Binary64's full `q ∈ [-1074, 971]` is comfortably inside both. -/

/-- The shift exponent `Q` from R14/R15. Both `floorLog10Pow2` and
    `floorLog10ThreeQuartersPow2` use the same shift width for D = 10. -/
def shiftQ : Nat := 41

/-- `⌊2^41 · log_10(2)⌋`. Magic constant from R14 / R15. -/
def constC : Int := 661971961083

/-- `⌊2^41 · log_10(3/4)⌋`. Magic constant from R14. -/
def constA : Int := -274743187321

/-- `⌊log_10(2^e)⌋` via R15. Valid for `e ∈ [-6432162, 6432162]`. -/
@[inline]
def floorLog10Pow2 (e : Int) : Int :=
  Int.fdiv (e * constC) (2 ^ shiftQ)

/-- `⌊log_10(3/4 · 2^e)⌋` via R14. Valid for `e ∈ [-3606689, 3150619]`. -/
@[inline]
def floorLog10ThreeQuartersPow2 (e : Int) : Int :=
  Int.fdiv (e * constC + constA) (2 ^ shiftQ)

/-! ## Schubfach's `k`

`k = ⌊log_D(‖R_v‖)⌋` from R10, computed as either `⌊log_10(2^q)⌋` (regular)
or `⌊log_10(3/4 · 2^q)⌋` (irregular). -/

/-- Schubfach's `k` from the decoded `(m, q)` of a finite Float. -/
def kOfMQ (m : Nat) (q : Int) : Int :=
  if isIrregular m q then
    floorLog10ThreeQuartersPow2 q
  else
    floorLog10Pow2 q

end Srtfp.Schubfach

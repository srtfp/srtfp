module
/- The cleared-denominator interval vocabulary of the original Schubfach
   reference, kept in the reference tier because the reader proofs are
   stated against it: `isIrregular`, the exact comparator `cmpScaledMixed`
   and the membership test `inRoundingInterval`. Definitions only; the
   printer that used them now lives in `Srtfp/Perf/Schubfach.lean`.
   Retired by the reader rewrite. -/

@[expose] public section

namespace Srtfp.Schubfach

/-- For binary64: precision `P = 53`, so the boundary mantissa is `2^{P-1} = 2^52`. -/
def minNormalSignificand : Nat := 1 <<< 52

/-- For binary64: minimum binary exponent `Q_min = -1074`. -/
def minBinaryExp : Int := -1074

/-- `true` iff `(m, q)` represents a value with irregular `R_v` spacing
    (`m = 2^{P-1} ∧ q > Q_min`). -/
def isIrregular (m : Nat) (q : Int) : Bool :=
  m = minNormalSignificand && q > minBinaryExp

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

end Srtfp.Schubfach

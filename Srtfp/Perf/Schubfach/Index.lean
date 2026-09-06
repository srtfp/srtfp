module
/- R14 and R15 on the biased exponent `qB = q + 1074`, producing the table
   index `kB = k − K_min = k + 324`. The products are offset by `2^60` so
   every intermediate is a non-negative word: no arithmetic shift, and the
   floor divisions are plain `>>> 41`. -/

public import Srtfp.Perf.Schubfach

@[expose] public section

namespace Srtfp.Schubfach

/-- R15: `⌊log₁₀ 2^q⌋ + 324` for `q = qB − 1074`.
    `(qB − 1074)·C = qB·C − 1074·C`; adding `2^60` keeps it positive, and
    `2^60 / 2^41 = 2^19` comes back off the quotient. -/
@[inline] def floorLog10Pow2B (qB : UInt64) : UInt64 :=
  ((qB * 661971961083 + 1152210546720643834) >>> 41) - 523964

/-- R14: `⌊log₁₀ (3/4 · 2^q)⌋ + 324` for `q = qB − 1074` (the offset also
    absorbs `A = ⌊2^41 log₁₀ (3/4)⌋`). -/
@[inline] def floorLog10ThreeQuartersPow2B (qB : UInt64) : UInt64 :=
  ((qB * 661971961083 + 1152210271977456513) >>> 41) - 523964

/-- Irregular spacing (§5): `c = 2^52` and `q > Q_min`, i.e. `qB ≥ 1`. -/
@[inline] def isIrregularB (mU qB : UInt64) : Bool :=
  mU = 4503599627370496 && qB ≥ 1

/-- `k + 324` (R10 through R14/R15). -/
@[inline] def kBOfMQ (mU qB : UInt64) : UInt64 :=
  if isIrregularB mU qB then floorLog10ThreeQuartersPow2B qB else floorLog10Pow2B qB

theorem floorLog10Pow2B_toNat (qB : UInt64) (hq : qB.toNat ≤ 2045) :
    ((floorLog10Pow2B qB).toNat : Int) = floorLog10Pow2 ((qB.toNat : Int) - 1074) + 324 := by
  unfold floorLog10Pow2B floorLog10Pow2 constC shiftQ
  rw [UInt64.toNat_sub, UInt64.toNat_shiftRight, UInt64.toNat_add, UInt64.toNat_mul,
    show (41 : UInt64).toNat % 64 = 41 from rfl,
    show (661971961083 : UInt64).toNat = 661971961083 from rfl,
    show (1152210546720643834 : UInt64).toNat = 1152210546720643834 from rfl,
    show (523964 : UInt64).toNat = 523964 from rfl,
    Int.fdiv_eq_ediv_of_nonneg _ (by decide), Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (by omega : qB.toNat * 661971961083 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : qB.toNat * 661971961083 + 1152210546720643834 < 2 ^ 64)]
  -- the biased quotient is the floor plus `2^19`
  have hD : (((qB.toNat * 661971961083 + 1152210546720643834) / 2 ^ 41 : Nat) : Int)
      = ((qB.toNat : Int) - 1074) * 661971961083 / 2 ^ 41 + 2 ^ 19 := by omega
  omega

theorem floorLog10ThreeQuartersPow2B_toNat (qB : UInt64) (hq : qB.toNat ≤ 2045) :
    ((floorLog10ThreeQuartersPow2B qB).toNat : Int)
      = floorLog10ThreeQuartersPow2 ((qB.toNat : Int) - 1074) + 324 := by
  unfold floorLog10ThreeQuartersPow2B floorLog10ThreeQuartersPow2 constC constA shiftQ
  rw [UInt64.toNat_sub, UInt64.toNat_shiftRight, UInt64.toNat_add, UInt64.toNat_mul,
    show (41 : UInt64).toNat % 64 = 41 from rfl,
    show (661971961083 : UInt64).toNat = 661971961083 from rfl,
    show (1152210271977456513 : UInt64).toNat = 1152210271977456513 from rfl,
    show (523964 : UInt64).toNat = 523964 from rfl,
    Int.fdiv_eq_ediv_of_nonneg _ (by decide), Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (by omega : qB.toNat * 661971961083 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : qB.toNat * 661971961083 + 1152210271977456513 < 2 ^ 64)]
  have hD : (((qB.toNat * 661971961083 + 1152210271977456513) / 2 ^ 41 : Nat) : Int)
      = (((qB.toNat : Int) - 1074) * 661971961083 + -274743187321) / 2 ^ 41 + 2 ^ 19 := by omega
  omega

theorem isIrregularB_eq (mU qB : UInt64) :
    isIrregularB mU qB = isIrregular mU.toNat ((qB.toNat : Int) - 1074) := by
  unfold isIrregularB isIrregular minNormalSignificand minBinaryExp
  congr 1
  · refine decide_eq_decide.mpr ?_
    rw [← UInt64.toNat_inj, show ((4503599627370496 : UInt64)).toNat = 1 <<< 52 from rfl]
  · refine decide_eq_decide.mpr ?_
    rw [ge_iff_le, UInt64.le_iff_toNat_le, show ((1 : UInt64)).toNat = 1 from rfl]
    omega

theorem kBOfMQ_toNat (mU qB : UInt64) (hq : qB.toNat ≤ 2045) :
    ((kBOfMQ mU qB).toNat : Int) = kOfMQ mU.toNat ((qB.toNat : Int) - 1074) + 324 := by
  unfold kBOfMQ kOfMQ
  rw [isIrregularB_eq]
  split
  · exact floorLog10ThreeQuartersPow2B_toNat qB hq
  · exact floorLog10Pow2B_toNat qB hq

end Srtfp.Schubfach

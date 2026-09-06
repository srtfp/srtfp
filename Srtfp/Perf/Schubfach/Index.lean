module
/- R14 and R15 on the biased exponent `qB = q + 1074`, producing the table
   index `kB = k − K_min = k + 324`. The products are offset by `2^60` so
   every intermediate is a non-negative word: no arithmetic shift, and the
   floor divisions are plain `>>> 41`. -/

public import Srtfp.Perf.Schubfach
public import Srtfp.Perf.Word

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

/-- Both estimates on words: `qB·C + D` carries the `2^60` offset, so the
    shift is a plain floor division and `2^19 − 324` comes back off. -/
theorem biased_toNat (qB D : UInt64) (hq : qB.toNat ≤ 2045) (hD1 : 523964 * 2 ^ 41 ≤ D.toNat)
    (hD2 : D.toNat ≤ 2 ^ 61) :
    ((((qB * 661971961083 + D) >>> 41) - 523964).toNat : Int)
      = (((qB.toNat : Int) - 1074) * 661971961083
          + ((D.toNat : Int) - 2 ^ 60 + 1074 * 661971961083)) / 2 ^ 41 + 324 := by
  word_simp
  rw [Nat.mod_eq_of_lt (by omega : qB.toNat * 661971961083 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : qB.toNat * 661971961083 + D.toNat < 2 ^ 64)]
  omega

theorem floorLog10Pow2B_toNat (qB : UInt64) (hq : qB.toNat ≤ 2045) :
    ((floorLog10Pow2B qB).toNat : Int) = floorLog10Pow2 ((qB.toNat : Int) - 1074) + 324 := by
  unfold floorLog10Pow2B floorLog10Pow2 constC shiftQ
  rw [biased_toNat _ _ hq (by decide) (by decide), Int.fdiv_eq_ediv_of_nonneg _ (by decide),
    show ((1152210546720643834 : UInt64).toNat : Int) = 1152210546720643834 from rfl]
  omega

theorem floorLog10ThreeQuartersPow2B_toNat (qB : UInt64) (hq : qB.toNat ≤ 2045) :
    ((floorLog10ThreeQuartersPow2B qB).toNat : Int)
      = floorLog10ThreeQuartersPow2 ((qB.toNat : Int) - 1074) + 324 := by
  unfold floorLog10ThreeQuartersPow2B floorLog10ThreeQuartersPow2 constC constA shiftQ
  rw [biased_toNat _ _ hq (by decide) (by decide), Int.fdiv_eq_ediv_of_nonneg _ (by decide),
    show ((1152210271977456513 : UInt64).toNat : Int) = 1152210271977456513 from rfl]
  omega

theorem isIrregularB_eq (mU qB : UInt64) :
    isIrregularB mU qB = isIrregular mU.toNat ((qB.toNat : Int) - 1074) := by
  unfold isIrregularB isIrregular minNormalSignificand minBinaryExp
  congr 1 <;> exact decide_eq_decide.mpr (by word)

theorem kBOfMQ_toNat (mU qB : UInt64) (hq : qB.toNat ≤ 2045) :
    ((kBOfMQ mU qB).toNat : Int) = kOfMQ mU.toNat ((qB.toNat : Int) - 1074) + 324 := by
  unfold kBOfMQ kOfMQ
  rw [isIrregularB_eq]
  split
  · exact floorLog10ThreeQuartersPow2B_toNat qB hq
  · exact floorLog10Pow2B_toNat qB hq

end Srtfp.Schubfach

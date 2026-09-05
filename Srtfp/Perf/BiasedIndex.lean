module
/- The biased-index surface of the live kernels: the `h + 2048` side
   table over the 128-bit power-of-ten table, the `UInt64` bridges for
   biased exponent arithmetic, and the biased floor-log / `k`
   computations `kBOfMQ` with their pointwise verification. -/

public import Srtfp.Perf.Uint64Kernel
public import Srtfp.Perf.TableInvariant
public import Srtfp.Perf.Tactics

@[expose] public section

namespace Srtfp.Schubfach

theorem lookup128_high (k : Int) (hlo : ¬ k < pow10Table128_kMin) :
    pow10Lookup128 (k + 1) = pow10Table128.getD ((k + 324).toNat + 1) pow10Table128_default := by
  have hlo' : ¬ k < (-324 : Int) := hlo
  have hidx : (k + 1 + 324).toNat = (k + 324).toNat + 1 := by omega
  unfold pow10Lookup128
  rw [if_neg (show ¬ (k + 1 < pow10Table128_kMin) from
        fun hc => absurd (show k + 1 < -324 from hc) (by omega)),
      hidx]

theorem lookup128_low (k : Int) (hlo : ¬ k < pow10Table128_kMin) :
    pow10Lookup128 k = pow10Table128.getD ((k + 324).toNat) pow10Table128_default := by
  unfold pow10Lookup128
  rw [if_neg hlo]

/-- `h + 2048` per 128-table entry (scalar-sized, unboxed reads). -/
def hB128 : Array UInt64 :=
  pow10Table128.map (fun t => UInt64.ofNat (t.2.2 + 2048).toNat)

/-- All 128-table `h` values lie in `[-2048, 2048)`. -/
private theorem hBound128_at (i : Nat) (hi : i < pow10Table128.size) :
    -2048 ≤ (pow10Table128[i]!).2.2 ∧ (pow10Table128[i]!).2.2 < 2048 := by
  rw [pow10Table128_size_eq] at hi
  rw [pow10Table128_getElem! i hi]
  exact pow10Shift_bounds _ (by show (-324 : Int) ≤ _; omega) (by show _ ≤ (324 : Int); omega)

theorem hB128_getD (i : Nat) (hi : i < pow10Table128.size) :
    hB128.getD i 0
      = UInt64.ofNat (((pow10Table128.getD i pow10Table128_default).2.2 + 2048).toNat) := by
  have hsz : i < hB128.size := by unfold hB128; rw [Array.size_map]; exact hi
  rw [(Array.getElem_eq_getD 0 (h := hsz)).symm,
      (Array.getElem_eq_getD pow10Table128_default (h := hi)).symm]
  unfold hB128 at hsz ⊢
  exact Array.getElem_map _ hsz

theorem toNat_qB (q : Int) (h1 : ¬ q < -1074) (h2 : ¬ q > 971) :
    ((UInt64.ofNat (q + 1074).toNat).toNat : Int) = q + 1074 := by
  rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  omega

theorem toNat_hb (h : Int) (hh : -2048 ≤ h ∧ h < 2048) :
    ((UInt64.ofNat (h + 2048).toNat).toNat : Int) = h + 2048 := by
  rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  omega

theorem toNat_tA (q h : Int) (h1 : ¬ q < -1074) (h2 : ¬ q > 971)
    (hh : -2048 ≤ h ∧ h < 2048) :
    (((UInt64.ofNat (h + 2048).toNat + 4096) - UInt64.ofNat (q + 1074).toNat).toNat : Int)
      = h - q + 5070 := by
  have hq := toNat_qB q h1 h2
  have hb := toNat_hb h hh
  rw [UInt64.toNat_sub, UInt64.toNat_add]
  rw [show ((4096 : UInt64)).toNat = 4096 from rfl]
  omega

theorem tA_lt (q h : Int) (h1 : ¬ q < -1074) (h2 : ¬ q > 971)
    (hh : -2048 ≤ h ∧ h < 2048) :
    (((UInt64.ofNat (h + 2048).toNat + 4096) - UInt64.ofNat (q + 1074).toNat)
        < (5258 : UInt64)) = (h - q < 188) := by
  have ht := toNat_tA q h h1 h2 hh
  rw [show (((UInt64.ofNat (h + 2048).toNat + 4096) - UInt64.ofNat (q + 1074).toNat)
        < (5258 : UInt64)) ↔ _ from UInt64.lt_iff_toNat_lt,
      show ((5258 : UInt64)).toNat = 5258 from rfl]
  exact propext (by omega)

theorem tA_ge (q h : Int) (h1 : ¬ q < -1074) (h2 : ¬ q > 971)
    (hh : -2048 ≤ h ∧ h < 2048) :
    (((UInt64.ofNat (h + 2048).toNat + 4096) - UInt64.ofNat (q + 1074).toNat)
        ≥ (5326 : UInt64)) = (h - q ≥ 256) := by
  have ht := toNat_tA q h h1 h2 hh
  rw [show (((UInt64.ofNat (h + 2048).toNat + 4096) - UInt64.ofNat (q + 1074).toNat)
        ≥ (5326 : UInt64)) ↔ _ from UInt64.le_iff_toNat_le,
      show ((5326 : UInt64)).toNat = 5326 from rfl]
  exact propext (by omega)

theorem tA_val (q h : Int) (h1 : ¬ q < -1074) (h2 : ¬ q > 971)
    (hh : -2048 ≤ h ∧ h < 2048) (hlo : ¬ h - q < 188) (hhi : ¬ h - q ≥ 256) :
    ((UInt64.ofNat (h + 2048).toNat + 4096) - UInt64.ofNat (q + 1074).toNat) - 5070
      = UInt64.ofNat (h - q).toNat := by
  have ht := toNat_tA q h h1 h2 hh
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_sub_of_le _ _ (by
        rw [UInt64.le_iff_toNat_le, show ((5070 : UInt64)).toNat = 5070 from rfl]
        omega),
      show ((5070 : UInt64)).toNat = 5070 from rfl,
      UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  omega

theorem toNat_uBC (q h : Int) (h1 : ¬ q < -1074) (h2 : ¬ q > 971)
    (hh : -2048 ≤ h ∧ h < 2048) :
    ((UInt64.ofNat (q + 1074).toNat + UInt64.ofNat (h + 2048).toNat).toNat : Int)
      = q + h + 3122 := by
  have hq := toNat_qB q h1 h2
  have hb := toNat_hb h hh
  rw [UInt64.toNat_add]
  omega

theorem uBC_lt (q h : Int) (h1 : ¬ q < -1074) (h2 : ¬ q > 971)
    (hh : -2048 ≤ h ∧ h < 2048) :
    ((UInt64.ofNat (q + 1074).toNat + UInt64.ofNat (h + 2048).toNat) < (3186 : UInt64))
      = (q + h < 64) := by
  have ht := toNat_uBC q h h1 h2 hh
  rw [show ((UInt64.ofNat (q + 1074).toNat + UInt64.ofNat (h + 2048).toNat) < (3186 : UInt64))
        ↔ _ from UInt64.lt_iff_toNat_lt,
      show ((3186 : UInt64)).toNat = 3186 from rfl]
  exact propext (by omega)

theorem uBC_gt (q h : Int) (h1 : ¬ q < -1074) (h2 : ¬ q > 971)
    (hh : -2048 ≤ h ∧ h < 2048) :
    ((UInt64.ofNat (q + 1074).toNat + UInt64.ofNat (h + 2048).toNat) > (3254 : UInt64))
      = (q + h > 132) := by
  have ht := toNat_uBC q h h1 h2 hh
  rw [show ((UInt64.ofNat (q + 1074).toNat + UInt64.ofNat (h + 2048).toNat) > (3254 : UInt64))
        ↔ _ from UInt64.lt_iff_toNat_lt,
      show ((3254 : UInt64)).toNat = 3254 from rfl]
  exact propext (by omega)

theorem uBC_val (q h : Int) (h1 : ¬ q < -1074) (h2 : ¬ q > 971)
    (hh : -2048 ≤ h ∧ h < 2048) (hlo : ¬ q + h < 64) (hhi : ¬ q + h > 132) :
    (UInt64.ofNat (q + 1074).toNat + UInt64.ofNat (h + 2048).toNat) - 3122
      = UInt64.ofNat (q + h).toNat := by
  have ht := toNat_uBC q h h1 h2 hh
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_sub_of_le _ _ (by
        rw [UInt64.le_iff_toNat_le, show ((3122 : UInt64)).toNat = 3122 from rfl]
        omega),
      show ((3122 : UInt64)).toNat = 3122 from rfl,
      UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  omega

theorem hBound128_getD (i : Nat) (hi : i < pow10Table128.size) :
    -2048 ≤ (pow10Table128.getD i pow10Table128_default).2.2
      ∧ (pow10Table128.getD i pow10Table128_default).2.2 < 2048 := by
  have h := hBound128_at i hi
  rwa [show pow10Table128[i]! = pow10Table128.getD i pow10Table128_default from
        Array.getElem!_eq_getD] at h

@[inline]
def floorLog10Pow2B (qB : UInt64) : UInt64 :=
  asrUInt64_41 (qB * constC_u64 - bias1074constC_u64) + 324

@[inline]
def floorLog10ThreeQuartersPow2B (qB : UInt64) : UInt64 :=
  asrUInt64_41 (qB * constC_u64 - bias1074constC_minus_constA_u64) + 324

@[inline]
def isIrregularB (mU qB : UInt64) : Bool :=
  mU = (4503599627370496 : UInt64) && qB ≥ 1

@[inline]
def kBOfMQ (mU qB : UInt64) : UInt64 :=
  if isIrregularB mU qB then floorLog10ThreeQuartersPow2B qB else floorLog10Pow2B qB

/-- Pointwise check of the biased floor-logs against the verified fast
    forms over the whole biased-q domain, plus `-324 ≤ k` (so the bias
    never truncates). -/
def kBOfMQ_checkBool : Bool :=
  (List.range 2046).all fun qn =>
    decide (-324 ≤ floorLog10Pow2_fast ((qn : Int) - 1074))
    && decide ((floorLog10Pow2B (UInt64.ofNat qn)).toNat
        = (floorLog10Pow2_fast ((qn : Int) - 1074) + 324).toNat)
    && decide (-324 ≤ floorLog10ThreeQuartersPow2_fast ((qn : Int) - 1074))
    && decide ((floorLog10ThreeQuartersPow2B (UInt64.ofNat qn)).toNat
        = (floorLog10ThreeQuartersPow2_fast ((qn : Int) - 1074) + 324).toNat)

theorem kBOfMQ_check : kBOfMQ_checkBool = true := by decide +kernel

private theorem kB_facts (qn : Nat) (hq : qn < 2046) :
    (-324 ≤ floorLog10Pow2_fast ((qn : Int) - 1074)
      ∧ (floorLog10Pow2B (UInt64.ofNat qn)).toNat
          = (floorLog10Pow2_fast ((qn : Int) - 1074) + 324).toNat)
    ∧ (-324 ≤ floorLog10ThreeQuartersPow2_fast ((qn : Int) - 1074)
      ∧ (floorLog10ThreeQuartersPow2B (UInt64.ofNat qn)).toNat
          = (floorLog10ThreeQuartersPow2_fast ((qn : Int) - 1074) + 324).toNat) := by
  have hAll := kBOfMQ_check
  unfold kBOfMQ_checkBool at hAll
  rw [List.all_eq_true] at hAll
  have h := hAll qn (List.mem_range.mpr hq)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨⟨h.1.1.1, h.1.1.2⟩, ⟨h.1.2, h.2⟩⟩

theorem isIrregularB_eq (mU qB : UInt64) :
    isIrregularB mU qB = isIrregular mU.toNat ((qB.toNat : Int) - 1074) := by
  unfold isIrregularB isIrregular minNormalSignificand minBinaryExp
  congr 1
  · refine decide_eq_decide.mpr ?_
    rw [← UInt64.toNat_inj, show ((4503599627370496 : UInt64)).toNat = 1 <<< 52 from rfl]
  · refine decide_eq_decide.mpr ?_
    rw [ge_iff_le, UInt64.le_iff_toNat_le, show ((1 : UInt64)).toNat = 1 from rfl]
    omega

theorem kBOfMQ_eq (mU qB : UInt64) (hq : qB.toNat ≤ 2045) :
    -324 ≤ kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074)
    ∧ (kBOfMQ mU qB).toNat
        = (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) + 324).toNat := by
  have hf := kB_facts qB.toNat (by omega)
  rw [UInt64.ofNat_toNat] at hf
  unfold kBOfMQ kOfMQ_fast
  rw [isIrregularB_eq]
  by_cases hi : isIrregular mU.toNat ((qB.toNat : Int) - 1074) = true
  · simp only [hi, if_true]
    exact ⟨hf.2.1, hf.2.2⟩
  · simp only [Bool.not_eq_true] at hi
    simp only [hi, Bool.false_eq_true, if_false]
    exact ⟨hf.1.1, hf.1.2⟩

end Srtfp.Schubfach

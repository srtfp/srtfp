module
/- The runtime fallback of the live printer kernel.

   When a 128-bit verdict of the live kernel is ambiguous it defers to
   this orchestration: kernel 0's decision tree with the R20 multiply-shift
   for `shiftedSig`, the `UInt64` comparator for every verdict it decides,
   and an exact `Nat` comparison only for the verdict it does not. Every
   quantity is a `Nat` or a small `Int`, so nothing is boxed as a big
   integer except inside the exact leaf; `Int` is unboxed only below 2^31,
   which is what makes the `Int`-typed `Orchestration` orchestration slow
   at runtime (it stays as the proof waypoint of the flip3 kernel). -/

public import Srtfp.Perf.Orchestration
public import Srtfp.Perf.Uint64Kernel

@[expose] public section

namespace Srtfp.Schubfach

/-! ## Exact comparison over `Nat` magnitudes -/

/-- `a · 2^q ⋚ b · 10^k` exactly, over `Nat` magnitudes: `cmpScaledMixed`
    with the powers looked up and the products formed in `Nat`. -/
def cmpExact (a : Nat) (q : Int) (b : Nat) (k : Int) : Int :=
  let qPos : Nat := if q ≥ 0 then q.toNat else 0
  let qNeg : Nat := if q < 0 then (-q).toNat else 0
  let kPos : Nat := if k ≥ 0 then k.toNat else 0
  let kNeg : Nat := if k < 0 then (-k).toNat else 0
  let lhs : Nat := a * pow2Lookup qPos * pow10Lookup kNeg
  let rhs : Nat := b * pow10Lookup kPos * pow2Lookup qNeg
  if lhs < rhs then -1 else if lhs = rhs then 0 else 1

theorem cmpExact_eq (a : Nat) (q : Int) (b : Nat) (k : Int) :
    cmpExact a q b k = cmpScaledMixed (a : Int) q (b : Int) k := by
  unfold cmpExact cmpScaledMixed
  simp only [pow2Lookup_eq, pow10Lookup_eq]
  generalize (if q ≥ 0 then q.toNat else 0) = qPos
  generalize (if q < 0 then (-q).toNat else 0) = qNeg
  generalize (if k ≥ 0 then k.toNat else 0) = kPos
  generalize (if k < 0 then (-k).toNat else 0) = kNeg
  have hl : ((a * 2 ^ qPos * 10 ^ kNeg : Nat) : Int) = (a : Int) * 2 ^ qPos * 10 ^ kNeg := by
    push_cast; rfl
  have hr : ((b * 10 ^ kPos * 2 ^ qNeg : Nat) : Int) = (b : Int) * 10 ^ kPos * 2 ^ qNeg := by
    push_cast; rfl
  have hlt_iff : ((a : Int) * 2 ^ qPos * 10 ^ kNeg < (b : Int) * 10 ^ kPos * 2 ^ qNeg)
      ↔ (a * 2 ^ qPos * 10 ^ kNeg < b * 10 ^ kPos * 2 ^ qNeg) := by
    rw [← hl, ← hr]; exact Int.ofNat_lt
  have heq_iff : ((a : Int) * 2 ^ qPos * 10 ^ kNeg = (b : Int) * 10 ^ kPos * 2 ^ qNeg)
      ↔ (a * 2 ^ qPos * 10 ^ kNeg = b * 10 ^ kPos * 2 ^ qNeg) := by
    rw [← hl, ← hr]; exact Int.ofNat_inj
  by_cases hlt : a * 2 ^ qPos * 10 ^ kNeg < b * 10 ^ kPos * 2 ^ qNeg
  · rw [if_pos hlt, if_pos (hlt_iff.mpr hlt)]
  · rw [if_neg hlt, if_neg (fun h => hlt (hlt_iff.mp h))]
    by_cases heq : a * 2 ^ qPos * 10 ^ kNeg = b * 10 ^ kPos * 2 ^ qNeg
    · rw [if_pos heq, if_pos (heq_iff.mpr heq)]
    · rw [if_neg heq, if_neg (fun h => heq (heq_iff.mp h))]

/-! ## The comparator: `UInt64` verdict, exact on ambiguity -/

/-- `cmpScaledMixed_packed` over `Nat` magnitudes: the `UInt64` kernel's
    verdict when it is strict, the exact comparison otherwise. -/
def cmpN (q k : Int) (gHi gLo : UInt64) (qPlusH : Int) (a b : Nat) : Int :=
  if b = 0 then cmpExact a q b k
  else if a ≥ 1 <<< 60 ∨ b ≥ 1 <<< 60 then cmpExact a q b k
  else if k < pow10Table128_kMin ∨ k > pow10Table128_kMax then cmpExact a q b k
  else if qPlusH < 64 ∨ qPlusH > 132 then cmpExact a q b k
  else
    let v := cmpScaledMixed_u64 gHi gLo (UInt64.ofNat qPlusH.toNat) (UInt64.ofNat a) (UInt64.ofNat b)
    if v = 0 then cmpExact a q b k else v

theorem cmpN_eq (q k : Int) (a b : Nat) :
    cmpN q k (pow10Lookup128 k).1 (pow10Lookup128 k).2.1 (q + (pow10Lookup128 k).2.2) a b
      = cmpScaledMixed (a : Int) q (b : Int) k := by
  unfold cmpN
  by_cases hb0 : b = 0
  · rw [if_pos hb0, cmpExact_eq]
  rw [if_neg hb0]
  by_cases hbig : a ≥ 1 <<< 60 ∨ b ≥ 1 <<< 60
  · rw [if_pos hbig, cmpExact_eq]
  rw [if_neg hbig]
  by_cases hk : k < pow10Table128_kMin ∨ k > pow10Table128_kMax
  · rw [if_pos hk, cmpExact_eq]
  rw [if_neg hk]
  by_cases hqh : q + (pow10Lookup128 k).2.2 < 64 ∨ q + (pow10Lookup128 k).2.2 > 132
  · rw [if_pos hqh, cmpExact_eq]
  rw [if_neg hqh]
  have hk' : ¬ (k < -324 ∨ k > 324) := hk
  have h60 : (1 <<< 60 : Nat) = 1152921504606846976 := by decide
  rw [h60] at hbig
  rw [← cmpScaledMixed_packed_eq (a : Int) q (b : Int) k,
    cmpScaledMixed_packed_eq_u64_branch _ _ _ _ _ _ _ (Int.natCast_nonneg a) (Int.natCast_nonneg b)
      (by omega) (by show (a : Int) < ((1 <<< 60 : Nat) : Int); rw [h60]; omega)
      (by show (b : Int) < ((1 <<< 60 : Nat) : Int); rw [h60]; omega)
      (by show (-324 : Int) ≤ k; omega) (by show k ≤ (324 : Int); omega) (by omega) (by omega)]
  simp only [Int.toNat_natCast]
  rw [cmpExact_eq, cmpScaledMixed_eq_fast]

/-! ## Kernel 0's decision tree over `Nat` -/

/-- `inRoundingInterval` over `Nat` magnitudes; faithful for `1 ≤ m`. -/
def inRoundingIntervalN (q k : Int) (gHi gLo : UInt64) (qPlusH : Int)
    (s m : Nat) (irregular : Bool) : Bool :=
  let m4 := 4 * m
  let leftN := if irregular then m4 - 1 else m4 - 2
  let rightN := m4 + 2
  let s4 := 4 * s
  let cmpL := cmpN q k gHi gLo qPlusH leftN s4
  let cmpR := cmpN q k gHi gLo qPlusH rightN s4
  let cEven := m % 2 = 0
  (cmpL < 0 || (cmpL = 0 && cEven)) && (cmpR > 0 || (cmpR = 0 && cEven))

theorem inRoundingIntervalN_eq {s m : Nat} {irregular : Bool} (q k : Int) (hm : 1 ≤ m) :
    inRoundingIntervalN q k (pow10Lookup128 k).1 (pow10Lookup128 k).2.1
        (q + (pow10Lookup128 k).2.2) s m irregular
      = inRoundingInterval s k m q irregular := by
  unfold inRoundingIntervalN inRoundingInterval
  simp only [cmpN_eq]
  have hL : (((if irregular then 4 * m - 1 else 4 * m - 2) : Nat) : Int)
      = (if irregular then 4 * (m : Int) - 1 else 4 * (m : Int) - 2) := by
    split <;> omega
  have hR : ((4 * m + 2 : Nat) : Int) = 4 * (m : Int) + 2 := by omega
  have hS : ((4 * s : Nat) : Int) = 4 * (s : Int) := by omega
  rw [hL, hR, hS]

/-- `pickNearer` over `Nat` magnitudes; faithful for `1 ≤ m`. -/
def pickNearerN (q k : Int) (gHi gLo : UInt64) (qPlusH : Int) (s m : Nat) : Nat :=
  let irregular := isIrregular m q
  let uIn := inRoundingIntervalN q k gHi gLo qPlusH s m irregular
  let wIn := inRoundingIntervalN q k gHi gLo qPlusH (s + 1) m irregular
  if uIn && !wIn then s
  else if !uIn && wIn then s + 1
  else
    let cmp := cmpN q k gHi gLo qPlusH (2 * m) (2 * s + 1)
    if cmp < 0 then s
    else if cmp > 0 then s + 1
    else if s % 2 = 0 then s
    else s + 1

theorem pickNearerN_eq {s m : Nat} (q k : Int) (hm : 1 ≤ m) :
    pickNearerN q k (pow10Lookup128 k).1 (pow10Lookup128 k).2.1 (q + (pow10Lookup128 k).2.2) s m
      = pickNearer s k m q := by
  unfold pickNearerN pickNearer
  simp only [inRoundingIntervalN_eq q k hm, cmpN_eq]
  have h2m : ((2 * m : Nat) : Int) = 2 * (m : Int) := by omega
  have h2s : ((2 * s + 1 : Nat) : Int) = 2 * (s : Int) + 1 := by omega
  rw [h2m, h2s]

/-- Kernel 0 over `Nat` magnitudes: the fallback the live kernel defers to.
    `m = 0` never reaches it (the callers emit the zero directly) and is
    routed to kernel 0 to keep the equation universal. -/
def shortestUnsignedN (m : Nat) (q : Int) : Nat × Int :=
  if m = 0 then shortestUnsigned m q
  else
    let irregular := isIrregular m q
    let k := kOfMQ m q
    let tS := pow10Lookup128 (-k)
    let s :=
      if 0 < m ∧ m < 2 ^ 53 ∧ -1074 ≤ q ∧ q ≤ 971 then
        shiftedSig_packed_w q k tS.1 tS.2.1 (tS.2.2 - q) m
      else
        shiftedSig m q k
    if s ≥ 10 then
      let kHigh : Int := k + 1
      let tH := pow10Lookup128 kHigh
      let sHigh := s / 10
      let uIn := inRoundingIntervalN q kHigh tH.1 tH.2.1 (q + tH.2.2) sHigh m irregular
      let wIn := inRoundingIntervalN q kHigh tH.1 tH.2.1 (q + tH.2.2) (sHigh + 1) m irregular
      if uIn then (sHigh, kHigh)
      else if wIn then (sHigh + 1, kHigh)
      else
        let tK := pow10Lookup128 k
        (pickNearerN q k tK.1 tK.2.1 (q + tK.2.2) s m, k)
    else
      let tK := pow10Lookup128 k
      (pickNearerN q k tK.1 tK.2.1 (q + tK.2.2) s m, k)

theorem shortestUnsignedN_eq (m : Nat) (q : Int) :
    shortestUnsignedN m q = shortestUnsigned m q := by
  unfold shortestUnsignedN
  by_cases h0 : m = 0
  · rw [if_pos h0]
  rw [if_neg h0]
  have hm : 1 ≤ m := Nat.pos_of_ne_zero h0
  have hS : (if 0 < m ∧ m < 2 ^ 53 ∧ -1074 ≤ q ∧ q ≤ 971 then
              shiftedSig_packed_w q (kOfMQ m q) (pow10Lookup128 (-(kOfMQ m q))).1
                (pow10Lookup128 (-(kOfMQ m q))).2.1
                ((pow10Lookup128 (-(kOfMQ m q))).2.2 - q) m
            else
              shiftedSig m q (kOfMQ m q)) = shiftedSig m q (kOfMQ m q) := by
    by_cases hbin : 0 < m ∧ m < 2 ^ 53 ∧ -1074 ≤ q ∧ q ≤ 971
    · rw [if_pos hbin]
      obtain ⟨hm', hm53, hq_lo, hq_hi⟩ := hbin
      exact shiftedSig_packed_w_eq_binary64 m q hm' hm53 hq_lo hq_hi
    · rw [if_neg hbin]
  unfold shortestUnsigned
  simp only [hS, inRoundingIntervalN_eq _ _ hm, pickNearerN_eq _ _ hm]

end Srtfp.Schubfach

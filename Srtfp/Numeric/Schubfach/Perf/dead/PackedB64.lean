/- DEAD CODE — verified reference, not on any live path.

   This module preserves the *original* `B < 2^64`-guarded packed
   128-bit kernel (`shiftedSig_packed`) and its correctness lemmas.

   Before the R20 §9.7 mechanisation, the fast UInt64 kernel was only
   provably correct in the *safe regime* `B = 2^qNeg · 10^kPos < 2^64`
   (where `m · B ≤ 2^s` makes the table-truncation slack harmless).  The
   dispatch therefore carried a `B < 2^64` accuracy guard and fell back
   to the boxed-`Nat` spec `shiftedSig` for the ~93% of binary64 inputs
   that failed it (large positive exponents, subnormals).

   With R20 proven unconditionally (`R20BandSweep`,
   `shiftedSig_packed_w_eq_binary64`), the guard is gone: the *widened*
   kernel `shiftedSig_packed_w` (in `Perf/KernelR20.lean`) is correct
   over the entire binary64 domain, and the live `shiftedSig_v2/v3/v3b`
   chain dispatches on the binary64 domain instead.  The B-guarded
   `shiftedSig_packed` below is no longer reachable from any `@[csimp]`
   entry point.

   It is retained here, fully proven, as a historical reference for the
   safe-regime construction.  It is imported by nothing on the live path.

   NOTE: the exact-`Nat` spec `shiftedSig` / `cmpScaledMixed` are NOT here
   — they remain the correctness reference and `@[csimp]` target in
   `Schubfach.lean`.
-/
import Srtfp.Numeric.Schubfach.Perf.Kernel128
import Srtfp.Numeric.Schubfach.Perf.Uint64Kernel

namespace PP.Numeric.Schubfach.Dead

open PP.Numeric.Schubfach

/-- Packed floor-multiply-shift with the `B < 2^64` accuracy guard:
    same body as `shiftedSig_fast2`, with the `(q, k)`-only
    precomputations supplied as direct arguments.  DEAD — superseded by
    `shiftedSig_packed_w`. -/
def shiftedSig_packed
    (q : Int) (k : Int)
    (gHi : UInt64) (gLo : UInt64) (shiftAmt : Int) (B : Nat)
    (m : Nat) : Nat :=
  if m ≥ (1 <<< 60 : Nat) then shiftedSig_fast m q k
  else
    let kLookup : Int := -k
    if kLookup < pow10Table128_kMin ∨ kLookup > pow10Table128_kMax then
      shiftedSig_fast m q k
    else
      if shiftAmt < 124 ∨ shiftAmt ≥ 192 then shiftedSig_fast m q k
      else
        if B ≥ (1 <<< 64 : Nat) then shiftedSig_fast m q k
        else
          let mU : UInt64 := UInt64.ofNat m
          let pLo  : UInt64 := mU * gLo
          let pLoH : UInt64 := mulHi64 mU gLo
          let pHi  : UInt64 := mU * gHi
          let pHiH : UInt64 := mulHi64 mU gHi
          let midSum   : UInt64 := pHi + pLoH
          let midCarry : UInt64 := if midSum < pHi then 1 else 0
          let rHi  : UInt64 := pHiH + midCarry
          let rMid : UInt64 := midSum
          let rLo  : UInt64 := pLo
          let s : UInt64 := UInt64.ofNat shiftAmt.toNat
          let resU : UInt64 :=
            if s < 64 then
              if s = 0 then rLo
              else (rLo >>> s) ||| (rMid <<< (64 - s))
            else if s < 128 then
              let s64 := s - 64
              if s64 = 0 then rMid
              else (rMid >>> s64) ||| (rHi <<< (64 - s64))
            else
              let s64 := s - 128
              rHi >>> s64
          resU.toNat

theorem shiftedSig_packed_eq_fast2 (m : Nat) (q k : Int) :
    shiftedSig_packed q k (pow10Lookup128 (-k)).1 (pow10Lookup128 (-k)).2.1
        ((pow10Lookup128 (-k)).2.2 - q)
        (2 ^ (if q < 0 then (-q).toNat else 0) *
          10 ^ (if k ≥ 0 then k.toNat else 0))
        m
      = shiftedSig_fast2 m q k := by
  unfold shiftedSig_packed shiftedSig_fast2
  rfl

theorem shiftedSig_packed_eq (m : Nat) (q k : Int) :
    shiftedSig_packed q k (pow10Lookup128 (-k)).1 (pow10Lookup128 (-k)).2.1
        ((pow10Lookup128 (-k)).2.2 - q)
        (2 ^ (if q < 0 then (-q).toNat else 0) *
          10 ^ (if k ≥ 0 then k.toNat else 0))
        m
      = shiftedSig m q k := by
  rw [shiftedSig_packed_eq_fast2, ← shiftedSig_eq_fast2]

/-- The packed kernel's body doesn't reference `B` once the `B < 2^64`
    guard is passed.  So for any two `B, B' < 2^64`, the result is the
    same. -/
theorem shiftedSig_packed_irrelevant_of_lt
    (q k : Int) (gHi gLo : UInt64) (shiftAmt : Int) (B B' : Nat) (m : Nat)
    (hB : B < (1 <<< 64 : Nat)) (hB' : B' < (1 <<< 64 : Nat)) :
    shiftedSig_packed q k gHi gLo shiftAmt B m
      = shiftedSig_packed q k gHi gLo shiftAmt B' m := by
  unfold shiftedSig_packed
  have hB_lt : ¬ B ≥ (1 <<< 64 : Nat) := by omega
  have hB'_lt : ¬ B' ≥ (1 <<< 64 : Nat) := by omega
  by_cases h1 : m ≥ (1 <<< 60 : Nat)
  · simp only [if_pos h1]
  · simp only [if_neg h1]
    by_cases h2 : (-k : Int) < pow10Table128_kMin ∨ (-k : Int) > pow10Table128_kMax
    · simp only [if_pos h2]
    · simp only [if_neg h2]
      by_cases h3 : shiftAmt < 124 ∨ shiftAmt ≥ 192
      · simp only [if_pos h3]
      · simp only [if_neg h3, if_neg hB_lt, if_neg hB'_lt]

/-- The pure UInt64 kernel agrees with the B-guarded `shiftedSig_packed`
    under fast-path preconditions (`B = 0`).  DEAD — superseded by
    `shiftedSig_u64_kernel_eq_packed_w`. -/
theorem shiftedSig_u64_kernel_eq_packed
    (q k : Int) (m : Nat) (gHi gLo : UInt64) (shiftAmt : Int)
    (hm : m < (1 <<< 60 : Nat))
    (hk_lo : pow10Table128_kMin ≤ -k) (hk_hi : -k ≤ pow10Table128_kMax)
    (hsh_lo : 124 ≤ shiftAmt) (hsh_hi : shiftAmt < 192) :
    shiftedSig_u64_kernel (UInt64.ofNat m) gHi gLo
        (UInt64.ofNat shiftAmt.toNat)
      = UInt64.ofNat (shiftedSig_packed q k gHi gLo shiftAmt 0 m) := by
  unfold shiftedSig_u64_kernel shiftedSig_packed
  rw [if_neg (by omega : ¬ m ≥ (1 <<< 60 : Nat))]
  rw [if_neg (by push_neg; constructor <;> omega
                : ¬ ((-k : Int) < pow10Table128_kMin ∨ (-k : Int) > pow10Table128_kMax))]
  rw [if_neg (by push_neg; constructor <;> omega
                : ¬ (shiftAmt < 124 ∨ shiftAmt ≥ 192))]
  rw [if_neg (by decide : ¬ (0 : Nat) ≥ (1 <<< 64 : Nat))]
  rw [UInt64.ofNat_toNat]

end PP.Numeric.Schubfach.Dead

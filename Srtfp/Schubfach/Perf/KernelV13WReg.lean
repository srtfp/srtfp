/- The `wReg` table-width sweep for KernelV13, in its own module.

   Each `wRegChunk_*` is a kernel `decide` over a 93-element slice of the
   2046-wide exponent range. They are kept in a dedicated module because
   kernel-reduction memory accumulates across a module's declarations on
   ≥4.32 toolchains: co-resident with KernelV13's other large proofs the
   later chunks trip the kernel's memory guard, while in a fresh process
   the whole sweep fits comfortably. -/

import Srtfp.Schubfach.Pow10Table128
import Srtfp.Schubfach.TableInvariant
import Srtfp.Schubfach

namespace Srtfp.Schubfach

/-- Per-index well-regulated predicate (shared by `wRegBool` and the
    chunked checker). -/
def wRegPred (qn : Nat) : Bool :=
  let q : Int := (qn : Int) - 1074
  let k : Int := floorLog10Pow2 q
  decide (k < -324 ∨ k + 1 > 324 ∨ 128 ≤ (pow10Lookup128 (-(k + 1))).2.2 - q)

def wRegBool : Bool :=
  (List.range 2046).all wRegPred

/-- Chunked checker: `wRegPred` holds across the sub-range `[lo, lo+n)`.
    A single `decide +kernel` over the full 2046-wide range expands the
    `pow10Lookup128` table 2046x in one kernel reduction (~20 GB peak).
    Splitting it into many narrow fixed-width chunks, each elaborated as a
    separate declaration so they never coexist in memory, caps the peak at
    one chunk's reduction (~4.5 GB at this width). Do NOT merge the chunks
    back into one `decide`, and keep the width small — that is what holds
    the module under the lakefile's `lean -M` budget. -/
def wRegChunk (lo n : Nat) : Bool :=
  (List.range' lo n).all wRegPred

theorem wRegChunk_0 : wRegChunk 0 93 = true := by decide +kernel
theorem wRegChunk_1 : wRegChunk 93 93 = true := by decide +kernel
theorem wRegChunk_2 : wRegChunk 186 93 = true := by decide +kernel
theorem wRegChunk_3 : wRegChunk 279 93 = true := by decide +kernel
theorem wRegChunk_4 : wRegChunk 372 93 = true := by decide +kernel
theorem wRegChunk_5 : wRegChunk 465 93 = true := by decide +kernel
theorem wRegChunk_6 : wRegChunk 558 93 = true := by decide +kernel
theorem wRegChunk_7 : wRegChunk 651 93 = true := by decide +kernel
theorem wRegChunk_8 : wRegChunk 744 93 = true := by decide +kernel
theorem wRegChunk_9 : wRegChunk 837 93 = true := by decide +kernel
theorem wRegChunk_10 : wRegChunk 930 93 = true := by decide +kernel
theorem wRegChunk_11 : wRegChunk 1023 93 = true := by decide +kernel
theorem wRegChunk_12 : wRegChunk 1116 93 = true := by decide +kernel
theorem wRegChunk_13 : wRegChunk 1209 93 = true := by decide +kernel
theorem wRegChunk_14 : wRegChunk 1302 93 = true := by decide +kernel
theorem wRegChunk_15 : wRegChunk 1395 93 = true := by decide +kernel
theorem wRegChunk_16 : wRegChunk 1488 93 = true := by decide +kernel
theorem wRegChunk_17 : wRegChunk 1581 93 = true := by decide +kernel
theorem wRegChunk_18 : wRegChunk 1674 93 = true := by decide +kernel
theorem wRegChunk_19 : wRegChunk 1767 93 = true := by decide +kernel
theorem wRegChunk_20 : wRegChunk 1860 93 = true := by decide +kernel
theorem wRegChunk_21 : wRegChunk 1953 93 = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem wRegRange_split : List.range 2046
    = List.range' 0 93 ++ (List.range' 93 93 ++ (List.range' 186 93 ++ (List.range' 279 93 ++ (List.range' 372 93 ++ (List.range' 465 93 ++ (List.range' 558 93 ++ (List.range' 651 93 ++ (List.range' 744 93 ++ (List.range' 837 93 ++ (List.range' 930 93 ++ (List.range' 1023 93 ++ (List.range' 1116 93 ++ (List.range' 1209 93 ++ (List.range' 1302 93 ++ (List.range' 1395 93 ++ (List.range' 1488 93 ++ (List.range' 1581 93 ++ (List.range' 1674 93 ++ (List.range' 1767 93 ++ (List.range' 1860 93 ++ (List.range' 1953 93))))))))))))))))))))) := by
  rfl

theorem wReg_check : wRegBool = true := by
  unfold wRegBool
  rw [wRegRange_split]
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨wRegChunk_0, wRegChunk_1, wRegChunk_2, wRegChunk_3, wRegChunk_4, wRegChunk_5, wRegChunk_6, wRegChunk_7, wRegChunk_8, wRegChunk_9, wRegChunk_10, wRegChunk_11, wRegChunk_12, wRegChunk_13, wRegChunk_14, wRegChunk_15, wRegChunk_16, wRegChunk_17, wRegChunk_18, wRegChunk_19, wRegChunk_20, wRegChunk_21⟩

theorem wReg_at (q : Int) (h1 : -1074 ≤ q) (h2 : q ≤ 971)
    (hklo : ¬ floorLog10Pow2 q < pow10Table128_kMin)
    (hkhi : ¬ floorLog10Pow2 q + 1 > pow10Table128_kMax) :
    128 ≤ (pow10Lookup128 (-(floorLog10Pow2 q + 1))).2.2 - q := by
  have hAll := wReg_check
  unfold wRegBool at hAll
  rw [List.all_eq_true] at hAll
  have h := hAll (q + 1074).toNat (List.mem_range.mpr (by omega))
  unfold wRegPred at h
  simp only [decide_eq_true_eq] at h
  have hq : (((q + 1074).toNat : Int)) - 1074 = q := by omega
  rw [hq] at h
  have hklo' : ¬ floorLog10Pow2 q < (-324 : Int) := hklo
  have hkhi' : ¬ floorLog10Pow2 q + 1 > (324 : Int) := hkhi
  rcases h with h | h | h
  · exact absurd h (by omega)
  · exact absurd h (by omega)
  · exact h


end Srtfp.Schubfach

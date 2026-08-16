import Srtfp.Schubfach.R20Keystone
import Srtfp.Schubfach

/-!
# R20 band sweeps — checkers and range predicates

Definitions and soundness lemmas shared by the per-band `decide` sweep
modules (`R20Band2Sweep.lean`, `R20Band1Sweep{A,B}.lean`) and their
combiner (`R20BandSweep.lean`). Split from the sweeps so the four
long-running kernel `decide`s elaborate in parallel lake jobs instead of
serially in one module.
-/

namespace Srtfp.Schubfach.R20Sweep

open Srtfp.Schubfach
open Srtfp.Schubfach (farFromMultipleBelow)

/-! ## Band 2 (`q ≥ 0`, modulus `5^k`) -/

/-- Band-2 far check at `(qNat, kNat)`: vacuously `true` outside the sweep
regime (`k < 31` or `k > q`), otherwise the decidable far check over the
candidate convergent denominators. -/
def farCheckAt2 (qNat kNat : Nat) : Bool :=
  if kNat < 31 ∨ qNat < kNat then true
  else (convDenoms (2^(qNat-kNat)) (5^kNat) (2^53)).all (fun Q => farB (5^kNat) (2^(qNat-kNat)) Q 71)

/-- Soundness of the band-2 far check in the sweep regime. -/
theorem farCheckAt2_sound (qNat kNat : Nat) (hk31 : 31 ≤ kNat) (hkq : kNat ≤ qNat)
    (hchk : farCheckAt2 qNat kNat = true) :
    ∀ m, 0 < m → m < 2^53 → farFromMultipleBelow (5^kNat) (2^(qNat-kNat)) m 71 := by
  unfold farCheckAt2 at hchk
  rw [if_neg (by omega)] at hchk
  apply farAll_of_sweep (5^kNat) (2^(qNat-kNat)) 71 (2^53)
  · exact Nat.pow_pos (by omega)
  · exact Nat.Coprime.pow _ _ (show Nat.Coprime 2 5 by decide)
  · calc (2:Nat)^53 ≤ 5^31 := by grind
      _ ≤ 5^kNat := Nat.pow_le_pow_right (by grind) hk31
  · exact Nat.le_refl _
  · rw [show 2*2^53 = 2^54 from by grind]; exact Nat.pow_le_pow_right (by grind) (by grind)
  · exact hchk

/-- Per-`q` band-2 check: both `kOfMQ` candidates (`floorLog10Pow2 q` and
`floorLog10ThreeQuartersPow2 q`). -/
def band2CheckQ (q : Nat) : Bool :=
  farCheckAt2 q (floorLog10Pow2 q).toNat && farCheckAt2 q (floorLog10ThreeQuartersPow2 q).toNat

/-- Band-2 range check on `[lo, lo+len)`. -/
def band2ForRange (lo len : Nat) : Prop :=
  (List.range len).all (fun i => band2CheckQ (lo + i)) = true

theorem band2ForRange_sound (lo len : Nat) (h : band2ForRange lo len) :
    ∀ q, lo ≤ q → q < lo + len → band2CheckQ q = true := by
  unfold band2ForRange at h
  rw [List.all_eq_true] at h
  intro q hlo hhi
  have := h (q - lo) (List.mem_range.mpr (by omega))
  rwa [show lo + (q - lo) = q from by omega] at this

/-! ## Band 1 (`q < 0`, modulus `2^e`, `e = qNeg − kNeg`) -/

/-- Band-1 far check at `(qNeg, kNeg)`: vacuously `true` outside the sweep
regime (`e < 72` or `kNeg > qNeg`), otherwise the decidable far check. -/
def farCheckAt1 (qNeg kNeg : Nat) : Bool :=
  if qNeg - kNeg < 72 ∨ qNeg < kNeg then true
  else (convDenoms (5^kNeg) (2^(qNeg-kNeg)) (2^53)).all
        (fun Q => farB (2^(qNeg-kNeg)) (5^kNeg) Q 71)

/-- Soundness of the band-1 far check in the sweep regime. -/
theorem farCheckAt1_sound (qNeg kNeg : Nat) (he72 : 72 ≤ qNeg - kNeg) (hkq : kNeg ≤ qNeg)
    (hchk : farCheckAt1 qNeg kNeg = true) :
    ∀ m, 0 < m → m < 2^53 → farFromMultipleBelow (2^(qNeg-kNeg)) (5^kNeg) m 71 := by
  unfold farCheckAt1 at hchk
  rw [if_neg (by omega)] at hchk
  apply farAll_of_sweep (2^(qNeg-kNeg)) (5^kNeg) 71 (2^53)
  · exact Nat.pow_pos (by omega)
  · exact Nat.Coprime.pow _ _ (show Nat.Coprime 5 2 by decide)
  · exact Nat.pow_le_pow_right (by grind) (by omega)
  · exact Nat.le_refl _
  · rw [show 2*2^53 = 2^54 from by grind]; exact Nat.pow_le_pow_right (by grind) (by grind)
  · exact hchk

/-- Per-`qNeg` band-1 check (`q = -qNeg`), both `kOfMQ` candidates. -/
def band1CheckQ (qNeg : Nat) : Bool :=
  let q : Int := -(qNeg : Int)
  farCheckAt1 qNeg (-(floorLog10Pow2 q)).toNat
    && farCheckAt1 qNeg (-(floorLog10ThreeQuartersPow2 q)).toNat

def band1ForRange (lo len : Nat) : Prop :=
  (List.range len).all (fun i => band1CheckQ (lo + i)) = true

theorem band1ForRange_sound (lo len : Nat) (h : band1ForRange lo len) :
    ∀ qNeg, lo ≤ qNeg → qNeg < lo + len → band1CheckQ qNeg = true := by
  unfold band1ForRange at h
  rw [List.all_eq_true] at h
  intro qNeg hlo hhi
  have := h (qNeg - lo) (List.mem_range.mpr (by omega))
  rwa [show lo + (qNeg - lo) = qNeg from by omega] at this


end Srtfp.Schubfach.R20Sweep

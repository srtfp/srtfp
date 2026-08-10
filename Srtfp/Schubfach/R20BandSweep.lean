import Srtfp.Schubfach.R20Keystone
import Srtfp.Schubfach

/-!
# R20 band sweeps: universal `farFromMultipleBelow` over the binary64 range

This file runs the decidable continued-fraction sweep (`farAll_of_sweep` from
`R20Keystone.lean`) over the binary64 exponent range, in both bands, and
combines it with the elementary small-exponent closers to obtain
`residueR20Cond` for *every* band input — with no `B < 2^64` accuracy guard.

* **Band 2** (`q ≥ 0`): modulus `M = 5^k`, multiplier `u = 2^(q−k)`.  The
  elementary closer (`residueR20Cond_band2_elementary`) handles `k ≤ 30`; the
  sweep handles `k ≥ 31` (there `5^k > 2^53`, so the sweep regime `bound ≤ M`
  holds).
* **Band 1** (`q < 0`): modulus `M = 2^e` (`e = qNeg − kNeg`), multiplier
  `u = 5^kNeg`.  Elementary handles `e ≤ 71`; the sweep handles `e ≥ 72`.

The Schubfach exponent `k = kOfMQ m q` is one of `floorLog10Pow2 q` (regular)
or `floorLog10ThreeQuartersPow2 q` (irregular); the sweep checks both per `q`.

The sweeps are closed by ordinary kernel `decide` (no `native_decide`): each
`(q,k)` reduces to `≤ 78` Euclidean-continuant far checks, and the whole
binary64 range finishes in ~100s (band 2) / ~150s (band 1) at build time, with
raised `maxRecDepth` / `exponentiation.threshold` / `maxHeartbeats`.

All results are sorry-free; axioms `propext`, `Quot.sound`, `Classical.choice`
only (no `native_decide`, no `Lean.ofReduceBool`).
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

set_option exponentiation.threshold 8192 in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 200000000 in
theorem band2_sweep_0_324 : band2ForRange 0 324 := by unfold band2ForRange; decide

set_option exponentiation.threshold 8192 in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 200000000 in
theorem band2_sweep_324_648 : band2ForRange 324 324 := by unfold band2ForRange; decide

set_option exponentiation.threshold 8192 in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 200000000 in
theorem band2_sweep_648_972 : band2ForRange 648 324 := by unfold band2ForRange; decide

/-- Every binary64 band-2 `q ∈ [0, 971]` passes the per-`q` check. -/
theorem band2CheckQ_holds (q : Nat) (hq : q ≤ 971) : band2CheckQ q = true := by
  rcases Nat.lt_or_ge q 324 with h | h
  · exact band2ForRange_sound 0 324 band2_sweep_0_324 q (by omega) (by omega)
  · rcases Nat.lt_or_ge q 648 with h2 | h2
    · exact band2ForRange_sound 324 324 band2_sweep_324_648 q (by omega) (by omega)
    · exact band2ForRange_sound 648 324 band2_sweep_648_972 q (by omega) (by omega)

/-- **Band-2 universal `far`.**  For every binary64 `q ∈ [0, 971]`, the
Schubfach `k = kOfMQ m q` with `31 ≤ k ≤ q`, and `m < 2^53`, the orbit point
`m·2^(q−k)` is far from multiples of `5^k`.  (The `k ≤ 30` case is the
elementary closer.) -/
theorem band2_far (m : Nat) (q : Nat) (hq : q ≤ 971) (kNat : Nat)
    (hk : kNat = (floorLog10Pow2 q).toNat ∨ kNat = (floorLog10ThreeQuartersPow2 q).toNat)
    (hk31 : 31 ≤ kNat) (hkq : kNat ≤ q) (hm : 0 < m) (hm53 : m < 2^53) :
    farFromMultipleBelow (5^kNat) (2^(q-kNat)) m 71 := by
  have hcheck := band2CheckQ_holds q hq
  unfold band2CheckQ at hcheck
  rw [Bool.and_eq_true] at hcheck
  have hat : farCheckAt2 q kNat = true := by
    rcases hk with h | h
    · rw [h]; exact hcheck.1
    · rw [h]; exact hcheck.2
  exact farCheckAt2_sound q kNat hk31 hkq hat m hm hm53

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

set_option exponentiation.threshold 8192 in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 400000000 in
theorem band1_sweep_1_269 : band1ForRange 1 269 := by unfold band1ForRange; decide

set_option exponentiation.threshold 8192 in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 400000000 in
theorem band1_sweep_270_538 : band1ForRange 270 269 := by unfold band1ForRange; decide

set_option exponentiation.threshold 8192 in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 400000000 in
theorem band1_sweep_539_806 : band1ForRange 539 268 := by unfold band1ForRange; decide

set_option exponentiation.threshold 8192 in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 400000000 in
theorem band1_sweep_807_1074 : band1ForRange 807 268 := by unfold band1ForRange; decide

/-- Every binary64 band-1 `qNeg ∈ [1, 1074]` passes the per-`qNeg` check. -/
theorem band1CheckQ_holds (qNeg : Nat) (h1 : 1 ≤ qNeg) (hq : qNeg ≤ 1074) :
    band1CheckQ qNeg = true := by
  rcases Nat.lt_or_ge qNeg 270 with h | h
  · exact band1ForRange_sound 1 269 band1_sweep_1_269 qNeg (by omega) (by omega)
  · rcases Nat.lt_or_ge qNeg 539 with h2 | h2
    · exact band1ForRange_sound 270 269 band1_sweep_270_538 qNeg (by omega) (by omega)
    · rcases Nat.lt_or_ge qNeg 807 with h3 | h3
      · exact band1ForRange_sound 539 268 band1_sweep_539_806 qNeg (by omega) (by omega)
      · exact band1ForRange_sound 807 268 band1_sweep_807_1074 qNeg (by omega) (by omega)

/-- **Band-1 universal `far`.**  For every binary64 `q < 0` (`qNeg = -q ∈
[1,1074]`), the Schubfach `k = kOfMQ m q` with `kNeg = -k`, `e = qNeg − kNeg ≥
72`, `kNeg ≤ qNeg`, and `m < 2^53`, the orbit point `m·5^kNeg` is far from
multiples of `2^e`.  (The `e ≤ 71` case is the elementary closer.) -/
theorem band1_far (m qNeg kNeg : Nat) (h1 : 1 ≤ qNeg) (hq : qNeg ≤ 1074)
    (hk : kNeg = (-(floorLog10Pow2 (-(qNeg:Int)))).toNat
          ∨ kNeg = (-(floorLog10ThreeQuartersPow2 (-(qNeg:Int)))).toNat)
    (he72 : 72 ≤ qNeg - kNeg) (hkq : kNeg ≤ qNeg) (hm : 0 < m) (hm53 : m < 2^53) :
    farFromMultipleBelow (2^(qNeg-kNeg)) (5^kNeg) m 71 := by
  have hcheck := band1CheckQ_holds qNeg h1 hq
  unfold band1CheckQ at hcheck
  rw [Bool.and_eq_true] at hcheck
  have hat : farCheckAt1 qNeg kNeg = true := by
    rcases hk with h | h
    · rw [h]; exact hcheck.1
    · rw [h]; exact hcheck.2
  exact farCheckAt1_sound qNeg kNeg he72 hkq hat m hm hm53

/-! ## Assembled `residueR20Cond` over the binary64 range (no `B < 2^64` guard)

Combine the sweep (`band{1,2}_far`, hard regime) with the elementary
small-exponent closers, for `m < 2^53` and `s ≥ 124` (the binary64 kernel
regime, `q + h ∈ [124, 134]`). -/

/-- Band-2 `residueR20Cond` for *every* binary64 `q ∈ [0, 971]` and Schubfach
`k = kOfMQ`-derived exponent (`k ≤ q`), `m < 2^53`, `s ≥ 124` — unconditional
(no `B < 2^64` guard).  Splits at `k = 30`: elementary below, sweep above. -/
theorem residueR20Cond_band2_binary64
    (m q kNat s : Nat) (hq : q ≤ 971)
    (hk : kNat = (floorLog10Pow2 q).toNat ∨ kNat = (floorLog10ThreeQuartersPow2 q).toNat)
    (hkq : kNat ≤ q) (hm : 0 < m) (hm53 : m < 2^53) (hs : 124 ≤ s) :
    residueR20Cond m (10 ^ kNat) s (m * 2 ^ q) := by
  rcases Nat.lt_or_ge kNat 31 with hk30 | hk31
  · -- elementary: m · 5^k ≤ 2^s since 5^30 < 2^70 and m < 2^53
    apply residueR20Cond_band2_elementary m q kNat s hkq
    calc m * 5 ^ kNat ≤ m * 5 ^ 30 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by grind) (by omega))
      _ ≤ (2^53 - 1) * 5 ^ 30 := Nat.mul_le_mul_right _ (by omega)
      _ ≤ 2 ^ 124 := by grind
      _ ≤ 2 ^ s := Nat.pow_le_pow_right (by grind) (by omega)
  · -- sweep: band2_far with a = 71, slack m·2^71 ≤ 2^s
    apply residueR20Cond_band2_of_far m q kNat s 71 hkq
      (band2_far m q hq kNat hk hk31 hkq hm hm53)
    calc m * 2 ^ 71 ≤ (2^53 - 1) * 2 ^ 71 := Nat.mul_le_mul_right _ (by omega)
      _ ≤ 2 ^ 124 := by grind
      _ ≤ 2 ^ s := Nat.pow_le_pow_right (by grind) (by omega)

/-- Band-1 `residueR20Cond` for *every* binary64 `q < 0` (`qNeg = -q ∈
[1,1074]`) and Schubfach `kNeg`, `kNeg ≤ qNeg`, `m < 2^53`, `s ≥ 124` —
unconditional.  Splits at `e = qNeg − kNeg = 71`: elementary below, sweep
above. -/
theorem residueR20Cond_band1_binary64
    (m qNeg kNeg s : Nat) (h1 : 1 ≤ qNeg) (hq : qNeg ≤ 1074)
    (hk : kNeg = (-(floorLog10Pow2 (-(qNeg:Int)))).toNat
          ∨ kNeg = (-(floorLog10ThreeQuartersPow2 (-(qNeg:Int)))).toNat)
    (hkq : kNeg ≤ qNeg) (hm : 0 < m) (hm53 : m < 2^53) (hs : 124 ≤ s) :
    residueR20Cond m (2 ^ qNeg) s (m * 10 ^ kNeg) := by
  rcases Nat.lt_or_ge (qNeg - kNeg) 72 with he71 | he72
  · -- elementary: m · 2^e ≤ 2^s since e ≤ 71 and m < 2^53
    apply residueR20Cond_band1_elementary m qNeg kNeg s hkq
    calc m * 2 ^ (qNeg - kNeg) ≤ m * 2 ^ 71 :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by grind) (by omega))
      _ ≤ (2^53 - 1) * 2 ^ 71 := Nat.mul_le_mul_right _ (by omega)
      _ ≤ 2 ^ 124 := by grind
      _ ≤ 2 ^ s := Nat.pow_le_pow_right (by grind) (by omega)
  · -- sweep: band1_far with a = 71
    apply residueR20Cond_band1_of_far m qNeg kNeg s 71 hkq
      (band1_far m qNeg kNeg h1 hq hk he72 hkq hm hm53)
    calc m * 2 ^ 71 ≤ (2^53 - 1) * 2 ^ 71 := Nat.mul_le_mul_right _ (by omega)
      _ ≤ 2 ^ 124 := by grind
      _ ≤ 2 ^ s := Nat.pow_le_pow_right (by grind) (by omega)

end Srtfp.Schubfach.R20Sweep

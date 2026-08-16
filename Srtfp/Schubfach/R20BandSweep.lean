import Srtfp.Schubfach.R20Band2Sweep
import Srtfp.Schubfach.R20Band1SweepA
import Srtfp.Schubfach.R20Band1SweepB

/-!
# R20 band sweeps: universal `farFromMultipleBelow` over the binary64 range

Combiners over the per-band `decide` sweeps (see `R20BandSweepDefs.lean`
for the checkers and the sweep modules for the kernel `decide`s, split
so they elaborate in parallel). All results are sorry-free; axioms
`propext`, `Quot.sound`, `Classical.choice` only (no `native_decide`).
-/

namespace Srtfp.Schubfach.R20Sweep

open Srtfp.Schubfach
open Srtfp.Schubfach (farFromMultipleBelow)

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

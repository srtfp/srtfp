module
/- Rounding to odd (Giulietti §9.3–§9.7).

   The tests of §9.2 compare the rationals `V_l`, `V`, `V_r` with
   integers. Definition 8's rounding to odd, `r_o`, keeps every such
   comparison exact: `x ⋚ 2h ⟺ r_o x ⋚ 2h` for integers `h`. Scaling
   the tests by `4` (or `2`) makes the integer sides even (R18), so the
   tests can be run on `v̄_l = r_o(4V_l)`, `v̄ = r_o(4V)`, `v̄_r = r_o(4V_r)`;
   R19 reads `s = ⌊V⌋` off `v̄`.

   The kernel does not have `V` but an overestimate `V'` within `ε/2`
   (R24). Result 20 (Nadezhin) keeps `2V` at distance `ε` from every
   integer it is not equal to; then `⌊2V'⌋ = ⌊2V⌋` (R21), and the
   modified rounding `r'_o` of Definition 9, applied to `4V'`, is
   `r_o(4V)` (R22). R23 is the form the kernel computes.

   Everything here is generic over `Rat`; Result 20 enters as the
   hypothesis `Separated ε (2V)`. -/

public import Srtfp.Perf.Schubfach.Exact

@[expose] public section

open Srtfp.Compat

namespace Srtfp.Schubfach

/-! ## Definition 8: `r_o` -/

/-- Round to odd: an even integer stays, anything else goes to the odd
    integer nearest to it. -/
def ro (x : Rat) : Int :=
  if ((x / 2).floor : Rat) = x / 2 then 2 * (x / 2).floor else 2 * (x / 2).floor + 1

/-- The comparison property of §9.3: `x ⋚ 2h ⟺ r_o x ⋚ 2h`. -/
theorem ro_lt_iff (x : Rat) (h : Int) : x < 2 * h ↔ ro x < 2 * h := by
  have hfl := Rat.floor_le (x / 2)
  have hlt := Rat.lt_floor_add_one (x / 2); push_cast at hlt
  have hup : ∀ z : Int, z < h → (z : Rat) + 1 ≤ h := fun z hz => by exact_mod_cast hz
  unfold ro; split <;> constructor <;> intro hx
  · have := Rat.floor_lt_iff.mpr (show x / 2 < (h : Rat) by grind); omega
  · have := hup (x / 2).floor (by omega); grind
  · have := Rat.floor_lt_iff.mpr (show x / 2 < (h : Rat) by grind); omega
  · have := hup (x / 2).floor (by omega); grind

theorem ro_eq_iff (x : Rat) (h : Int) : x = 2 * h ↔ ro x = 2 * h := by
  have hfl := Rat.floor_le (x / 2)
  have hlt := Rat.lt_floor_add_one (x / 2); push_cast at hlt
  have hif : x = 2 * h → (x / 2).floor = h := fun hx => floor_eq_of (by grind) (by grind)
  unfold ro; split <;> constructor <;> intro hx
  · have := hif hx; omega
  · have : ((x / 2).floor : Rat) = h := by exact_mod_cast (by omega : (x / 2).floor = h)
    grind
  · rename_i hne; exact absurd (by rw [hif hx]; grind) hne
  · omega

theorem ro_gt_iff (x : Rat) (h : Int) : 2 * h < x ↔ 2 * h < ro x := by
  have := ro_lt_iff x h; have := ro_eq_iff x h
  have := Rat.lt_trichotomy (2 * h) x; have := Int.lt_trichotomy (2 * h) (ro x)
  grind

theorem ro_le_iff (x : Rat) (h : Int) : x ≤ 2 * h ↔ ro x ≤ 2 * h := by
  rw [← Rat.not_lt, ro_gt_iff, Int.not_lt]

theorem ro_ge_iff (x : Rat) (h : Int) : 2 * h ≤ x ↔ 2 * h ≤ ro x := by
  rw [← Rat.not_lt, ro_lt_iff, Int.not_lt]

/-- `r_o x` is `2⌊x/2⌋` or `2⌊x/2⌋ + 1`. -/
theorem ro_eq_or (x : Rat) : ro x = 2 * (x / 2).floor ∨ ro x = 2 * (x / 2).floor + 1 := by
  unfold ro; split <;> simp

/-! ## R18: the tests on `v̄_l`, `v̄`, `v̄_r`

`out = 0` when the endpoints belong to `R_v` (`c` even), `1` otherwise;
then `V_l ⪯_l n ⟺ r_o(4V_l) + out ≤ 4n` and `n ⪯_r V_r ⟺ 4n + out ≤ r_o(4V_r)`. -/

/-- `out`: `0` when `c` is even, `1` when odd. -/
def out (m : Nat) : Int := if m % 2 = 0 then 0 else 1

theorem R18_left (m : Nat) (a : Rat) (n : Int) :
    Exact.leL m a n = decide (ro (4 * a) + out m ≤ 4 * n) := by
  unfold Exact.leL out
  have h1 := ro_le_iff (4 * a) (2 * n)
  have h2 := ro_lt_iff (4 * a) (2 * n)
  by_cases hev : m % 2 = 0
  · rw [if_pos hev, if_pos hev, decide_eq_decide]
    rw [show (4 : Rat) * a ≤ 2 * ((2 * n : Int) : Rat) ↔ a ≤ n by push_cast; grind] at h1
    rw [h1]; push_cast; omega
  · rw [if_neg hev, if_neg hev, decide_eq_decide]
    rw [show (4 : Rat) * a < 2 * ((2 * n : Int) : Rat) ↔ a < n by push_cast; grind] at h2
    rw [h2]; push_cast; omega

theorem R18_right (m : Nat) (n : Int) (a : Rat) :
    Exact.leR m n a = decide (4 * n + out m ≤ ro (4 * a)) := by
  unfold Exact.leR out
  have h1 := ro_ge_iff (4 * a) (2 * n)
  have h2 := ro_gt_iff (4 * a) (2 * n)
  by_cases hev : m % 2 = 0
  · rw [if_pos hev, if_pos hev, decide_eq_decide]
    rw [show 2 * ((2 * n : Int) : Rat) ≤ (4 : Rat) * a ↔ n ≤ a by push_cast; grind] at h1
    rw [h1]; push_cast; omega
  · rw [if_neg hev, if_neg hev, decide_eq_decide]
    rw [show 2 * ((2 * n : Int) : Rat) < (4 : Rat) * a ↔ n < a by push_cast; grind] at h2
    rw [h2]; push_cast; omega

/-- The midpoint test: `2V ⋚ n ⟺ r_o(4V) ⋚ 2n`. -/
theorem R18_mid_lt (x : Rat) (n : Int) : 2 * x < n ↔ ro (4 * x) < 2 * n := by
  rw [← ro_lt_iff]; push_cast; grind

theorem R18_mid_gt (x : Rat) (n : Int) : (n : Rat) < 2 * x ↔ 2 * n < ro (4 * x) := by
  rw [← ro_gt_iff]; push_cast; grind

/-! ## R19: `s = v̄ / 4` -/

/-- `⌊y⌋ / 2 = ⌊y / 2⌋` (R28 for `n = 2`). -/
theorem floor_ediv_two (y : Rat) : y.floor / 2 = (y / 2).floor := by
  have := floor_div_natCast y (n := 2) (by decide); push_cast at this; exact this.symm

theorem R19 (x : Rat) : ro (4 * x) / 4 = x.floor := by
  have h2 : (4 * x / 2 : Rat) = 2 * x := by grind
  rcases ro_eq_or (4 * x) with h | h <;> rw [h, h2]
  · rw [show (2 : Int) * (2 * x).floor / 4 = (2 * x).floor / 2 by omega, floor_ediv_two]
    congr 1; grind
  · rw [show ((2 : Int) * (2 * x).floor + 1) / 4 = (2 * x).floor / 2 by omega, floor_ediv_two]
    congr 1; grind

/-! ## R20 as a hypothesis, R21 -/

/-- The paper's `ε = 2^-64` (Result 20). -/
def eps : Rat := (2 : Rat) ^ (-(64 : Nat) : Int)

/-- `x` is an integer, or at distance at least `ε` from the integers on
    both sides (the shape of Result 20). -/
def Separated (ε x : Rat) : Prop := x = x.floor ∨ (x.floor + ε ≤ x ∧ x ≤ x.floor + 1 - ε)

/-- R21: a good overestimate has the same floor (`ε ≤ 1`). -/
theorem R21 {ε x x' : Rat} (hε1 : ε ≤ 1) (hsep : Separated ε (2 * x)) (hlo : 0 ≤ x' - x)
    (hhi : x' - x < ε / 2) : (2 * x').floor = (2 * x).floor := by
  have hfl := Rat.floor_le (2 * x)
  refine floor_eq_of (by grind) ?_
  rcases hsep with h | ⟨-, h⟩
  · grind
  · grind

/-! ## Definition 9, R22, R23: the modified rounding -/

/-- `r'_o`: as `r_o`, but an `x` within `ε` above an even integer counts as
    that integer. -/
def ro' (ε x : Rat) : Int :=
  if x / 2 - (x / 2).floor < ε then 2 * (x / 2).floor else 2 * (x / 2).floor + 1

/-- R22: on a good overestimate, `r'_o` computes `r_o` of the exact value. -/
theorem R22 {ε x x' : Rat} (hε1 : ε ≤ 1) (hsep : Separated ε (2 * x)) (hlo : 0 ≤ x' - x)
    (hhi : x' - x < ε / 2) : ro' ε (4 * x') = ro (4 * x) := by
  unfold ro' ro
  have h4 : (4 * x' / 2 : Rat) = 2 * x' := by grind
  have h4' : (4 * x / 2 : Rat) = 2 * x := by grind
  rw [h4, h4', R21 hε1 hsep hlo hhi]
  have hfl := Rat.floor_le (2 * x)
  have hlt := Rat.lt_floor_add_one (2 * x)
  rcases hsep with h | ⟨h1, h2⟩
  · -- `2x` is an integer: `2x'` is within `ε` above it
    rw [if_pos (by grind), if_pos h.symm]
  · -- `2x` is at least `ε` above its floor, so is `2x'`; and `2x ≠ ⌊2x⌋`
    rw [if_neg (by grind), if_neg (by grind)]

/-- R23: `r'_o` from `⌊x⌋`, for `2ε ≤ 1`. -/
theorem R23 {ε : Rat} (hε : 2 * ε ≤ 1) (x : Rat) :
    ro' ε x = if x / 2 - (x / 2).floor < ε then x.floor
      else if x.floor % 2 = 0 then x.floor + 1 else x.floor := by
  unfold ro'
  have hfl := Rat.floor_le (x / 2)
  have hlt := Rat.lt_floor_add_one (x / 2)
  have hx : x = 2 * (x / 2) := by grind
  have hx2 : (x.floor / 2) = (x / 2).floor := floor_ediv_two x
  by_cases hc : x / 2 - (x / 2).floor < ε
  · rw [if_pos hc, if_pos hc]
    -- `x < 2⌊x/2⌋ + 2ε ≤ 2⌊x/2⌋ + 1`, so `⌊x⌋ = 2⌊x/2⌋`
    have : x.floor = 2 * (x / 2).floor := floor_eq_of (by push_cast; grind) (by push_cast; grind)
    exact this.symm
  · rw [if_neg hc, if_neg hc]
    split <;> omega

end Srtfp.Schubfach

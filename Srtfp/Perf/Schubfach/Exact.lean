module
/- Schubfach in exact arithmetic (Giulietti, "The Schubfach way to render
   doubles", §8–§9.2): F7 with `M = 1`, over the rationals.

   With `k` from R10 (`10^k ≤ ‖R_v‖ < 10^{k+1}`), the grid `10^k` meets
   `R_v` and the grid `10^{k+1}` meets it at most once, so the shortest
   decimal is one of four candidates: the neighbours `u', w'` of `v` on
   `10^{k+1}`, or the neighbours `u, w` on `10^k`, the nearer one (ties
   to even) when both are in `R_v` (R11). Definition 7 scales
   everything by `10^{-k}`: the tests become comparisons of `V_l`, `V_r`
   with the integers `s = ⌊V⌋` and `t = s + 1` (§9.2).

   `shortest_spec` shows the result denotes the grid scan's first hit
   (`Srtfp/Printer.lean`), which is the specification's shortest
   decimal (`Srtfp/Proofs/Printer/Spec.lean`). -/

public import Srtfp.Correctness
public import Srtfp.Proofs.Decimal
public import Srtfp.Proofs.Decimal.Canonical
public import Srtfp.Perf.Schubfach
public import Srtfp.Perf.Schubfach.R14R15

@[expose] public section

open Srtfp.Compat

open Float.Model.UnpackedFloat (Sign)

namespace Srtfp.Schubfach.Exact

open Srtfp Srtfp.Printer

variable {m : Nat} {q k : Int}

/-! ## Definition 7: `V`, `V_l`, `V_r` -/

/-- `V = v · 10^{-k}`. -/
def V (m : Nat) (q k : Int) : Rat := v m q / (10 : Rat) ^ k

/-- `V_l = v_l · 10^{-k}`. -/
def Vl (m : Nat) (q k : Int) : Rat := vl m q / (10 : Rat) ^ k

/-- `V_r = v_r · 10^{-k}`. -/
def Vr (m : Nat) (q k : Int) : Rat := vr m q / (10 : Rat) ^ k


/-! ## §9.2: the tests

`u ∈ R_v` is `v_l ⪯_l u` since `u ≤ v < v_r` always holds, where `⪯_l`
is `≤` when `v_l ∈ R_v` (`c` even) and `<` otherwise; dividing by
`10^k` makes it `V_l ⪯_l s`. Likewise `w ∈ R_v` is `t ⪯_r V_r`. -/

/-- `a ⪯_l x`. -/
def leL (m : Nat) (a x : Rat) : Bool :=
  if m % 2 = 0 then decide (a ≤ x) else decide (a < x)

/-- `x ⪯_r a`. -/
def leR (m : Nat) (x a : Rat) : Bool :=
  if m % 2 = 0 then decide (x ≤ a) else decide (x < a)

/-- A grid point at or below `v` is in `R_v` iff `v_l ⪯_l` it. -/
theorem InRv_of_le_v {x : Rat} (hx : x ≤ v m q) :
    InRv m q x = (if m % 2 = 0 then decide (vl m q ≤ x) else decide (vl m q < x)) := by
  have := v_lt_vr (m := m) (q := q); unfold InRv
  by_cases hev : m % 2 = 0 <;> simp only [hev, ↓reduceIte, decide_eq_decide] <;> grind

/-- A grid point above `v` is in `R_v` iff it `⪯_r v_r`. -/
theorem InRv_of_v_lt {x : Rat} (hm : 1 ≤ m) (hx : v m q < x) :
    InRv m q x = (if m % 2 = 0 then decide (x ≤ vr m q) else decide (x < vr m q)) := by
  have := vl_lt_v (q := q) hm; unfold InRv
  by_cases hev : m % 2 = 0 <;> simp only [hev, ↓reduceIte, decide_eq_decide] <;> grind

/-- `u ∈ R_v ⟺ V_l ⪯_l s`. -/
theorem u_mem (hm : 1 ≤ m) : leL m (Vl m q k) (s m q k) = InRv m q (u m q k) := by
  rw [InRv_of_le_v (u_le_v hm)]; unfold leL Vl u
  simp only [div_le_iff (ten_zpow_pos k), Rat.div_lt_iff (ten_zpow_pos k)]

/-- `w ∈ R_v ⟺ t ⪯_r V_r`. -/
theorem w_mem (hm : 1 ≤ m) :
    leR m ((s m q k + 1 : Nat) : Rat) (Vr m q k) = InRv m q (w m q k) := by
  rw [InRv_of_v_lt hm (v_lt_w hm),
    show w m q k = ((s m q k + 1 : Nat) : Rat) * (10 : Rat) ^ k by unfold w; push_cast; rfl]
  unfold leR Vr
  simp only [le_div_iff (ten_zpow_pos k), Rat.lt_div_iff (ten_zpow_pos k)]

/-- R4 on the next grid: the scan's `s` there is `s / 10`. -/
theorem s_succ (k : Int) : Printer.s m q (k + 1) = Printer.s m q k / 10 := by
  unfold Printer.s
  have := floor_div_natCast (v m q / (10 : Rat) ^ k) (n := 10) (by decide); push_cast at this
  rw [Rat.zpow_add_one (by decide), div_div, this]
  omega

/-- The neighbours on the next grid, `10^{k+1}`, in terms of `s`: `u' = 10 s'`
    and `w' = 10 t'` on the grid `10^k`, with `s' = s / 10`. -/
theorem u_succ : u m q (k + 1) = ((10 * (s m q k / 10) : Nat) : Rat) * (10 : Rat) ^ k := by
  unfold u; rw [s_succ, Rat.zpow_add_one (by decide)]; push_cast; grind

theorem w_succ : w m q (k + 1) = ((10 * (s m q k / 10 + 1) : Nat) : Rat) * (10 : Rat) ^ k := by
  unfold w; rw [s_succ, Rat.zpow_add_one (by decide)]; push_cast; grind

/-- `u' ∈ R_v ⟺ V_l ⪯_l 10 s'`. -/
theorem u'_mem (hm : 1 ≤ m) :
    leL m (Vl m q k) ((10 * (s m q k / 10) : Nat) : Rat) = InRv m q (u m q (k + 1)) := by
  rw [InRv_of_le_v (u_le_v hm), u_succ]; unfold leL Vl
  simp only [div_le_iff (ten_zpow_pos k), Rat.div_lt_iff (ten_zpow_pos k)]

/-- `w' ∈ R_v ⟺ 10 t' ⪯_r V_r`. -/
theorem w'_mem (hm : 1 ≤ m) :
    leR m ((10 * (s m q k / 10 + 1) : Nat) : Rat) (Vr m q k) = InRv m q (w m q (k + 1)) := by
  rw [InRv_of_v_lt hm (v_lt_w hm), w_succ]; unfold leR Vr
  simp only [le_div_iff (ten_zpow_pos k), Rat.lt_div_iff (ten_zpow_pos k)]

/-- `v − u ⋚ w − v ⟺ 2V ⋚ s + t`. -/
theorem twoV_lt_iff :
    2 * V m q k < (s m q k : Rat) + ((s m q k + 1 : Nat) : Rat)
      ↔ v m q - u m q k < w m q k - v m q := by
  unfold V u w; push_cast
  rw [show (2 : Rat) * (v m q / 10 ^ k) = (2 * v m q) / 10 ^ k by grind, Rat.div_lt_iff (ten_zpow_pos k)]
  constructor <;> intro h <;> grind

theorem twoV_gt_iff :
    (s m q k : Rat) + ((s m q k + 1 : Nat) : Rat) < 2 * V m q k
      ↔ w m q k - v m q < v m q - u m q k := by
  unfold V u w; push_cast
  rw [show (2 : Rat) * (v m q / 10 ^ k) = (2 * v m q) / 10 ^ k by grind, Rat.lt_div_iff (ten_zpow_pos k)]
  constructor <;> intro h <;> grind

/-! ## F7 with `M = 1` -/

/-- The choice on the grid `10^k`: `u` or `w` when exactly one is in `R_v`,
    else the nearer, ties to even (R3 and F1). -/
def pick (m : Nat) (q k : Int) (s : Nat) : Nat :=
  let t := s + 1
  let uIn := leL m (Vl m q k) s
  let wIn := leR m t (Vr m q k)
  if uIn && !wIn then s
  else if !uIn && wIn then t
  else if 2 * V m q k < s + t then s
  else if (s : Rat) + t < 2 * V m q k then t
  else if s % 2 = 0 then s
  else t

/-- Schubfach (F7, `M = 1`): the significand and exponent of the shortest
    decimal of `m · 2^q`, before canonicalisation. -/
def shortest (m : Nat) (q : Int) : Nat × Int :=
  let k := kOfMQ m q
  let s := Printer.s m q k
  if s ≥ 10 then
    let s' := s / 10
    if leL m (Vl m q k) ((10 * s' : Nat) : Rat) then (s', k + 1)
    else if leR m ((10 * (s' + 1) : Nat) : Rat) (Vr m q k) then (s' + 1, k + 1)
    else (pick m q k s, k)
  else (pick m q k s, k)

/-! ## The choice is the scan's candidate -/

/-- On a grid that meets `R_v`, `pick` is what `candidate` returns. -/
theorem candidate_eq_pick (hm : 1 ≤ m)
    (hhit : InRv m q (u m q k) = true ∨ InRv m q (w m q k) = true) :
    candidate m q k = some (pick m q k (s m q k)) := by
  rw [candidate_def]
  unfold pick
  simp only [u_mem hm, w_mem hm]
  cases hU : InRv m q (u m q k) <;> cases hW : InRv m q (w m q k) <;> simp only [hU, hW] at hhit ⊢ <;>
    simp only [Bool.not_true, Bool.not_false, Bool.and_true, Bool.and_false,
      Bool.false_eq_true, if_false, if_true] <;> try rfl
  · exact absurd hhit (by simp)
  · -- both: the nearer, ties to even
    by_cases h1 : v m q - u m q k < w m q k - v m q
    · rw [if_pos (twoV_lt_iff.mpr h1), if_pos (Or.inl h1)]
    · rw [if_neg (fun h => h1 (twoV_lt_iff.mp h))]
      by_cases h2 : w m q k - v m q < v m q - u m q k
      · rw [if_pos (twoV_gt_iff.mpr h2), if_neg (by grind)]
      · rw [if_neg (fun h => h2 (twoV_gt_iff.mp h))]
        have heq : v m q - u m q k = w m q k - v m q := by grind
        by_cases he : s m q k % 2 = 0
        · rw [if_pos he, if_pos (Or.inr ⟨heq, he⟩)]
        · rw [if_neg he, if_neg (by grind)]

/-! ## R10: `10^k ≤ ‖R_v‖ < 10^{k+1}` -/

theorem isIrregular_iff : isIrregular m q = true ↔ (m = 2 ^ 52 ∧ q > -1074) := by
  unfold isIrregular minNormalSignificand minBinaryExp
  simp [Nat.shiftLeft_eq]

/-- R10 for Schubfach's `k` (R14/R15 on the binary64 range). -/
theorem k_spec (h : InRange m q) :
    (10 : Rat) ^ kOfMQ m q ≤ vr m q - vl m q ∧ vr m q - vl m q < (10 : Rat) ^ (kOfMQ m q + 1) := by
  have hq1 := h.2.2.1
  have hq2 := h.2.2.2.1
  rw [width_eq]
  unfold kOfMQ
  by_cases hirr : isIrregular m q = true
  · rw [if_pos hirr, if_pos (isIrregular_iff.mp hirr)]
    have hR := R14HoldsAt_in_binary64_range q hq1 hq2
    dsimp only [R14HoldsAt] at hR
    have e1 := le_of_ratio hR.1
    have e2 := lt_of_ratio hR.2
    push_cast at e1 e2
    constructor <;> grind
  · rw [if_neg hirr, if_neg (fun h => hirr (isIrregular_iff.mpr h))]
    have hR := R15HoldsAt_in_binary64_range q hq1 hq2
    dsimp only [R15HoldsAt] at hR
    have e1 := le_of_ratio (a := 1) (c := 1) (by rw [Nat.one_mul, Nat.one_mul]; exact hR.1)
    have e2 := lt_of_ratio (a := 1) (c := 1) (by rw [Nat.one_mul, Nat.one_mul]; exact hR.2)
    push_cast at e1 e2
    constructor <;> grind

/-! ## R8, R9: grids around `k` -/

/-- R8: two grid points of `R_v` on a grid coarser than `‖R_v‖` coincide. -/
theorem eq_of_onGrid_coarse {j : Int} (hj : vr m q - vl m q < (10 : Rat) ^ j) {x y : Rat}
    (hx : OnGrid j x) (hxR : InRv m q x = true) (hy : OnGrid j y) (hyR : InRv m q y = true) : x = y := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  obtain ⟨hxl, hxr⟩ := le_of_InRv hxR
  obtain ⟨hyl, hyr⟩ := le_of_InRv hyR
  have h10 := ten_zpow_pos j
  rcases Nat.lt_trichotomy a b with hab | hab | hab
  · exfalso
    have : ((a : Rat) + 1) * (10 : Rat) ^ j ≤ b * (10 : Rat) ^ j :=
      Rat.mul_le_mul_of_nonneg_right (by exact_mod_cast hab) (Rat.le_of_lt h10)
    grind
  · rw [hab]
  · exfalso
    have : ((b : Rat) + 1) * (10 : Rat) ^ j ≤ a * (10 : Rat) ^ j :=
      Rat.mul_le_mul_of_nonneg_right (by exact_mod_cast hab) (Rat.le_of_lt h10)
    grind

/-- R9: a grid no finer than `‖R_v‖` meets `R_v`. -/
theorem hit_of_le_width {j : Int} (hm : 1 ≤ m) (hj : (10 : Rat) ^ j ≤ vr m q - vl m q) :
    ∃ x, OnGrid j x ∧ InRv m q x = true := by
  have h10 := ten_zpow_pos j
  have hvl := vl_pos (q := q) hm
  -- the first grid point above `vl`: `c + 1` with `c = ⌊vl / 10^j⌋`
  have hfl := (le_div_iff h10).mp (Rat.floor_le (vl m q / (10 : Rat) ^ j))
  have hlt := (Rat.div_lt_iff h10).mp (Rat.lt_floor_add_one (vl m q / (10 : Rat) ^ j))
  obtain ⟨c, hc⟩ : ∃ c : Nat, ((vl m q / (10 : Rat) ^ j).floor : Rat) = c :=
    ⟨_, by rw [← Rat.intCast_natCast, Int.toNat_of_nonneg (floor_nonneg (Rat.le_of_lt (div_pos hvl h10)))]⟩
  push_cast at hlt
  rw [hc] at hfl hlt
  refine ⟨((c + 1 : Nat) : Rat) * (10 : Rat) ^ j, ⟨c + 1, rfl⟩, ?_⟩
  push_cast
  -- `vl < x ≤ vl + 10^j ≤ vr`
  have hlo : vl m q < ((c : Rat) + 1) * (10 : Rat) ^ j := hlt
  have hhi : ((c : Rat) + 1) * (10 : Rat) ^ j ≤ vr m q := by grind
  unfold InRv
  by_cases hev : m % 2 = 0
  · rw [if_pos hev]; simp only [decide_eq_true_eq]; exact ⟨Rat.le_of_lt hlo, hhi⟩
  · rw [if_neg hev]; simp only [decide_eq_true_eq]
    refine ⟨hlo, Rat.lt_of_le_of_ne hhi fun heq => ?_⟩
    -- the endpoint case: `‖R_v‖ = 10^j` and `vl` on the grid, impossible for odd `m`
    have hw : vr m q - vl m q = (10 : Rat) ^ j := by grind
    have hvl' : vl m q = (c : Rat) * (10 : Rat) ^ j := by grind
    have hreg : ¬ (m = 2 ^ 52 ∧ q > -1074) := fun h => hev (by rw [h.1])
    rw [width_eq, if_neg hreg, Rat.one_mul] at hw
    unfold vl at hvl'
    rw [if_neg hreg, ← hw] at hvl'
    have hp := two_zpow_pos q
    have : ((m : Rat) - 1/2) = c := (mul_left_inj' (Rat.ne_of_gt hp)).mp hvl'
    have : (2 * m : Rat) = 2 * c + 1 := by grind
    have : 2 * m = 2 * c + 1 := by exact_mod_cast this
    omega

/-! ## F7 is the scan -/

/-- Schubfach's `(s, k)` denotes the scan's first hit. -/
theorem shortest_spec (h : InRange m q) :
    1 ≤ (shortest m q).1
    ∧ ((shortest m q).1 : Rat) * (10 : Rat) ^ (shortest m q).2
        = ((Printer.shortest m q).1 : Rat) * (10 : Rat) ^ (Printer.shortest m q).2 := by
  have hm := h.1
  rcases ho : Printer.shortest m q with ⟨n, i⟩
  obtain ⟨hn, -, -, hc, hnone⟩ := scan_spec h ho
  obtain ⟨-, -, hmemn, -, -⟩ := candidate_some hm hc
  obtain ⟨hk1, hk2⟩ := k_spec h
  generalize hk : kOfMQ m q = k at hk1 hk2
  have hhitk : ∃ x, OnGrid k x ∧ InRv m q x = true := hit_of_le_width hm hk1
  have hck : candidate m q k ≠ none := fun hno => (candidate_none_iff hm).mp hno hhitk
  have hik : k ≤ i := Int.not_lt.mp fun hlt => hck (hnone k hlt)
  -- with a hit on `10^k`, `pick` is the scan's candidate
  have hpick : candidate m q k = some (pick m q k (Printer.s m q k)) :=
    candidate_eq_pick hm ((hit_iff_neighbour hm).mp hhitk)
  -- no hit on any grid above `k` forces `i = k` and `n` the pick
  have finish (hnohit : ∀ j, k < j → candidate m q j = none) :
      n = pick m q k (Printer.s m q k) ∧ i = k := by
    obtain rfl : i = k :=
      Int.le_antisymm (Int.not_lt.mp fun hlt => by rw [hnohit i hlt] at hc; cases hc) hik
    rw [hpick] at hc
    exact ⟨(Option.some.inj hc).symm, rfl⟩
  unfold shortest
  simp only [hk, u'_mem hm, w'_mem hm]
  by_cases h10 : Printer.s m q k ≥ 10
  · rw [if_pos h10]
    have hs1 : 1 ≤ Printer.s m q (k + 1) := by rw [s_succ]; omega
    have hu' : (Printer.s m q k / 10 : Nat) = Printer.s m q (k + 1) := (s_succ k).symm
    -- a hit on `10^(k+1)` is unique, and above it the scan can hit nothing else
    have hval_of_hit (x : Rat) (hx : OnGrid (k + 1) x) (hxR : InRv m q x = true) :
        (n : Rat) * (10 : Rat) ^ i = x := by
      have hlt : k + 1 ≤ i := Int.not_lt.mp fun hlt =>
        (candidate_none_iff hm).mp (hnone (k + 1) (by omega)) ⟨x, hx, hxR⟩
      exact eq_of_onGrid_coarse hk2 (onGrid_of_le hlt ⟨n, rfl⟩) hmemn hx hxR
    cases hU : InRv m q (u m q (k + 1)) <;> cases hW : InRv m q (w m q (k + 1)) <;>
      simp only [Bool.false_eq_true, if_false, if_true]
    · -- neither: no hit on `10^(k+1)`, hence none above `k`
      obtain ⟨rfl, rfl⟩ := finish fun j hj => by
        rw [candidate_none_iff hm]
        rintro ⟨x, hx, hxR⟩
        rcases (hit_iff_neighbour (i := k + 1) hm).mp ⟨x, onGrid_of_le (i := k + 1) (by omega) hx, hxR⟩
          with h1 | h1
        · rw [hU] at h1; cases h1
        · rw [hW] at h1; cases h1
      exact ⟨hn, rfl⟩
    · exact ⟨by omega, by rw [hval_of_hit _ onGrid_w hW]; unfold w; rw [hu']; push_cast; rfl⟩
    · exact ⟨by omega, by rw [hval_of_hit _ onGrid_u hU]; unfold u; rw [hu']⟩
    · exfalso
      have := eq_of_onGrid_coarse hk2 onGrid_u hU onGrid_w hW
      unfold u w at this
      have h10 := ten_zpow_pos (k + 1)
      grind
  · rw [if_neg h10]
    -- Schubfach picks on `10^k`. So does the scan, unless `10^(k+1) ∈ R_v`:
    -- then the scan says `1 · 10^(k+1)`, and Schubfach `10 · 10^k`.
    have hs0 : Printer.s m q (k + 1) = 0 := by rw [s_succ]; omega
    have hv10 : v m q < (10 : Rat) ^ (k + 1) :=
      Rat.not_le.mp fun hle => by have := s_pos_iff.mpr hle; omega
    have hu0 : u m q (k + 1) = 0 := by unfold u; rw [hs0]; simp
    have hw1 : w m q (k + 1) = (10 : Rat) ^ (k + 1) := by unfold w; rw [hs0]; grind
    have hvl := vl_pos (q := q) hm
    have hU0 : InRv m q (u m q (k + 1)) = false := by
      rw [hu0]; exact Bool.eq_false_iff.mpr fun hx => by have := (le_of_InRv hx).1; grind
    have hT := ten_zpow_pos (k + 1)
    -- nothing of `R_v` on any grid above `k + 1`
    have hnone_above : ∀ j, k + 1 < j → candidate m q j = none := by
      intro j hj
      rw [candidate_none_iff hm]
      rintro ⟨x, ⟨c, rfl⟩, hxR⟩
      obtain ⟨hl, hr⟩ := le_of_InRv hxR
      have hc : 1 ≤ c := Nat.pos_of_ne_zero fun h0 => by subst h0; simp at hl; grind
      have h1 : (10 : Rat) ^ (k + 2) ≤ (10 : Rat) ^ j := zpow_le_zpow_right₀ (by decide) (by omega)
      have h2 : (10 : Rat) ^ (k + 2) = 10 ^ (k + 1) * 10 := by
        rw [show k + 2 = (k + 1) + 1 by omega, Rat.zpow_add_one (by decide)]
      have h3 : (1 : Rat) * 10 ^ j ≤ (c : Rat) * 10 ^ j :=
        Rat.mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (Rat.le_of_lt (ten_zpow_pos j))
      have hvlv := vl_lt_v (q := q) hm
      grind
    by_cases hW : InRv m q ((10 : Rat) ^ (k + 1)) = true
    · -- the scan hits at `k + 1` with `1`
      have hc1 : candidate m q (k + 1) = some 1 := by
        rw [candidate_def, hU0, hw1, hW, hs0]
      obtain rfl : i = k + 1 := Int.le_antisymm
        (Int.not_lt.mp fun h => by rw [hnone_above i h] at hc; cases hc)
        (Int.not_lt.mp fun h => by rw [hnone (k + 1) h] at hc1; cases hc1)
      rw [hc1] at hc
      obtain rfl := Option.some.inj hc
      -- `v` is above `9 · 10^k`: if `9 · 10^k ∈ R_v` by T3, else by convexity
      have h10k := ten_zpow_pos k
      have hTi : (10 : Rat) ^ (k + 1) = 10 ^ k * 10 := Rat.zpow_add_one (by decide) k
      have hT3 : 9 * (10 : Rat) ^ k < v m q ∧
          (InRv m q (9 * (10 : Rat) ^ k) = true → (10 : Rat) ^ (k + 1) - v m q < v m q - 9 * 10 ^ k) := by
        have key (h9R : InRv m q (9 * (10 : Rat) ^ k) = true) :
            (10 : Rat) ^ (k + 1) - v m q < v m q - 9 * 10 ^ k := by
          have := ten_pow_closer h hW (by rw [show k + 1 - 1 = k by omega]; exact h9R)
          rwa [show k + 1 - 1 = k by omega] at this
        refine ⟨?_, key⟩
        rcases lt_or_ge (9 * (10 : Rat) ^ k) (v m q) with hlt | hge
        · exact hlt
        · have h9R : InRv m q (9 * (10 : Rat) ^ k) = true :=
            InRv_convex (InRv_v hm) hW hge (by rw [hTi]; grind)
          have := key h9R
          rw [hTi] at this
          grind
      -- so `s = 9`, and the pick is `10`
      have hs9 : Printer.s m q k = 9 := by
        have hfl : (9 : Int) ≤ (v m q / (10 : Rat) ^ k).floor :=
          Rat.le_floor_iff.mpr (by rw [le_div_iff h10k]; push_cast; exact Rat.le_of_lt hT3.1)
        have hsc : ((Printer.s m q k : Nat) : Int) = (v m q / (10 : Rat) ^ k).floor := by
          exact_mod_cast s_cast (q := q) (i := k) hm
        omega
      obtain ⟨-, hcase, hmemp, hclose, -⟩ := candidate_some hm hpick
      have hp10 : pick m q k (Printer.s m q k) = 10 := by
        rcases hcase with e | e
        · exfalso
          rw [e, hs9] at hmemp hclose
          have h1 := hclose _ ⟨10, rfl⟩ (by rw [hTi] at hW; push_cast; rw [Rat.mul_comm]; exact hW)
          have h2 := hT3.2 (by push_cast at hmemp; exact hmemp)
          push_cast at h1
          rw [hTi] at h2
          rw [Rat.abs_of_nonneg (by grind), Rat.abs_of_nonpos (by grind)] at h1
          grind
        · omega
      rw [hp10]
      refine ⟨by omega, ?_⟩
      push_cast
      rw [hTi]; grind
    · -- `10^(k+1) ∉ R_v`: nothing above `k`, so the scan's hit is Schubfach's pick
      obtain ⟨rfl, rfl⟩ := finish fun j hj => by
        rcases Int.lt_or_eq_of_le (show k + 1 ≤ j by omega) with hlt | heq
        · exact hnone_above j hlt
        · subst heq
          rw [candidate_none_iff hm]
          rintro ⟨x, hx, hxR⟩
          rcases (hit_iff_neighbour hm).mp ⟨x, hx, hxR⟩ with h1 | h1
          · rw [hU0] at h1; cases h1
          · rw [hw1] at h1; exact hW h1
      exact ⟨hn, rfl⟩

end Srtfp.Schubfach.Exact

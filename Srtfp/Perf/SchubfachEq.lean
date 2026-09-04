module
/- Kernel 0 of the Perf chain: the Nat-form Schubfach printer equals the
   reference (Giulietti, "The Schubfach way to render doubles", §8–9).
   Schubfach computes `k` with `10^k ≤ |R_v| < 10^(k+1)` (R10, via the
   magic constants of R14/R15 in `Srtfp/Perf/Schubfach/R14R15.lean`),
   tries the coarser grid `10^(k+1)` first, and otherwise picks on `10^k`.
   Every grid above `10^(k+1)` is coarser than `R_v`, so that is exactly
   the scan's first hit, and the two decimals canonicalise alike. -/
public import Srtfp.Correctness
public import Srtfp.Proofs.Decimal
public import Srtfp.Proofs.Decimal.Canonical
public import Srtfp.Perf.Schubfach
public import Srtfp.Perf.Schubfach.R14R15
public import Srtfp.Perf.Unpack

@[expose] public section

open Srtfp.Compat

namespace Srtfp.Schubfach

open Srtfp Srtfp.Float Srtfp.Printer

variable {m : Nat} {q : Int}

/-! ## Clearing denominators -/

/-- `2^{max(-q,0)} · 10^{max(-k,0)}`, the factor that clears both denominators. -/
def clear (q k : Int) : Rat :=
  (2 : Rat) ^ (if q < 0 then (-q).toNat else 0) * (10 : Rat) ^ (if k < 0 then (-k).toNat else 0)

theorem clear_pos (q k : Int) : 0 < clear q k :=
  Rat.mul_pos (Rat.pow_pos (by decide)) (Rat.pow_pos (by decide))

theorem lhs_eq (a q k : Int) :
    ((a * 2 ^ (if q ≥ 0 then q.toNat else 0) * 10 ^ (if k < 0 then (-k).toNat else 0) : Int) : Rat)
      = (a : Rat) * (2 : Rat) ^ q * clear q k := by
  unfold clear
  push_cast
  rw [← zpow_two_split q]
  grind

theorem rhs_eq (b q k : Int) :
    ((b * 10 ^ (if k ≥ 0 then k.toNat else 0) * 2 ^ (if q < 0 then (-q).toNat else 0) : Int) : Rat)
      = (b : Rat) * (10 : Rat) ^ k * clear q k := by
  unfold clear
  push_cast
  rw [← zpow_ten_split k]
  grind

/-- `cmpScaledMixed a q b k` compares `a · 2^q` with `b · 10^k`. -/
theorem cmpScaledMixed_spec (a q b k : Int) :
    (cmpScaledMixed a q b k < 0 ↔ (a : Rat) * (2 : Rat) ^ q < (b : Rat) * (10 : Rat) ^ k)
    ∧ (cmpScaledMixed a q b k = 0 ↔ (a : Rat) * (2 : Rat) ^ q = (b : Rat) * (10 : Rat) ^ k)
    ∧ (0 < cmpScaledMixed a q b k ↔ (b : Rat) * (10 : Rat) ^ k < (a : Rat) * (2 : Rat) ^ q) := by
  unfold cmpScaledMixed
  simp only
  have hc := clear_pos q k
  have hlt : (a * 2 ^ (if q ≥ 0 then q.toNat else 0) * 10 ^ (if k < 0 then (-k).toNat else 0) : Int)
      < b * 10 ^ (if k ≥ 0 then k.toNat else 0) * 2 ^ (if q < 0 then (-q).toNat else 0)
      ↔ (a : Rat) * (2 : Rat) ^ q < (b : Rat) * (10 : Rat) ^ k := by
    rw [← Rat.intCast_lt_intCast, lhs_eq, rhs_eq, Rat.mul_lt_mul_right hc]
  have heq : (a * 2 ^ (if q ≥ 0 then q.toNat else 0) * 10 ^ (if k < 0 then (-k).toNat else 0) : Int)
      = b * 10 ^ (if k ≥ 0 then k.toNat else 0) * 2 ^ (if q < 0 then (-q).toNat else 0)
      ↔ (a : Rat) * (2 : Rat) ^ q = (b : Rat) * (10 : Rat) ^ k := by
    rw [← Rat.intCast_inj, lhs_eq, rhs_eq, mul_left_inj' (Rat.ne_of_gt hc)]
  generalize (a * 2 ^ (if q ≥ 0 then q.toNat else 0) * 10 ^ (if k < 0 then (-k).toNat else 0) : Int) = L
    at hlt heq ⊢
  generalize (b * 10 ^ (if k ≥ 0 then k.toNat else 0) * 2 ^ (if q < 0 then (-q).toNat else 0) : Int) = R
    at hlt heq ⊢
  generalize (a : Rat) * (2 : Rat) ^ q = A at hlt heq ⊢
  generalize (b : Rat) * (10 : Rat) ^ k = B at hlt heq ⊢
  by_cases h1 : L < R
  · rw [if_pos h1]; refine ⟨by simp [hlt.mp h1], by simp; grind, by simp; grind⟩
  · rw [if_neg h1]
    by_cases h2 : L = R
    · rw [if_pos h2]; refine ⟨by simp; grind, by simp [heq.mp h2], by simp; grind⟩
    · rw [if_neg h2]
      have h3 : R < L := by omega
      refine ⟨by simp; grind, by simp; grind, by simp; grind⟩

/-! ## The membership test is `InRv` -/

theorem isIrregular_iff : isIrregular m q = true ↔ (m = 2 ^ 52 ∧ q > -1074) := by
  unfold isIrregular minNormalSignificand minBinaryExp
  simp [Nat.shiftLeft_eq]

theorem inRoundingInterval_iff (s : Nat) (k : Int) :
    inRoundingInterval s k m q (isIrregular m q) = true
      ↔ InRv m q ((s : Rat) * (10 : Rat) ^ k) = true := by
  unfold inRoundingInterval InRv vl vr
  simp only
  have hp := two_zpow_pos q
  have ht := ten_zpow_pos k
  obtain ⟨hL1, hL2, hL3⟩ := cmpScaledMixed_spec (if isIrregular m q then 4 * (m : Int) - 1 else 4 * m - 2) q
    (4 * s) k
  obtain ⟨hR1, hR2, hR3⟩ := cmpScaledMixed_spec (4 * (m : Int) + 2) q (4 * s) k
  by_cases hirr : isIrregular m q = true
  · rw [if_pos hirr, if_pos (isIrregular_iff.mp hirr)]
    rw [if_pos hirr] at hL1 hL2 hL3
    push_cast at hL1 hL2 hL3 hR1 hR2 hR3
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, hL1, hL2, hR2, hR3]
    generalize (2 : Rat) ^ q = p at *
    generalize (10 : Rat) ^ k = t at *
    split <;> grind
  · rw [if_neg hirr, if_neg (fun h => hirr (isIrregular_iff.mpr h))]
    rw [if_neg hirr] at hL1 hL2 hL3
    push_cast at hL1 hL2 hL3 hR1 hR2 hR3
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, hL1, hL2, hR2, hR3]
    generalize (2 : Rat) ^ q = p at *
    generalize (10 : Rat) ^ k = t at *
    split <;> grind

/-! ## `shiftedSig` is the scan's floor -/

/-- Integer division is the floor of the rational quotient. -/
theorem floor_natDiv (N D : Nat) (hD : 0 < D) : ((N : Rat) / D).floor = (N / D : Nat) := by
  have hDq : (0 : Rat) < D := by exact_mod_cast hD
  have h1 : ((N / D : Nat) : Rat) ≤ (N : Rat) / D := by
    rw [Reader.le_div_iff hDq]; exact_mod_cast Nat.div_mul_le_self N D
  have h2 : (N : Rat) / D < (N / D : Nat) + 1 := by
    rw [Rat.div_lt_iff hDq]
    have hdm := Nat.div_add_mod N D
    have hmod := Nat.mod_lt N hD
    have : N < (N / D + 1) * D :=
      calc N = D * (N / D) + N % D := hdm.symm
        _ < D * (N / D) + D := Nat.add_lt_add_left hmod _
        _ = (N / D + 1) * D := by rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]
    exact_mod_cast this
  have h3 : ((N / D : Nat) : Int) ≤ ((N : Rat) / D).floor := Rat.le_floor_iff.mpr h1
  have h4 : ((N : Rat) / D).floor < ((N / D : Nat) : Int) + 1 :=
    Rat.floor_lt_iff.mpr (by push_cast; exact h2)
  omega

theorem shiftedSig_eq (m : Nat) (q k : Int) : shiftedSig m q k = Printer.s m q k := by
  unfold shiftedSig Printer.s v
  simp only
  have hD : 0 < 2 ^ (if q < 0 then (-q).toNat else 0) * 10 ^ (if k ≥ 0 then k.toNat else 0) :=
    Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos (by decide))
  have hDq : (0 : Rat) < ((2 ^ (if q < 0 then (-q).toNat else 0)
      * 10 ^ (if k ≥ 0 then k.toNat else 0) : Nat) : Rat) := by exact_mod_cast hD
  have ht := ten_zpow_pos k
  have hy := Rat.div_mul_cancel (a := (m : Rat) * 2 ^ q) (Rat.ne_of_gt ht)
  have hq : ((m * 2 ^ (if q ≥ 0 then q.toNat else 0) * 10 ^ (if k < 0 then (-k).toNat else 0) : Nat) : Rat)
      / ((2 ^ (if q < 0 then (-q).toNat else 0) * 10 ^ (if k ≥ 0 then k.toNat else 0) : Nat) : Rat)
      = (m : Rat) * 2 ^ q / 10 ^ k := by
    rw [Reader.div_eq_iff hDq]
    push_cast
    rw [← zpow_two_split q, ← zpow_ten_split k]
    generalize (m : Rat) * 2 ^ q / 10 ^ k = y at hy ⊢
    generalize (2 : Rat) ^ (if q < 0 then (-q).toNat else 0) = A
    generalize (10 : Rat) ^ (if k < 0 then (-k).toNat else 0) = B
    grind
  rw [← hq, floor_natDiv _ _ hD, Int.toNat_natCast]

/-! ## R10: `10^k ≤ |R_v| < 10^(k+1)` -/

/-- `b^e` as the ratio of the two `Nat` powers `R14HoldsAt`/`R15HoldsAt` use. -/
theorem zpow_ratio (b : Nat) (hb : 0 < b) (e : Int) :
    (b : Rat) ^ e * ((if e ≥ 0 then 1 else b ^ e.natAbs : Nat) : Rat)
      = ((if e ≥ 0 then b ^ e.natAbs else 1 : Nat) : Rat) := by
  have hbq : (b : Rat) ≠ 0 := by have : (0 : Rat) < b := by exact_mod_cast hb
                                 grind
  by_cases he : e ≥ 0
  · rw [if_pos he, if_pos he]
    have h1 : ((e.natAbs : Nat) : Int) = e := Int.natAbs_of_nonneg he
    push_cast
    rw [Rat.mul_one, ← Rat.zpow_natCast, h1]
  · rw [if_neg he, if_neg he]
    have h1 : ((e.natAbs : Nat) : Int) = -e := Int.ofNat_natAbs_of_nonpos (by omega)
    push_cast
    rw [← Rat.zpow_natCast, h1, ← Rat.zpow_add hbq, show e + -e = 0 by omega, Rat.zpow_zero]

theorem denom_pos (b : Nat) (hb : 0 < b) (e : Int) :
    (0 : Rat) < ((if e ≥ 0 then 1 else b ^ e.natAbs : Nat) : Rat) := by
  have : 0 < (if e ≥ 0 then 1 else b ^ e.natAbs : Nat) := by
    split
    · decide
    · exact Nat.pow_pos hb
  exact_mod_cast this

/-- R10 for Schubfach's `k`: `10^k ≤ |R_v| < 10^(k+1)`. -/
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
    obtain ⟨h1, h2⟩ := hR
    generalize hk : floorLog10ThreeQuartersPow2 q = k at h1 h2 ⊢
    have r2 := zpow_ratio 2 (by decide) q
    have r10 := zpow_ratio 10 (by decide) k
    have r10' := zpow_ratio 10 (by decide) (k + 1)
    have d2 := denom_pos 2 (by decide) q
    have d10 := denom_pos 10 (by decide) k
    have d10' := denom_pos 10 (by decide) (k + 1)
    have h1' : ((4 * (if k ≥ 0 then 10 ^ k.natAbs else 1) * (if q ≥ 0 then 1 else 2 ^ q.natAbs) : Nat) : Rat)
        ≤ ((3 * (if q ≥ 0 then 2 ^ q.natAbs else 1) * (if k ≥ 0 then 1 else 10 ^ k.natAbs) : Nat) : Rat) := by
      exact_mod_cast h1
    have h2' : ((3 * (if q ≥ 0 then 2 ^ q.natAbs else 1) * (if k + 1 ≥ 0 then 1 else 10 ^ (k + 1).natAbs) : Nat) : Rat)
        < ((4 * (if k + 1 ≥ 0 then 10 ^ (k + 1).natAbs else 1) * (if q ≥ 0 then 1 else 2 ^ q.natAbs) : Nat) : Rat) := by
      exact_mod_cast h2
    push_cast at h1' h2'
    rw [← r2, ← r10] at h1'
    rw [← r2, ← r10'] at h2'
    generalize ((if q ≥ 0 then 1 else 2 ^ q.natAbs : Nat) : Rat) = D2 at *
    generalize ((if k ≥ 0 then 1 else 10 ^ k.natAbs : Nat) : Rat) = D10 at *
    generalize ((if k + 1 ≥ 0 then 1 else 10 ^ (k + 1).natAbs : Nat) : Rat) = D10' at *
    have hp := two_zpow_pos q
    constructor
    · exact Rat.le_of_mul_le_mul_right (c := 4 * D2 * D10) (by grind) (by grind)
    · exact Rat.lt_of_mul_lt_mul_right (c := 4 * D2 * D10') (by grind) (by grind)
  · rw [if_neg hirr, if_neg (fun h => hirr (isIrregular_iff.mpr h))]
    have hR := R15HoldsAt_in_binary64_range q hq1 hq2
    dsimp only [R15HoldsAt] at hR
    obtain ⟨h1, h2⟩ := hR
    generalize hk : floorLog10Pow2 q = k at h1 h2 ⊢
    have r2 := zpow_ratio 2 (by decide) q
    have r10 := zpow_ratio 10 (by decide) k
    have r10' := zpow_ratio 10 (by decide) (k + 1)
    have d2 := denom_pos 2 (by decide) q
    have d10 := denom_pos 10 (by decide) k
    have d10' := denom_pos 10 (by decide) (k + 1)
    have h1' : (((if k ≥ 0 then 10 ^ k.natAbs else 1) * (if q ≥ 0 then 1 else 2 ^ q.natAbs) : Nat) : Rat)
        ≤ (((if q ≥ 0 then 2 ^ q.natAbs else 1) * (if k ≥ 0 then 1 else 10 ^ k.natAbs) : Nat) : Rat) := by
      exact_mod_cast h1
    have h2' : (((if q ≥ 0 then 2 ^ q.natAbs else 1) * (if k + 1 ≥ 0 then 1 else 10 ^ (k + 1).natAbs) : Nat) : Rat)
        < (((if k + 1 ≥ 0 then 10 ^ (k + 1).natAbs else 1) * (if q ≥ 0 then 1 else 2 ^ q.natAbs) : Nat) : Rat) := by
      exact_mod_cast h2
    push_cast at h1' h2'
    rw [← r2, ← r10] at h1'
    rw [← r2, ← r10'] at h2'
    generalize ((if q ≥ 0 then 1 else 2 ^ q.natAbs : Nat) : Rat) = D2 at *
    generalize ((if k ≥ 0 then 1 else 10 ^ k.natAbs : Nat) : Rat) = D10 at *
    generalize ((if k + 1 ≥ 0 then 1 else 10 ^ (k + 1).natAbs : Nat) : Rat) = D10' at *
    have hp := two_zpow_pos q
    rw [Rat.one_mul]
    constructor
    · exact Rat.le_of_mul_le_mul_right (c := D2 * D10) (by grind) (by grind)
    · exact Rat.lt_of_mul_lt_mul_right (c := D2 * D10') (by grind) (by grind)

/-! ## Grids around `k` -/

/-- The scan's `s` on the next grid. -/
theorem s_succ (hm : 1 ≤ m) (k : Int) : Printer.s m q (k + 1) = Printer.s m q k / 10 := by
  have h10 := ten_zpow_pos k
  have hx : v m q / (10 : Rat) ^ (k + 1) = v m q / (10 : Rat) ^ k / 10 := by
    rw [Rat.zpow_add_one (by decide), Reader.div_eq_iff (Rat.mul_pos h10 (by decide)),
      Rat.mul_comm ((10 : Rat) ^ k), ← Rat.mul_assoc, Rat.div_mul_cancel (by grind),
      Rat.div_mul_cancel (Rat.ne_of_gt h10)]
  have hcast := s_cast (q := q) (i := k) hm
  have hfl := Rat.floor_le (v m q / (10 : Rat) ^ k)
  have hlt := Rat.lt_floor_add_one (v m q / (10 : Rat) ^ k)
  push_cast at hlt
  rw [← hcast] at hfl hlt
  generalize Printer.s m q k = n at hfl hlt ⊢
  generalize v m q / (10 : Rat) ^ k = x at hx hfl hlt
  unfold Printer.s
  rw [hx]
  have hdm := Nat.div_add_mod n 10
  have hmod := Nat.mod_lt n (by decide : 0 < 10)
  have h1 : ((n / 10 : Nat) : Rat) ≤ x / 10 := by
    rw [Reader.le_div_iff (by decide)]
    have : ((n / 10 : Nat) : Rat) * 10 ≤ n := by exact_mod_cast (Nat.div_mul_le_self n 10)
    grind
  have h2 : x / 10 < ((n / 10 : Nat) : Rat) + 1 := by
    rw [Rat.div_lt_iff (by decide)]
    have : (n : Rat) + 1 ≤ ((n / 10 : Nat) : Rat) * 10 + 10 := by
      have : n + 1 ≤ n / 10 * 10 + 10 := by omega
      exact_mod_cast this
    grind
  have h3 : ((n / 10 : Nat) : Int) ≤ (x / 10).floor := Rat.le_floor_iff.mpr h1
  have h4 : (x / 10).floor < ((n / 10 : Nat) : Int) + 1 := Rat.floor_lt_iff.mpr (by push_cast; exact h2)
  have : (x / 10).floor = ((n / 10 : Nat) : Int) := by omega
  rw [this, Int.toNat_natCast]

/-- Two grid points of `R_v` on a grid coarser than `|R_v|` coincide. -/
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
      Rat.mul_le_mul_of_nonneg_right (by exact_mod_cast hab) (le_of_lt h10)
    grind
  · rw [hab]
  · exfalso
    have : ((b : Rat) + 1) * (10 : Rat) ^ j ≤ a * (10 : Rat) ^ j :=
      Rat.mul_le_mul_of_nonneg_right (by exact_mod_cast hab) (le_of_lt h10)
    grind

/-- R11: a grid no finer than `|R_v|` meets `R_v`. -/
theorem hit_of_le_width {j : Int} (hm : 1 ≤ m) (hj : (10 : Rat) ^ j ≤ vr m q - vl m q) :
    ∃ x, OnGrid j x ∧ InRv m q x = true := by
  have h10 := ten_zpow_pos j
  have hvl := vl_pos (q := q) hm
  -- the first grid point above `vl`
  have hfl := Rat.floor_le (vl m q / (10 : Rat) ^ j)
  have hlt := Rat.lt_floor_add_one (vl m q / (10 : Rat) ^ j)
  have hfl0 : 0 ≤ (vl m q / (10 : Rat) ^ j).floor := by
    rcases Int.lt_or_le (vl m q / (10 : Rat) ^ j).floor 0 with hneg | hnn
    · exfalso
      have := Rat.floor_lt_iff.mp hneg
      have : 0 < vl m q / (10 : Rat) ^ j := (Rat.lt_div_iff h10).mpr (by rw [Rat.zero_mul]; exact hvl)
      simp at *; grind
    · exact hnn
  obtain ⟨c, hc⟩ : ∃ c : Nat, ((vl m q / (10 : Rat) ^ j).floor : Rat) = c :=
    ⟨_, by rw [← Rat.intCast_natCast, Int.toNat_of_nonneg hfl0]⟩
  push_cast at hlt
  rw [hc] at hfl hlt
  have hfl' := Rat.mul_le_mul_of_nonneg_right hfl (le_of_lt h10)
  have hlt' := Rat.mul_lt_mul_of_pos_right hlt h10
  rw [Rat.div_mul_cancel (Rat.ne_of_gt h10)] at hfl' hlt'
  refine ⟨((c + 1 : Nat) : Rat) * (10 : Rat) ^ j, ⟨c + 1, rfl⟩, ?_⟩
  push_cast
  -- `vl < x ≤ vl + 10^j ≤ vr`
  have hlo : vl m q < ((c : Rat) + 1) * (10 : Rat) ^ j := hlt'
  have hhi : ((c : Rat) + 1) * (10 : Rat) ^ j ≤ vr m q := by grind
  unfold InRv
  by_cases hev : m % 2 = 0
  · rw [if_pos hev]; simp only [decide_eq_true_eq]; exact ⟨le_of_lt hlo, hhi⟩
  · rw [if_neg hev]; simp only [decide_eq_true_eq]
    refine ⟨hlo, lt_of_le_of_ne hhi fun heq => ?_⟩
    -- the endpoint case: `|R_v| = 10^j` and `vl` on the grid, impossible for odd `m`
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

/-! ## Schubfach's choice is the scan's -/

theorem inRoundingInterval_eq (s : Nat) (k : Int) :
    inRoundingInterval s k m q (isIrregular m q) = InRv m q ((s : Rat) * (10 : Rat) ^ k) := by
  rw [Bool.eq_iff_iff]; exact inRoundingInterval_iff s k

/-- On a grid that meets `R_v`, `pickNearer` is what `candidate` returns. -/
theorem candidate_eq_pickNearer (_hm : 1 ≤ m) {k : Int}
    (hhit : InRv m q (u m q k) = true ∨ InRv m q (w m q k) = true) :
    candidate m q k = some (pickNearer (Printer.s m q k) k m q) := by
  rw [candidate_def]
  unfold pickNearer
  simp only [inRoundingInterval_eq, gt_iff_lt]
  have hu' : (Printer.s m q k : Rat) * 10 ^ k = u m q k := rfl
  have hw' : ((Printer.s m q k + 1 : Nat) : Rat) * 10 ^ k = w m q k := by unfold w; push_cast; rfl
  rw [hu', hw']
  obtain ⟨c1, c2, c3⟩ := cmpScaledMixed_spec (2 * (m : Int)) q (2 * (Printer.s m q k : Int) + 1) k
  push_cast at c1 c2 c3
  have hv : (2 : Rat) * m * 2 ^ q = 2 * v m q := by unfold v; grind
  have huw : (2 * (Printer.s m q k : Rat) + 1) * 10 ^ k = u m q k + w m q k := by unfold u w; grind
  rw [hv, huw] at c1 c2 c3
  generalize hcmp : cmpScaledMixed (2 * (m : Int)) q (2 * (Printer.s m q k : Int) + 1) k = c at c1 c2 c3 ⊢
  cases hU : InRv m q (u m q k) <;> cases hW : InRv m q (w m q k) <;> simp only [hU, hW] at hhit ⊢ <;>
    simp only [Bool.not_true, Bool.not_false, Bool.and_true, Bool.and_false,
      Bool.false_eq_true, if_false, if_true] <;> try rfl
  · exact absurd hhit (by simp)
  · -- both: the nearer, ties to even
    by_cases h1 : 2 * v m q < u m q k + w m q k
    · rw [if_pos (c1.mpr h1), if_pos (Or.inl (by grind))]
    · rw [if_neg (fun h => h1 (c1.mp h))]
      by_cases h2 : u m q k + w m q k < 2 * v m q
      · rw [if_pos (c3.mpr h2), if_neg (by grind)]
      · rw [if_neg (fun h => h2 (c3.mp h))]
        have heq : v m q - u m q k = w m q k - v m q := by grind
        by_cases he : Printer.s m q k % 2 = 0
        · rw [if_pos he, if_pos (Or.inr ⟨heq, he⟩)]
        · rw [if_neg he, if_neg (by grind)]

/-- `mk'` keeps the value. -/
theorem mk'_value (s : Bool) {n : Nat} (hn : n ≠ 0) (i : Int) :
    ((Decimal.mk' s n i).significand : Rat) * (10 : Rat) ^ (Decimal.mk' s n i).exponent
      = (n : Rat) * (10 : Rat) ^ i := by
  obtain ⟨-, -, -, hle, hv⟩ := mk_pos_props s n i hn
  generalize Decimal.mk' s n i = d at *
  rw [← hv]
  push_cast
  rw [ten_zpow_split hle]
  grind

theorem mk'_eq_of_value_eq (s : Bool) {n n' : Nat} {i i' : Int} (hn : 1 ≤ n) (hn' : 1 ≤ n')
    (h : (n : Rat) * (10 : Rat) ^ i = (n' : Rat) * (10 : Rat) ^ i') :
    Decimal.mk' s n i = Decimal.mk' s n' i' := by
  obtain ⟨hs, hne, -, -, -⟩ := mk_pos_props s n i (by omega)
  obtain ⟨hs', hne', -, -, -⟩ := mk_pos_props s n' i' (by omega)
  exact canonical_eq_of_value_eq (d := Decimal.mk' s n i) (d' := Decimal.mk' s n' i')
    (Decimal.canonical_isCanonical _) (Decimal.canonical_isCanonical _)
    (by rw [hs, hs']) (by omega) (by omega)
    (by rw [mk'_value s (by omega), mk'_value s (by omega), h])

/-! ## Kernel 0 is the scan -/

/-- Schubfach's `(sig, exp)` denotes the scan's first hit. -/
theorem shortestUnsigned_spec (h : InRange m q) :
    1 ≤ (shortestUnsigned m q).1
    ∧ ((shortestUnsigned m q).1 : Rat) * (10 : Rat) ^ (shortestUnsigned m q).2
        = ((shortest m q).1 : Rat) * (10 : Rat) ^ (shortest m q).2 := by
  have hm := h.1
  rcases ho : shortest m q with ⟨n, i⟩
  obtain ⟨hn, -, -, hc, hnone⟩ := scan_spec h ho
  obtain ⟨-, -, hmemn, -, -⟩ := candidate_some hm hc
  obtain ⟨hk1, hk2⟩ := k_spec h
  generalize hk : kOfMQ m q = k at hk1 hk2
  have hhitk : ∃ x, OnGrid k x ∧ InRv m q x = true := hit_of_le_width hm hk1
  have hck : candidate m q k ≠ none := fun hno => (candidate_none_iff hm).mp hno hhitk
  have hik : k ≤ i := Int.not_lt.mp fun hlt => hck (hnone k hlt)
  have hu' : (Printer.s m q k / 10 : Nat) = Printer.s m q (k + 1) := (s_succ hm k).symm
  -- with a hit on `10^k`, `pickNearer` is the scan's candidate
  have hpick : candidate m q k = some (pickNearer (Printer.s m q k) k m q) :=
    candidate_eq_pickNearer hm ((hit_iff_neighbour hm).mp hhitk)
  -- no hit on any grid above `k` forces `i = k` and `n` the pick
  have finish (hnohit : ∀ j, k < j → candidate m q j = none) :
      n = pickNearer (Printer.s m q k) k m q ∧ i = k := by
    have hik' : i = k := by
      rcases Int.lt_or_eq_of_le hik with hlt | heq
      · exact absurd hc (by rw [hnohit i hlt]; simp)
      · exact heq.symm
    subst hik'
    rw [hpick] at hc
    exact ⟨(Option.some.inj hc).symm, rfl⟩
  unfold shortestUnsigned
  simp only [hk, shiftedSig_eq, inRoundingInterval_eq]
  by_cases h10 : Printer.s m q k ≥ 10
  · rw [if_pos h10]
    have hs1 : 1 ≤ Printer.s m q (k + 1) := by omega
    have huu : ((Printer.s m q k / 10 : Nat) : Rat) * (10 : Rat) ^ (k + 1) = u m q (k + 1) := by
      unfold u; rw [hu']
    have hww : ((Printer.s m q k / 10 + 1 : Nat) : Rat) * (10 : Rat) ^ (k + 1) = w m q (k + 1) := by
      unfold w; rw [hu']; push_cast; rfl
    rw [huu, hww]
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
    have hs0 : Printer.s m q (k + 1) = 0 := by omega
    have hv10 : v m q < (10 : Rat) ^ (k + 1) :=
      Rat.not_le.mp fun hle => by have := (s_pos_iff hm).mpr hle; omega
    have hu0 : u m q (k + 1) = 0 := by unfold u; rw [hs0]; simp
    have hw1 : w m q (k + 1) = (10 : Rat) ^ (k + 1) := by unfold w; rw [hs0]; grind
    have hvl := vl_pos (q := q) hm
    have hU0 : InRv m q (u m q (k + 1)) = false := by
      rw [hu0]
      cases hx : InRv m q 0
      · rfl
      · exfalso; have := (le_of_InRv hx).1; grind
    have hT := ten_zpow_pos (k + 1)
    -- nothing of `R_v` on any grid above `k + 1`
    have hnone_above : ∀ j, k + 1 < j → candidate m q j = none := by
      intro j hj
      rw [candidate_none_iff hm]
      rintro ⟨x, ⟨c, rfl⟩, hxR⟩
      obtain ⟨hl, hr⟩ := le_of_InRv hxR
      have hc : 1 ≤ c := by
        rcases Nat.eq_zero_or_pos c with h0 | h0
        · exfalso; subst h0; simp at hl; grind
        · exact h0
      have h1 : (10 : Rat) ^ (k + 2) ≤ (10 : Rat) ^ j := zpow_le_zpow_right₀ (by decide) (by omega)
      have h2 : (10 : Rat) ^ (k + 2) = 10 ^ (k + 1) * 10 := by
        rw [show k + 2 = (k + 1) + 1 by omega, Rat.zpow_add_one (by decide)]
      have h3 : (1 : Rat) * 10 ^ j ≤ (c : Rat) * 10 ^ j :=
        Rat.mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (le_of_lt (ten_zpow_pos j))
      have hvlv := vl_lt_v (q := q) hm
      grind
    by_cases hW : InRv m q ((10 : Rat) ^ (k + 1)) = true
    · -- the scan hits at `k + 1` with `1`
      have hc1 : candidate m q (k + 1) = some 1 := by
        rw [candidate_def, hU0, hw1, hW, hs0]
      have hi : i = k + 1 := by
        rcases Int.lt_trichotomy i (k + 1) with hlt | heq | hgt
        · exfalso; have := hnone (k + 1) hlt; rw [hc1] at this; cases this
        · exact heq
        · exfalso; have := hnone_above i hgt; rw [this] at hc; cases hc
      subst hi
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
          Rat.le_floor_iff.mpr (by rw [Reader.le_div_iff h10k]; push_cast; exact le_of_lt hT3.1)
        have hsc : ((Printer.s m q k : Nat) : Int) = (v m q / (10 : Rat) ^ k).floor := by
          exact_mod_cast s_cast (q := q) (i := k) hm
        omega
      obtain ⟨-, hcase, hmemp, hclose, -⟩ := candidate_some hm hpick
      have hp10 : pickNearer (Printer.s m q k) k m q = 10 := by
        rcases hcase with e | e
        · exfalso
          rw [e, hs9] at hmemp hclose
          have h1 := hclose _ ⟨10, rfl⟩ (by rw [hTi] at hW; push_cast; rw [Rat.mul_comm]; exact hW)
          have h2 := hT3.2 (by push_cast at hmemp; exact hmemp)
          push_cast at h1
          rw [hTi] at h2
          rw [abs_of_nonneg (by grind), abs_of_nonpos (by grind)] at h1
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

/-- The finite case: Schubfach's canonicalised decimal is the scan's. -/
theorem finite_eq (sb : Bool) (h : InRange m q) :
    (Except.ok (Decimal.mk' sb (shortestUnsigned m q).1 (shortestUnsigned m q).2) : Except String Decimal)
      = Except.ok ⟨sb, (shortest m q).1, (shortest m q).2⟩ := by
  obtain ⟨hpos, hval⟩ := shortestUnsigned_spec h
  rcases hr : shortestUnsigned m q with ⟨n', k'⟩
  rcases ho : shortest m q with ⟨n, i⟩
  have hn := (scan_spec h ho).1
  have h10 := out_ten h ho
  rw [hr, ho] at hval; rw [hr] at hpos
  simp only at hval hpos
  obtain ⟨hsign, hne, -, -, -⟩ := mk_pos_props sb n' k' (by omega)
  have hd : Decimal.mk' sb n' k' = ⟨sb, n, i⟩ :=
    canonical_eq_of_value_eq (d := Decimal.mk' sb n' k') (d' := ⟨sb, n, i⟩)
      (Decimal.canonical_isCanonical ⟨sb, n', k'⟩)
      (Or.inr ⟨Nat.pos_iff_ne_zero.mp hn, h10⟩) hsign (Nat.pos_of_ne_zero hne) hn
      (by rw [mk'_value sb (by omega)]; exact hval)
  rw [hd]

/-- **Kernel 0 is the reference printer.** -/
theorem toDecimalBits_eq_printer : Schubfach.toDecimalBits = Printer.toDecimalBits := by
  funext w
  unfold Schubfach.toDecimalBits Printer.toDecimalBits
  rw [unpack_eq]
  have hb := word_biasedExp_lt w
  have hmlt := word_mantissa_lt w
  by_cases h1 : Word.biasedExp w = 2047
  · -- NaN or infinity
    rw [if_pos h1]
    have hnan : Word.isNaN w = decide (Word.mantissa w ≠ 0) := by unfold Word.isNaN; simp [h1]
    have hinf : Word.isInf w = decide (Word.mantissa w = 0) := by unfold Word.isInf; simp [h1]
    by_cases h2 : Word.mantissa w = 0
    · rw [if_pos h2]; simp [hnan, hinf, h2]; cases Word.signBit w <;> rfl
    · rw [if_neg h2]; simp [hnan, h2]
  · rw [if_neg h1]
    have hnan : Word.isNaN w = false := by unfold Word.isNaN; simp [h1]
    have hinf : Word.isInf w = false := by unfold Word.isInf; simp [h1]
    rw [hnan, hinf]
    simp only [Bool.false_eq_true, if_false]
    by_cases h0 : Word.biasedExp w = 0
    · rw [if_pos h0]
      have hdec : Word.decode w = ⟨Word.signBit w, Word.mantissa w, -1074⟩ := by
        unfold Word.decode; rw [if_pos h0]
      rw [hdec]
      by_cases h2 : Word.mantissa w = 0
      · rw [dif_pos h2]; simp [h2, negative_sign]
      · rw [dif_neg h2, if_neg h2]
        dsimp only
        rw [negative_sign]
        exact finite_eq (Word.signBit w)
          ⟨Nat.pos_of_ne_zero h2, by omega, by omega, by omega, fun h => absurd rfl h⟩
    · rw [if_neg h0]
      have hdec : Word.decode w =
          ⟨Word.signBit w, Word.mantissa w + 2 ^ 52, (Word.biasedExp w : Int) - 1075⟩ := by
        unfold Word.decode; rw [if_neg h0]
        simp only [Decoded.mk.injEq, Nat.shiftLeft_eq, Nat.one_mul, true_and]
        omega
      rw [hdec, if_neg (by omega : ¬ (Word.mantissa w + 2 ^ 52 = 0))]
      dsimp only
      rw [negative_sign]
      exact finite_eq (Word.signBit w) ⟨by omega, by omega, by omega, by omega, fun _ => by omega⟩

theorem toDecimal_eq_printer : Schubfach.toDecimal = Printer.toDecimal :=
  funext fun f => congrArg (· f.toBits) toDecimalBits_eq_printer

end Srtfp.Schubfach

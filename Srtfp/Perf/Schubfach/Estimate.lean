module
/- Results 24 and 25 assembled with R22: from the table entry `g`, the shift
   `h` of (9), and R20, algorithm F8 computes the exact `r_o(4x)` for each of
   `x = V, V_l, V_r`. Also `h` from R16 on the table index, and the range of
   `k` (`K_min ≤ k ≤ K_max`). -/

public import Srtfp.Perf.Schubfach.Product
public import Srtfp.Perf.Schubfach.NadezhinBands

@[expose] public section

open Srtfp.Compat

namespace Srtfp.Schubfach

open Srtfp.Printer Exact R20

variable {m : Nat} {q : Int}

/-! ## The range of `k` -/

/-- `K_min ≤ k ≤ K_max` (the table covers every binary64). -/
theorem k_range (h : InRange m q) : kMin ≤ kOfMQ m q ∧ kOfMQ m q ≤ kMax := by
  obtain ⟨h1, h2⟩ := k_spec h
  have hq1 : -1074 ≤ q := h.2.2.1
  have hq2 : q ≤ 971 := h.2.2.2.1
  rw [width_eq] at h1 h2
  generalize kOfMQ m q = k at *
  have h2q : (0 : Rat) < 2 ^ q := Rat.zpow_pos (by decide)
  unfold kMin kMax
  constructor
  · -- `10^{-324} < 2^{-1076} ≤ (3/4)·2^q < 10^{k+1}`
    have hw : (3 / 4 : Rat) * 2 ^ q ≤ (if m = 2 ^ 52 ∧ q > -1074 then 3 / 4 else 1) * 2 ^ q := by
      split <;> grind
    have hlo : (2 : Rat) ^ (-1076 : Int) ≤ 3 / 4 * 2 ^ q := by
      have : (2 : Rat) ^ (-1076 : Int) * 4 = 2 ^ (-1074 : Int) := by
        rw [show (-1074 : Int) = -1076 + ((2 : Nat) : Int) by rfl, Rat.zpow_add (by decide),
          Rat.zpow_natCast]
        rfl
      have := zpow_le_zpow_right₀ (a := (2 : Rat)) (by decide) hq1
      grind
    have hnum : (10 : Rat) ^ (-324 : Int) < (2 : Rat) ^ (-1076 : Int) := by
      rw [show (-324 : Int) = -((324 : Nat) : Int) from rfl,
        show (-1076 : Int) = -((1076 : Nat) : Int) from rfl,
        zpow_neg_natCast, zpow_neg_natCast]
      exact inv_lt_inv (Rat.pow_pos (by decide))
        (by exact_mod_cast (by decide +kernel : (2 : Nat) ^ 1076 < 10 ^ 324))
    have : (10 : Rat) ^ (-324 : Int) < 10 ^ (k + 1) := by grind
    have := lt_of_zpow_lt (by decide) this
    omega
  · -- `10^k ≤ 2^q ≤ 2^971 < 10^293`
    have hw : (if m = 2 ^ 52 ∧ q > -1074 then 3 / 4 else 1) * (2 : Rat) ^ q ≤ 2 ^ q := by
      split <;> grind
    have hhi : (2 : Rat) ^ q ≤ 2 ^ (971 : Int) := zpow_le_zpow_right₀ (by decide) hq2
    have hnum : (2 : Rat) ^ (971 : Int) < (10 : Rat) ^ (293 : Int) := by
      rw [show (971 : Int) = ((971 : Nat) : Int) from rfl, show (293 : Int) = ((293 : Nat) : Int) from rfl,
        Rat.zpow_natCast, Rat.zpow_natCast]
      exact_mod_cast (by decide +kernel : 2 ^ 971 < 10 ^ 293)
    have : (10 : Rat) ^ k < 10 ^ (293 : Int) := by grind
    have := lt_of_zpow_lt (by decide) this
    omega

/-! ## `h = q + ⌊log₂ 10^{-k}⌋ + 2` (9) -/

/-- `1 ≤ 2^q·10^{-k} < 2^4` (from R10 and the width of `R_v`). -/
theorem ratio_bounds (h : InRange m q) :
    1 ≤ (2 : Rat) ^ q * 10 ^ (-(kOfMQ m q)) ∧ (2 : Rat) ^ q * 10 ^ (-(kOfMQ m q)) < 16 := by
  obtain ⟨h1, h2⟩ := k_spec h
  rw [width_eq] at h1 h2
  generalize kOfMQ m q = k at *
  have h2q : (0 : Rat) < 2 ^ q := Rat.zpow_pos (by decide)
  have hT : (0 : Rat) < 10 ^ (-k) := Rat.zpow_pos (by decide)
  have e1 : (10 : Rat) ^ k * 10 ^ (-k) = 1 := by
    rw [← Rat.zpow_add (by decide), show k + -k = 0 by omega, Rat.zpow_zero]
  constructor
  · have hw : (10 : Rat) ^ k ≤ 2 ^ q := by
      have : (if m = 2 ^ 52 ∧ q > -1074 then 3 / 4 else 1) * (2 : Rat) ^ q ≤ 2 ^ q := by
        split <;> grind
      grind
    have := Rat.mul_le_mul_of_nonneg_right hw (Rat.le_of_lt hT)
    grind
  · have hw : (3 / 4 : Rat) * 2 ^ q < 10 ^ (k + 1) := by
      have : (3 / 4 : Rat) * 2 ^ q ≤ (if m = 2 ^ 52 ∧ q > -1074 then 3 / 4 else 1) * 2 ^ q := by
        split <;> grind
      grind
    have h10 : (10 : Rat) ^ (k + 1) = 10 ^ k * 10 := Rat.zpow_add_one (by decide) k
    have hR : (10 : Rat) ^ k * 10 * 10 ^ (-k) = 10 := by
      rw [Rat.mul_assoc, Rat.mul_comm (10 : Rat), ← Rat.mul_assoc, e1, Rat.one_mul]
    have := Rat.mul_lt_mul_of_pos_right hw hT
    rw [h10, hR] at this
    grind

/-- `q + r ∈ [−125, −122]`, from `1 ≤ 2^q·10^{-k} < 2^4` and the definition of
    `r` (R24). -/
theorem q_add_r (h : InRange m q) :
    -125 ≤ q + r (kOfMQ m q) ∧ q + r (kOfMQ m q) ≤ -122 := by
  obtain ⟨hlo, hhi⟩ := ratio_bounds h
  obtain ⟨hr1, hr2⟩ := r_spec (kOfMQ m q)
  generalize kOfMQ m q = k at *
  have h2q : (0 : Rat) < 2 ^ q := Rat.zpow_pos (by decide)
  have h16 : (2 : Rat) ^ (4 : Int) = 16 := by
    rw [show (4 : Int) = ((4 : Nat) : Int) from rfl, Rat.zpow_natCast]; rfl
  rw [← h16] at hhi
  constructor
  · -- `1 ≤ 2^q·10^{-k} < 2^q·2^{r+126}`
    have : (2 : Rat) ^ (0 : Int) < 2 ^ (q + (r k + 126)) := by
      rw [Rat.zpow_zero, Rat.zpow_add (by decide)]
      have := Rat.mul_lt_mul_of_pos_left hr2 h2q
      grind
    have := lt_of_zpow_lt (by decide) this
    omega
  · -- `2^q·2^{r+125} ≤ 2^q·10^{-k} < 2^4`
    have : (2 : Rat) ^ (q + (r k + 125)) < 2 ^ (4 : Int) := by
      rw [Rat.zpow_add (by decide)]
      have := Rat.mul_le_mul_of_nonneg_left hr1 (Rat.le_of_lt h2q)
      grind
    have := lt_of_zpow_lt (by decide) this
    omega

/-- `⌊log₂ 10^{-k}⌋ + 2^20` by R16 from the table index `kB = k − K_min`
    (so `−k = 324 − kB`); the bias keeps the product non-negative. -/
@[inline] def flog2B (kB : UInt64) : UInt64 :=
  ((324 - kB) * 913124641741 + 288230376151711744) >>> 38

theorem flog2B_toNat (kB : UInt64) (hk : kB.toNat ≤ 616) :
    ((flog2B kB).toNat : Int) = flog2pow10 (324 - kB.toNat) + 2 ^ 20 := by
  unfold flog2B flog2pow10
  rw [UInt64.toNat_shiftRight, UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_sub,
    show (38 : UInt64).toNat % 64 = 38 from rfl, show (324 : UInt64).toNat = 324 from rfl,
    show (913124641741 : UInt64).toNat = 913124641741 from rfl,
    show (288230376151711744 : UInt64).toNat = 2 ^ 58 from rfl,
    Int.fdiv_eq_ediv_of_nonneg _ (by decide), Nat.shiftRight_eq_div_pow]
  omega

/-- `h` of (9), from the biased `qB = q + 1074` and the table index `kB`. -/
@[inline] def hOf (qB kB : UInt64) : UInt64 := qB + flog2B kB - 1049648

theorem hOf_toNat (qB kB : UInt64) (hk : kB.toNat ≤ 616)
    (hlo : 2 ≤ (qB.toNat : Int) - 1074 + flog2pow10 (324 - kB.toNat) + 2)
    (hhi : (qB.toNat : Int) - 1074 + flog2pow10 (324 - kB.toNat) + 2 ≤ 5) :
    ((hOf qB kB).toNat : Int) = (qB.toNat : Int) - 1074 + flog2pow10 (324 - kB.toNat) + 2 := by
  unfold hOf
  have hf := flog2B_toNat kB hk
  rw [UInt64.toNat_sub, UInt64.toNat_add, show (1049648 : UInt64).toNat = 1049648 from rfl]
  omega

/-- `h = q + r + 127` for `k` in range (R16 is exact there). -/
theorem h_eq (h : InRange m q) :
    q + flog2pow10 (-(kOfMQ m q)) + 2 = q + r (kOfMQ m q) + 127 := by
  obtain ⟨hk1, hk2⟩ := k_range h
  rw [flog2pow10_eq_exact _ (by unfold kMax at hk2; omega) (by unfold kMin at hk1; omega)]
  unfold r
  omega

/-! ## Bounds on `r_o` -/

theorem ro_nonneg {x : Rat} (hx : 0 ≤ x) : 0 ≤ ro x := by
  unfold ro
  have : (0 : Int) ≤ (x / 2).floor := by
    rw [Rat.le_floor_iff]; rw [le_div_iff (by decide)]; grind
  split <;> omega

theorem ro_le (x : Rat) : (ro x : Rat) ≤ x + 1 := by
  unfold ro
  have := Rat.floor_le (x / 2)
  split <;> push_cast <;> grind

/-! ## R24 + R25 + R22: F8 computes `r_o(4x)` -/

theorem eps_half : eps / 2 = (2 : Rat) ^ (-65 : Int) := by
  unfold eps
  rw [show (-65 : Int) = -((64 : Nat) : Int) - 1 by rfl, Rat.zpow_sub_one (by decide)]
  rfl

/-- With `cp = mb·2^h`, `h = q + r + 127` and `g` from the table, F8 on
    `(g₁, g₀, cp)` is `r_o(4x)` for `x = (mb/4)·2^q·10^{-k}`, given R20 for
    `2x`. -/
theorem rop_eq_ro (mb : Nat) (q k : Int) (g1 g0 cp : UInt64) (hh : Nat)
    (hk : kMin ≤ k ∧ k ≤ kMax) (hmb55 : mb < 2 ^ 55)
    (hg1 : g1.toNat = g k / 2 ^ 63) (hg0 : g0.toNat = g k % 2 ^ 63)
    (hcp : cp.toNat = mb * 2 ^ hh) (hh2 : 2 ≤ hh) (hh5 : hh ≤ 5)
    (hhq : (hh : Int) = q + r k + 127)
    (hsep : Separated eps (2 * ((mb : Rat) / 4 * (2 : Rat) ^ q * (10 : Rat) ^ (-k)))) :
    ((rop g1 g0 cp).toNat : Int) = ro (4 * ((mb : Rat) / 4 * (2 : Rat) ^ q * (10 : Rat) ^ (-k))) := by
  have hg126 := g_lt_two_pow_126 k hk.1 hk.2
  have hg := Nat.div_add_mod (g k) (2 ^ 63)
  have h2h : 2 ^ hh ≤ 2 ^ 5 := Nat.pow_le_pow_right (by decide) hh5
  rw [rop_eq g1 g0 cp (by rw [hg1]; omega) (by rw [hg0]; omega)
    (by rw [hcp]; calc mb * 2 ^ hh < 2 ^ 55 * 2 ^ 5 := Nat.mul_lt_mul_of_lt_of_le hmb55 h2h (by decide)
      _ = 2 ^ 60 := by decide)
    (by rw [hcp]; exact Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega : 1 ≤ hh)) (Nat.dvd_mul_left _ _))]
  rw [hcp, hg1, hg0, Nat.mul_comm (g k / 2 ^ 63), hg]
  -- the estimate `x' = (mb/4)·2^q·g·2^r`
  set x : Rat := (mb : Rat) / 4 * (2 : Rat) ^ q * (10 : Rat) ^ (-k) with hx
  set x' : Rat := (mb : Rat) / 4 * (2 : Rat) ^ q * ((g k : Rat) * (2 : Rat) ^ (r k)) with hx'
  have hx'4 : (((mb * 2 ^ hh * g k : Nat) : Rat) / ((2 ^ 127 : Nat) : Rat)) = 4 * x' := by
    rw [hx', div_eq_iff (by exact_mod_cast Nat.two_pow_pos 127)]
    push_cast
    have e : (2 : Rat) ^ hh = 2 ^ q * 2 ^ (r k) * (2 : Rat) ^ (127 : Nat) := by
      rw [← Rat.zpow_natCast, ← Rat.zpow_natCast, ← Rat.zpow_add (by decide),
        ← Rat.zpow_add (by decide)]
      congr 1
      all_goals omega
    rw [e]
    grind
  rw [hx'4]
  have h2q : (0 : Rat) < 2 ^ q := Rat.zpow_pos (by decide)
  have hR : (0 : Rat) < 2 ^ (r k) := Rat.zpow_pos (by decide)
  have hmb4 : (0 : Rat) ≤ (mb : Rat) / 4 := by
    rw [le_div_iff (by decide)]; rw [Rat.zero_mul]; exact_mod_cast Nat.zero_le mb
  have hA : (0 : Rat) ≤ (mb : Rat) / 4 * 2 ^ q := Rat.mul_nonneg hmb4 (Rat.le_of_lt h2q)
  -- `10^{-k} < g·2^r` and `g·2^r − 2^r ≤ 10^{-k}` (R24)
  have hRinv : (2 : Rat) ^ (-(r k)) * 2 ^ (r k) = 1 := by
    rw [← Rat.zpow_add (by decide), show -(r k) + r k = 0 by omega, Rat.zpow_zero]
  obtain ⟨hg1s, hg2s⟩ := g_spec k
  have hgpos : 1 ≤ g k := by have := two_pow_125_lt_g k; omega
  have hgc : ((g k - 1 : Nat) : Rat) = (g k : Rat) - 1 := by
    have h' : ((g k - 1 + 1 : Nat) : Rat) = (g k : Rat) := by rw [Nat.sub_add_cancel hgpos]
    push_cast at h'; grind
  have hT1 : (10 : Rat) ^ (-k) < (g k : Rat) * 2 ^ (r k) := by
    have := Rat.mul_lt_mul_of_pos_right hg2s hR
    rwa [Rat.mul_comm ((2 : Rat) ^ (-(r k))), Rat.mul_assoc, hRinv, Rat.mul_one] at this
  have hT2 : (g k : Rat) * 2 ^ (r k) - 2 ^ (r k) ≤ (10 : Rat) ^ (-k) := by
    have := Rat.mul_le_mul_of_nonneg_right hg1s (Rat.le_of_lt hR)
    rw [hgc, Rat.mul_comm ((2 : Rat) ^ (-(r k))), Rat.mul_assoc, hRinv, Rat.mul_one] at this
    grind
  have hdiff : x' - x = ((mb : Rat) / 4 * 2 ^ q) * ((g k : Rat) * 2 ^ (r k) - 10 ^ (-k)) := by
    rw [hx, hx']; grind
  have hε1 : eps ≤ 1 := by
    unfold eps
    have := zpow_le_zpow_right₀ (a := (2 : Rat)) (by decide) (show -((64 : Nat) : Int) ≤ 0 by omega)
    rwa [Rat.zpow_zero] at this
  refine R22 hε1 hsep ?_ ?_
  · rw [hdiff]; exact Rat.mul_nonneg hA (by grind)
  · rw [hdiff, eps_half]
    -- `A·(g·2^r − 10^{-k}) ≤ A·2^r = (mb/4)·2^{q+r} < 2^53·2^{-122} = 2^{-69} < 2^{-65}`
    have h1 : (mb : Rat) / 4 < 2 ^ (53 : Int) := by
      rw [Rat.div_lt_iff (by decide),
        show (2 : Rat) ^ (53 : Int) * 4 = 2 ^ (55 : Int) by
          rw [show (55 : Int) = 53 + 2 by rfl, Rat.zpow_add (by decide)]; rfl,
        show (55 : Int) = ((55 : Nat) : Int) from rfl, Rat.zpow_natCast]
      exact_mod_cast hmb55
    have h2 : (2 : Rat) ^ q * 2 ^ (r k) ≤ 2 ^ (-122 : Int) := by
      rw [← Rat.zpow_add (by decide)]; exact zpow_le_zpow_right₀ (by decide) (by omega)
    have hAR : (mb : Rat) / 4 * 2 ^ q * 2 ^ (r k) < (2 : Rat) ^ (-65 : Int) :=
      calc (mb : Rat) / 4 * 2 ^ q * 2 ^ (r k) = (mb : Rat) / 4 * (2 ^ q * 2 ^ (r k)) :=
            Rat.mul_assoc _ _ _
        _ ≤ (mb : Rat) / 4 * 2 ^ (-122 : Int) := Rat.mul_le_mul_of_nonneg_left h2 hmb4
        _ < 2 ^ (53 : Int) * 2 ^ (-122 : Int) :=
            Rat.mul_lt_mul_of_pos_right h1 (Rat.zpow_pos (by decide))
        _ = 2 ^ (-69 : Int) := by rw [← Rat.zpow_add (by decide)]; rfl
        _ < 2 ^ (-65 : Int) := zpow_lt_zpow (by decide) (by decide)
    calc (mb : Rat) / 4 * 2 ^ q * ((g k : Rat) * 2 ^ (r k) - 10 ^ (-k))
          ≤ (mb : Rat) / 4 * 2 ^ q * 2 ^ (r k) := Rat.mul_le_mul_of_nonneg_left (by grind) hA
      _ < 2 ^ (-65 : Int) := hAR

end Srtfp.Schubfach

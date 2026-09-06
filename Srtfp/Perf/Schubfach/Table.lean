module
/- The table of powers of ten (Giulietti §9.8.2, R24).

   For each `k ∈ [K_min, K_max]` the kernel needs an overestimate of
   `10^{-k}` of the form `g · 2^r` with `g` a 126-bit integer:

     r = ⌊log₂ 10^{-k}⌋ − 125        g = ⌊2^{-r} · 10^{-k}⌋ + 1

   so that `2^125 < g ≤ 2^126` and `(g − 1) · 2^r ≤ 10^{-k} < g · 2^r`.
   The paper's table check (`g < 2^126` for every entry) is a kernel
   `decide`. The table is computed here at load time from those
   definitions; the kernel reads `g₁ = g / 2^63` and `g₀ = g mod 2^63`
   from two scalar arrays. -/

public import Srtfp.Perf.Schubfach.Exact

@[expose] public section

open Srtfp.Compat

namespace Srtfp.Schubfach

/-! ## R24: `r` and `g` -/

/-- `K_min = ⌊log₁₀ 2^{Q_min}⌋`. -/
def kMin : Int := -324

/-- `K_max = ⌊log₁₀ 2^{Q_max}⌋`. -/
def kMax : Int := 292

/-- `⌊log₂ 10^e⌋`, exactly: `10^e` is not a power of two unless `e = 0`, so
    for `e < 0` the floor is `−(⌊log₂ 10^{-e}⌋ + 1)`. -/
def flog2pow10Exact (e : Int) : Int :=
  if 0 ≤ e then ((10 ^ e.toNat).log2 : Int) else -(((10 ^ (-e).toNat).log2 : Int) + 1)

/-- `r = ⌊log₂ 10^{-k}⌋ − 125`. -/
def r (k : Int) : Int := flog2pow10Exact (-k) - 125

/-- `g = ⌊2^{-r} · 10^{-k}⌋ + 1`, computed in `Nat` by the signs of `−k` and `r`. -/
def g (k : Int) : Nat :=
  if 0 ≤ -k then
    if 0 ≤ r k then 10 ^ (-k).toNat / 2 ^ (r k).toNat + 1
    else 10 ^ (-k).toNat * 2 ^ (-(r k)).toNat + 1
  else
    2 ^ (-(r k)).toNat / 10 ^ k.toNat + 1

/-! ## The invariant -/

theorem log2_bounds {n : Nat} (hn : 0 < n) : 2 ^ n.log2 ≤ n ∧ n < 2 ^ (n.log2 + 1) :=
  ⟨Nat.log2_self_le (Nat.pos_iff_ne_zero.mp hn), Nat.lt_log2_self⟩

/-- `10^e` is not a power of two for `e ≥ 1`. -/
theorem ten_pow_ne_two_pow (e : Nat) (he : 1 ≤ e) (j : Nat) : 10 ^ e ≠ 2 ^ j := by
  intro h
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  have h5 : 5 ∣ 2 ^ j := ⟨2 * 10 ^ e', by rw [← h, Nat.pow_succ]; grind⟩
  have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right j (by decide : Nat.Coprime 5 2)) h5
  omega

/-- `2^{⌊log₂ 10^e⌋} ≤ 10^e < 2^{⌊log₂ 10^e⌋ + 1}`, over `Rat` for every `e : Int`. -/
theorem flog2pow10Exact_spec (e : Int) :
    (2 : Rat) ^ flog2pow10Exact e ≤ (10 : Rat) ^ e
    ∧ (10 : Rat) ^ e < (2 : Rat) ^ (flog2pow10Exact e + 1) := by
  unfold flog2pow10Exact
  by_cases he : 0 ≤ e
  · rw [if_pos he]
    obtain ⟨n, rfl⟩ : ∃ n : Nat, e = n := ⟨e.toNat, (Int.toNat_of_nonneg he).symm⟩
    simp only [Int.toNat_natCast]
    obtain ⟨h1, h2⟩ := log2_bounds (Nat.pow_pos (by decide) : 0 < 10 ^ n)
    refine ⟨by rw [Rat.zpow_natCast, Rat.zpow_natCast]; exact_mod_cast h1, ?_⟩
    rw [Rat.zpow_add_one (by decide), Rat.zpow_natCast, Rat.zpow_natCast]
    rw [Nat.pow_succ] at h2
    exact_mod_cast h2
  · rw [if_neg he]
    obtain ⟨n, hn⟩ : ∃ n : Nat, e = -(n : Int) :=
      ⟨(-e).toNat, by have := Int.toNat_of_nonneg (show 0 ≤ -e by omega); omega⟩
    subst hn
    simp only [Int.neg_neg, Int.toNat_natCast]
    have hn1 : 1 ≤ n := by omega
    obtain ⟨h1, h2⟩ := log2_bounds (Nat.pow_pos (by decide) : 0 < 10 ^ n)
    -- strict on the left: `10^n` is no power of two
    have h1s : 2 ^ (10 ^ n).log2 < 10 ^ n :=
      Nat.lt_of_le_of_ne h1 (fun h => ten_pow_ne_two_pow _ hn1 _ h.symm)
    generalize hL : (10 ^ n).log2 = L at h1s h2 ⊢
    have h1' : (2 : Rat) ^ (L : Int) < (10 : Rat) ^ (n : Int) := by
      rw [Rat.zpow_natCast, Rat.zpow_natCast]; exact_mod_cast h1s
    have h2' : (10 : Rat) ^ (n : Int) ≤ (2 : Rat) ^ ((L : Int) + 1) := by
      rw [show (L : Int) + 1 = ((L + 1 : Nat) : Int) by push_cast; rfl, Rat.zpow_natCast,
        Rat.zpow_natCast]
      exact_mod_cast Nat.le_of_lt h2
    rw [show -((L : Int) + 1) + 1 = -(L : Int) by omega]
    -- invert: `10^{-n} = (10^n)⁻¹`
    have hpos10 := Printer.ten_zpow_pos (n : Int)
    have hinv : (10 : Rat) ^ (-(n : Int)) * (10 : Rat) ^ (n : Int) = 1 := by
      rw [← Rat.zpow_add (by decide), show -(n : Int) + n = 0 by omega, Rat.zpow_zero]
    have hA : (2 : Rat) ^ (-((L : Int) + 1)) * (2 : Rat) ^ ((L : Int) + 1) = 1 := by
      rw [← Rat.zpow_add (by decide), show -((L : Int) + 1) + ((L : Int) + 1) = 0 by omega,
        Rat.zpow_zero]
    have hB : (2 : Rat) ^ (-(L : Int)) * (2 : Rat) ^ (L : Int) = 1 := by
      rw [← Rat.zpow_add (by decide), show -(L : Int) + L = 0 by omega, Rat.zpow_zero]
    have hp1 := Printer.two_zpow_pos ((L : Int) + 1)
    have hpL := Printer.two_zpow_pos (L : Int)
    constructor
    · refine Rat.le_of_mul_le_mul_right (c := (10 : Rat) ^ (n : Int) * (2 : Rat) ^ ((L : Int) + 1)) ?_
        (Rat.mul_pos hpos10 hp1)
      rw [show (2 : Rat) ^ (-((L : Int) + 1)) * ((10 : Rat) ^ (n : Int) * 2 ^ ((L : Int) + 1))
            = 10 ^ (n : Int) * (2 ^ (-((L : Int) + 1)) * 2 ^ ((L : Int) + 1)) by grind,
        hA, Rat.mul_one,
        show (10 : Rat) ^ (-(n : Int)) * ((10 : Rat) ^ (n : Int) * 2 ^ ((L : Int) + 1))
            = (10 ^ (-(n : Int)) * 10 ^ (n : Int)) * 2 ^ ((L : Int) + 1) by grind,
        hinv, Rat.one_mul]
      exact h2'
    · refine Rat.lt_of_mul_lt_mul_right (c := (10 : Rat) ^ (n : Int) * (2 : Rat) ^ (L : Int)) ?_
        (Rat.le_of_lt (Rat.mul_pos hpos10 hpL))
      rw [show (10 : Rat) ^ (-(n : Int)) * ((10 : Rat) ^ (n : Int) * 2 ^ (L : Int))
            = (10 ^ (-(n : Int)) * 10 ^ (n : Int)) * 2 ^ (L : Int) by grind,
        hinv, Rat.one_mul,
        show (2 : Rat) ^ (-(L : Int)) * ((10 : Rat) ^ (n : Int) * 2 ^ (L : Int))
            = 10 ^ (n : Int) * (2 ^ (-(L : Int)) * 2 ^ (L : Int)) by grind,
        hB, Rat.mul_one]
      exact h1'

/-! ## `r`: `2^{r+125} ≤ 10^{-k} < 2^{r+126}` -/

theorem r_spec (k : Int) :
    (2 : Rat) ^ (r k + 125) ≤ (10 : Rat) ^ (-k) ∧ (10 : Rat) ^ (-k) < (2 : Rat) ^ (r k + 126) := by
  have := flog2pow10Exact_spec (-k)
  unfold r
  rw [show flog2pow10Exact (-k) - 125 + 125 = flog2pow10Exact (-k) by omega,
    show flog2pow10Exact (-k) - 125 + 126 = flog2pow10Exact (-k) + 1 by omega]
  exact this

/-- R16's magic constant agrees with the exact floor-log on the table's range. -/
theorem flog2pow10_eq_exact (e : Int) (hlo : -292 ≤ e) (hhi : e ≤ 324) :
    flog2pow10 e = flog2pow10Exact e := by
  have hR := R16HoldsAt_in_range e hlo hhi
  dsimp only [R16HoldsAt] at hR
  obtain ⟨h1, h2⟩ := hR
  generalize hk : flog2pow10 e = a at h1 h2 ⊢
  -- the cross-multiplied R16 as `2^a ≤ 10^e < 2^(a+1)` over `Rat`
  have r10 := Exact.zpow_ratio 10 (by decide) e
  have r2 := Exact.zpow_ratio 2 (by decide) a
  have r2' := Exact.zpow_ratio 2 (by decide) (a + 1)
  have d10 := Exact.denom_pos 10 (by decide) e
  have d2 := Exact.denom_pos 2 (by decide) a
  have d2' := Exact.denom_pos 2 (by decide) (a + 1)
  have h1' : (((if a ≥ 0 then 2 ^ a.natAbs else 1) * (if e ≥ 0 then 1 else 10 ^ e.natAbs) : Nat) : Rat)
      ≤ (((if e ≥ 0 then 10 ^ e.natAbs else 1) * (if a ≥ 0 then 1 else 2 ^ a.natAbs) : Nat) : Rat) := by
    exact_mod_cast h1
  have h2' : (((if e ≥ 0 then 10 ^ e.natAbs else 1) * (if a + 1 ≥ 0 then 1 else 2 ^ (a + 1).natAbs) : Nat) : Rat)
      < (((if a + 1 ≥ 0 then 2 ^ (a + 1).natAbs else 1) * (if e ≥ 0 then 1 else 10 ^ e.natAbs) : Nat) : Rat) := by
    exact_mod_cast h2
  push_cast at h1' h2'
  rw [← r10, ← r2] at h1'
  rw [← r10, ← r2'] at h2'
  generalize ((if e ≥ 0 then 1 else 10 ^ e.natAbs : Nat) : Rat) = D10 at *
  generalize ((if a ≥ 0 then 1 else 2 ^ a.natAbs : Nat) : Rat) = D2 at *
  generalize ((if a + 1 ≥ 0 then 1 else 2 ^ (a + 1).natAbs : Nat) : Rat) = D2' at *
  have hA : (2 : Rat) ^ a ≤ (10 : Rat) ^ e :=
    Rat.le_of_mul_le_mul_right (c := D10 * D2) (by grind) (by grind)
  have hB : (10 : Rat) ^ e < (2 : Rat) ^ (a + 1) :=
    Rat.lt_of_mul_lt_mul_right (c := D10 * D2') (by grind) (by grind)
  -- both `a` and the exact value are the floor of `log₂ 10^e`
  obtain ⟨hC, hD⟩ := flog2pow10Exact_spec e
  generalize flog2pow10Exact e = b at hC hD ⊢
  have lt_of_zpow_lt {x y : Int} (h : (2 : Rat) ^ x < (2 : Rat) ^ y) : x < y := by
    rcases Int.lt_or_le x y with hxy | hxy
    · exact hxy
    · exact absurd h (Rat.not_lt.mpr (zpow_le_zpow_right₀ (by decide) hxy))
  have h1 := lt_of_zpow_lt (lt_of_le_of_lt hA hD)
  have h2 := lt_of_zpow_lt (lt_of_le_of_lt hC hB)
  omega

/-! ## `g`: `(g − 1) · 2^r ≤ 10^{-k} < g · 2^r`, `2^125 < g ≤ 2^126` -/

/-- Integer division brackets the rational quotient. -/
theorem natDiv_bounds (N D : Nat) (hD : 0 < D) :
    ((N / D : Nat) : Rat) ≤ (N : Rat) / D ∧ (N : Rat) / D < ((N / D : Nat) : Rat) + 1 := by
  have hDq : (0 : Rat) < D := by exact_mod_cast hD
  constructor
  · rw [Exact.le_div_iff' hDq]; exact_mod_cast Nat.div_mul_le_self N D
  · rw [Exact.div_lt_iff' hDq]
    have hdm := Nat.div_add_mod N D
    have hmod := Nat.mod_lt N hD
    have : N < (N / D + 1) * D := by
      calc N = D * (N / D) + N % D := hdm.symm
        _ < D * (N / D) + D := Nat.add_lt_add_left hmod _
        _ = (N / D + 1) * D := by rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]
    exact_mod_cast this

/-- `10^e` as a `Nat` power, for `e ≥ 0`. -/
theorem ten_zpow_toNat {e : Int} (he : 0 ≤ e) : (10 : Rat) ^ e = ((10 ^ e.toNat : Nat) : Rat) := by
  push_cast; rw [← Printer.zpow_natCast_lit, Int.toNat_of_nonneg he]

theorem two_zpow_toNat' {e : Int} (he : 0 ≤ e) : (2 : Rat) ^ e = ((2 ^ e.toNat : Nat) : Rat) := by
  push_cast; rw [← Printer.zpow_natCast_lit, Int.toNat_of_nonneg he]

/-- `2^{-e}` as the inverse of a `Nat` power, for `e ≥ 0`. -/
theorem two_zpow_neg_toNat {e : Int} (he : 0 ≤ e) :
    (2 : Rat) ^ (-e) = (((2 ^ e.toNat : Nat) : Rat))⁻¹ := by
  rw [← Int.toNat_of_nonneg he, Printer.two_zpow_neg_eq, Int.toNat_natCast]; push_cast; rfl

theorem ten_zpow_neg_toNat {e : Int} (he : 0 ≤ e) :
    (10 : Rat) ^ (-e) = (((10 ^ e.toNat : Nat) : Rat))⁻¹ := by
  rw [← Int.toNat_of_nonneg he, Printer.ten_zpow_neg_eq, Int.toNat_natCast]; push_cast; rfl

/-- The numerator and denominator `g` is computed from: `2^{-r} · 10^{-k} = gNum / gDen`. -/
def gNum (k : Int) : Nat :=
  if 0 ≤ -k then (if 0 ≤ r k then 10 ^ (-k).toNat else 10 ^ (-k).toNat * 2 ^ (-(r k)).toNat)
  else 2 ^ (-(r k)).toNat

def gDen (k : Int) : Nat :=
  if 0 ≤ -k then (if 0 ≤ r k then 2 ^ (r k).toNat else 1) else 10 ^ k.toNat

theorem gDen_pos (k : Int) : 0 < gDen k := by
  unfold gDen
  by_cases he : 0 ≤ -k
  · rw [if_pos he]
    by_cases hr : 0 ≤ r k
    · rw [if_pos hr]; exact Nat.pow_pos (by decide)
    · rw [if_neg hr]; decide
  · rw [if_neg he]; exact Nat.pow_pos (by decide)

theorem g_eq (k : Int) : g k = gNum k / gDen k + 1 := by
  unfold g gNum gDen
  by_cases he : 0 ≤ -k
  · rw [if_pos he, if_pos he, if_pos he]
    by_cases hr : 0 ≤ r k
    · rw [if_pos hr, if_pos hr, if_pos hr]
    · rw [if_neg hr, if_neg hr, if_neg hr, Nat.div_one]
  · rw [if_neg he, if_neg he, if_neg he]

/-- `r < 0` when `k > 0`: then `⌊log₂ 10^{-k}⌋ ≤ −1`. -/
theorem r_neg_of_k_pos (k : Int) (hk : 0 < k) : r k < 0 := by
  unfold r flog2pow10Exact
  rw [if_neg (by omega)]
  omega

theorem gNum_div_gDen (k : Int) :
    (gNum k : Rat) / gDen k = (2 : Rat) ^ (-(r k)) * (10 : Rat) ^ (-k) := by
  rw [Reader.div_eq_iff (by exact_mod_cast gDen_pos k)]
  unfold gNum gDen
  by_cases he : 0 ≤ -k
  · rw [if_pos he, if_pos he, ten_zpow_toNat he]
    by_cases hr : 0 ≤ r k
    · rw [if_pos hr, if_pos hr]
      have hA : (2 : Rat) ^ (-(r k)) * (2 : Rat) ^ (r k) = 1 := by
        rw [← Rat.zpow_add (by decide), show -(r k) + r k = 0 by omega, Rat.zpow_zero]
      rw [two_zpow_toNat' hr] at hA
      grind
    · rw [if_neg hr, if_neg hr, two_zpow_toNat' (by omega : 0 ≤ -(r k))]
      push_cast
      grind
  · rw [if_neg he, if_neg he]
    have hr : r k < 0 := r_neg_of_k_pos k (by omega)
    have hA : (10 : Rat) ^ (-k) * (10 : Rat) ^ k = 1 := by
      rw [← Rat.zpow_add (by decide), show -k + k = 0 by omega, Rat.zpow_zero]
    rw [ten_zpow_toNat (by omega : 0 ≤ k)] at hA
    rw [two_zpow_toNat' (by omega : 0 ≤ -(r k))]
    grind

/-- R24: `(g − 1) ≤ 2^{-r} 10^{-k} < g`. -/
theorem g_spec (k : Int) :
    ((g k - 1 : Nat) : Rat) ≤ (2 : Rat) ^ (-(r k)) * (10 : Rat) ^ (-k)
    ∧ (2 : Rat) ^ (-(r k)) * (10 : Rat) ^ (-k) < (g k : Rat) := by
  rw [← gNum_div_gDen, g_eq, Nat.add_sub_cancel]
  have := natDiv_bounds (gNum k) (gDen k) (gDen_pos k)
  push_cast
  exact this

/-- `2^n` as an integer power and as a `Nat`. -/
theorem two_zpow_lit (n : Nat) : (2 : Rat) ^ (n : Int) = ((2 ^ n : Nat) : Rat) := by
  rw [Printer.zpow_natCast_lit]; push_cast; rfl

theorem two_pow_125_lt_g (k : Int) : 2 ^ 125 < g k := by
  obtain ⟨hr, -⟩ := r_spec k
  obtain ⟨-, hg⟩ := g_spec k
  have hp := Printer.two_zpow_pos (-(r k))
  -- `2^125 = 2^{-r} · 2^{r+125} ≤ 2^{-r} · 10^{-k} < g`
  have h1 : ((2 ^ 125 : Nat) : Rat) ≤ (2 : Rat) ^ (-(r k)) * (10 : Rat) ^ (-k) := by
    calc ((2 ^ 125 : Nat) : Rat) = (2 : Rat) ^ (-(r k)) * (2 : Rat) ^ (r k + 125) := by
          rw [← Rat.zpow_add (by decide), show -(r k) + (r k + 125) = ((125 : Nat) : Int) by omega,
            two_zpow_lit]
      _ ≤ (2 : Rat) ^ (-(r k)) * (10 : Rat) ^ (-k) :=
          Rat.mul_le_mul_of_nonneg_left hr (Rat.le_of_lt hp)
  have h2 : ((2 ^ 125 : Nat) : Rat) < (g k : Rat) := lt_of_le_of_lt h1 hg
  exact_mod_cast h2

/-- The paper's table check: every entry is strictly below `2^126`. -/
def gBelowBool : Bool :=
  (List.range 617).all fun i => decide (g ((i : Int) + kMin) < 2 ^ 126)

set_option maxRecDepth 16384 in
theorem gBelow : gBelowBool = true := by decide +kernel

theorem g_lt_two_pow_126 (k : Int) (hlo : kMin ≤ k) (hhi : k ≤ kMax) : g k < 2 ^ 126 := by
  have hAll := gBelow
  unfold gBelowBool at hAll
  rw [List.all_eq_true] at hAll
  have := hAll (k - kMin).toNat (List.mem_range.mpr (by unfold kMin kMax at *; omega))
  rw [show (((k - kMin).toNat : Nat) : Int) + kMin = k by
    rw [Int.toNat_of_nonneg (by omega)]; omega] at this
  exact of_decide_eq_true this

/-! ## The table: `g₁ = g / 2^63`, `g₀ = g mod 2^63` -/

/-- `g₁` for `k = K_min + i`. -/
def g1Table : Array UInt64 :=
  (Array.range 617).map fun (i : Nat) => UInt64.ofNat (g ((i : Int) + kMin) / 2 ^ 63)

/-- `g₀` for `k = K_min + i`. -/
def g0Table : Array UInt64 :=
  (Array.range 617).map fun (i : Nat) => UInt64.ofNat (g ((i : Int) + kMin) % 2 ^ 63)

theorem g1Table_size : g1Table.size = 617 := by simp [g1Table]
theorem g0Table_size : g0Table.size = 617 := by simp [g0Table]

theorem g1Table_getD (k : Int) (hlo : kMin ≤ k) (hhi : k ≤ kMax) :
    (g1Table.getD (k - kMin).toNat 0).toNat = g k / 2 ^ 63 := by
  have hi : (k - kMin).toNat < g1Table.size := by rw [g1Table_size]; unfold kMin kMax at *; omega
  rw [(Array.getElem_eq_getD 0 (h := hi)).symm]
  unfold g1Table at hi ⊢
  rw [Array.getElem_map, Array.getElem_range]
  rw [show (((k - kMin).toNat : Nat) : Int) + kMin = k by rw [Int.toNat_of_nonneg (by omega)]; omega]
  rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt]
  have := g_lt_two_pow_126 k hlo hhi
  omega

theorem g0Table_getD (k : Int) (hlo : kMin ≤ k) (hhi : k ≤ kMax) :
    (g0Table.getD (k - kMin).toNat 0).toNat = g k % 2 ^ 63 := by
  have hi : (k - kMin).toNat < g0Table.size := by rw [g0Table_size]; unfold kMin kMax at *; omega
  rw [(Array.getElem_eq_getD 0 (h := hi)).symm]
  unfold g0Table at hi ⊢
  rw [Array.getElem_map, Array.getElem_range]
  rw [show (((k - kMin).toNat : Nat) : Int) + kMin = k by rw [Int.toNat_of_nonneg (by omega)]; omega]
  rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt]
  have := Nat.mod_lt (g k) (by decide : 0 < 2 ^ 63)
  omega

end Srtfp.Schubfach

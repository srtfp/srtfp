module
/- From the scan to the specification: `Printer.toDecimalBits w` is the
   unique decimal satisfying `Srtfp.Spec.ShortestDecimal w`, and so a
   function is a correct printer iff it is `toDecimalBits`. -/
public import Srtfp.Proofs.Printer.Scan
public import Srtfp.Proofs.Reader.Spec

@[expose] public section

open Srtfp.Compat

namespace Srtfp.Printer

open Srtfp Srtfp.Model Srtfp.Reader
open Float.Model (UnpackedFloat)
open Float.Model.UnpackedFloat (Sign)

variable {m : Nat} {q i : Int} {n : Nat} {wd : UInt64} {d : Decimal}

/-! ## Canonical decimals -/

/-- A canonical decimal other than the signed zero has a positive significand
    with no trailing zero. -/
theorem canonical_sig (hc : d.IsCanonical) (hne : d ≠ ⟨d.sign, 0, 0⟩) :
    1 ≤ d.significand ∧ d.significand % 10 ≠ 0 := by
  rcases hc with ⟨h0, he⟩ | ⟨h0, h10⟩
  · exfalso; apply hne; cases d; simp_all
  · exact ⟨Nat.pos_of_ne_zero h0, h10⟩

/-- Canonical decimals of the same sign and value are equal. -/
theorem canonical_eq_of_value_eq (hc : d.IsCanonical) {d' : Decimal} (hc' : d'.IsCanonical)
    (hs : d.sign = d'.sign) (h1 : 1 ≤ d.significand) (h1' : 1 ≤ d'.significand)
    (hv : (d.significand : Rat) * (10 : Rat) ^ d.exponent
          = (d'.significand : Rat) * (10 : Rat) ^ d'.exponent) : d = d' := by
  have h10 := canonical_sig hc (by intro h; rw [h] at h1; simp at h1)
  have h10' := canonical_sig hc' (by intro h; rw [h] at h1'; simp at h1')
  -- equal exponents, else the coarser one is divisible by ten
  have hexp : d.exponent = d'.exponent := by
    rcases Int.lt_or_le d.exponent d'.exponent with hlt | hge
    · exfalso
      exact not_onGrid_of_finer hlt h10.2 ⟨d'.significand, hv⟩
    rcases Int.lt_or_eq_of_le hge with hgt | heq
    · exfalso
      exact not_onGrid_of_finer hgt h10'.2 ⟨d.significand, hv.symm⟩
    · exact heq.symm
  rw [hexp] at hv
  have hsig : d.significand = d'.significand := by
    have h10p := ten_zpow_pos d'.exponent
    exact_mod_cast (mul_left_inj' (Rat.ne_of_gt h10p)).mp hv
  cases d; cases d'; simp_all

/-- Adding one changes the digit count only at a power of ten. -/
theorem digits_succ_of_not_ten_dvd {a : Nat} (ha : 1 ≤ a) (h : (a + 1) % 10 ≠ 0) :
    digits (a + 1) = digits a := by
  rcases Nat.lt_or_ge (digits a) (digits (a + 1)) with hlt | hge
  · exfalso
    have h1 : 10 ^ digits a ≤ a + 1 :=
      Nat.le_trans (Nat.pow_le_pow_right (by decide) (show digits a ≤ digits (a + 1) - 1 by omega))
        (pow_digits_le (by omega))
    have h2 := lt_pow_digits a
    have h3 : a + 1 = 10 ^ digits a := by omega
    have := digits_pos a
    obtain ⟨j, hj⟩ : ∃ j, digits a = j + 1 := ⟨digits a - 1, by omega⟩
    rw [hj, Nat.pow_succ] at h3
    exact h (by rw [h3]; simp)
  · exact Nat.le_antisymm hge (digits_le_of_le (Nat.le_succ a))

/-! ## What the scan gives us -/

section Nonzero

variable (h : InRange m q) (hs : shortest m q = (n, i))
include h hs

theorem out_facts :
    1 ≤ n ∧ (n = s m q i ∨ n = s m q i + 1)
    ∧ InRv m q ((n : Rat) * (10 : Rat) ^ i) = true
    ∧ (∀ x, OnGrid i x → InRv m q x = true → |v m q - n * (10 : Rat) ^ i| ≤ |v m q - x|)
    ∧ (∀ x, OnGrid i x → InRv m q x = true → x ≠ n * (10 : Rat) ^ i →
         |v m q - n * (10 : Rat) ^ i| = |v m q - x| → n % 2 = 0) :=
  candidate_some h.1 (scan_spec h hs).2.2.2.1

/-- Nothing of `R_v` lies on a coarser grid. -/
theorem no_coarser {j : Int} (hj : i < j) {y : Rat} (hy : OnGrid j y) (hyR : InRv m q y = true) :
    False :=
  no_hit_above h hs hj ⟨y, hy, hyR⟩

/-- The output has no trailing zero. -/
theorem out_ten : n % 10 ≠ 0 :=
  fun h10 => no_coarser h hs (by omega) (onGrid_succ_of_ten_dvd h10) (out_facts h hs).2.2.1

/-! ## Ties -/

/-- Equidistant from `v` as the output and on the same grid: it is a neighbour. -/
theorem tie_eq_u_or_w {y : Rat} (hy : OnGrid i y) (hyR : InRv m q y = true)
    (heq : |v m q - n * (10 : Rat) ^ i| = |v m q - y|) : y = u m q i ∨ y = w m q i := by
  have hm := h.1
  obtain ⟨_, _, _, hclose, _⟩ := out_facts h hs
  have huv := u_le_v (q := q) (i := i) hm
  have hvw := v_lt_w (q := q) (i := i) hm
  rcases grid_point_side hm hy hyR with hyu | ⟨hwy, hwR⟩
  · left
    have huR : InRv m q (u m q i) = true := InRv_convex hyR (InRv_v hm) hyu huv
    have h1 := hclose _ onGrid_u huR
    rw [heq] at h1
    rw [abs_of_nonneg (by grind), abs_of_nonneg (by grind)] at h1
    grind
  · right
    have h1 := hclose _ onGrid_w hwR
    rw [heq] at h1
    rw [abs_of_nonpos (by grind), abs_of_nonpos (by grind)] at h1
    grind

/-- On the output's grid, an exact tie is between the two neighbours `s` and
    `s + 1`; the output is the even one, so the competitor is odd. -/
theorem tie_analysis {f : Nat} (hyR : InRv m q ((f : Rat) * (10 : Rat) ^ i) = true)
    (hfn : f ≠ n) (heq : |v m q - n * (10 : Rat) ^ i| = |v m q - f * (10 : Rat) ^ i|) :
    n % 2 = 0 ∧ f % 2 = 1 := by
  obtain ⟨hn, hcase, hmem, _, htie⟩ := out_facts h hs
  have h10 := ten_zpow_pos i
  have hne : (f : Rat) * (10 : Rat) ^ i ≠ n * (10 : Rat) ^ i := by
    intro e
    have : (f : Rat) = n := (mul_left_inj' (Rat.ne_of_gt h10)).mp e
    exact hfn (by exact_mod_cast this)
  have heven := htie _ ⟨f, rfl⟩ hyR hne heq
  refine ⟨heven, ?_⟩
  rcases tie_eq_u_or_w h hs ⟨f, rfl⟩ hyR heq with hyu | hyw
  · -- `y = u`, so `f = s` and `n = s + 1`
    have hfs : f = s m q i := by
      unfold u at hyu
      exact_mod_cast (mul_left_inj' (Rat.ne_of_gt h10)).mp hyu
    omega
  · -- `y = w`, so `f = s + 1` and `n = s`
    have hfs : f = s m q i + 1 := by
      unfold w at hyw
      have : (f : Rat) = ((s m q i + 1 : Nat) : Rat) := by
        push_cast; exact (mul_left_inj' (Rat.ne_of_gt h10)).mp hyw
      exact_mod_cast this
    omega

/-! ## Competitors -/

omit h hs in
theorem grid_mono {a b : Nat} (hab : a ≤ b) :
    (a : Rat) * (10 : Rat) ^ i ≤ (b : Rat) * (10 : Rat) ^ i :=
  Rat.mul_le_mul_of_nonneg_right (by exact_mod_cast hab) (le_of_lt (ten_zpow_pos i))

omit h hs in
/-- A positive value off the grid lies strictly between two consecutive grid points. -/
theorem between_grid {y : Rat} (hy : 0 < y) (hyng : ¬ OnGrid i y) :
    ∃ dy : Nat, (dy : Rat) * (10 : Rat) ^ i < y ∧ y < ((dy : Rat) + 1) * (10 : Rat) ^ i := by
  have h10 := ten_zpow_pos i
  have hV : 0 < y / (10 : Rat) ^ i := (Rat.lt_div_iff h10).mpr (by rw [Rat.zero_mul]; exact hy)
  have hfl0 : 0 ≤ (y / (10 : Rat) ^ i).floor := by
    rcases Int.lt_or_le (y / (10 : Rat) ^ i).floor 0 with hneg | hnn
    · exfalso; have := Rat.floor_lt_iff.mp hneg; simp at this; grind
    · exact hnn
  refine ⟨(y / (10 : Rat) ^ i).floor.toNat, ?_, ?_⟩
  · have hle := Rat.floor_le (y / (10 : Rat) ^ i)
    have := Rat.mul_le_mul_of_nonneg_right hle (le_of_lt h10)
    rw [Rat.div_mul_cancel (Rat.ne_of_gt h10)] at this
    rw [← Rat.intCast_natCast, Int.toNat_of_nonneg hfl0]
    by_cases hlt : ((y / (10 : Rat) ^ i).floor : Rat) * (10 : Rat) ^ i < y
    · exact hlt
    · exfalso
      have heq := Rat.le_antisymm this (Rat.not_lt.mp hlt)
      apply hyng
      refine ⟨(y / (10 : Rat) ^ i).floor.toNat, ?_⟩
      rw [← Rat.intCast_natCast, Int.toNat_of_nonneg hfl0, heq]
  · have hlt := Rat.lt_floor_add_one (y / (10 : Rat) ^ i)
    have := Rat.mul_lt_mul_of_pos_right hlt h10
    rw [Rat.div_mul_cancel (Rat.ne_of_gt h10)] at this
    rw [← Rat.intCast_natCast, Int.toNat_of_nonneg hfl0]
    push_cast at this ⊢
    exact this

/-- Every grid point of `R_v` has the output's length. -/
theorem same_len {c : Nat} (hc1 : 1 ≤ c)
    (hcR : InRv m q ((c : Rat) * (10 : Rat) ^ i) = true) : digits c = digits n := by
  obtain ⟨hn, _, hmem, _, _⟩ := out_facts h hs
  have hnohit : ∀ e : Nat, InRv m q ((e : Rat) * (10 : Rat) ^ i) = true
      → ¬ OnGrid (i + 1) ((e : Rat) * (10 : Rat) ^ i) :=
    fun e he hg => no_coarser h hs (by omega) hg he
  rcases Nat.lt_or_ge c n with hlt | hge
  · exact same_digits_on_grid hc1 (Nat.le_of_lt hlt)
      (fun e hce hen => hnohit e (InRv_convex hcR hmem (grid_mono hce) (grid_mono hen)))
  · exact (same_digits_on_grid hn hge
      (fun e hne hec => hnohit e (InRv_convex hmem hcR (grid_mono hne) (grid_mono hec)))).symm

/-- The spec's clauses against one competitor `f · 10^b` in `R_v`, other
    than the output; strengthened with the competitor's parity on a tie. -/
theorem competitor {f : Nat} {b : Int} (hf1 : 1 ≤ f) (hf10 : f % 10 ≠ 0)
    (hyR : InRv m q ((f : Rat) * (10 : Rat) ^ b) = true)
    (hne : (f : Rat) * (10 : Rat) ^ b ≠ (n : Rat) * (10 : Rat) ^ i) :
    digits n < digits f
    ∨ (digits f = digits n
       ∧ (|v m q - n * (10 : Rat) ^ i| < |v m q - f * (10 : Rat) ^ b|
          ∨ (|v m q - n * (10 : Rat) ^ i| = |v m q - f * (10 : Rat) ^ b|
             ∧ n % 2 = 0 ∧ f % 2 = 1))) := by
  have hm := h.1
  obtain ⟨hn, hcase, hmem, hclose, _⟩ := out_facts h hs
  have huv := u_le_v (q := q) (i := i) hm
  have hvw := v_lt_w (q := q) (i := i) hm
  have h10 := ten_zpow_pos i
  have hfpos := digits_pos f
  -- a coarser competitor would be a hit on a coarser grid
  have hbi : b ≤ i := by
    rcases Int.lt_or_le i b with hlt | hle
    · exact absurd hyR (fun hR => no_coarser h hs hlt ⟨f, rfl⟩ hR)
    · exact hle
  rcases Int.lt_or_eq_of_le hbi with hb | hb
  · -- finer grid: strictly between two consecutive points of the output's grid
    have hypos : 0 < (f : Rat) * (10 : Rat) ^ b :=
      Rat.mul_pos (by exact_mod_cast hf1) (ten_zpow_pos b)
    obtain ⟨dy, hlo, hhi⟩ := between_grid hypos (not_onGrid_of_finer hb hf10)
    -- the two ways a finer point is strictly farther than the output
    have below (hyu : (f : Rat) * (10 : Rat) ^ b < u m q i) :
        |v m q - n * (10 : Rat) ^ i| < |v m q - f * (10 : Rat) ^ b| := by
      have huR : InRv m q (u m q i) = true := InRv_convex hyR (InRv_v hm) (le_of_lt hyu) huv
      have hcu := hclose _ onGrid_u huR
      rw [abs_of_nonneg (show 0 ≤ v m q - u m q i by grind)] at hcu
      rw [abs_of_nonneg (show 0 ≤ v m q - f * (10 : Rat) ^ b by grind)]
      grind
    rcases Nat.lt_or_ge dy n with hlt | hge
    · rcases Nat.eq_zero_or_pos dy with hdy0 | hdy1
      · -- below every grid point of `R_v`: `10^i ∈ R_v`, so `n` has one digit
        subst hdy0
        have h01 : (((0 : Nat) : Rat) + 1) = ((1 : Nat) : Rat) := by grind
        rw [h01] at hhi
        have h1R : InRv m q ((1 : Nat) * (10 : Rat) ^ i) = true :=
          InRv_convex hyR hmem (le_of_lt hhi) (grid_mono hn)
        have hdig : digits n = 1 := by
          rw [← same_len h hs (by omega) h1R]; exact digits_eq_one_of_le_nine (by omega)
        rcases Nat.lt_or_ge 1 (digits f) with hf | hf
        · left; omega
        · right
          refine ⟨by omega, Or.inl ?_⟩
          -- a one-digit competitor: `f ≤ 9`, so `f · 10^b ≤ 9 · 10^(i-1)`
          have hf9 : f ≤ 9 := by
            have h1 := lt_pow_digits f
            have h2 : digits f = 1 := by omega
            rw [h2] at h1; omega
          have hT := ten_zpow_pos (i - 1)
          have h9 : (f : Rat) * (10 : Rat) ^ b ≤ 9 * (10 : Rat) ^ (i - 1) := by
            have hb' : (10 : Rat) ^ b ≤ (10 : Rat) ^ (i - 1) :=
              zpow_le_zpow_right₀ (by decide) (by omega)
            have hf9' : (f : Rat) ≤ 9 := by exact_mod_cast hf9
            have h1 : (f : Rat) * (10 : Rat) ^ b ≤ (f : Rat) * (10 : Rat) ^ (i - 1) :=
              Rat.mul_le_mul_of_nonneg_left hb' (by exact_mod_cast Nat.zero_le f)
            have h2 : (f : Rat) * (10 : Rat) ^ (i - 1) ≤ 9 * (10 : Rat) ^ (i - 1) :=
              Rat.mul_le_mul_of_nonneg_right hf9' (le_of_lt hT)
            exact le_trans h1 h2
          rcases Nat.eq_zero_or_pos (s m q i) with hs0 | hs1
          · -- `s = 0`: the output is `10^i` and `v < 10^i`; T3 decides
            have hn1 : n = 1 := by omega
            have hTi : (10 : Rat) ^ i = 10 ^ (i - 1) * 10 := by
              rw [← Rat.zpow_add_one (by decide), Int.sub_add_cancel]
            have hw10 : w m q i = (10 : Rat) ^ i := by
              unfold w; rw [hs0, show ((0 : Nat) : Rat) = 0 by simp, Rat.zero_add, Rat.one_mul]
            have hmem1 : InRv m q ((10 : Rat) ^ i) = true := by
              rw [hn1] at hmem; simpa using hmem
            have h9R : InRv m q (9 * (10 : Rat) ^ (i - 1)) = true := by
              apply InRv_convex hyR hmem1 h9
              rw [hTi]; grind
            have hT3 := ten_pow_closer h hmem1 h9R
            rw [hw10] at hvw
            rw [hn1]
            push_cast
            rw [hTi] at hT3 hvw ⊢
            have hvpos : 9 * (10 : Rat) ^ (i - 1) < v m q := by grind
            rw [abs_of_nonpos (by grind), abs_of_nonneg (by grind)]
            grind
          · -- `s ≥ 1`: the competitor lies below `u ≤ v`
            exact below (lt_of_lt_of_le hhi (by unfold u; exact grid_mono (i := i) hs1))
      · -- `(dy + 1) · 10^i ∈ R_v` shares `n`'s length, and `dy + 1` is not a power of ten
        have hd1R : InRv m q (((dy + 1 : Nat) : Rat) * (10 : Rat) ^ i) = true :=
          InRv_convex hyR hmem (by push_cast; exact le_of_lt hhi) (grid_mono (by omega))
        have hdig1 : digits (dy + 1) = digits n := same_len h hs (by omega) hd1R
        have h10' : (dy + 1) % 10 ≠ 0 :=
          fun e => no_coarser h hs (by omega) (onGrid_succ_of_ten_dvd e) hd1R
        have hdig2 := digits_succ_of_not_ten_dvd hdy1 h10'
        have := finer_is_longer hb hdy1 hlo
        left; omega
    · -- above the output: `dy · 10^i ∈ R_v` shares `n`'s length
      have hdR : InRv m q ((dy : Rat) * (10 : Rat) ^ i) = true :=
        InRv_convex hmem hyR (grid_mono hge) (le_of_lt hlo)
      have hdig : digits dy = digits n := same_len h hs (by omega) hdR
      have := finer_is_longer hb (by omega) hlo
      left; omega
  · -- the output's grid: `hclose` decides closeness and `tie_analysis` the ties
    subst hb
    have hfn : f ≠ n := fun e => hne (by rw [e])
    have hle := hclose _ ⟨f, rfl⟩ hyR
    right
    refine ⟨same_len h hs hf1 hyR, ?_⟩
    rcases Rat.eq_or_lt_of_le hle with heq | hlt
    · exact Or.inr ⟨heq, tie_analysis h hs hyR hfn heq⟩
    · exact Or.inl hlt

end Nonzero

/-! ## The output of `toDecimalBits` -/

/-- `Beats`, with the competitor's parity known on a tie: what the output
    achieves, and what makes it unique. -/
def BeatsOdd (w : UInt64) (d d' : Decimal) : Prop :=
  digits d.significand < digits d'.significand
  ∨ (digits d'.significand = digits d.significand
     ∧ (Spec.dist d w < Spec.dist d' w
        ∨ (Spec.dist d w = Spec.dist d' w ∧ d.significand % 2 = 0 ∧ d'.significand % 2 = 1)))

theorem BeatsOdd.beats {w : UInt64} {d d' : Decimal} (h : BeatsOdd w d d') : Spec.Beats w d d' := by
  rcases h with h | ⟨h1, h2 | ⟨h2, h3, -⟩⟩
  · exact .shorter h
  · exact .closer h1 h2
  · exact .even h1 h2 h3

/-- Nothing beats what beats it with an odd tie. -/
theorem BeatsOdd.not_beats {w : UInt64} {d d' : Decimal} (h : BeatsOdd w d d')
    (h' : Spec.Beats w d' d) : False := by
  rcases h with h | ⟨h1, h2 | ⟨h2, h3, h4⟩⟩ <;> rcases h' with h' | ⟨h1', h2'⟩ | ⟨h1', h2', h3'⟩ <;> grind

/-- Finite nonzero words: the output is canonical, reads back, and beats
    every competitor. -/
theorem nonzero_output {s : Sign} {hm : 0 < m} (hu : Spec.unpack wd = .finite s m q hm) :
    ∃ d₀, toDecimalBits wd = .ok d₀ ∧ d₀.IsCanonical ∧ Reader.ofDecimalBits d₀ = wd
      ∧ ∀ d' : Decimal, d' ≠ d₀ → d'.IsCanonical → Reader.ofDecimalBits d' = wd →
          BeatsOdd wd d₀ d' := by
  have h : InRange m q := ⟨hm, legal_of_unpack hu⟩
  have hfin : (Spec.unpack wd).isFinite = true := by rw [hu]; rfl
  have hri := reads_to_finite_iff hu
  have hdist : ∀ z : Decimal, Spec.dist z wd = |Spec.signVal s * v m q
      - Spec.signVal z.sign * ((z.significand : Rat) * (10 : Rat) ^ z.exponent)| := by
    intro z; rw [Reader.dist_eq z hfin, hu]; rfl
  rcases hsh : shortest m q with ⟨n, i⟩
  obtain ⟨hn, _, hmem, _, _⟩ := out_facts h hsh
  have h10 := out_ten h hsh
  have hcan : (⟨s, n, i⟩ : Decimal).IsCanonical :=
    Or.inr ⟨Nat.pos_iff_ne_zero.mp hn, h10⟩
  refine ⟨⟨s, n, i⟩, ?_, hcan, ?_, ?_⟩
  · unfold toDecimalBits; rw [hu]; simp only [hsh]
  · exact (hri _).mpr ⟨rfl, hmem⟩
  · intro d' hne hc' hrt'
    obtain ⟨hsign', hmem'⟩ := (hri d').mp hrt'
    have hf1 : 1 ≤ d'.significand := by
      rcases Nat.eq_zero_or_pos d'.significand with h0 | h0
      · exfalso
        rw [h0, show ((0 : Nat) : Rat) = 0 by simp, Rat.zero_mul] at hmem'
        have := (le_of_InRv hmem').1
        have := vl_pos (q := q) hm
        grind
      · exact h0
    have hf10 : d'.significand % 10 ≠ 0 :=
      (canonical_sig hc' (by intro e; rw [e] at hf1; simp at hf1)).2
    have hvne : (d'.significand : Rat) * (10 : Rat) ^ d'.exponent ≠ (n : Rat) * (10 : Rat) ^ i := by
      intro e
      apply hne
      exact canonical_eq_of_value_eq hc' hcan (by rw [hsign']) hf1 hn e
    have hc := competitor h hsh hf1 hf10 hmem' hvne
    have hd₀ : Spec.dist ⟨s, n, i⟩ wd = |v m q - n * (10 : Rat) ^ i| := by
      rw [hdist]; exact dist_of_sign _ _ _
    have hd' : Spec.dist d' wd = |v m q - d'.significand * (10 : Rat) ^ d'.exponent| := by
      rw [hdist, hsign']; exact dist_of_sign _ _ _
    unfold BeatsOdd
    simp only
    rw [hd₀, hd']
    exact hc

/-- Zero words: the signed zero is the output; every competitor is farther. -/
theorem zero_output {s : Sign} (hu : Spec.unpack wd = .zero s) :
    ∃ d₀, toDecimalBits wd = .ok d₀ ∧ d₀.IsCanonical ∧ Reader.ofDecimalBits d₀ = wd
      ∧ ∀ d' : Decimal, d' ≠ d₀ → d'.IsCanonical → Reader.ofDecimalBits d' = wd →
          BeatsOdd wd d₀ d' := by
  have hfin : (Spec.unpack wd).isFinite = true := by rw [hu]; rfl
  have hri := reads_to_iff hfin
  have hmq : mq (Spec.unpack wd) = (0, -1074) := by rw [hu]; rfl
  have hus : usign (Spec.unpack wd) = s := by rw [hu]; rfl
  rw [hmq, hus] at hri
  have hP := two_zpow_pos (-1074 : Int)
  have hv0 : v 0 (-1074) = 0 := by
    unfold v; rw [show ((0 : Nat) : Rat) = 0 by simp, Rat.zero_mul]
  refine ⟨⟨s, 0, 0⟩, ?_, Or.inl ⟨rfl, rfl⟩, ?_, ?_⟩
  · unfold toDecimalBits; rw [hu]
  · rw [hri]
    refine ⟨rfl, ?_⟩
    have h0 : ((⟨s, 0, 0⟩ : Decimal).significand : Rat)
        * (10 : Rat) ^ (⟨s, 0, 0⟩ : Decimal).exponent = 0 := by simp
    rw [h0]
    apply InRv_of_strict
    · unfold vl; rw [if_neg (by decide), show ((0 : Nat) : Rat) = 0 by simp]
      generalize (2 : Rat) ^ (-1074 : Int) = P at hP ⊢; grind
    · unfold vr; rw [show ((0 : Nat) : Rat) = 0 by simp]
      generalize (2 : Rat) ^ (-1074 : Int) = P at hP ⊢; grind
  · intro d' hne hc' hrt'
    obtain ⟨hsign', hmem'⟩ := (hri d').mp hrt'
    have hf1 : 1 ≤ d'.significand := by
      rcases Nat.eq_zero_or_pos d'.significand with h0 | hpos
      · exfalso
        apply hne
        rcases hc' with ⟨_, he⟩ | ⟨hne0, _⟩
        · cases d'; simp_all
        · exact absurd h0 hne0
      · exact hpos
    have hneg : ∀ a b : Rat, a * 0 - b = -b := fun a b => by grind
    have hd₀ : Spec.dist ⟨s, 0, 0⟩ wd = 0 := by
      rw [Reader.dist_eq _ hfin, hmq, hus, hv0, Rat.mul_zero, show ((0 : Nat) : Rat) = 0 by simp,
        Rat.zero_mul, Rat.mul_zero, sub_zero]
      exact abs_zero
    have hd' : 0 < Spec.dist d' wd := by
      rw [Reader.dist_eq _ hfin, hmq, hus, hv0, hsign', hneg, abs_neg, sign_mul_abs]
      exact abs_pos.mpr (Rat.ne_of_gt (Rat.mul_pos (by exact_mod_cast hf1) (ten_zpow_pos _)))
    rcases Nat.lt_or_ge 1 (digits d'.significand) with hd | hd
    · left; rw [digits_zero]; exact hd
    · right
      have := digits_pos d'.significand
      exact ⟨by rw [digits_zero]; omega, Or.inl (by rw [hd₀]; exact hd')⟩

/-! ## The specification -/

/-- The output beats every competitor, with the competitor's parity on a tie. -/
theorem output_beats (hw : (Spec.unpack wd).isFinite = true) :
    ∃ d₀, toDecimalBits wd = .ok d₀ ∧ d₀.IsCanonical ∧ Reader.ofDecimalBits d₀ = wd
      ∧ ∀ d' : Decimal, d' ≠ d₀ → d'.IsCanonical → Reader.ofDecimalBits d' = wd →
          BeatsOdd wd d₀ d' := by
  rcases hu : Spec.unpack wd with s | _ | s | ⟨s, m, q, hm⟩
  · rw [hu] at hw; simp [UnpackedFloat.isFinite] at hw
  · rw [hu] at hw; simp [UnpackedFloat.isFinite] at hw
  · exact zero_output hu
  · exact nonzero_output hu

theorem toDecimalBits_spec (hw : (Spec.unpack wd).isFinite = true) :
    ∃ d, toDecimalBits wd = .ok d ∧ Spec.ShortestDecimal wd d :=
  let ⟨d₀, h₀, hc, hrt, hb⟩ := output_beats hw
  ⟨d₀, h₀, hc, (readsTo_iff d₀ wd).mpr hrt,
    fun d' hne hc' hrt' => (hb d' hne hc' ((readsTo_iff d' wd).mp hrt')).beats⟩

/-- Anything satisfying the specification is the output. -/
theorem eq_output_of_shortest (hw : (Spec.unpack wd).isFinite = true) {d d₀ : Decimal}
    (h₀ : toDecimalBits wd = .ok d₀) (hd : Spec.ShortestDecimal wd d) : d = d₀ := by
  by_cases hne : d = d₀
  · exact hne
  obtain ⟨d₁, h₁, hc₁, hrt₁, hb⟩ := output_beats hw
  rw [h₁] at h₀; obtain rfl := Except.ok.inj h₀
  exact ((hb d hne hd.canonical ((readsTo_iff d wd).mp hd.roundTrip)).not_beats
    (hd.shortest d₁ (Ne.symm hne) hc₁ ((readsTo_iff d₁ wd).mpr hrt₁))).elim

theorem shortestDecimal_exists_unique (w : UInt64) (h_fin : (Spec.unpack w).isFinite = true) :
    ∃ d : Decimal, Spec.ShortestDecimal w d ∧ ∀ d' : Decimal, Spec.ShortestDecimal w d' → d' = d :=
  let ⟨d, h₀, hd⟩ := toDecimalBits_spec h_fin
  ⟨d, hd, fun _ hd' => eq_output_of_shortest h_fin h₀ hd'⟩

/-- `toDecimalBits` is a correct printer. -/
theorem correctPrinter_toDecimalBits : Spec.CorrectPrinter toDecimalBits where
  nan w h := by unfold toDecimalBits; rw [h]
  inf w s h := by unfold toDecimalBits; rw [h]; cases s <;> rfl
  finite w hw := toDecimalBits_spec hw

/-- **The printer theorem.** A function is a correct printer iff it is
`toDecimalBits`. -/
theorem correctPrinter_iff_toDecimal (p : UInt64 → Except String Decimal) :
    Spec.CorrectPrinter p ↔ p = toDecimalBits := by
  constructor
  · intro hp
    funext w
    have fin (hfin : (Spec.unpack w).isFinite = true) : p w = toDecimalBits w := by
      obtain ⟨d, hd, hds⟩ := hp.finite w hfin
      obtain ⟨d', hd', -⟩ := toDecimalBits_spec hfin
      rw [hd, hd', eq_output_of_shortest hfin hd' hds]
    rcases hu : Spec.unpack w with s | _ | s | ⟨s, m, e, hm⟩
    · rw [hp.inf w s hu, correctPrinter_toDecimalBits.inf w s hu]
    · rw [hp.nan w hu, correctPrinter_toDecimalBits.nan w hu]
    · exact fin (by rw [hu]; rfl)
    · exact fin (by rw [hu]; rfl)
  · rintro rfl
    exact correctPrinter_toDecimalBits

end Srtfp.Printer

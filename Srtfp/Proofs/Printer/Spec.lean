module
/- From the scan to the specification: `Printer.toDecimalBits w` is the
   unique decimal satisfying `Srtfp.Spec.ShortestDecimal w`, and so a
   function is a correct printer iff it is `toDecimalBits`. -/
public import Srtfp.Spec
public import Srtfp.Proofs.Printer.Scan
public import Srtfp.Proofs.Reader.Spec
public import Srtfp.Proofs.Decimal.Canonical
public import Srtfp.Proofs.Decimal

@[expose] public section

open Srtfp.Compat

namespace Srtfp.Printer

open Srtfp Srtfp.Float Srtfp.Clinger

variable {m : Nat} {q i : Int} {n : Nat} {wd : UInt64} {d : Decimal}

/-! ## Vocabulary bridges -/

theorem inRange_of_decode (hw : Word.isFinite wd = true) (hm : 1 ≤ (Word.decode wd).m) :
    InRange (Word.decode wd).m (Word.decode wd).q := by
  have := decode_legal hw
  unfold Legal at this; unfold InRange; omega

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

theorem mk'_of_not_ten_dvd (sign : Bool) (hn : 1 ≤ n) (h10 : n % 10 ≠ 0) :
    Decimal.mk' sign n i = ⟨sign, n, i⟩ :=
  Decimal.mk'_eq_self_of_isCanonical (Or.inr ⟨Nat.pos_iff_ne_zero.mp hn, h10⟩)

theorem mk'_ten (sign : Bool) : Decimal.mk' sign 10 i = ⟨sign, 1, i + 1⟩ := by
  unfold Decimal.mk' Decimal.canonical
  dsimp only
  rw [if_neg (by decide : (10 : Nat) ≠ 0), Decimal.canonicaliseAux_div 10 i (by decide) (by decide),
      Decimal.canonicaliseAux_not_div 1 (i + 1) (by decide) (by decide)]

theorem digits_eq_one_of_le_nine (hn : n ≤ 9) : digits n = 1 := by
  rw [Spec.digits, if_pos (by omega)]

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
    1 ≤ n ∧ 1 ≤ s m q i ∧ (n = s m q i ∨ n = s m q i + 1)
    ∧ InRv m q ((n : Rat) * (10 : Rat) ^ i) = true
    ∧ (∀ x, OnGrid i x → InRv m q x = true → |v m q - n * (10 : Rat) ^ i| ≤ |v m q - x|)
    ∧ (∀ x, OnGrid i x → InRv m q x = true → x ≠ n * (10 : Rat) ^ i →
         |v m q - n * (10 : Rat) ^ i| = |v m q - x| → n % 2 = 0) := by
  obtain ⟨hn, _, _, hc, _⟩ := scan_spec h hs
  obtain ⟨_, hs1, hcase, hmem, hclose, htie⟩ := candidate_some h.1 hc
  exact ⟨hn, hs1, hcase, hmem, hclose, htie⟩

/-- A hit on the next grid means that grid is coarser than `v`'s leading digit. -/
theorem next_zero_of_hit {y : Rat} (hy : OnGrid (i + 1) y) (hyR : InRv m q y = true) :
    s m q (i + 1) = 0 := by
  rcases no_hit_above h hs (show i < i + 1 by omega) with h0 | hno
  · exact h0
  · exact absurd ⟨y, hy, hyR⟩ hno

omit hs in
theorem s_le_nine_of_next_zero (hnext : s m q (i + 1) = 0) : s m q i ≤ 9 := by
  have hm := h.1
  have hv : v m q < (10 : Rat) ^ (i + 1) :=
    Rat.not_le.mp (fun hle => absurd ((s_pos_iff (q := q) (i := i + 1) hm).mpr hle) (by omega))
  have hu := u_le_v (q := q) (i := i) hm
  unfold u at hu
  rw [Rat.zpow_add_one (by decide)] at hv
  have h10 := ten_zpow_pos i
  have : (s m q i : Rat) * 10 ^ i < 10 * 10 ^ i := by grind
  have : (s m q i : Rat) < 10 := Rat.lt_of_mul_lt_mul_right this (le_of_lt h10)
  have : s m q i < 10 := by exact_mod_cast this
  omega

theorem n_le_ten_of_next_zero (hnext : s m q (i + 1) = 0) : n ≤ 10 := by
  have := s_le_nine_of_next_zero h hnext
  rcases (out_facts h hs).2.2.1 with e | e <;> omega

/-- The output significand has no trailing zero, except for the single
    case `n = 10`, which arises only when the next grid is above `v`. -/
theorem output_form : n % 10 ≠ 0 ∨ (n = 10 ∧ s m q (i + 1) = 0) := by
  obtain ⟨hn, _, _, hmem, _, _⟩ := out_facts h hs
  by_cases h10 : n % 10 = 0
  · right
    have hnext := next_zero_of_hit h hs (onGrid_succ_of_ten_dvd h10) hmem
    have := n_le_ten_of_next_zero h hs hnext
    exact ⟨by omega, hnext⟩
  · exact Or.inl h10

/-- The canonical significand of the output. -/
def outSig (n : Nat) : Nat := if n = 10 then 1 else n

omit h hs in
theorem outSig_of_ne_ten (h10 : n ≠ 10) : outSig n = n := by unfold outSig; rw [if_neg h10]

theorem out_decimal (sgn : Bool) :
    Decimal.mk' sgn n i = if n = 10 then ⟨sgn, 1, i + 1⟩ else ⟨sgn, n, i⟩ := by
  rcases output_form h hs with h10 | ⟨rfl, _⟩
  · rw [if_neg (by omega)]; exact mk'_of_not_ten_dvd sgn (out_facts h hs).1 h10
  · rw [if_pos rfl]; exact mk'_ten sgn

theorem out_sig (sgn : Bool) : (Decimal.mk' sgn n i).significand = outSig n := by
  rw [out_decimal h hs]; unfold outSig; split <;> rfl

theorem out_sign (sgn : Bool) : (Decimal.mk' sgn n i).sign = sgn := by
  rw [out_decimal h hs]; split <;> rfl

theorem out_value (sgn : Bool) :
    ((Decimal.mk' sgn n i).significand : Rat) * (10 : Rat) ^ (Decimal.mk' sgn n i).exponent
      = (n : Rat) * (10 : Rat) ^ i := by
  rw [out_decimal h hs]
  split
  · rename_i h10; subst h10
    show (1 : Rat) * 10 ^ (i + 1) = (10 : Rat) * 10 ^ i
    rw [Rat.zpow_add_one (by decide)]; grind
  · rfl

theorem outSig_digits (hnext : s m q (i + 1) = 0) : digits (outSig n) = 1 := by
  have := n_le_ten_of_next_zero h hs hnext
  unfold outSig; split
  · exact digits_eq_one_of_le_nine (by omega)
  · exact digits_eq_one_of_le_nine (by omega)

/-! ## Ties -/

/-- Equidistant from `v` as the output and on the same grid: it is a neighbour. -/
theorem tie_eq_u_or_w {y : Rat} (hy : OnGrid i y) (hyR : InRv m q y = true)
    (heq : |v m q - n * (10 : Rat) ^ i| = |v m q - y|) : y = u m q i ∨ y = w m q i := by
  have hm := h.1
  obtain ⟨_, _, _, _, hclose, _⟩ := out_facts h hs
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
    `s + 1`; the output is the even one, so the competitor is odd, and the
    `9`/`10` tie never happens. -/
theorem tie_analysis {f : Nat} (hyR : InRv m q ((f : Rat) * (10 : Rat) ^ i) = true)
    (hfn : f ≠ n) (heq : |v m q - n * (10 : Rat) ^ i| = |v m q - f * (10 : Rat) ^ i|) :
    n % 2 = 0 ∧ f % 2 = 1 ∧ n ≠ 10 := by
  have hm := h.1
  obtain ⟨hn, hs1, hcase, hmem, _, htie⟩ := out_facts h hs
  have hne : (f : Rat) * (10 : Rat) ^ i ≠ n * (10 : Rat) ^ i := by
    intro e
    have h10 := ten_zpow_pos i
    have : (f : Rat) = n := (mul_left_inj' (Rat.ne_of_gt h10)).mp e
    exact hfn (by exact_mod_cast this)
  have heven := htie _ ⟨f, rfl⟩ hyR hne heq
  have h10 := ten_zpow_pos i
  rcases tie_eq_u_or_w h hs ⟨f, rfl⟩ hyR heq with hyu | hyw
  · -- `y = u`, so `f = s` and `n = s + 1`
    have hfs : f = s m q i := by
      unfold u at hyu
      exact_mod_cast (mul_left_inj' (Rat.ne_of_gt h10)).mp hyu
    have hn' : n = s m q i + 1 := by rcases hcase with e | e <;> omega
    refine ⟨heven, by omega, ?_⟩
    -- `n = 10` would be the `9`/`10` tie
    intro h10n
    apply nine_ten_tie_impossible h (i := i)
    have hs9 : s m q i = 9 := by omega
    have hu9 : u m q i = 9 * (10 : Rat) ^ i := by unfold u; rw [hs9]; push_cast; rfl
    have hw10 : w m q i = 10 * (10 : Rat) ^ i := by unfold w; rw [hs9]; push_cast; grind
    refine ⟨by rw [← hu9, ← hyu]; exact hyR, by rw [hn', hs9] at hmem; push_cast at hmem; exact hmem, ?_⟩
    -- the tie, unfolded
    rw [hfs, hs9, hn', hs9] at heq
    push_cast at heq
    have huv := u_le_v (q := q) (i := i) hm
    have hvw := v_lt_w (q := q) (i := i) hm
    rw [hu9] at huv; rw [hw10] at hvw
    rw [abs_of_nonpos (by grind), abs_of_nonneg (by grind)] at heq
    grind
  · -- `y = w`, so `f = s + 1` and `n = s`
    have hfs : f = s m q i + 1 := by
      unfold w at hyw
      have : (f : Rat) = ((s m q i + 1 : Nat) : Rat) := by
        push_cast; exact (mul_left_inj' (Rat.ne_of_gt h10)).mp hyw
      exact_mod_cast this
    have hn' : n = s m q i := by rcases hcase with e | e <;> omega
    refine ⟨heven, by omega, ?_⟩
    intro h10n
    -- `n = s = 10` puts `u` on the next grid; then `s ≤ 9`
    have hnext := next_zero_of_hit h hs (onGrid_succ_of_ten_dvd (by rw [h10n])) hmem
    have := s_le_nine_of_next_zero h hnext
    omega

/-! ## Competitors -/

omit h hs in
theorem grid_mono {a b : Nat} (hab : a ≤ b) :
    (a : Rat) * (10 : Rat) ^ i ≤ (b : Rat) * (10 : Rat) ^ i :=
  Rat.mul_le_mul_of_nonneg_right (by exact_mod_cast hab) (le_of_lt (ten_zpow_pos i))

omit h hs in
theorem grid_mono' {a b : Nat} (hab : a + 1 ≤ b) :
    ((a : Rat) + 1) * (10 : Rat) ^ i ≤ (b : Rat) * (10 : Rat) ^ i := by
  have := grid_mono (i := i) hab; push_cast at this; exact this

omit h hs in
theorem grid_mono'' {a b : Nat} (hab : a ≤ b + 1) :
    (a : Rat) * (10 : Rat) ^ i ≤ ((b : Rat) + 1) * (10 : Rat) ^ i := by
  have := grid_mono (i := i) hab; push_cast at this; exact this

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

/-- With no hit on the next grid, every grid point of `R_v` has the output's length. -/
theorem same_len (hnext : ¬ s m q (i + 1) = 0) {c : Nat} (hc1 : 1 ≤ c)
    (hcR : InRv m q ((c : Rat) * (10 : Rat) ^ i) = true) : digits c = digits n := by
  obtain ⟨hn, _, _, hmem, _, _⟩ := out_facts h hs
  have hnohit : ∀ e : Nat, InRv m q ((e : Rat) * (10 : Rat) ^ i) = true
      → ¬ OnGrid (i + 1) ((e : Rat) * (10 : Rat) ^ i) :=
    fun e he hg => hnext (next_zero_of_hit h hs hg he)
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
    digits (outSig n) < digits f
    ∨ (digits f = digits (outSig n)
       ∧ (|v m q - n * (10 : Rat) ^ i| < |v m q - f * (10 : Rat) ^ b|
          ∨ (|v m q - n * (10 : Rat) ^ i| = |v m q - f * (10 : Rat) ^ b|
             ∧ outSig n % 2 = 0 ∧ f % 2 = 1))) := by
  have hm := h.1
  obtain ⟨hn, hs1, hcase, hmem, hclose, _⟩ := out_facts h hs
  have huv := u_le_v (q := q) (i := i) hm
  have hvw := v_lt_w (q := q) (i := i) hm
  have h10 := ten_zpow_pos i
  have hfpos := digits_pos f
  -- with no hit on the next grid, grid points in `R_v` avoid it and share `n`'s length
  have nohit_case (hnext : ¬ s m q (i + 1) = 0) :
      (∀ c : Nat, InRv m q ((c : Rat) * (10 : Rat) ^ i) = true → ¬ OnGrid (i + 1) ((c : Rat) * (10 : Rat) ^ i))
      ∧ n % 10 ≠ 0 ∧ outSig n = n := by
    have hnohit : ∀ c : Nat, InRv m q ((c : Rat) * (10 : Rat) ^ i) = true
        → ¬ OnGrid (i + 1) ((c : Rat) * (10 : Rat) ^ i) :=
      fun c hc hg => hnext (next_zero_of_hit h hs hg hc)
    have hn10 : n % 10 ≠ 0 := fun e => hnohit n hmem (onGrid_succ_of_ten_dvd e)
    exact ⟨hnohit, hn10, outSig_of_ne_ten (by omega)⟩
  by_cases hyg : OnGrid i ((f : Rat) * (10 : Rat) ^ b)
  · -- on the output's grid: `hclose` decides closeness and `tie_analysis` the ties
    obtain ⟨f', hf'⟩ := hyg
    have hbi : i ≤ b := by
      rcases Int.lt_or_le b i with hlt | hle
      · exact absurd ⟨f', hf'⟩ (not_onGrid_of_finer hlt hf10)
      · exact hle
    have hff' : f' = f * 10 ^ (b - i).toNat := by
      rw [ten_zpow_split hbi] at hf'
      have : (f' : Rat) = ((f * 10 ^ (b - i).toNat : Nat) : Rat) := by
        push_cast
        exact (mul_left_inj' (Rat.ne_of_gt h10)).mp (by rw [← hf']; grind)
      exact_mod_cast this
    have hyR' : InRv m q ((f' : Rat) * (10 : Rat) ^ i) = true := by rw [← hf']; exact hyR
    have hf'n : f' ≠ n := fun e => hne (by rw [hf', e])
    have hle := hclose _ ⟨f', hf'⟩ hyR
    -- a tie forces `b = i` (an odd `f'` is not a multiple of ten), with the parities of `tie_analysis`
    have tie (heq : |v m q - n * (10 : Rat) ^ i| = |v m q - f * (10 : Rat) ^ b|) :
        n % 2 = 0 ∧ f % 2 = 1 ∧ n ≠ 10 := by
      obtain ⟨he, hfo, hn10⟩ := tie_analysis h hs hyR' hf'n (by rw [← hf']; exact heq)
      rcases Int.lt_or_eq_of_le hbi with hlt | heq'
      · exfalso
        obtain ⟨k, hk⟩ : ∃ k, (b - i).toNat = k + 1 := ⟨(b - i).toNat - 1, by omega⟩
        rw [hff', hk, Nat.pow_succ] at hfo
        have h2 : 2 ∣ f * (10 ^ k * 10) :=
          Nat.dvd_trans ⟨5, rfl⟩ (Nat.dvd_trans (Nat.dvd_mul_left 10 (10 ^ k)) (Nat.dvd_mul_left _ f))
        omega
      · have h0 : (b - i).toNat = 0 := by omega
        rw [h0, Nat.pow_zero, Nat.mul_one] at hff'
        subst hff'
        exact ⟨he, hfo, hn10⟩
    have close_or_tie :
        |v m q - n * (10 : Rat) ^ i| < |v m q - f * (10 : Rat) ^ b|
        ∨ (|v m q - n * (10 : Rat) ^ i| = |v m q - f * (10 : Rat) ^ b|
           ∧ outSig n % 2 = 0 ∧ f % 2 = 1) := by
      by_cases hlt : |v m q - n * (10 : Rat) ^ i| < |v m q - f * (10 : Rat) ^ b|
      · exact Or.inl hlt
      · have heq := Rat.le_antisymm hle (Rat.not_lt.mp hlt)
        obtain ⟨he, hfo, hn10⟩ := tie heq
        exact Or.inr ⟨heq, by rw [outSig_of_ne_ten hn10]; exact he, hfo⟩
    by_cases hnext : s m q (i + 1) = 0
    · have hD := outSig_digits h hs hnext
      rcases Nat.lt_or_ge 1 (digits f) with hf | hf
      · left; omega
      · right; exact ⟨by omega, close_or_tie⟩
    · obtain ⟨-, -, hD⟩ := nohit_case hnext
      -- a coarser competitor would be a hit on the next grid
      have hbi' : b = i := by
        rcases Int.lt_or_eq_of_le hbi with hlt | heq'
        · exact absurd (next_zero_of_hit h hs (onGrid_of_le (by omega) ⟨f, rfl⟩) hyR) hnext
        · exact heq'.symm
      subst hbi'
      have hdig : digits f = digits n := same_len h hs hnext hf1 hyR
      right
      rw [hD]
      exact ⟨hdig, by have := close_or_tie; rw [hD] at this; exact this⟩
  · -- off the output's grid: strictly between two of its points
    have hb : b < i := by
      rcases Int.lt_or_le b i with hlt | hle
      · exact hlt
      · exact absurd (onGrid_of_le hle ⟨f, rfl⟩) hyg
    have hyng := hyg
    have hypos : 0 < (f : Rat) * (10 : Rat) ^ b :=
      Rat.mul_pos (by exact_mod_cast hf1) (ten_zpow_pos b)
    obtain ⟨dy, hlo, hhi⟩ := between_grid hypos hyng
    -- the two ways a finer point is strictly farther than the output
    have below (hyu : (f : Rat) * (10 : Rat) ^ b < u m q i) :
        |v m q - n * (10 : Rat) ^ i| < |v m q - f * (10 : Rat) ^ b| := by
      have huR : InRv m q (u m q i) = true := InRv_convex hyR (InRv_v hm) (le_of_lt hyu) huv
      have hcu := hclose _ onGrid_u huR
      rw [abs_of_nonneg (show 0 ≤ v m q - u m q i by grind)] at hcu
      rw [abs_of_nonneg (show 0 ≤ v m q - f * (10 : Rat) ^ b by grind)]
      grind
    have above (hwy : w m q i < (f : Rat) * (10 : Rat) ^ b) :
        |v m q - n * (10 : Rat) ^ i| < |v m q - f * (10 : Rat) ^ b| := by
      have hwR : InRv m q (w m q i) = true := InRv_convex (InRv_v hm) hyR (le_of_lt hvw) (le_of_lt hwy)
      have hcw := hclose _ onGrid_w hwR
      rw [abs_of_nonpos (show v m q - w m q i ≤ 0 by grind)] at hcw
      rw [abs_of_nonpos (show v m q - f * (10 : Rat) ^ b ≤ 0 by grind)]
      grind
    have finish_one (hD : digits (outSig n) = 1)
        (hstrict : |v m q - n * (10 : Rat) ^ i| < |v m q - f * (10 : Rat) ^ b|) :
        digits (outSig n) < digits f
        ∨ (digits f = digits (outSig n)
           ∧ (|v m q - n * (10 : Rat) ^ i| < |v m q - f * (10 : Rat) ^ b|
              ∨ (|v m q - n * (10 : Rat) ^ i| = |v m q - f * (10 : Rat) ^ b|
                 ∧ outSig n % 2 = 0 ∧ f % 2 = 1))) := by
      rcases Nat.lt_or_ge 1 (digits f) with hf | hf
      · left; omega
      · right; exact ⟨by omega, Or.inl hstrict⟩
    by_cases hnext : s m q (i + 1) = 0
    · have hD := outSig_digits h hs hnext
      rcases Nat.lt_trichotomy dy (s m q i) with hlt | heq | hgt
      · exact finish_one hD (below (lt_of_lt_of_le hhi (grid_mono' (by omega))))
      · subst heq
        have := finer_is_longer hb hs1 hlo
        have := digits_pos (s m q i)
        left; omega
      · exact finish_one hD (above (lt_of_le_of_lt (grid_mono' (by omega)) hlo))
    · obtain ⟨hnohit, hn10, hD⟩ := nohit_case hnext
      rw [hD]
      rcases Nat.lt_or_ge dy n with hlt | hge
      · rcases Nat.eq_zero_or_pos dy with hdy0 | hdy1
        · -- below every grid point of `R_v`: `1 · 10^i ∈ R_v`, so `n` has one digit
          subst hdy0
          have h01 : (((0 : Nat) : Rat) + 1) = ((1 : Nat) : Rat) := by simp [Rat.zero_add]
          rw [h01] at hhi
          have h1R : InRv m q ((1 : Nat) * (10 : Rat) ^ i) = true :=
            InRv_convex hyR hmem (le_of_lt hhi) (grid_mono hn)
          have hdig : digits n = 1 := by
            rw [← same_len h hs hnext (by omega) h1R]; exact digits_eq_one_of_le_nine (by omega)
          have hstrict := below (lt_of_lt_of_le hhi (grid_mono (i := i) hs1))
          rcases Nat.lt_or_ge 1 (digits f) with hf | hf
          · left; omega
          · right; exact ⟨by omega, Or.inl hstrict⟩
        · -- `(dy + 1) · 10^i ∈ R_v` shares `n`'s length, and `dy + 1` is not a power of ten
          have hd1R : InRv m q (((dy + 1 : Nat) : Rat) * (10 : Rat) ^ i) = true :=
            InRv_convex hyR hmem (by push_cast; exact le_of_lt hhi) (grid_mono (by omega))
          have hdig1 : digits (dy + 1) = digits n := same_len h hs hnext (by omega) hd1R
          have h10' : (dy + 1) % 10 ≠ 0 := fun e => hnohit (dy + 1) hd1R (onGrid_succ_of_ten_dvd e)
          have hdig2 := digits_succ_of_not_ten_dvd hdy1 h10'
          have := finer_is_longer hb hdy1 hlo
          left; omega
      · -- above the output: `dy · 10^i ∈ R_v` shares `n`'s length
        have hdR : InRv m q ((dy : Rat) * (10 : Rat) ^ i) = true :=
          InRv_convex hmem hyR (grid_mono hge) (le_of_lt hlo)
        have hdig : digits dy = digits n := same_len h hs hnext (by omega) hdR
        have := finer_is_longer hb (by omega) hlo
        left; omega

end Nonzero

/-! ## The output of `toDecimalBits` -/

theorem isInf_false_of_isFinite (hw : Word.isFinite wd = true) : Word.isInf wd = false := by
  unfold Word.isFinite at hw; unfold Word.isInf
  simp at hw ⊢; omega

theorem toDecimalBits_of_finite (hw : Word.isFinite wd = true) :
    toDecimalBits wd =
      (if (Word.decode wd).m = 0 then .ok ⟨(Word.decode wd).sign, 0, 0⟩
       else
         let (sig, exp) := shortest (Word.decode wd).m (Word.decode wd).q
         .ok (Decimal.mk' (Word.decode wd).sign sig exp)) := by
  unfold toDecimalBits
  rw [word_isNaN_false_of_isFinite wd hw, isInf_false_of_isFinite hw]
  simp only [Bool.false_eq_true, if_false]

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

/-- Nonzero words: the output is canonical, reads back, and beats every
    competitor. -/
theorem nonzero_output (hw : Word.isFinite wd = true) (hm : 1 ≤ (Word.decode wd).m) :
    ∃ d₀, toDecimalBits wd = .ok d₀ ∧ d₀.IsCanonical ∧ Clinger.ofDecimalBits d₀ = wd
      ∧ ∀ d' : Decimal, d' ≠ d₀ → d'.IsCanonical → Clinger.ofDecimalBits d' = wd →
          BeatsOdd wd d₀ d' := by
  have h := inRange_of_decode hw hm
  have hri := reads_to_iff hw hm
  have hdist : ∀ z, Spec.dist z wd = |(if (Word.decode wd).sign then -1 else 1 : Rat)
      * v (Word.decode wd).m (Word.decode wd).q
      - (if z.sign then -1 else 1 : Rat) * ((z.significand : Rat) * (10 : Rat) ^ z.exponent)| :=
    fun z => Clinger.dist_eq z wd
  rcases hdec : Word.decode wd with ⟨sgn, m, q⟩
  rw [hdec] at h hri hm hdist
  dsimp only at h hri hm hdist
  rcases hsh : shortest m q with ⟨n, i⟩
  have hsig := out_sig h hsh sgn
  have hsign := out_sign h hsh sgn
  have hval := out_value h hsh sgn
  obtain ⟨hn, _, _, hmem, _, _⟩ := out_facts h hsh
  have hsig1 : 1 ≤ outSig n := by unfold outSig; split <;> omega
  have hcan : (Decimal.mk' sgn n i).IsCanonical := Decimal.canonical_isCanonical _
  refine ⟨Decimal.mk' sgn n i, ?_, hcan, ?_, ?_⟩
  · rw [toDecimalBits_of_finite hw, hdec]
    dsimp only
    rw [if_neg (by omega), hsh]
  · rw [hri]
    exact ⟨by rw [hsig]; omega, hsign, by rw [hval]; exact hmem⟩
  · intro d' hne hc' hrt'
    obtain ⟨hsig', hsign', hmem'⟩ := (hri d').mp hrt'
    have hf := canonical_sig hc' (by intro e; rw [e] at hsig'; exact hsig' rfl)
    have hvne : (d'.significand : Rat) * (10 : Rat) ^ d'.exponent ≠ (n : Rat) * (10 : Rat) ^ i := by
      intro e
      apply hne
      apply canonical_eq_of_value_eq hc' hcan (by rw [hsign', hsign]) hf.1 (by rw [hsig]; exact hsig1)
      rw [e, hval]
    have hc := competitor h hsh hf.1 hf.2 hmem' hvne
    have hd₀ : Spec.dist (Decimal.mk' sgn n i) wd = |v m q - n * (10 : Rat) ^ i| := by
      rw [hdist, hsign, hval]; exact dist_of_sign _ _ _
    have hd' : Spec.dist d' wd = |v m q - d'.significand * (10 : Rat) ^ d'.exponent| := by
      rw [hdist, hsign']; exact dist_of_sign _ _ _
    unfold BeatsOdd
    rw [hsig, hd₀, hd']
    exact hc

/-- Zero words: the signed zero is the output; every competitor is farther. -/
theorem zero_output (hw : Word.isFinite wd = true) (hm : (Word.decode wd).m = 0) :
    ∃ d₀, toDecimalBits wd = .ok d₀ ∧ d₀.IsCanonical ∧ Clinger.ofDecimalBits d₀ = wd
      ∧ ∀ d' : Decimal, d' ≠ d₀ → d'.IsCanonical → Clinger.ofDecimalBits d' = wd →
          BeatsOdd wd d₀ d' := by
  refine ⟨⟨(Word.decode wd).sign, 0, 0⟩, ?_, Or.inl ⟨rfl, rfl⟩, ?_, ?_⟩
  · rw [toDecimalBits_of_finite hw, if_pos hm]
  · show Word.pack (Word.decode wd).sign 0 0 = wd
    apply eq_of_decode_eq
    rw [decode_pack _ (by decide) (by decide), if_pos rfl]
    have hq : (Word.decode wd).q = -1074 := by
      unfold Word.decode at hm ⊢
      by_cases he : Word.biasedExp wd = 0
      · simp [he]
      · exfalso; simp only [he, if_false, Nat.shiftLeft_eq] at hm; omega
    rcases hdec : Word.decode wd with ⟨s, mm, qq⟩
    rw [hdec] at hm hq
    simp only at hm hq
    rw [hm, hq]
  · intro d' hne hc' hrt'
    have hsign' := sign_of_reads_to hw hrt'
    have hf1 : 1 ≤ d'.significand := by
      rcases Nat.eq_zero_or_pos d'.significand with h0 | hpos
      · exfalso
        apply hne
        rcases hc' with ⟨_, he⟩ | ⟨hne0, _⟩
        · cases d'; simp_all
        · exact absurd h0 hne0
      · exact hpos
    have hv0 : v (Word.decode wd).m (Word.decode wd).q = 0 := by rw [hm]; exact v_zero_iff.mpr rfl
    have hneg : ∀ a b : Rat, a * 0 - b = -b := fun a b => by grind
    have hd₀ : Spec.dist ⟨(Word.decode wd).sign, 0, 0⟩ wd = 0 := by
      rw [Clinger.dist_eq, hv0]; simp; rw [Rat.sub_self]
    have hd' : 0 < Spec.dist d' wd := by
      rw [Clinger.dist_eq, hv0, hneg, abs_neg, sign_mul_abs]
      exact abs_pos.mpr (Rat.ne_of_gt (Rat.mul_pos (by exact_mod_cast hf1) (ten_zpow_pos _)))
    rcases Nat.lt_or_ge 1 (digits d'.significand) with hd | hd
    · left; rw [digits_zero]; exact hd
    · right
      have := digits_pos d'.significand
      exact ⟨by rw [digits_zero]; omega, Or.inl (by rw [hd₀]; exact hd')⟩

/-! ## The specification -/

/-- The output beats every competitor, with the competitor's parity on a tie. -/
theorem output_beats (hw : Word.isFinite wd = true) :
    ∃ d₀, toDecimalBits wd = .ok d₀ ∧ d₀.IsCanonical ∧ Clinger.ofDecimalBits d₀ = wd
      ∧ ∀ d' : Decimal, d' ≠ d₀ → d'.IsCanonical → Clinger.ofDecimalBits d' = wd →
          BeatsOdd wd d₀ d' := by
  rcases Nat.eq_zero_or_pos (Word.decode wd).m with hm | hm
  · exact zero_output hw hm
  · exact nonzero_output hw hm

theorem toDecimalBits_spec (hw : Word.isFinite wd = true) :
    ∃ d, toDecimalBits wd = .ok d ∧ Spec.ShortestDecimal wd d :=
  let ⟨d₀, h₀, hc, hrt, hb⟩ := output_beats hw
  ⟨d₀, h₀, hc, hrt, fun d' hne hc' hrt' => (hb d' hne hc' hrt').beats⟩

/-- Anything satisfying the specification is the output. -/
theorem eq_output_of_shortest (hw : Word.isFinite wd = true) {d d₀ : Decimal}
    (h₀ : toDecimalBits wd = .ok d₀) (hd : Spec.ShortestDecimal wd d) : d = d₀ := by
  by_cases hne : d = d₀
  · exact hne
  obtain ⟨d₁, h₁, hc₁, hrt₁, hb⟩ := output_beats hw
  rw [h₁] at h₀; obtain rfl := Except.ok.inj h₀
  exact ((hb d hne hd.canonical hd.roundTrip).not_beats (hd.shortest d₁ (Ne.symm hne) hc₁ hrt₁)).elim

theorem shortestDecimal_exists_unique (w : UInt64) (h_fin : Word.isFinite w = true) :
    ∃! d : Decimal, Spec.ShortestDecimal w d :=
  let ⟨d, h₀, hd⟩ := toDecimalBits_spec h_fin
  ⟨d, hd, fun _ hd' => eq_output_of_shortest h_fin h₀ hd'⟩

/-- `toDecimalBits` is a correct printer. -/
theorem correctPrinter_toDecimalBits : Spec.CorrectPrinter toDecimalBits where
  nan w h := by unfold toDecimalBits; rw [h]; rfl
  inf w h := by
    have hn : Word.isNaN w = false := by
      unfold Word.isInf at h; unfold Word.isNaN; simp at h ⊢; omega
    unfold toDecimalBits; rw [hn, h]; rfl
  finite _ hw := toDecimalBits_spec hw

/-- **The printer theorem.** A function is a correct printer iff it is
`toDecimalBits`. -/
theorem correctPrinter_iff_toDecimal (p : UInt64 → Except String Decimal) :
    Spec.CorrectPrinter p ↔ p = toDecimalBits := by
  constructor
  · intro hp
    funext w
    by_cases h1 : Word.isNaN w = true
    · rw [hp.nan w h1, correctPrinter_toDecimalBits.nan w h1]
    by_cases h2 : Word.isInf w = true
    · rw [hp.inf w h2, correctPrinter_toDecimalBits.inf w h2]
    have h3 : Word.isFinite w = true := by
      unfold Word.isNaN at h1; unfold Word.isInf at h2; unfold Word.isFinite
      simp at h1 h2 ⊢
      have := word_biasedExp_lt w
      omega
    obtain ⟨d, hd, hds⟩ := hp.finite w h3
    obtain ⟨d', hd', -⟩ := toDecimalBits_spec h3
    rw [hd, hd', eq_output_of_shortest h3 hd' hds]
  · rintro rfl
    exact correctPrinter_toDecimalBits

end Srtfp.Printer

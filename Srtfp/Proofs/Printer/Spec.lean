/- From the scan to the specification: `Printer.toDecimalBits w` is the
   unique decimal satisfying `Srtfp.Spec.ShortestDecimal w`. -/
import Srtfp.Proofs.Printer.Scan
import Srtfp.Proofs.Clinger.Interface
import Srtfp.Proofs.Decimal.Canonical
import Srtfp.Proofs.Decimal

open Srtfp.Compat

namespace Srtfp.Printer

open Srtfp Srtfp.Float Srtfp.Schubfach Srtfp.Clinger

/-- The spec's `ShortestDecimal`, spelled with this file's vocabulary
    (definitionally the same clauses as `Srtfp.Spec.ShortestDecimal`). -/
def IsShortest (w : UInt64) (d : Decimal) : Prop :=
    d.IsCanonical
  ∧ Clinger.ofDecimalBits d = w
  ∧ (∀ d' : Decimal, d' ≠ d → d'.IsCanonical → Clinger.ofDecimalBits d' = w →
       ( digits d.significand < digits d'.significand
       ∨ ( digits d'.significand = digits d.significand
         ∧ ( |toRat d - wordVal w| < |toRat d' - wordVal w|
           ∨ ( |toRat d - wordVal w| = |toRat d' - wordVal w|
               ∧ d.significand % 2 = 0 )))))

variable {m : Nat} {q i : Int} {n : Nat} {wd : UInt64} {d : Decimal}

/-! ## Vocabulary bridges -/

theorem inRange_of_decode (hw : Word.isFinite wd = true) (hm : 1 ≤ (Word.decode wd).m) :
    InRange (Word.decode wd).m (Word.decode wd).q := by
  have := decode_legalIEEE_bits wd hw (Nat.pos_iff_ne_zero.mp hm)
  unfold LegalIEEE at this; unfold InRange; omega

/-- The sign factor cancels out of the spec's distances. -/
theorem dist_eq (sgn : Bool) (V x : ℚ) :
    |(if sgn then -1 else 1) * x - (if sgn then -1 else 1) * V| = |V - x| := by
  cases sgn
  · show |1 * x - 1 * V| = |V - x|
    rw [show (1 : ℚ) * x - 1 * V = x - V by grind, abs_sub_comm]
  · show |-1 * x - -1 * V| = |V - x|
    rw [show (-1 : ℚ) * x - -1 * V = V - x by grind]

theorem toRat_eq (d : Decimal) :
    toRat d = (if d.sign then -1 else 1) * ((d.significand : ℚ) * (10 : ℚ) ^ d.exponent) := rfl

theorem wordVal_eq (w : UInt64) :
    wordVal w = (if (Word.decode w).sign then -1 else 1) * v (Word.decode w).m (Word.decode w).q := rfl

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
    (hv : (d.significand : ℚ) * (10 : ℚ) ^ d.exponent
          = (d'.significand : ℚ) * (10 : ℚ) ^ d'.exponent) : d = d' := by
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
  unfold digits; rw [Nat.log_eq_zero_of_not (by omega)]

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
    ∧ InRv m q ((n : ℚ) * (10 : ℚ) ^ i) = true
    ∧ (∀ x, OnGrid i x → InRv m q x = true → |v m q - n * (10 : ℚ) ^ i| ≤ |v m q - x|)
    ∧ (∀ x, OnGrid i x → InRv m q x = true → x ≠ n * (10 : ℚ) ^ i →
         |v m q - n * (10 : ℚ) ^ i| = |v m q - x| → n % 2 = 0) := by
  obtain ⟨hn, _, _, hc, _⟩ := scan_spec h hs
  obtain ⟨_, hs1, hcase, hmem, hclose, htie⟩ := candidate_some h.1 hc
  exact ⟨hn, hs1, hcase, hmem, hclose, htie⟩

/-- A hit on the next grid means that grid is coarser than `v`'s leading digit. -/
theorem next_zero_of_hit {y : ℚ} (hy : OnGrid (i + 1) y) (hyR : InRv m q y = true) :
    s m q (i + 1) = 0 := by
  rcases no_hit_above h hs (show i < i + 1 by omega) with h0 | hno
  · exact h0
  · exact absurd ⟨y, hy, hyR⟩ hno

omit hs in
theorem s_le_nine_of_next_zero (hnext : s m q (i + 1) = 0) : s m q i ≤ 9 := by
  have hm := h.1
  have hv : v m q < (10 : ℚ) ^ (i + 1) :=
    Rat.not_le.mp (fun hle => absurd ((s_pos_iff (q := q) (i := i + 1) hm).mpr hle) (by omega))
  have hu := u_le_v (q := q) (i := i) hm
  unfold u at hu
  rw [Rat.zpow_add_one (by decide)] at hv
  have h10 := ten_zpow_pos i
  have : (s m q i : ℚ) * 10 ^ i < 10 * 10 ^ i := by grind
  have : (s m q i : ℚ) < 10 := Rat.lt_of_mul_lt_mul_right this (le_of_lt h10)
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
    ((Decimal.mk' sgn n i).significand : ℚ) * (10 : ℚ) ^ (Decimal.mk' sgn n i).exponent
      = (n : ℚ) * (10 : ℚ) ^ i := by
  rw [out_decimal h hs]
  split
  · rename_i h10; subst h10
    show (1 : ℚ) * 10 ^ (i + 1) = (10 : ℚ) * 10 ^ i
    rw [Rat.zpow_add_one (by decide)]; grind
  · rfl

theorem outSig_digits (hnext : s m q (i + 1) = 0) : digits (outSig n) = 1 := by
  have := n_le_ten_of_next_zero h hs hnext
  unfold outSig; split
  · exact digits_eq_one_of_le_nine (by omega)
  · exact digits_eq_one_of_le_nine (by omega)

/-! ## Ties -/

/-- Equidistant from `v` as the output and on the same grid: it is a neighbour. -/
theorem tie_eq_u_or_w {y : ℚ} (hy : OnGrid i y) (hyR : InRv m q y = true)
    (heq : |v m q - n * (10 : ℚ) ^ i| = |v m q - y|) : y = u m q i ∨ y = w m q i := by
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
theorem tie_analysis {f : Nat} (hyR : InRv m q ((f : ℚ) * (10 : ℚ) ^ i) = true)
    (hfn : f ≠ n) (heq : |v m q - n * (10 : ℚ) ^ i| = |v m q - f * (10 : ℚ) ^ i|) :
    n % 2 = 0 ∧ f % 2 = 1 ∧ n ≠ 10 := by
  have hm := h.1
  obtain ⟨hn, hs1, hcase, hmem, _, htie⟩ := out_facts h hs
  have hne : (f : ℚ) * (10 : ℚ) ^ i ≠ n * (10 : ℚ) ^ i := by
    intro e
    have h10 := ten_zpow_pos i
    have : (f : ℚ) = n := (mul_left_inj' (Rat.ne_of_gt h10)).mp e
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
    have hu9 : u m q i = 9 * (10 : ℚ) ^ i := by unfold u; rw [hs9]; push_cast; rfl
    have hw10 : w m q i = 10 * (10 : ℚ) ^ i := by unfold w; rw [hs9]; push_cast; grind
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
      have : (f : ℚ) = ((s m q i + 1 : Nat) : ℚ) := by
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
    (a : ℚ) * (10 : ℚ) ^ i ≤ (b : ℚ) * (10 : ℚ) ^ i :=
  Rat.mul_le_mul_of_nonneg_right (by exact_mod_cast hab) (le_of_lt (ten_zpow_pos i))

omit h hs in
theorem grid_mono' {a b : Nat} (hab : a + 1 ≤ b) :
    ((a : ℚ) + 1) * (10 : ℚ) ^ i ≤ (b : ℚ) * (10 : ℚ) ^ i := by
  have := grid_mono (i := i) hab; push_cast at this; exact this

omit h hs in
theorem grid_mono'' {a b : Nat} (hab : a ≤ b + 1) :
    (a : ℚ) * (10 : ℚ) ^ i ≤ ((b : ℚ) + 1) * (10 : ℚ) ^ i := by
  have := grid_mono (i := i) hab; push_cast at this; exact this

omit h hs in
/-- A positive value off the grid lies strictly between two consecutive grid points. -/
theorem between_grid {y : ℚ} (hy : 0 < y) (hyng : ¬ OnGrid i y) :
    ∃ dy : Nat, (dy : ℚ) * (10 : ℚ) ^ i < y ∧ y < ((dy : ℚ) + 1) * (10 : ℚ) ^ i := by
  have h10 := ten_zpow_pos i
  have hV : 0 < y / (10 : ℚ) ^ i := (Rat.lt_div_iff h10).mpr (by rw [Rat.zero_mul]; exact hy)
  have hfl0 : 0 ≤ (y / (10 : ℚ) ^ i).floor := by
    rcases Int.lt_or_le (y / (10 : ℚ) ^ i).floor 0 with hneg | hnn
    · exfalso; have := Rat.floor_lt_iff.mp hneg; simp at this; grind
    · exact hnn
  refine ⟨(y / (10 : ℚ) ^ i).floor.toNat, ?_, ?_⟩
  · have hle := Rat.floor_le (y / (10 : ℚ) ^ i)
    have := Rat.mul_le_mul_of_nonneg_right hle (le_of_lt h10)
    rw [Rat.div_mul_cancel (Rat.ne_of_gt h10)] at this
    rw [← Rat.intCast_natCast, Int.toNat_of_nonneg hfl0]
    by_cases hlt : ((y / (10 : ℚ) ^ i).floor : ℚ) * (10 : ℚ) ^ i < y
    · exact hlt
    · exfalso
      have heq := Rat.le_antisymm this (Rat.not_lt.mp hlt)
      apply hyng
      refine ⟨(y / (10 : ℚ) ^ i).floor.toNat, ?_⟩
      rw [← Rat.intCast_natCast, Int.toNat_of_nonneg hfl0, heq]
  · have hlt := Rat.lt_floor_add_one (y / (10 : ℚ) ^ i)
    have := Rat.mul_lt_mul_of_pos_right hlt h10
    rw [Rat.div_mul_cancel (Rat.ne_of_gt h10)] at this
    rw [← Rat.intCast_natCast, Int.toNat_of_nonneg hfl0]
    push_cast at this ⊢
    exact this

/-- The spec's clauses against one competitor `f · 10^b` in `R_v`, other
    than the output; strengthened with the competitor's parity on a tie. -/
theorem competitor {f : Nat} {b : Int} (hf1 : 1 ≤ f) (hf10 : f % 10 ≠ 0)
    (hyR : InRv m q ((f : ℚ) * (10 : ℚ) ^ b) = true)
    (hne : (f : ℚ) * (10 : ℚ) ^ b ≠ (n : ℚ) * (10 : ℚ) ^ i) :
    digits (outSig n) < digits f
    ∨ (digits f = digits (outSig n)
       ∧ (|v m q - n * (10 : ℚ) ^ i| < |v m q - f * (10 : ℚ) ^ b|
          ∨ (|v m q - n * (10 : ℚ) ^ i| = |v m q - f * (10 : ℚ) ^ b|
             ∧ outSig n % 2 = 0 ∧ f % 2 = 1))) := by
  have hm := h.1
  obtain ⟨hn, hs1, hcase, hmem, hclose, _⟩ := out_facts h hs
  have huv := u_le_v (q := q) (i := i) hm
  have hvw := v_lt_w (q := q) (i := i) hm
  have h10 := ten_zpow_pos i
  have hfpos := digits_pos f
  -- with no hit on the next grid, grid points in `R_v` avoid it and share `n`'s length
  have nohit_case (hnext : ¬ s m q (i + 1) = 0) :
      (∀ c : Nat, InRv m q ((c : ℚ) * (10 : ℚ) ^ i) = true → ¬ OnGrid (i + 1) ((c : ℚ) * (10 : ℚ) ^ i))
      ∧ n % 10 ≠ 0 ∧ outSig n = n := by
    have hnohit : ∀ c : Nat, InRv m q ((c : ℚ) * (10 : ℚ) ^ i) = true
        → ¬ OnGrid (i + 1) ((c : ℚ) * (10 : ℚ) ^ i) :=
      fun c hc hg => hnext (next_zero_of_hit h hs hg hc)
    have hn10 : n % 10 ≠ 0 := fun e => hnohit n hmem (onGrid_succ_of_ten_dvd e)
    exact ⟨hnohit, hn10, outSig_of_ne_ten (by omega)⟩
  rcases Int.lt_or_le i b with hb | hb
  · -- (A) coarser grid than the output: at most one digit, and no tie
    have hyg1 : OnGrid (i + 1) ((f : ℚ) * (10 : ℚ) ^ b) := onGrid_of_le (by omega) ⟨f, rfl⟩
    have hyg : OnGrid i ((f : ℚ) * (10 : ℚ) ^ b) := onGrid_of_le (by omega) ⟨f, rfl⟩
    have hnext := next_zero_of_hit h hs hyg1 hyR
    have hD := outSig_digits h hs hnext
    rcases Nat.lt_or_ge 1 (digits f) with hf | hf
    · left; omega
    right
    refine ⟨by omega, ?_⟩
    have hle := hclose _ hyg hyR
    by_cases hlt : |v m q - n * (10 : ℚ) ^ i| < |v m q - f * (10 : ℚ) ^ b|
    · exact Or.inl hlt
    exfalso
    have heq := Rat.le_antisymm hle (Rat.not_lt.mp hlt)
    have hs9 := s_le_nine_of_next_zero h hnext
    rcases tie_eq_u_or_w h hs hyg hyR heq with hyu | hyw
    · -- `y = u` on the next grid: `10 ∣ s`, impossible for `1 ≤ s ≤ 9`
      have : s m q i % 10 = 0 :=
        ten_dvd_of_onGrid_succ (i := i) (n := s m q i) (by rw [show ((s m q i : ℕ) : ℚ) * 10 ^ i = u m q i from rfl, ← hyu]; exact hyg1)
      omega
    · -- `y = w` on the next grid: `s + 1 = 10`, the `9`/`10` tie
      have h10' : (s m q i + 1) % 10 = 0 :=
        ten_dvd_of_onGrid_succ (i := i) (n := s m q i + 1)
          (by rw [show ((s m q i + 1 : ℕ) : ℚ) * 10 ^ i = w m q i by unfold w; push_cast; rfl, ← hyw]; exact hyg1)
      have hs9' : s m q i = 9 := by omega
      rcases hcase with hn9 | hn10
      · apply nine_ten_tie_impossible h (i := i)
        have hu9 : u m q i = 9 * (10 : ℚ) ^ i := by unfold u; rw [hs9']; push_cast; rfl
        have hw10 : w m q i = 10 * (10 : ℚ) ^ i := by unfold w; rw [hs9']; push_cast; grind
        refine ⟨by rw [hn9, hs9'] at hmem; push_cast at hmem; exact hmem,
                by rw [← hw10, ← hyw]; exact hyR, ?_⟩
        rw [hn9, hs9', hyw, hw10] at heq
        push_cast at heq
        rw [hu9] at huv; rw [hw10] at hvw
        rw [abs_of_nonneg (by grind), abs_of_nonpos (by grind)] at heq
        grind
      · exact hne (by rw [hyw, hn10]; unfold w; push_cast; rfl)
  rcases Int.lt_or_eq_of_le hb with hb | hb
  · -- (C) finer grid than the output
    have hyng : ¬ OnGrid i ((f : ℚ) * (10 : ℚ) ^ b) := not_onGrid_of_finer hb hf10
    have hypos : 0 < (f : ℚ) * (10 : ℚ) ^ b :=
      Rat.mul_pos (by exact_mod_cast hf1) (ten_zpow_pos b)
    obtain ⟨dy, hlo, hhi⟩ := between_grid hypos hyng
    -- the two ways a finer point is strictly farther than the output
    have below (hyu : (f : ℚ) * (10 : ℚ) ^ b < u m q i) :
        |v m q - n * (10 : ℚ) ^ i| < |v m q - f * (10 : ℚ) ^ b| := by
      have huR : InRv m q (u m q i) = true := InRv_convex hyR (InRv_v hm) (le_of_lt hyu) huv
      have hcu := hclose _ onGrid_u huR
      rw [abs_of_nonneg (show 0 ≤ v m q - u m q i by grind)] at hcu
      rw [abs_of_nonneg (show 0 ≤ v m q - f * (10 : ℚ) ^ b by grind)]
      grind
    have above (hwy : w m q i < (f : ℚ) * (10 : ℚ) ^ b) :
        |v m q - n * (10 : ℚ) ^ i| < |v m q - f * (10 : ℚ) ^ b| := by
      have hwR : InRv m q (w m q i) = true := InRv_convex (InRv_v hm) hyR (le_of_lt hvw) (le_of_lt hwy)
      have hcw := hclose _ onGrid_w hwR
      rw [abs_of_nonpos (show v m q - w m q i ≤ 0 by grind)] at hcw
      rw [abs_of_nonpos (show v m q - f * (10 : ℚ) ^ b ≤ 0 by grind)]
      grind
    have finish_one (hD : digits (outSig n) = 1)
        (hstrict : |v m q - n * (10 : ℚ) ^ i| < |v m q - f * (10 : ℚ) ^ b|) :
        digits (outSig n) < digits f
        ∨ (digits f = digits (outSig n)
           ∧ (|v m q - n * (10 : ℚ) ^ i| < |v m q - f * (10 : ℚ) ^ b|
              ∨ (|v m q - n * (10 : ℚ) ^ i| = |v m q - f * (10 : ℚ) ^ b|
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
          have h01 : (((0 : ℕ) : ℚ) + 1) = ((1 : ℕ) : ℚ) := by simp [Rat.zero_add]
          rw [h01] at hhi
          have h1R : InRv m q ((1 : ℕ) * (10 : ℚ) ^ i) = true :=
            InRv_convex hyR hmem (le_of_lt hhi) (grid_mono hn)
          have hdig : digits n = 1 := by
            rw [← digits_eq_one_of_le_nine (n := 1) (by omega)]
            exact (same_digits_on_grid (by omega) hn
              (fun c h1c hcn => hnohit c (InRv_convex h1R hmem (grid_mono h1c) (grid_mono hcn)))).symm
          have hstrict := below (lt_of_lt_of_le hhi (grid_mono (i := i) hs1))
          rcases Nat.lt_or_ge 1 (digits f) with hf | hf
          · left; omega
          · right; exact ⟨by omega, Or.inl hstrict⟩
        · -- `(dy + 1) · 10^i ∈ R_v` shares `n`'s length, and `dy + 1` is not a power of ten
          have hd1R : InRv m q (((dy + 1 : ℕ) : ℚ) * (10 : ℚ) ^ i) = true :=
            InRv_convex hyR hmem (by push_cast; exact le_of_lt hhi) (grid_mono (by omega))
          have hdig1 : digits (dy + 1) = digits n :=
            same_digits_on_grid (by omega) (by omega)
              (fun c hc1 hcn => hnohit c (InRv_convex hd1R hmem (grid_mono hc1) (grid_mono hcn)))
          have h10' : (dy + 1) % 10 ≠ 0 := fun e => hnohit (dy + 1) hd1R (onGrid_succ_of_ten_dvd e)
          have hdig2 := digits_succ_of_not_ten_dvd hdy1 h10'
          have := finer_is_longer hb hdy1 hlo
          left; omega
      · -- above the output: `dy · 10^i ∈ R_v` shares `n`'s length
        have hdR : InRv m q ((dy : ℚ) * (10 : ℚ) ^ i) = true :=
          InRv_convex hmem hyR (grid_mono hge) (le_of_lt hlo)
        have hdig : digits dy = digits n :=
          (same_digits_on_grid hn hge
            (fun c hnc hcd => hnohit c (InRv_convex hmem hdR (grid_mono hnc) (grid_mono hcd)))).symm
        have := finer_is_longer hb (by omega) hlo
        left; omega
  · -- (B) the output's own grid
    rw [hb] at hyR hne ⊢
    have hfn : f ≠ n := fun e => hne (by rw [e])
    have hyg : OnGrid i ((f : ℚ) * (10 : ℚ) ^ i) := ⟨f, rfl⟩
    have hle := hclose _ hyg hyR
    -- closeness or tie, uniformly
    have close_or_tie (hD : outSig n = n ∨ digits (outSig n) = 1 ∧ digits f = 1) :
        |v m q - n * (10 : ℚ) ^ i| < |v m q - f * (10 : ℚ) ^ i|
        ∨ (|v m q - n * (10 : ℚ) ^ i| = |v m q - f * (10 : ℚ) ^ i|
           ∧ outSig n % 2 = 0 ∧ f % 2 = 1) := by
      by_cases hlt : |v m q - n * (10 : ℚ) ^ i| < |v m q - f * (10 : ℚ) ^ i|
      · exact Or.inl hlt
      · have heq := Rat.le_antisymm hle (Rat.not_lt.mp hlt)
        obtain ⟨hev, hfo, hn10⟩ := tie_analysis h hs hyR hfn heq
        exact Or.inr ⟨heq, by rw [outSig_of_ne_ten hn10]; exact hev, hfo⟩
    by_cases hnext : s m q (i + 1) = 0
    · have hD := outSig_digits h hs hnext
      rcases Nat.lt_or_ge 1 (digits f) with hf | hf
      · left; omega
      · right; exact ⟨by omega, close_or_tie (Or.inr ⟨hD, by omega⟩)⟩
    · obtain ⟨hnohit, hn10, hD⟩ := nohit_case hnext
      have hdig : digits f = digits n := by
        rcases Nat.lt_or_ge f n with hlt | hge
        · exact same_digits_on_grid hf1 (Nat.le_of_lt hlt)
            (fun c hfc hcn => hnohit c (InRv_convex hyR hmem (grid_mono hfc) (grid_mono hcn)))
        · exact (same_digits_on_grid hn hge
            (fun c hnc hcf => hnohit c (InRv_convex hmem hyR (grid_mono hnc) (grid_mono hcf)))).symm
      right
      rw [hD]
      exact ⟨hdig, by have := close_or_tie (Or.inl hD); rw [hD] at this; exact this⟩

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

/-- Nonzero words: the output is canonical, reads back, and beats every
    competitor, with the competitor's parity known on a tie. -/
theorem nonzero_output (hw : Word.isFinite wd = true) (hm : 1 ≤ (Word.decode wd).m) :
    ∃ d₀, toDecimalBits wd = .ok d₀ ∧ d₀.IsCanonical ∧ Clinger.ofDecimalBits d₀ = wd
      ∧ ∀ d' : Decimal, d' ≠ d₀ → d'.IsCanonical → Clinger.ofDecimalBits d' = wd →
          ( digits d₀.significand < digits d'.significand
          ∨ ( digits d'.significand = digits d₀.significand
            ∧ ( |toRat d₀ - wordVal wd| < |toRat d' - wordVal wd|
              ∨ ( |toRat d₀ - wordVal wd| = |toRat d' - wordVal wd|
                ∧ d₀.significand % 2 = 0 ∧ d'.significand % 2 = 1 )))) := by
  have h := inRange_of_decode hw hm
  have hri := reads_to_iff hw hm
  have hwv := wordVal_eq wd
  rcases hdec : Word.decode wd with ⟨sgn, m, q⟩
  rw [hdec] at h hri hm hwv
  dsimp only at h hri hm hwv
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
    have hvne : (d'.significand : ℚ) * (10 : ℚ) ^ d'.exponent ≠ (n : ℚ) * (10 : ℚ) ^ i := by
      intro e
      apply hne
      apply canonical_eq_of_value_eq hc' hcan (by rw [hsign', hsign]) hf.1 (by rw [hsig]; exact hsig1)
      rw [e, hval]
    have hc := competitor h hsh hf.1 hf.2 hmem' hvne
    -- translate the vocabulary
    have hd₀ : |toRat (Decimal.mk' sgn n i) - wordVal wd| = |v m q - n * (10 : ℚ) ^ i| := by
      rw [toRat_eq, hwv, hsign, hval, dist_eq]
    have hd' : |toRat d' - wordVal wd| = |v m q - d'.significand * (10 : ℚ) ^ d'.exponent| := by
      rw [toRat_eq, hwv, hsign', dist_eq]
    rw [hsig, hd₀, hd']
    exact hc

/-- Zero words: the signed zero is the output; every competitor is farther. -/
theorem zero_output (hw : Word.isFinite wd = true) (hm : (Word.decode wd).m = 0) :
    ∃ d₀, toDecimalBits wd = .ok d₀ ∧ d₀.IsCanonical ∧ Clinger.ofDecimalBits d₀ = wd
      ∧ ∀ d' : Decimal, d' ≠ d₀ → d'.IsCanonical → Clinger.ofDecimalBits d' = wd →
          ( digits d₀.significand < digits d'.significand
          ∨ ( digits d'.significand = digits d₀.significand
            ∧ |toRat d₀ - wordVal wd| < |toRat d' - wordVal wd| )) := by
  refine ⟨⟨(Word.decode wd).sign, 0, 0⟩, ?_, Or.inl ⟨rfl, rfl⟩, ?_, ?_⟩
  · rw [toDecimalBits_of_finite hw, if_pos hm]
  · rw [zero_reads_to_zero]; exact (word_of_decode_zero hw hm).symm
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
    have hw0 : wordVal wd = 0 := by rw [wordVal_eq, hm]; unfold v; simp
    have hd₀ : |toRat ⟨(Word.decode wd).sign, 0, 0⟩ - wordVal wd| = 0 := by
      have h0 : toRat ⟨(Word.decode wd).sign, 0, 0⟩ = 0 := by unfold toRat; simp
      rw [h0, hw0, Rat.sub_self]; rfl
    have hd' : 0 < |toRat d' - wordVal wd| := by
      rw [hw0, toRat_eq, sub_zero]
      have h10 := ten_zpow_pos d'.exponent
      have hpos : (0 : ℚ) < (d'.significand : ℚ) * 10 ^ d'.exponent :=
        Rat.mul_pos (by exact_mod_cast hf1) h10
      cases d'.sign
      · show 0 < |1 * ((d'.significand : ℚ) * 10 ^ d'.exponent)|
        rw [abs_of_nonneg (by grind)]; grind
      · show 0 < |-1 * ((d'.significand : ℚ) * 10 ^ d'.exponent)|
        rw [abs_of_nonpos (by grind)]; grind
    rcases Nat.lt_or_ge 1 (digits d'.significand) with hd | hd
    · left; rw [digits_zero]; exact hd
    · right
      have := digits_pos d'.significand
      exact ⟨by rw [digits_zero]; omega, by rw [hd₀]; exact hd'⟩

/-! ## The specification -/

theorem toDecimalBits_spec (hw : Word.isFinite wd = true) :
    ∃ d, toDecimalBits wd = .ok d ∧ IsShortest wd d := by
  rcases Nat.eq_zero_or_pos (Word.decode wd).m with hm | hm
  · obtain ⟨d₀, h₀, hc, hrt, hcomp⟩ := zero_output hw hm
    refine ⟨d₀, h₀, hc, hrt, fun d' hne hc' hrt' => ?_⟩
    rcases hcomp d' hne hc' hrt' with h1 | ⟨h1, h2⟩
    · exact Or.inl h1
    · exact Or.inr ⟨h1, Or.inl h2⟩
  · obtain ⟨d₀, h₀, hc, hrt, hcomp⟩ := nonzero_output hw hm
    refine ⟨d₀, h₀, hc, hrt, fun d' hne hc' hrt' => ?_⟩
    rcases hcomp d' hne hc' hrt' with h1 | ⟨h1, h2 | ⟨h2, h3, _⟩⟩
    · exact Or.inl h1
    · exact Or.inr ⟨h1, Or.inl h2⟩
    · exact Or.inr ⟨h1, Or.inr ⟨h2, h3⟩⟩

/-- Anything satisfying the specification is the output. -/
theorem eq_output_of_isShortest (hw : Word.isFinite wd = true) {d d₀ : Decimal}
    (h₀ : toDecimalBits wd = .ok d₀) (hd : IsShortest wd d) : d = d₀ := by
  by_cases hne : d = d₀
  · exact hne
  exfalso
  obtain ⟨hc, hrt, hcomp⟩ := hd
  rcases Nat.eq_zero_or_pos (Word.decode wd).m with hm | hm
  · obtain ⟨d₁, h₁, hc₁, hrt₁, hcomp₁⟩ := zero_output hw hm
    rw [h₁] at h₀; obtain rfl := Except.ok.inj h₀
    have hA := hcomp d₁ (Ne.symm hne) hc₁ hrt₁
    have hB := hcomp₁ d hne hc hrt
    rcases hA with hA | ⟨hA1, hA2 | ⟨hA2, _⟩⟩ <;> rcases hB with hB | ⟨hB1, hB2⟩ <;> grind
  · obtain ⟨d₁, h₁, hc₁, hrt₁, hcomp₁⟩ := nonzero_output hw hm
    rw [h₁] at h₀; obtain rfl := Except.ok.inj h₀
    have hA := hcomp d₁ (Ne.symm hne) hc₁ hrt₁
    have hB := hcomp₁ d hne hc hrt
    rcases hA with hA | ⟨hA1, hA2 | ⟨hA2, hA3⟩⟩ <;>
      rcases hB with hB | ⟨hB1, hB2 | ⟨hB2, hB3, hB4⟩⟩ <;> grind

theorem shortest_unique (hw : Word.isFinite wd = true) {d d' : Decimal}
    (hd : IsShortest wd d) (hd' : IsShortest wd d') : d = d' := by
  obtain ⟨d₀, h₀, _⟩ := toDecimalBits_spec hw
  rw [eq_output_of_isShortest hw h₀ hd, eq_output_of_isShortest hw h₀ hd']

/-- What `toDecimalBits` returns on every word. -/
theorem toDecimalBits_correct (w : UInt64) :
    (Word.isNaN w = true → toDecimalBits w = .error "NaN")
    ∧ (Word.isInf w = true →
         toDecimalBits w = .error (if Word.signBit w then "-Infinity" else "Infinity"))
    ∧ (Word.isFinite w = true → ∃ d, toDecimalBits w = .ok d ∧ IsShortest w d) := by
  refine ⟨fun h => ?_, fun h => ?_, toDecimalBits_spec⟩
  · unfold toDecimalBits; rw [h]; rfl
  · have hn : Word.isNaN w = false := by
      unfold Word.isInf at h; unfold Word.isNaN; simp at h ⊢; omega
    unfold toDecimalBits; rw [hn, h]; rfl

/-- **A function is a correct shortest-decimal printer iff it is
`toDecimalBits`.** The statement is `Srtfp.Spec.correct_iff_toDecimal` with
the vocabulary unfolded to this file's. -/
theorem correct_iff_toDecimal_proof (p : UInt64 → Except String Decimal) :
    ( ∀ w : UInt64,
        (Word.isNaN w = true → p w = .error "NaN")
      ∧ (Word.isInf w = true →
           p w = .error (if Word.signBit w then "-Infinity" else "Infinity"))
      ∧ (Word.isFinite w = true →
           ∃ d : Decimal, p w = .ok d ∧ IsShortest w d) )
    ↔ p = toDecimalBits := by
  constructor
  · intro hp
    funext w
    obtain ⟨hnan, hinf, hfin⟩ := hp w
    obtain ⟨hnan', hinf', hfin'⟩ := toDecimalBits_correct w
    by_cases h1 : Word.isNaN w = true
    · rw [hnan h1, hnan' h1]
    by_cases h2 : Word.isInf w = true
    · rw [hinf h2, hinf' h2]
    have h3 : Word.isFinite w = true := by
      unfold Word.isNaN at h1; unfold Word.isInf at h2; unfold Word.isFinite
      simp at h1 h2 ⊢
      have := word_biasedExp_lt w
      omega
    obtain ⟨d, hd, hds⟩ := hfin h3
    obtain ⟨d', hd', hds'⟩ := hfin' h3
    rw [hd, hd', shortest_unique h3 hds hds']
  · rintro rfl
    exact toDecimalBits_correct

theorem shortest_decimal_exists_unique_proof (w : UInt64) (h_fin : Word.isFinite w = true) :
    ∃! d : Decimal, IsShortest w d := by
  obtain ⟨d, _, hd⟩ := toDecimalBits_spec h_fin
  exact ⟨d, hd, fun d' hd' => shortest_unique h_fin hd' hd⟩

end Srtfp.Printer

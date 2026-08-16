/- Correctness foundations for the `cmpScaledMixed` / `shiftedSig`
   multiply-shift kernels.

   This file bridges the per-component Nat lemmas in `Kernel192.lean` to
   the integer-level comparisons in `cmpScaledMixed` / `shiftedSig`.  It
   contains the *foundational* lemmas shared between the 128-bit Perf
   variant (`Perf/Kernel128.lean`) and the 192-bit Perf variant
   (`Perf/Kernel192Correctness.lean`):

   - 192-bit comparison: `gt192_iff`, `le192_iff`
   - Abstract verdict correctness: `verdict_plus_one_correct`,
     `verdict_minus_one_correct`, `table_invariant_scaled`
   - Sign analysis: `cmpScaledMixed_of_nonneg`
   - Power regrouping: `two_pow_regroup`, `two_pow_regroup_of_eq`
   - Nat verdict ⇒ Int comparison: `cmpScaledMixed_plus_one`,
     `cmpScaledMixed_minus_one`
   - Kernel R bridge: `kernel_R_eq` (exact when `b < 2^60`)
   - UInt64 bound helpers: `UInt64_ofNat_toNat_of_lt`,
     `UInt64_lt_64_iff`, `UInt64_lt_128_iff`
   - Sandwich + slack lemmas for `shiftedSig`: `shiftedSig_sandwich`,
     `shiftedSig_floor_safe`, `shiftedSig_floor_strict_precision_param`,
     `shiftedSig_slack_bound_strict_param`, …

   The final 128-bit assembly (`cmpScaledMixed_eq_fast2`,
   `shiftedSig_eq_fast2`) and the `@[csimp]` registrations live in
   `Perf/Kernel128.lean`.

   ## Strategy

   `cmpScaledMixed_fast2` returns one of three values:
   - `+1`  if the 192-bit triple `L = a · 2^{q+h}` strictly exceeds
            `R = b · g`,
   - `-1`  if `L + b ≤ R`,
   - otherwise falls back to `cmpScaledMixed_fast` (which equals
            `cmpScaledMixed`).

   The Schubfach table invariant (`pow10Lookup128_invariant`) states
   that `g = ⌈10^k · 2^h⌉` in the appropriate signed sense, i.e.,
   `b · g ≥ b · 10^k · 2^h` and `b · g < b · 10^k · 2^h + b`.
   This sandwich is the crux: in the `+1` branch `L > b · g ≥
   b · 10^k · 2^h`, so `a · 2^q > b · 10^k`; in the `-1` branch
   `L + b ≤ b · g < b · 10^k · 2^h + b`, so `L < b · 10^k · 2^h`
   strictly and `a · 2^q < b · 10^k`.
-/
import Srtfp.Schubfach
import Srtfp.Tactics
import Srtfp.Schubfach.Kernel192
import Srtfp.Schubfach.TableInvariant

namespace Srtfp.Schubfach

/- Clean-context helper: on ≥4.32 toolchains `omega`/`grind` blow up when
this subtraction shuffle must be discharged amid large-magnitude
hypotheses (upstream large-coefficient regression). -/
private theorem sub_add_sub_shuffle (A B C : Nat) (hBA : B ≤ A) (hC : 1 ≤ C) :
    (A - B) + (C - 1) = A + C - B - 1 := by omega

set_option maxHeartbeats 1000000

/-! ## 192-bit comparison: gt192 / le192 reflect Nat order on triples -/

/-- `gt192` matches `>` on `triple192Nat`. -/
theorem gt192_iff (hi₁ mid₁ lo₁ hi₂ mid₂ lo₂ : UInt64) :
    gt192 hi₁ mid₁ lo₁ hi₂ mid₂ lo₂ = true
      ↔ triple192Nat hi₁ mid₁ lo₁ > triple192Nat hi₂ mid₂ lo₂ := by
  unfold gt192 triple192Nat
  have hHi₁ : hi₁.toNat < 2 ^ 64 := hi₁.toNat_lt
  have hHi₂ : hi₂.toNat < 2 ^ 64 := hi₂.toNat_lt
  have hMid₁ : mid₁.toNat < 2 ^ 64 := mid₁.toNat_lt
  have hMid₂ : mid₂.toNat < 2 ^ 64 := mid₂.toNat_lt
  have hLo₁ : lo₁.toNat < 2 ^ 64 := lo₁.toNat_lt
  have hLo₂ : lo₂.toNat < 2 ^ 64 := lo₂.toNat_lt
  have h128 : (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 := by decide
  by_cases hHi : hi₁ = hi₂
  · -- hi equal
    rw [hHi]
    have hHi_eq : hi₂.toNat = hi₂.toNat := rfl
    simp only [ne_eq, not_true_eq_false, ↓reduceIte]
    by_cases hMid : mid₁ = mid₂
    · -- mid equal
      rw [hMid]
      simp only [not_true_eq_false, ↓reduceIte, decide_eq_true_eq]
      -- Just need lo₁ > lo₂ ↔ same Nat sums
      rw [show (lo₁ > lo₂) = (lo₂ < lo₁) from rfl, UInt64.lt_iff_toNat_lt]
      constructor
      · intro hLt; omega
      · intro hGt; omega
    · -- mid different
      have hMid_ne : mid₁.toNat ≠ mid₂.toNat := by
        intro h
        apply hMid
        exact UInt64.toNat_inj.mp h
      simp only [hMid, not_false_eq_true, ↓reduceIte, decide_eq_true_eq]
      rw [show (mid₁ > mid₂) = (mid₂ < mid₁) from rfl, UInt64.lt_iff_toNat_lt]
      -- Need: mid₂ < mid₁ ↔ mid₁ · 2^64 + lo₁ > mid₂ · 2^64 + lo₂
      constructor
      · intro hLt
        have hLo_bd : mid₁.toNat * 2 ^ 64 > mid₂.toNat * 2 ^ 64 := by
          apply Nat.mul_lt_mul_right (Nat.two_pow_pos 64) |>.mpr hLt
        grind
      · intro hGt
        by_contra hContra
        push_neg at hContra
        -- mid₁ ≤ mid₂.  But not =, so mid₁ < mid₂.
        have : mid₁.toNat < mid₂.toNat := by omega
        have : mid₁.toNat * 2 ^ 64 + 2 ^ 64 ≤ mid₂.toNat * 2 ^ 64 := by
          have h1 : (mid₁.toNat + 1) * 2 ^ 64 ≤ mid₂.toNat * 2 ^ 64 :=
            Nat.mul_le_mul_right _ (by omega)
          omega
        omega
  · -- hi different
    have hHi_ne : hi₁.toNat ≠ hi₂.toNat := by
      intro h; exact hHi (UInt64.toNat_inj.mp h)
    simp only [hHi, ne_eq, not_false_eq_true, ↓reduceIte, decide_eq_true_eq]
    rw [show (hi₁ > hi₂) = (hi₂ < hi₁) from rfl, UInt64.lt_iff_toNat_lt]
    constructor
    · intro hLt
      have hLoSum_lt : mid₂.toNat * 2 ^ 64 + lo₂.toNat < 2 ^ 128 := by
        have h1 : mid₂.toNat * 2 ^ 64 ≤ (2 ^ 64 - 1) * 2 ^ 64 := by
          apply Nat.mul_le_mul_right; omega
        rw [h128]; grind
      have hHi_step : hi₁.toNat ≥ hi₂.toNat + 1 := by omega
      have hHi_mul : hi₁.toNat * 2 ^ 128 ≥ (hi₂.toNat + 1) * 2 ^ 128 :=
        Nat.mul_le_mul_right _ hHi_step
      have : hi₁.toNat * 2 ^ 128 ≥ hi₂.toNat * 2 ^ 128 + 2 ^ 128 := by omega
      grind
    · intro hGt
      by_contra hContra
      push_neg at hContra
      have hHi_le : hi₁.toNat ≤ hi₂.toNat := hContra
      have hHi_lt : hi₁.toNat < hi₂.toNat := by omega
      have hLoSum_lt : mid₁.toNat * 2 ^ 64 + lo₁.toNat < 2 ^ 128 := by
        have h1 : mid₁.toNat * 2 ^ 64 ≤ (2 ^ 64 - 1) * 2 ^ 64 := by
          apply Nat.mul_le_mul_right; omega
        rw [h128]; grind
      have hHi_step : hi₂.toNat ≥ hi₁.toNat + 1 := by omega
      have hHi_mul : hi₂.toNat * 2 ^ 128 ≥ (hi₁.toNat + 1) * 2 ^ 128 :=
        Nat.mul_le_mul_right _ hHi_step
      have : hi₂.toNat * 2 ^ 128 ≥ hi₁.toNat * 2 ^ 128 + 2 ^ 128 := by omega
      omega

/-- `le192` matches `≤` on `triple192Nat`. -/
theorem le192_iff (hi₁ mid₁ lo₁ hi₂ mid₂ lo₂ : UInt64) :
    le192 hi₁ mid₁ lo₁ hi₂ mid₂ lo₂ = true
      ↔ triple192Nat hi₁ mid₁ lo₁ ≤ triple192Nat hi₂ mid₂ lo₂ := by
  unfold le192 triple192Nat
  have hHi₁ : hi₁.toNat < 2 ^ 64 := hi₁.toNat_lt
  have hHi₂ : hi₂.toNat < 2 ^ 64 := hi₂.toNat_lt
  have hMid₁ : mid₁.toNat < 2 ^ 64 := mid₁.toNat_lt
  have hMid₂ : mid₂.toNat < 2 ^ 64 := mid₂.toNat_lt
  have hLo₁ : lo₁.toNat < 2 ^ 64 := lo₁.toNat_lt
  have hLo₂ : lo₂.toNat < 2 ^ 64 := lo₂.toNat_lt
  have h128 : (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 := by decide
  by_cases hHi : hi₁ = hi₂
  · rw [hHi]
    simp only [ne_eq, not_true_eq_false, ↓reduceIte]
    by_cases hMid : mid₁ = mid₂
    · rw [hMid]
      simp only [not_true_eq_false, ↓reduceIte, decide_eq_true_eq]
      rw [UInt64.le_iff_toNat_le]
      constructor
      · intro hLe; omega
      · intro hGe; omega
    · have hMid_ne : mid₁.toNat ≠ mid₂.toNat := by
        intro h; exact hMid (UInt64.toNat_inj.mp h)
      simp only [hMid, not_false_eq_true, ↓reduceIte, decide_eq_true_eq]
      rw [UInt64.lt_iff_toNat_lt]
      constructor
      · intro hLt
        have hLoSum_lt : lo₁.toNat < 2 ^ 64 := hLo₁
        have h2 : mid₁.toNat + 1 ≤ mid₂.toNat := by omega
        have h3 : (mid₁.toNat + 1) * 2 ^ 64 ≤ mid₂.toNat * 2 ^ 64 :=
          Nat.mul_le_mul_right _ h2
        omega
      · intro hLe
        by_contra hContra
        push_neg at hContra
        have hMid_ge : mid₂.toNat ≤ mid₁.toNat := hContra
        have hMid_lt : mid₂.toNat < mid₁.toNat := by omega
        have hMid_step : mid₁.toNat ≥ mid₂.toNat + 1 := by omega
        have : (mid₂.toNat + 1) * 2 ^ 64 ≤ mid₁.toNat * 2 ^ 64 :=
          Nat.mul_le_mul_right _ hMid_step
        omega
  · have hHi_ne : hi₁.toNat ≠ hi₂.toNat := by
      intro h; exact hHi (UInt64.toNat_inj.mp h)
    simp only [hHi, ne_eq, not_false_eq_true, ↓reduceIte, decide_eq_true_eq]
    rw [UInt64.lt_iff_toNat_lt]
    constructor
    · intro hLt
      have hLoSum_lt : mid₁.toNat * 2 ^ 64 + lo₁.toNat < 2 ^ 128 := by
        have h1 : mid₁.toNat * 2 ^ 64 ≤ (2 ^ 64 - 1) * 2 ^ 64 := by
          apply Nat.mul_le_mul_right; omega
        rw [h128]; grind
      have hHi_step : hi₂.toNat ≥ hi₁.toNat + 1 := by omega
      have : (hi₁.toNat + 1) * 2 ^ 128 ≤ hi₂.toNat * 2 ^ 128 :=
        Nat.mul_le_mul_right _ hHi_step
      omega
    · intro hLe
      by_contra hContra
      push_neg at hContra
      have hHi_ge : hi₂.toNat ≤ hi₁.toNat := hContra
      have hHi_lt : hi₂.toNat < hi₁.toNat := by omega
      have hLoSum_lt : mid₂.toNat * 2 ^ 64 + lo₂.toNat < 2 ^ 128 := by
        have h1 : mid₂.toNat * 2 ^ 64 ≤ (2 ^ 64 - 1) * 2 ^ 64 := by
          apply Nat.mul_le_mul_right; omega
        rw [h128]; grind
      have hHi_step : hi₁.toNat ≥ hi₂.toNat + 1 := by omega
      have : (hi₂.toNat + 1) * 2 ^ 128 ≤ hi₁.toNat * 2 ^ 128 :=
        Nat.mul_le_mul_right _ hHi_step
      omega

/-! ## Abstract verdict correctness (Schubfach §9.6–9.8 inner bound)

Given the table-ceiling invariant `T ≤ g · 10^kNeg · 2^hNeg < T + 10^kNeg · 2^hNeg`
where `T = 10^kPos · 2^hPos`, the verdict branches of `cmpScaledMixed_fast2`
correctly carve out the strictly-positive and strictly-negative sign zones
of `a · 2^q - b · 10^k`.

This section proves the *abstract* verdict argument in pure Nat / Int.
The full assembly (case-splitting `q + h` into `[0, 192)` and grafting
on the lookups) is the remaining work.
-/

/-- The ceiling-rounded table satisfies: multiplying through by `b > 0`,
    `b · g · 10^kNeg · 2^hNeg ∈ [b · T, b · T + b · 10^kNeg · 2^hNeg)`
    where `T = 10^kPos · 2^hPos`.

    The `0 < b` precondition is needed for the strict upper bound;
    Schubfach's caller always has `b ≥ 1` in practice. -/
theorem table_invariant_scaled (g b kPos kNeg hPos hNeg : Nat)
    (hb_pos : 0 < b)
    (hInv : 10 ^ kPos * 2 ^ hPos ≤ g * 10 ^ kNeg * 2 ^ hNeg
              ∧ g * 10 ^ kNeg * 2 ^ hNeg < 10 ^ kPos * 2 ^ hPos + 10 ^ kNeg * 2 ^ hNeg) :
    b * g * 10 ^ kNeg * 2 ^ hNeg ≥ b * (10 ^ kPos * 2 ^ hPos)
    ∧ b * g * 10 ^ kNeg * 2 ^ hNeg < b * (10 ^ kPos * 2 ^ hPos) + b * (10 ^ kNeg * 2 ^ hNeg) := by
  obtain ⟨hLo, hHi⟩ := hInv
  constructor
  · have := Nat.mul_le_mul_left b hLo
    calc b * (10 ^ kPos * 2 ^ hPos)
        ≤ b * (g * 10 ^ kNeg * 2 ^ hNeg) := this
      _ = b * g * 10 ^ kNeg * 2 ^ hNeg := by grind
  · have hmul : b * (g * 10 ^ kNeg * 2 ^ hNeg)
                  < b * (10 ^ kPos * 2 ^ hPos + 10 ^ kNeg * 2 ^ hNeg) :=
      Nat.mul_lt_mul_left hb_pos |>.mpr hHi
    calc b * g * 10 ^ kNeg * 2 ^ hNeg
        = b * (g * 10 ^ kNeg * 2 ^ hNeg) := by grind
      _ < b * (10 ^ kPos * 2 ^ hPos + 10 ^ kNeg * 2 ^ hNeg) := hmul
      _ = b * (10 ^ kPos * 2 ^ hPos) + b * (10 ^ kNeg * 2 ^ hNeg) := by grind

/-- Verdict `+1` correctness: if `L > R` (where `L = a · 2^(q+h)` and
    `R = b · g`), and the table invariant holds, then
    `a · 2^q · 10^kNeg · 2^hNeg > b · 10^kPos · 2^hPos` (rearranged
    cross-multiplication form of `a · 2^q > b · 10^k`).

    Stated in `Nat`; the integer adapter handles sign downstream. -/
theorem verdict_plus_one_correct
    (a g b kPos kNeg hPos hNeg s : Nat)
    (hb_pos : 0 < b)
    (hInv : 10 ^ kPos * 2 ^ hPos ≤ g * 10 ^ kNeg * 2 ^ hNeg
              ∧ g * 10 ^ kNeg * 2 ^ hNeg < 10 ^ kPos * 2 ^ hPos + 10 ^ kNeg * 2 ^ hNeg)
    (hL : a * 2 ^ s > b * g) :
    a * 2 ^ s * 10 ^ kNeg * 2 ^ hNeg > b * (10 ^ kPos * 2 ^ hPos) := by
  have ⟨hLo, _⟩ := table_invariant_scaled g b kPos kNeg hPos hNeg hb_pos hInv
  have h10 : 0 < 10 ^ kNeg := Nat.pow_pos (by decide)
  have h2 : 0 < 2 ^ hNeg := Nat.two_pow_pos _
  have h_pow : 0 < 10 ^ kNeg * 2 ^ hNeg := Nat.mul_pos h10 h2
  have hL' : a * 2 ^ s * 10 ^ kNeg * 2 ^ hNeg
                ≥ (b * g + 1) * 10 ^ kNeg * 2 ^ hNeg :=
    Nat.mul_le_mul_right (2 ^ hNeg)
      (Nat.mul_le_mul_right (10 ^ kNeg) (by omega : b * g + 1 ≤ a * 2 ^ s))
  have hExpand : (b * g + 1) * 10 ^ kNeg * 2 ^ hNeg
                  = b * g * 10 ^ kNeg * 2 ^ hNeg + 10 ^ kNeg * 2 ^ hNeg := by grind
  omega

/-- Verdict `-1` correctness: if `L + b ≤ R = b · g`, and the table
    invariant holds (with `0 < b`), then
    `a · 2^q · 10^kNeg · 2^hNeg < b · 10^kPos · 2^hPos`.

    Key step: from `L + b ≤ b · g`, derive `L ≤ b · (g - 1)`, then use
    the upper bound `g · 10^kNeg · 2^hNeg < T + 10^kNeg · 2^hNeg`. -/
theorem verdict_minus_one_correct
    (a g b kPos kNeg hPos hNeg s : Nat)
    (hb_pos : 0 < b)
    (hInv : 10 ^ kPos * 2 ^ hPos ≤ g * 10 ^ kNeg * 2 ^ hNeg
              ∧ g * 10 ^ kNeg * 2 ^ hNeg < 10 ^ kPos * 2 ^ hPos + 10 ^ kNeg * 2 ^ hNeg)
    (hL : a * 2 ^ s + b ≤ b * g) :
    a * 2 ^ s * 10 ^ kNeg * 2 ^ hNeg < b * (10 ^ kPos * 2 ^ hPos) := by
  obtain ⟨hLo, hHi⟩ := hInv
  have h10 : 0 < 10 ^ kNeg := Nat.pow_pos (by decide)
  have h2 : 0 < 2 ^ hNeg := Nat.two_pow_pos _
  have h_pow : 0 < 10 ^ kNeg * 2 ^ hNeg := Nat.mul_pos h10 h2
  have h_b_pow_pos : 0 < b * (10 ^ kNeg * 2 ^ hNeg) := Nat.mul_pos hb_pos h_pow
  -- Phase 1: derive `a * 2^s ≤ b * (g - 1)` (using `g ≥ 1` since `b * g ≥ b`).
  have hg_pos : 1 ≤ g := by
    by_contra hg0
    push_neg at hg0
    have hg_eq : g = 0 := by omega
    rw [hg_eq] at hL; simp at hL; omega
  have hExpand : b * g = b * (g - 1) + b := by
    have h : b * (g - 1) = b * g - b := by rw [Nat.mul_sub, Nat.mul_one]
    omega
  have hLB' : a * 2 ^ s ≤ b * (g - 1) := by omega
  have hL_scaled : a * 2 ^ s * 10 ^ kNeg * 2 ^ hNeg
                     ≤ b * (g - 1) * 10 ^ kNeg * 2 ^ hNeg :=
    Nat.mul_le_mul_right (2 ^ hNeg)
      (Nat.mul_le_mul_right (10 ^ kNeg) hLB')
  -- Phase 2: b · g · 10^kNeg · 2^hNeg < b · T + b · 10^kNeg · 2^hNeg
  -- from the scaled invariant.
  have hbg_lt : b * g * 10 ^ kNeg * 2 ^ hNeg
                  < b * (10 ^ kPos * 2 ^ hPos) + b * (10 ^ kNeg * 2 ^ hNeg) :=
    (table_invariant_scaled g b kPos kNeg hPos hNeg hb_pos ⟨hLo, hHi⟩).2
  -- Phase 3: combine via algebraic identity.
  have hAlgebra : b * (g - 1) * 10 ^ kNeg * 2 ^ hNeg + b * (10 ^ kNeg * 2 ^ hNeg)
                     = b * g * 10 ^ kNeg * 2 ^ hNeg := by
    have h1 : b * (g - 1) + b = b * g := by omega
    have h2 : (b * (g - 1) + b) * (10 ^ kNeg * 2 ^ hNeg)
                = b * g * (10 ^ kNeg * 2 ^ hNeg) := by rw [h1]
    have h3 : b * (g - 1) * 10 ^ kNeg * 2 ^ hNeg + b * (10 ^ kNeg * 2 ^ hNeg)
                = (b * (g - 1) + b) * (10 ^ kNeg * 2 ^ hNeg) := by grind
    have h4 : b * g * (10 ^ kNeg * 2 ^ hNeg) = b * g * 10 ^ kNeg * 2 ^ hNeg := by grind
    rw [h3, h2, h4]
  omega

/-! ## Sign analysis: Int ⇒ Nat reduction

`cmpScaledMixed` is defined on `Int` inputs.  In the fast2 path the
strict-verdict branches only fire after `a ≥ 0 ∧ b ≥ 0` is checked,
and the kernel uses `a.toNat`, `b.toNat`.  This section reduces the
Int-level inequality on `lhs < rhs` to a Nat inequality. -/

/-- When `a ≥ 0` and `b ≥ 0`, the Int-level comparison in
    `cmpScaledMixed` is determined by the Nat comparison of the
    cleared products. -/
theorem cmpScaledMixed_of_nonneg (a b : Int) (q k : Int)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    let qPos : Nat := if q ≥ 0 then q.toNat else 0
    let qNeg : Nat := if q < 0 then (-q).toNat else 0
    let kPos : Nat := if k ≥ 0 then k.toNat else 0
    let kNeg : Nat := if k < 0 then (-k).toNat else 0
    let lhsN : Nat := a.toNat * 2 ^ qPos * 10 ^ kNeg
    let rhsN : Nat := b.toNat * 10 ^ kPos * 2 ^ qNeg
    cmpScaledMixed a q b k =
      (if lhsN < rhsN then -1 else if lhsN = rhsN then 0 else 1) := by
  unfold cmpScaledMixed
  simp only
  have ha_toNat : (a.toNat : Int) = a := Int.toNat_of_nonneg ha
  have hb_toNat : (b.toNat : Int) = b := Int.toNat_of_nonneg hb
  -- The Int-level lhs and rhs are nonneg, so their comparison matches the Nat one.
  set qPos : Nat := if q ≥ 0 then q.toNat else 0
  set qNeg : Nat := if q < 0 then (-q).toNat else 0
  set kPos : Nat := if k ≥ 0 then k.toNat else 0
  set kNeg : Nat := if k < 0 then (-k).toNat else 0
  set lhsI : Int := a * (2 ^ qPos : Int) * (10 ^ kNeg : Int)
  set rhsI : Int := b * (10 ^ kPos : Int) * (2 ^ qNeg : Int)
  have hlhsI_eq : lhsI = ((a.toNat * 2 ^ qPos * 10 ^ kNeg : Nat) : Int) := by
    show a * (2 ^ qPos : Int) * (10 ^ kNeg : Int)
          = ((a.toNat * 2 ^ qPos * 10 ^ kNeg : Nat) : Int)
    push_cast
    rw [ha_toNat]
  have hrhsI_eq : rhsI = ((b.toNat * 10 ^ kPos * 2 ^ qNeg : Nat) : Int) := by
    show b * (10 ^ kPos : Int) * (2 ^ qNeg : Int)
          = ((b.toNat * 10 ^ kPos * 2 ^ qNeg : Nat) : Int)
    push_cast
    rw [hb_toNat]
  set lhsN : Nat := a.toNat * 2 ^ qPos * 10 ^ kNeg
  set rhsN : Nat := b.toNat * 10 ^ kPos * 2 ^ qNeg
  rw [hlhsI_eq, hrhsI_eq]
  repeat' split
  all_goals omega

/-! ## Power regrouping

`2^s · 2^qNeg · 2^hNeg = 2^qPos · 2^hPos` when `s = q + h` and we
split each variable into positive/negative parts.  Used to convert
between the kernel's `a · 2^s` form and the `cmpScaledMixed` lhs's
`a · 2^qPos · 10^kNeg` form. -/

/-- When `s + qNeg + hNeg = qPos + hPos` as Nats (which is the form of
    the equation `s = (qPos - qNeg) + (hPos - hNeg)` rearranged to
    avoid Nat subtraction), the powers regroup. -/
theorem two_pow_regroup (s qPos qNeg hPos hNeg : Nat)
    (hsum : s + qNeg + hNeg = qPos + hPos) :
    (2 : Nat) ^ s * 2 ^ qNeg * 2 ^ hNeg = 2 ^ qPos * 2 ^ hPos := by
  rw [← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add]
  congr 1

/-- Variant: split apart the LHS using the signed equation `s = q + h`. -/
theorem two_pow_regroup_of_eq (q h s : Int) (hsum : s = q + h) :
    let qPos : Nat := if q ≥ 0 then q.toNat else 0
    let qNeg : Nat := if q < 0 then (-q).toNat else 0
    let hPos : Nat := if h ≥ 0 then h.toNat else 0
    let hNeg : Nat := if h < 0 then (-h).toNat else 0
    let sPos : Nat := if s ≥ 0 then s.toNat else 0
    let sNeg : Nat := if s < 0 then (-s).toNat else 0
    sPos + qNeg + hNeg = qPos + hPos + sNeg := by
  -- Reduce to integer linear arithmetic on the toNat parts.
  have h_q_split : (q : Int) =
      (if q ≥ 0 then (q.toNat : Int) else 0) - (if q < 0 then ((-q).toNat : Int) else 0) := by
    by_cases hq : q ≥ 0
    · have hnotneg : ¬ q < 0 := by omega
      simp only [if_pos hq, if_neg hnotneg]
      rw [Int.toNat_of_nonneg hq]; grind
    · push_neg at hq
      have hnotpos : ¬ q ≥ 0 := by omega
      simp only [if_neg hnotpos, if_pos hq]
      rw [Int.toNat_of_nonneg (by omega : 0 ≤ -q)]; omega
  have h_h_split : (h : Int) =
      (if h ≥ 0 then (h.toNat : Int) else 0) - (if h < 0 then ((-h).toNat : Int) else 0) := by
    by_cases hh : h ≥ 0
    · have hnotneg : ¬ h < 0 := by omega
      simp only [if_pos hh, if_neg hnotneg]
      rw [Int.toNat_of_nonneg hh]; grind
    · push_neg at hh
      have hnotpos : ¬ h ≥ 0 := by omega
      simp only [if_neg hnotpos, if_pos hh]
      rw [Int.toNat_of_nonneg (by omega : 0 ≤ -h)]; omega
  have h_s_split : (s : Int) =
      (if s ≥ 0 then (s.toNat : Int) else 0) - (if s < 0 then ((-s).toNat : Int) else 0) := by
    by_cases hs : s ≥ 0
    · have hnotneg : ¬ s < 0 := by omega
      simp only [if_pos hs, if_neg hnotneg]
      rw [Int.toNat_of_nonneg hs]; grind
    · push_neg at hs
      have hnotpos : ¬ s ≥ 0 := by omega
      simp only [if_neg hnotpos, if_pos hs]
      rw [Int.toNat_of_nonneg (by omega : 0 ≤ -s)]; omega
  -- Sum: s = q + h gives a linear relation between the Nat parts.
  have heq : (if s ≥ 0 then (s.toNat : Int) else 0)
              - (if s < 0 then ((-s).toNat : Int) else 0)
              = ((if q ≥ 0 then (q.toNat : Int) else 0)
                  - (if q < 0 then ((-q).toNat : Int) else 0))
                + ((if h ≥ 0 then (h.toNat : Int) else 0)
                  - (if h < 0 then ((-h).toNat : Int) else 0)) := by
    rw [← h_s_split, ← h_q_split, ← h_h_split]; exact hsum
  -- Push to Nat: eliminate every `if` (in `hsum` and the goal) by case
  -- splitting; omega closes each branch, pruning the contradictory ones.
  repeat' split at hsum
  all_goals repeat' split
  all_goals omega

/-! ## Nat verdict ⇒ Int comparison

These lemmas bridge from the abstract verdict lemmas
(`verdict_plus_one_correct`, `verdict_minus_one_correct`, in Nat) to
the integer comparison `cmpScaledMixed = ±1`.

The key algebraic step is:
  `a · 2^qPos · 10^kNeg > b · 10^kPos · 2^qNeg`
  ⇔ multiply by `2^hPos · 2^hNeg > 0`
  ⇔ `(a · 2^qPos · 2^hPos) · 10^kNeg · 2^hNeg
     > (b · 10^kPos · 2^qNeg) · 2^hPos · 2^hNeg`
  ⇔ (using `2^s · 2^qNeg · 2^hNeg = 2^qPos · 2^hPos`):
     `a · 2^s · 10^kNeg · 2^hNeg · 2^qNeg
      > b · 10^kPos · 2^qNeg · 2^hPos · 2^hNeg`
  ⇔ divide by `2^qNeg > 0`, multiply by `2^hPos·2^hNeg`...

We avoid the divisions by using `Nat.mul_lt_mul_*` directly. -/

/-- The +1 verdict in Nat ⇒ `cmpScaledMixed = 1` (after Int → Nat reduction).

    Given `a · 2^s · 10^kNeg · 2^hNeg > b · 10^kPos · 2^hPos` (Nat),
    and `2^s · 2^qNeg · 2^hNeg = 2^qPos · 2^hPos`, conclude
    `a · 2^qPos · 10^kNeg > b · 10^kPos · 2^qNeg` (Nat). -/
theorem cmpScaledMixed_plus_one
    (a b s qPos qNeg hPos hNeg kPos kNeg : Nat)
    (hRegroup : 2 ^ s * 2 ^ qNeg * 2 ^ hNeg = 2 ^ qPos * 2 ^ hPos)
    (hVerdict : a * 2 ^ s * 10 ^ kNeg * 2 ^ hNeg > b * (10 ^ kPos * 2 ^ hPos)) :
    a * 2 ^ qPos * 10 ^ kNeg > b * 10 ^ kPos * 2 ^ qNeg := by
  -- Multiply both sides of the desired inequality by 2^hPos · 2^hNeg.
  -- a · 2^qPos · 10^kNeg · (2^hPos · 2^hNeg)
  --   = a · 10^kNeg · (2^qPos · 2^hPos) · 2^hNeg
  --   = a · 10^kNeg · (2^s · 2^qNeg · 2^hNeg) · 2^hNeg
  -- and the verdict gives us:
  --   a · 2^s · 10^kNeg · 2^hNeg > b · 10^kPos · 2^hPos
  -- multiply by 2^qNeg · 2^hNeg:
  --   a · 2^s · 10^kNeg · 2^hNeg · 2^qNeg · 2^hNeg
  --     > b · 10^kPos · 2^hPos · 2^qNeg · 2^hNeg
  have h2hNeg_pos : 0 < 2 ^ hNeg := Nat.two_pow_pos _
  have h2hPos_pos : 0 < 2 ^ hPos := Nat.two_pow_pos _
  have h2qNeg_pos : 0 < 2 ^ qNeg := Nat.two_pow_pos _
  -- Strategy: assume the goal fails, i.e. `a · 2^qPos · 10^kNeg ≤ b · 10^kPos · 2^qNeg`.
  -- Then multiply by `2^hPos · 2^hNeg` to get a contradiction with `hVerdict`.
  by_contra hContra
  push_neg at hContra
  -- hContra : a · 2^qPos · 10^kNeg ≤ b · 10^kPos · 2^qNeg
  have hMul : a * 2 ^ qPos * 10 ^ kNeg * (2 ^ hPos * 2 ^ hNeg)
                ≤ b * 10 ^ kPos * 2 ^ qNeg * (2 ^ hPos * 2 ^ hNeg) :=
    Nat.mul_le_mul_right _ hContra
  -- Rewrite LHS to involve 2^s.
  have hLHS_rw : a * 2 ^ qPos * 10 ^ kNeg * (2 ^ hPos * 2 ^ hNeg)
                  = a * 2 ^ s * 10 ^ kNeg * 2 ^ hNeg * (2 ^ qNeg * 2 ^ hNeg) := by
    -- a · 2^qPos · 2^hPos = a · (2^s · 2^qNeg · 2^hNeg)
    have h1 : 2 ^ qPos * 2 ^ hPos = 2 ^ s * 2 ^ qNeg * 2 ^ hNeg := hRegroup.symm
    calc a * 2 ^ qPos * 10 ^ kNeg * (2 ^ hPos * 2 ^ hNeg)
        = a * (2 ^ qPos * 2 ^ hPos) * 10 ^ kNeg * 2 ^ hNeg := by grind
      _ = a * (2 ^ s * 2 ^ qNeg * 2 ^ hNeg) * 10 ^ kNeg * 2 ^ hNeg := by rw [h1]
      _ = a * 2 ^ s * 10 ^ kNeg * 2 ^ hNeg * (2 ^ qNeg * 2 ^ hNeg) := by grind
  -- Rewrite RHS.
  have hRHS_rw : b * 10 ^ kPos * 2 ^ qNeg * (2 ^ hPos * 2 ^ hNeg)
                  = b * (10 ^ kPos * 2 ^ hPos) * (2 ^ qNeg * 2 ^ hNeg) := by grind
  rw [hLHS_rw, hRHS_rw] at hMul
  -- a · 2^s · 10^kNeg · 2^hNeg · X ≤ b · (10^kPos · 2^hPos) · X
  -- where X = 2^qNeg · 2^hNeg > 0.  Cancel X.
  have hX_pos : 0 < 2 ^ qNeg * 2 ^ hNeg := Nat.mul_pos h2qNeg_pos h2hNeg_pos
  have hcontra2 : a * 2 ^ s * 10 ^ kNeg * 2 ^ hNeg ≤ b * (10 ^ kPos * 2 ^ hPos) :=
    Nat.le_of_mul_le_mul_right hMul hX_pos
  -- But hVerdict says strict greater than.
  omega

/-- The -1 verdict in Nat ⇒ `cmpScaledMixed = -1` (after Int → Nat reduction).

    Given `a · 2^s · 10^kNeg · 2^hNeg < b · 10^kPos · 2^hPos` (Nat strict),
    conclude `a · 2^qPos · 10^kNeg < b · 10^kPos · 2^qNeg` (Nat strict). -/
theorem cmpScaledMixed_minus_one
    (a b s qPos qNeg hPos hNeg kPos kNeg : Nat)
    (hRegroup : 2 ^ s * 2 ^ qNeg * 2 ^ hNeg = 2 ^ qPos * 2 ^ hPos)
    (hVerdict : a * 2 ^ s * 10 ^ kNeg * 2 ^ hNeg < b * (10 ^ kPos * 2 ^ hPos)) :
    a * 2 ^ qPos * 10 ^ kNeg < b * 10 ^ kPos * 2 ^ qNeg := by
  have h2hNeg_pos : 0 < 2 ^ hNeg := Nat.two_pow_pos _
  have h2hPos_pos : 0 < 2 ^ hPos := Nat.two_pow_pos _
  have h2qNeg_pos : 0 < 2 ^ qNeg := Nat.two_pow_pos _
  by_contra hContra
  push_neg at hContra
  -- hContra : a · 2^qPos · 10^kNeg ≥ b · 10^kPos · 2^qNeg
  have hMul : a * 2 ^ qPos * 10 ^ kNeg * (2 ^ hPos * 2 ^ hNeg)
                ≥ b * 10 ^ kPos * 2 ^ qNeg * (2 ^ hPos * 2 ^ hNeg) :=
    Nat.mul_le_mul_right _ hContra
  have hLHS_rw : a * 2 ^ qPos * 10 ^ kNeg * (2 ^ hPos * 2 ^ hNeg)
                  = a * 2 ^ s * 10 ^ kNeg * 2 ^ hNeg * (2 ^ qNeg * 2 ^ hNeg) := by
    have h1 : 2 ^ qPos * 2 ^ hPos = 2 ^ s * 2 ^ qNeg * 2 ^ hNeg := hRegroup.symm
    calc a * 2 ^ qPos * 10 ^ kNeg * (2 ^ hPos * 2 ^ hNeg)
        = a * (2 ^ qPos * 2 ^ hPos) * 10 ^ kNeg * 2 ^ hNeg := by grind
      _ = a * (2 ^ s * 2 ^ qNeg * 2 ^ hNeg) * 10 ^ kNeg * 2 ^ hNeg := by rw [h1]
      _ = a * 2 ^ s * 10 ^ kNeg * 2 ^ hNeg * (2 ^ qNeg * 2 ^ hNeg) := by grind
  have hRHS_rw : b * 10 ^ kPos * 2 ^ qNeg * (2 ^ hPos * 2 ^ hNeg)
                  = b * (10 ^ kPos * 2 ^ hPos) * (2 ^ qNeg * 2 ^ hNeg) := by grind
  rw [hLHS_rw, hRHS_rw] at hMul
  have hX_pos : 0 < 2 ^ qNeg * 2 ^ hNeg := Nat.mul_pos h2qNeg_pos h2hNeg_pos
  have hcontra2 : a * 2 ^ s * 10 ^ kNeg * 2 ^ hNeg ≥ b * (10 ^ kPos * 2 ^ hPos) :=
    Nat.le_of_mul_le_mul_right hMul hX_pos
  omega

/-! ## Kernel R = b · g is exact when b < 2^60

`mul192_b_g_toNat` gives `R.toNat = (b · g) % 2^192`.  When `b < 2^60`
and `g < 2^128`, `b · g < 2^188 < 2^192`, so the `mod` is trivial. -/

/-- When `b < 2^60`, the 192-bit triple constructed from
    `(bU * gLo, mulHi64 bU gLo, bU * gHi, mulHi64 bU gHi)` plus carry
    represents the exact product `b · (gHi · 2^64 + gLo)`. -/
theorem kernel_R_eq (bU gHi gLo : UInt64)
    (hb_lt : bU.toNat < 2 ^ 60) :
    let rLo  := bU * gLo
    let rLoH := mulHi64 bU gLo
    let rHi  := bU * gHi
    let rHiH := mulHi64 bU gHi
    let midSum   : UInt64 := rHi + rLoH
    let midCarry : UInt64 := if midSum < rHi then 1 else 0
    let r_hi  : UInt64 := rHiH + midCarry
    let r_mid : UInt64 := midSum
    let r_lo  : UInt64 := rLo
    triple192Nat r_hi r_mid r_lo
      = bU.toNat * (gHi.toNat * 2 ^ 64 + gLo.toNat) := by
  -- Use mul192_b_g_toNat and bound the product.
  have hkey := mul192_b_g_toNat bU gHi gLo
  simp only at hkey
  -- b · g < 2^60 · 2^128 = 2^188 < 2^192.
  have hgHi : gHi.toNat < 2 ^ 64 := gHi.toNat_lt
  have hgLo : gLo.toNat < 2 ^ 64 := gLo.toNat_lt
  have hg_lt : gHi.toNat * 2 ^ 64 + gLo.toNat < 2 ^ 128 := by
    have h128 : (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 := by decide
    have h1 : gHi.toNat * 2 ^ 64 ≤ (2 ^ 64 - 1) * 2 ^ 64 := by
      apply Nat.mul_le_mul_right; omega
    have h2 : (2 ^ 64 - 1) * 2 ^ 64 + 2 ^ 64 = 2 ^ 64 * 2 ^ 64 := by
      have hpow_pos : (0 : Nat) < 2 ^ 64 := Nat.two_pow_pos _
      have : (2 ^ 64 - 1) * 2 ^ 64 = 2 ^ 64 * 2 ^ 64 - 2 ^ 64 := by
        rw [Nat.sub_mul]
      omega
    omega
  have hprod_lt : bU.toNat * (gHi.toNat * 2 ^ 64 + gLo.toNat) < 2 ^ 192 := by
    have : bU.toNat * (gHi.toNat * 2 ^ 64 + gLo.toNat) < 2 ^ 60 * 2 ^ 128 :=
      Nat.mul_lt_mul_of_lt_of_lt hb_lt hg_lt
    have h60_128 : (2 : Nat) ^ 60 * 2 ^ 128 ≤ 2 ^ 192 := by
      rw [← Nat.pow_add]; decide
    omega
  simp only
  rw [hkey, Nat.mod_eq_of_lt hprod_lt]

/-! ## Bounds on `qPlusH.toNat` when `64 ≤ qPlusH < 192`

The kernel uses `s := UInt64.ofNat qPlusH.toNat`, then dispatches on
`s < 64`, `s < 128`, etc.  We need to show `s.toNat = qPlusH.toNat`
and bound this. -/

theorem UInt64_ofNat_toNat_of_lt (n : Nat) (hn : n < 2 ^ 64) :
    (UInt64.ofNat n).toNat = n := by
  apply UInt64.toNat_ofNat_of_lt'
  show n < UInt64.size
  have : UInt64.size = 2 ^ 64 := rfl
  rw [this]; exact hn

theorem UInt64_lt_64_iff (s : UInt64) :
    s < (64 : UInt64) ↔ s.toNat < 64 := by
  rw [UInt64.lt_iff_toNat_lt]
  rfl

theorem UInt64_lt_128_iff (s : UInt64) :
    s < (128 : UInt64) ↔ s.toNat < 128 := by
  rw [UInt64.lt_iff_toNat_lt]
  rfl

/-! ## Sandwich lemma for the `shiftedSig` kernel

The Schubfach §9 multiply-shift correctness theorem rests on a
fundamental two-sided inequality:

    N · 2^s ≤ m · g · B < N · 2^s + m · B

where `N = m · 2^qPos · 10^kNeg`, `B = 2^qNeg · 10^kPos`, and `s = h - q`
is the shift amount.  This bounds `m · g · B` (the kernel's pre-shift
product, scaled by the denominator) between consecutive multiples of
`2^s · (something)`, allowing extraction of the floor.

The sandwich is a direct algebraic consequence of the ceiling table
invariant `10^kLookupPos · 2^hPos ≤ g · 10^kLookupNeg · 2^hNeg < 10^kLookupPos · 2^hPos + 10^kLookupNeg · 2^hNeg`
with `kLookup = -k`, which translates to
`10^kNeg · 2^hPos ≤ g · 10^kPos · 2^hNeg < 10^kNeg · 2^hPos + 10^kPos · 2^hNeg`
in `shiftedSig`'s decomposition variables. -/

/-- Abstract sandwich on the kernel pre-shift product.

    Given the ceiling-table invariant (in `shiftedSig`'s decomposition
    variables, where the table's `kLookupPos` is the spec's `kNeg` and
    vice versa), the regrouping identity for `s = h - q ≥ 0`, and
    `m > 0`, the pre-shift product `m · g · B` sandwiches `N · 2^s`
    from below and strictly above with slack `m · B`.

    The strict upper bound requires `m > 0`; for `m = 0` the upper
    bound degenerates to `0 < 0` and fails.  The kernel uses `m < 2^60`
    upstream, where `m = 0` is a trivial input that `shiftedSig` handles
    correctly via the early `m / D = 0` branch. -/
theorem shiftedSig_sandwich
    (m g qPos qNeg kPos kNeg hPos hNeg s : Nat)
    (hm_pos : 0 < m)
    (hRegroup : 2 ^ s * 2 ^ qPos * 2 ^ hNeg = 2 ^ qNeg * 2 ^ hPos)
    (hInv : 10 ^ kNeg * 2 ^ hPos ≤ g * 10 ^ kPos * 2 ^ hNeg
              ∧ g * 10 ^ kPos * 2 ^ hNeg < 10 ^ kNeg * 2 ^ hPos + 10 ^ kPos * 2 ^ hNeg) :
    m * 2 ^ qPos * 10 ^ kNeg * 2 ^ s ≤ m * g * (2 ^ qNeg * 10 ^ kPos)
      ∧ m * g * (2 ^ qNeg * 10 ^ kPos)
          < m * 2 ^ qPos * 10 ^ kNeg * 2 ^ s + m * (2 ^ qNeg * 10 ^ kPos) := by
  obtain ⟨hLo, hHi⟩ := hInv
  have h2hPos_pos : 0 < 2 ^ hPos := Nat.two_pow_pos _
  have h2qPos_pos : 0 < 2 ^ qPos := Nat.two_pow_pos _
  have hmq_pos : 0 < m * 2 ^ qPos := Nat.mul_pos hm_pos h2qPos_pos
  -- Scale invariant by m · 2^qPos.
  have hLo_m :
      m * 2 ^ qPos * (10 ^ kNeg * 2 ^ hPos)
        ≤ m * 2 ^ qPos * (g * 10 ^ kPos * 2 ^ hNeg) :=
    Nat.mul_le_mul_left _ hLo
  have hHi_m :
      m * 2 ^ qPos * (g * 10 ^ kPos * 2 ^ hNeg)
        < m * 2 ^ qPos * (10 ^ kNeg * 2 ^ hPos + 10 ^ kPos * 2 ^ hNeg) :=
    (Nat.mul_lt_mul_left hmq_pos).mpr hHi
  -- Scale by 2^s, apply regroup, divide by 2^hPos.
  have hLo_scaled :
      (m * 2 ^ qPos * 10 ^ kNeg) * 2 ^ s * 2 ^ hPos
        ≤ m * g * (2 ^ qNeg * 10 ^ kPos) * 2 ^ hPos := by
    have h := Nat.mul_le_mul_right (2 ^ s) hLo_m
    have hLHS :
        m * 2 ^ qPos * (10 ^ kNeg * 2 ^ hPos) * 2 ^ s
          = (m * 2 ^ qPos * 10 ^ kNeg) * 2 ^ s * 2 ^ hPos := by grind
    have hRHS :
        m * 2 ^ qPos * (g * 10 ^ kPos * 2 ^ hNeg) * 2 ^ s
          = m * g * 10 ^ kPos * (2 ^ s * 2 ^ qPos * 2 ^ hNeg) := by grind
    have hRHS' :
        m * g * 10 ^ kPos * (2 ^ s * 2 ^ qPos * 2 ^ hNeg)
          = m * g * (2 ^ qNeg * 10 ^ kPos) * 2 ^ hPos := by
      rw [hRegroup]; grind
    rw [hLHS, hRHS, hRHS'] at h
    exact h
  have hLowerBound :
      (m * 2 ^ qPos * 10 ^ kNeg) * 2 ^ s
        ≤ m * g * (2 ^ qNeg * 10 ^ kPos) :=
    Nat.le_of_mul_le_mul_right hLo_scaled h2hPos_pos
  have hHi_scaled :
      m * g * (2 ^ qNeg * 10 ^ kPos) * 2 ^ hPos
        < ((m * 2 ^ qPos * 10 ^ kNeg) * 2 ^ s + m * (2 ^ qNeg * 10 ^ kPos)) * 2 ^ hPos := by
    have h : m * 2 ^ qPos * (g * 10 ^ kPos * 2 ^ hNeg) * 2 ^ s
              < m * 2 ^ qPos * (10 ^ kNeg * 2 ^ hPos + 10 ^ kPos * 2 ^ hNeg) * 2 ^ s :=
      (Nat.mul_lt_mul_right (Nat.two_pow_pos s)).mpr hHi_m
    have hLHS' :
        m * 2 ^ qPos * (g * 10 ^ kPos * 2 ^ hNeg) * 2 ^ s
          = m * g * 10 ^ kPos * (2 ^ s * 2 ^ qPos * 2 ^ hNeg) := by grind
    have hLHS'_eq :
        m * g * 10 ^ kPos * (2 ^ s * 2 ^ qPos * 2 ^ hNeg)
          = m * g * (2 ^ qNeg * 10 ^ kPos) * 2 ^ hPos := by
      rw [hRegroup]; grind
    have hRHS' :
        m * 2 ^ qPos * (10 ^ kNeg * 2 ^ hPos + 10 ^ kPos * 2 ^ hNeg) * 2 ^ s
          = (m * 2 ^ qPos * 10 ^ kNeg) * 2 ^ s * 2 ^ hPos
            + m * 10 ^ kPos * (2 ^ s * 2 ^ qPos * 2 ^ hNeg) := by grind
    have hRHS'_eq :
        (m * 2 ^ qPos * 10 ^ kNeg) * 2 ^ s * 2 ^ hPos
          + m * 10 ^ kPos * (2 ^ s * 2 ^ qPos * 2 ^ hNeg)
          = ((m * 2 ^ qPos * 10 ^ kNeg) * 2 ^ s + m * (2 ^ qNeg * 10 ^ kPos)) * 2 ^ hPos := by
      rw [hRegroup]; grind
    rw [hLHS', hLHS'_eq, hRHS', hRHS'_eq] at h
    exact h
  have hUpperBound :
      m * g * (2 ^ qNeg * 10 ^ kPos)
        < (m * 2 ^ qPos * 10 ^ kNeg) * 2 ^ s + m * (2 ^ qNeg * 10 ^ kPos) :=
    Nat.lt_of_mul_lt_mul_right hHi_scaled
  refine ⟨?_, ?_⟩
  · -- Goal: m · 2^qPos · 10^kNeg · 2^s ≤ m · g · B.
    calc m * 2 ^ qPos * 10 ^ kNeg * 2 ^ s
        = (m * 2 ^ qPos * 10 ^ kNeg) * 2 ^ s := by grind
      _ ≤ m * g * (2 ^ qNeg * 10 ^ kPos) := hLowerBound
  · -- Goal: m · g · B < m · 2^qPos · 10^kNeg · 2^s + m · B.
    calc m * g * (2 ^ qNeg * 10 ^ kPos)
        < (m * 2 ^ qPos * 10 ^ kNeg) * 2 ^ s + m * (2 ^ qNeg * 10 ^ kPos) := hUpperBound
      _ = m * 2 ^ qPos * 10 ^ kNeg * 2 ^ s + m * (2 ^ qNeg * 10 ^ kPos) := by grind

/-! ### Floor-extraction: upper bound `N/B ≤ K` always holds

The lower-side of the sandwich `N · 2^s ≤ m · g · B` gives
`N · 2^s ≤ K · 2^s · B + r` for `r < 2^s · B`, hence `N / B ≤ K`.
This direction is unconditional and follows from the sandwich alone. -/

/-- From the lower-side sandwich, `⌊N/B⌋ ≤ ⌊m · g / 2^s⌋` always. -/
theorem shiftedSig_quotient_upper
    (m g B s N : Nat)
    (hB_pos : 0 < B)
    (hSandwichLo : N * 2 ^ s ≤ m * g * B) :
    N / B ≤ (m * g) / 2 ^ s := by
  have h2s_pos : 0 < 2 ^ s := Nat.two_pow_pos s
  -- Strategy: from N · 2^s ≤ m · g · B, derive (N/B) · 2^s ≤ m · g.
  -- Then K = m·g/2^s and N/B ≤ K via Nat.div_le_div_right.
  have hN_lo : (N / B) * B ≤ N := Nat.div_mul_le_self N B
  -- (N/B) · B · 2^s ≤ N · 2^s ≤ m · g · B.
  have h1 : (N / B) * B * 2 ^ s ≤ m * g * B := by
    have := Nat.mul_le_mul_right (2 ^ s) hN_lo
    omega
  -- Cancel B: (N/B) · 2^s ≤ m · g.
  have h2 : (N / B) * 2 ^ s ≤ m * g := by
    have hrw : (N / B) * B * 2 ^ s = (N / B) * 2 ^ s * B := by grind
    rw [hrw] at h1
    exact Nat.le_of_mul_le_mul_right h1 hB_pos
  -- Divide both sides by 2^s: (N/B) ≤ ⌊m · g / 2^s⌋.
  have : (N / B) ≤ (m * g) / 2 ^ s := by
    have := Nat.div_le_div_right (c := 2 ^ s) h2
    have hself : (N / B) * 2 ^ s / 2 ^ s = N / B :=
      Nat.mul_div_cancel _ h2s_pos
    rw [hself] at this
    exact this
  exact this

/-! ### Safe sub-regime: when `m · B ≤ 2^s`, the floors agree

This is the simpler half of the §9 argument.  When the slack `m · B`
is small relative to the shift `2^s`, the sandwich pins `K · B ≤ N`,
forcing `⌊m · g / 2^s⌋ = ⌊N / B⌋`. -/

/-- Safe floor-extraction.  When the slack `m · B ≤ 2^s`, the kernel
    floor `K = ⌊m·g/2^s⌋` equals `⌊N/B⌋`. -/
theorem shiftedSig_floor_safe
    (m g B s N : Nat)
    (hB_pos : 0 < B)
    (hSafe : m * B ≤ 2 ^ s)
    (hSandwich : N * 2 ^ s ≤ m * g * B ∧ m * g * B < N * 2 ^ s + m * B) :
    (m * g) / 2 ^ s = N / B := by
  obtain ⟨hLo, hHi⟩ := hSandwich
  have h2s_pos : 0 < 2 ^ s := Nat.two_pow_pos s
  have hUpper : N / B ≤ (m * g) / 2 ^ s :=
    shiftedSig_quotient_upper m g B s N hB_pos hLo
  -- Show K ≤ N/B, i.e., K · B ≤ N.
  set K := (m * g) / 2 ^ s with hK_def
  -- K · 2^s ≤ m · g.
  have hK_lo : K * 2 ^ s ≤ m * g := Nat.div_mul_le_self _ _
  -- K · 2^s · B ≤ m · g · B.
  have h1 : K * 2 ^ s * B ≤ m * g * B := Nat.mul_le_mul_right B hK_lo
  -- m · g · B < N · 2^s + m · B ≤ N · 2^s + 2^s = (N + 1) · 2^s (well, with m·B ≤ 2^s).
  -- So K · B · 2^s < (N + 1) · 2^s? No, we want K · B ≤ N.
  -- K · B · 2^s ≤ m · g · B < N · 2^s + m · B ≤ N · 2^s + 2^s = (N + 1) · 2^s.
  -- Hence K · B · 2^s < (N + 1) · 2^s, so K · B < N + 1, i.e., K · B ≤ N.
  have h2 : K * B * 2 ^ s < (N + 1) * 2 ^ s := by
    calc K * B * 2 ^ s
        = K * 2 ^ s * B := by grind
      _ ≤ m * g * B := h1
      _ < N * 2 ^ s + m * B := hHi
      _ ≤ N * 2 ^ s + 2 ^ s := by omega
      _ = (N + 1) * 2 ^ s := by grind
  have h3 : K * B < N + 1 :=
    Nat.lt_of_mul_lt_mul_right h2
  have hKB_le_N : K * B ≤ N := by omega
  have hLower : K ≤ N / B := by
    -- K · B ≤ N, so K ≤ N / B.
    exact (Nat.le_div_iff_mul_le hB_pos).mpr hKB_le_N
  omega

/-! ### Floor-extraction closing lemma

Given the sandwich plus an oracle that the kernel's `K · B ≤ N`, the
floors agree.  This packages the "easy direction" of the argument
into a clean lemma, leaving only the `K · B ≤ N` claim for the
residue analysis to supply.  Useful for separating the analytic
core from the §9.7 number-theoretic argument. -/

/-- Floor extraction given the kernel oracle `K · B ≤ N`.  Combined
    with the always-true `N/B ≤ K`, this forces `K = N/B`. -/
theorem shiftedSig_floor_of_oracle
    (m g B s N : Nat)
    (hB_pos : 0 < B)
    (hSandwichLo : N * 2 ^ s ≤ m * g * B)
    (hOracle : (m * g) / 2 ^ s * B ≤ N) :
    (m * g) / 2 ^ s = N / B := by
  have hUpper : N / B ≤ (m * g) / 2 ^ s :=
    shiftedSig_quotient_upper m g B s N hB_pos hSandwichLo
  have hLower : (m * g) / 2 ^ s ≤ N / B :=
    (Nat.le_div_iff_mul_le hB_pos).mpr hOracle
  omega

/-- Unconditional disagreement bound: under the sandwich and `m < 2^s`, the
    kernel floor `K = ⌊m·g/2^s⌋` exceeds the spec floor `⌊N/B⌋` by at most
    one.  No table-precision assumption needed; the bound is purely a
    consequence of the sandwich's slack-width `m·B` and `m < 2^s`.

    To upgrade to `K = ⌊N/B⌋` (i.e., rule out the `K = ⌊N/B⌋ + 1` case),
    one further needs the residue condition that `B - (N mod B) ≥ m·B/2^s`,
    i.e., that the spec quotient is not within `m/2^s` of an integer.  For
    Schubfach-chosen `k`, this is Nadezhin's R20 (cf. §9.5 of the paper). -/
theorem shiftedSig_floor_disagreement_le_one
    (m g B s N : Nat)
    (hB_pos : 0 < B)
    (hm_lt_2s : m < 2 ^ s)
    (hSandwich : N * 2 ^ s ≤ m * g * B ∧ m * g * B < N * 2 ^ s + m * B) :
    (m * g) / 2 ^ s ≤ N / B + 1 := by
  obtain ⟨_hLo, hHi⟩ := hSandwich
  have h2s_pos : 0 < 2 ^ s := Nat.two_pow_pos s
  set K := (m * g) / 2 ^ s with hK_def
  have hK_lo : K * 2 ^ s ≤ m * g := Nat.div_mul_le_self _ _
  have h1 : K * 2 ^ s * B < N * 2 ^ s + m * B := by
    calc K * 2 ^ s * B ≤ m * g * B := Nat.mul_le_mul_right B hK_lo
      _ < N * 2 ^ s + m * B := hHi
  set Ks := N / B with hKs_def
  have hN_decomp : B * Ks + N % B = N := Nat.div_add_mod N B
  have h_mod_lt : N % B < B := Nat.mod_lt N hB_pos
  have hN_lt : N < (Ks + 1) * B := by
    have heq : (Ks + 1) * B = B * Ks + B := by grind
    omega
  have h2 : N * 2 ^ s < (Ks + 1) * B * 2 ^ s :=
    (Nat.mul_lt_mul_right h2s_pos).mpr hN_lt
  have h3 : K * 2 ^ s * B < (Ks + 1) * B * 2 ^ s + m * B := by omega
  by_contra hContra
  push_neg at hContra
  have hK_ge : Ks + 2 ≤ K := by omega
  have h4 : (Ks + 2) * 2 ^ s * B ≤ K * 2 ^ s * B := by
    apply Nat.mul_le_mul_right
    apply Nat.mul_le_mul_right
    exact hK_ge
  have h5 : (Ks + 2) * 2 ^ s * B < (Ks + 1) * B * 2 ^ s + m * B := by
    calc (Ks + 2) * 2 ^ s * B ≤ K * 2 ^ s * B := h4
      _ < (Ks + 1) * B * 2 ^ s + m * B := h3
  have h6 : 2 ^ s * B < m * B := by
    have h_diff : (Ks + 2) * 2 ^ s * B = (Ks + 1) * 2 ^ s * B + 2 ^ s * B := by grind
    have h_rearrange : (Ks + 1) * B * 2 ^ s = (Ks + 1) * 2 ^ s * B := by grind
    omega
  have : 2 ^ s < m := Nat.lt_of_mul_lt_mul_right h6
  omega

/-! ### R20 residue condition: the floor-extraction closing oracle

The disagreement bound above leaves exactly the `K = ⌊N/B⌋ + 1` case to
rule out.  That case happens iff the kernel quotient `K · B` exceeds `N`,
which (since `⌊N/B⌋ ≤ K ≤ ⌊N/B⌋ + 1`) is equivalent to `K = ⌊N/B⌋ + 1`.

Nadezhin's R20 / Schubfach §9.7 says this never happens for a
Schubfach-chosen `k`: the spec residue `N mod B` stays far enough below
`B` that the table's ceiling-rounding slack `m · B` cannot push the floor
up.  The exact computable form is the *residue condition*

      `(B − (N mod B)) · 2^s ≥ m · B`

i.e. the gap from `N` up to the next multiple of `B`, scaled by `2^s`, is
at least the sandwich slack `m · B`.  Empirically (verified by exact
integer sweep over every binary64 `(m, q)` passing the kernel width
guards) this holds with margin `≳ 2^124` everywhere — see
`tools/r20_residue_sweep.py`.

`shiftedSig_floor_of_residue` discharges the floor equality from this
condition alone; it is the sound reduction target for the R20 proof.  The
*remaining* analytic obligation is to establish `residueR20Cond` over the
binary64 domain (the continued-fraction / irrationality-measure bound). -/

/-- The R20 residue condition, as a `Prop` on the kernel quantities.
    `(B − (N mod B)) · 2^s ≥ m · B`: the spec quotient `N/B` is far enough
    below the next integer that the table truncation slack `m · B` (scaled
    by `2^s`) cannot bump the floor.  This is the computable form of
    Nadezhin's R20 residue bound (Schubfach §9.7). -/
def residueR20Cond (m B s N : Nat) : Prop :=
  (B - N % B) * 2 ^ s ≥ m * B

/-- Arithmetic reduction of `residueR20Cond` to a *normalised distance*
    bound.  If the spec residue is bounded away from `B` by a factor `2^a`
    (`B ≤ (B − N mod B) · 2^a`, i.e. `N mod B ≤ B · (1 − 2^{−a})`) and the
    kernel slack absorbs that factor (`m · 2^a ≤ 2^s`), then the residue
    condition holds.

    For binary64 the kernel guarantees `m < 2^53` and `s ≥ 124`, so any
    `a ≤ 71` makes `m · 2^a < 2^124 ≤ 2^s` automatic — reducing the
    analytic R20 obligation to the *single* distance bound
    `N mod B ≤ B · (1 − 2^{−71})` (the exact-integer sweep shows the true
    closest approach is `≈ 1 − 2^{−21.3}`, a `2^{49}` safety margin). -/
theorem residueR20Cond_of_dist (m B s N a : Nat)
    (hDist : B ≤ (B - N % B) * 2 ^ a)
    (hSlack : m * 2 ^ a ≤ 2 ^ s) :
    residueR20Cond m B s N := by
  unfold residueR20Cond
  -- m · B ≤ m · ((B − ρ) · 2^a) = (B − ρ) · (m · 2^a) ≤ (B − ρ) · 2^s.
  calc m * B ≤ m * ((B - N % B) * 2 ^ a) := Nat.mul_le_mul_left _ hDist
    _ = (B - N % B) * (m * 2 ^ a) := by grind
    _ ≤ (B - N % B) * 2 ^ s := Nat.mul_le_mul_left _ hSlack

/-- R20 residue holds whenever `B` divides `N` (residue 0, the spec
    quotient is exact).  Covers the `B = 1` band and the 2-adic
    `kNeg ≥ qNeg` sub-band where `N mod B = 0`.  Requires only the kernel
    slack `m ≤ 2^s` (automatic for binary64: `m < 2^53 ≤ 2^124 ≤ 2^s`). -/
theorem residueR20Cond_of_dvd (m B s N : Nat)
    (hDvd : B ∣ N) (hSlack : m ≤ 2 ^ s) :
    residueR20Cond m B s N := by
  unfold residueR20Cond
  have hmod : N % B = 0 := Nat.mod_eq_zero_of_dvd hDvd
  rw [hmod, Nat.sub_zero]
  calc m * B = B * m := by grind
    _ ≤ B * 2 ^ s := Nat.mul_le_mul_left _ hSlack

/-- R20 residue holds in the *safe regime* `m · B ≤ 2^s`.  Since
    `N mod B < B` gives `B − N mod B ≥ 1`, the slack `2^s` already
    dominates `m · B`.  This is the residue-shaped repackaging of the
    safe-regime closing step (`shiftedSig_floor_safe`), letting the
    widened floor lemma discharge the safe sub-band uniformly through
    `residueR20Cond`.  Empirically (sweep) the safe regime covers ≈7 %
    of each guard-passing band; the remaining bulk needs the genuine
    §9.7 distance bound. -/
theorem residueR20Cond_of_safe (m B s N : Nat)
    (hB_pos : 0 < B)
    (hSafe : m * B ≤ 2 ^ s) :
    residueR20Cond m B s N := by
  unfold residueR20Cond
  have hmod : N % B < B := Nat.mod_lt N hB_pos
  have hge1 : 1 ≤ B - N % B := by omega
  calc m * B ≤ 2 ^ s := hSafe
    _ = 1 * 2 ^ s := by grind
    _ ≤ (B - N % B) * 2 ^ s := Nat.mul_le_mul_right _ hge1

/-! ### Band 1 (`q < 0, k < 0`): reduction to a 2-adic distance bound

For `q < 0, k < 0` the kernel quantities specialise to `B = 2^qNeg`
(since `kPos = 0`) and `N = m · 10^kNeg` (since `qPos = 0`), with
`kNeg ≤ qNeg` (true for every guard-passing band-1 input, where
`k = ⌊q·log₁₀2⌋` gives `|k| < |q|`, i.e. `e := qNeg − kNeg ≥ 0`).

Writing `N = m · 2^kNeg · 5^kNeg` and factoring `2^kNeg` out of the
residue (`5` is a 2-adic unit), the gap from `N` up to the next multiple
of `B` is

    B − N mod B = 2^kNeg · (2^e − ((m·5^kNeg) mod 2^e)).

The residue condition `(B − N mod B)·2^s ≥ m·B` therefore cancels the
common `2^kNeg` and reduces to the **2-adic distance bound**

    (2^e − ((m·5^kNeg) mod 2^e)) · 2^s ≥ m · 2^e          (†)

i.e. `m·5^kNeg` stays bounded (2-adically) away from the next multiple
of `2^e`.  `(†)` is the band-1 form of the §9.7 / Nadezhin R20
obligation; it is genuinely number-theoretic (the closest approach is
governed by the 2-adic expansion of `5^kNeg`, equivalently the
irrationality measure of `log₂5`), not closable by the elementary
slack argument once `e` exceeds the slack `s − 53` (the empirical worst
case needs `2^e − r ≳ 2^{e−71}` with `e` up to ≈315). -/

/-- Algebraic reduction for band 1: residue factoring `2^kNeg`.  Given
    `kNeg ≤ qNeg` and the 2-adic distance bound `(†)`, the residue
    condition holds for `B = 2^qNeg`, `N = m · 10^kNeg` — exactly the
    `(qPos, kPos) = (0, 0)` instance consumed by
    `shiftedSig_floor_widened_of_residue`. -/
theorem residueR20Cond_band1_of_twoAdic
    (m qNeg kNeg s : Nat)
    (hkle : kNeg ≤ qNeg)
    (hDist : (2 ^ (qNeg - kNeg) - (m * 5 ^ kNeg) % 2 ^ (qNeg - kNeg)) * 2 ^ s
              ≥ m * 2 ^ (qNeg - kNeg)) :
    residueR20Cond m (2 ^ qNeg) s (m * 10 ^ kNeg) := by
  unfold residueR20Cond
  set e := qNeg - kNeg with he
  have h10 : (10 : Nat) ^ kNeg = 2 ^ kNeg * 5 ^ kNeg := by
    rw [show (10 : Nat) = 2 * 5 from rfl, Nat.mul_pow]
  have hsplit : (2 : Nat) ^ qNeg = 2 ^ kNeg * 2 ^ e := by
    rw [he, ← Nat.pow_add]; congr 1; omega
  have hN : m * 10 ^ kNeg = (m * 5 ^ kNeg) * 2 ^ kNeg := by rw [h10]; grind
  have hmod : (m * 10 ^ kNeg) % 2 ^ qNeg = 2 ^ kNeg * ((m * 5 ^ kNeg) % 2 ^ e) := by
    rw [hN, hsplit, Nat.mul_comm (m * 5 ^ kNeg) (2 ^ kNeg),
        Nat.mul_mod_mul_left (2 ^ kNeg) (m * 5 ^ kNeg) (2 ^ e)]
  set r := (m * 5 ^ kNeg) % 2 ^ e with hr
  have hgap : 2 ^ qNeg - (m * 10 ^ kNeg) % 2 ^ qNeg = 2 ^ kNeg * (2 ^ e - r) := by
    rw [hmod, hsplit, Nat.mul_sub]
  rw [hgap, hsplit]
  have hcancel : m * (2 ^ kNeg * 2 ^ e) = 2 ^ kNeg * (m * 2 ^ e) := by grind
  have hRHS : 2 ^ kNeg * (2 ^ e - r) * 2 ^ s = 2 ^ kNeg * ((2 ^ e - r) * 2 ^ s) := by grind
  rw [hcancel, hRHS]
  apply Nat.mul_le_mul_left
  rw [Nat.mul_comm (2 ^ e - r) (2 ^ s)] at hDist ⊢
  omega

/-! ### Band 2 (`q ≥ 0, k ≥ 0`): reduction to a 5-adic distance bound

For `q ≥ 0, k ≥ 0` the kernel quantities specialise to `B = 10^k`
(since `qNeg = 0`) and `N = m · 2^q` (since `kNeg = 0`), with
`k ≤ q` (true for every guard-passing band-2 input, where
`k = ⌊q·log₁₀2⌋ ≤ q`).

Writing `10^k = 2^k · 5^k` and `2^q = 2^k · 2^j` with `j := q − k ≥ 0`,
the residue `(m·2^q) mod 10^k = 2^k · ((m·2^j) mod 5^k)` (factoring the
common `2^k` out of the modulus — `5` is the *odd* part), so the gap up
to the next multiple of `B` is

    B − N mod B = 2^k · (5^k − ((m·2^j) mod 5^k)).

The residue condition `(B − N mod B)·2^s ≥ m·B` therefore cancels the
common `2^k` and reduces to the **5-adic distance bound**

    (5^k − ((m·2^j) mod 5^k)) · 2^s ≥ m · 5^k          (‡)

i.e. `m·2^j` stays bounded (5-adically) away from the next multiple of
`5^k`.  This is the band-2 mirror of `residueR20Cond_band1_of_twoAdic`:
it converts the modulus from the composite `10^k` to the *odd* prime
power `5^k`, in which `2` is a unit — the clean setting for the §9.7
distance bound. -/

/-- Algebraic reduction for band 2: residue factoring `2^k`.  Given
    `k ≤ q` and the 5-adic distance bound `(‡)`, the residue condition
    holds for `B = 10^k`, `N = m · 2^q` — exactly the
    `(qNeg, kNeg) = (0, 0)` instance consumed by
    `shiftedSig_floor_widened_of_residue`. -/
theorem residueR20Cond_band2_of_fiveAdic
    (m q k s : Nat)
    (hkle : k ≤ q)
    (hDist : (5 ^ k - (m * 2 ^ (q - k)) % 5 ^ k) * 2 ^ s
              ≥ m * 5 ^ k) :
    residueR20Cond m (10 ^ k) s (m * 2 ^ q) := by
  unfold residueR20Cond
  set j := q - k with hj
  have h10 : (10 : Nat) ^ k = 2 ^ k * 5 ^ k := by
    rw [show (10 : Nat) = 2 * 5 from rfl, Nat.mul_pow]
  have hsplit : (2 : Nat) ^ q = 2 ^ k * 2 ^ j := by
    rw [hj, ← Nat.pow_add]; congr 1; omega
  -- N = m·2^q = 2^k · (m·2^j)
  have hN : m * 2 ^ q = 2 ^ k * (m * 2 ^ j) := by rw [hsplit]; grind
  -- residue factors the common 2^k out of the (composite) modulus 10^k
  have hmod : (m * 2 ^ q) % 10 ^ k = 2 ^ k * ((m * 2 ^ j) % 5 ^ k) := by
    rw [hN, h10, Nat.mul_mod_mul_left (2 ^ k) (m * 2 ^ j) (5 ^ k)]
  set r := (m * 2 ^ j) % 5 ^ k with hr
  have hgap : 10 ^ k - (m * 2 ^ q) % 10 ^ k = 2 ^ k * (5 ^ k - r) := by
    rw [hmod, h10, Nat.mul_sub]
  rw [hgap, h10]
  -- m · (2^k · 5^k) = 2^k · (m · 5^k)
  have hcancel : m * (2 ^ k * 5 ^ k) = 2 ^ k * (m * 5 ^ k) := by grind
  have hRHS : 2 ^ k * (5 ^ k - r) * 2 ^ s = 2 ^ k * ((5 ^ k - r) * 2 ^ s) := by grind
  rw [hcancel, hRHS]
  apply Nat.mul_le_mul_left
  rw [Nat.mul_comm (5 ^ k - r) (2 ^ s)] at hDist ⊢
  omega

/-- Elementary closure of the band-2 5-adic distance bound `(‡)` in the
    *small-exponent* regime `m · 5^k ≤ 2^s`.  Since the residue
    `(m·2^j) mod 5^k < 5^k`, the gap `5^k − residue ≥ 1`, so the slack
    `2^s` already dominates `m·5^k`.

    For binary64 this covers every band-2 input with `k ≤ 30`: there
    `5^k ≤ 5^30 < 2^70` and `m < 2^53`, hence
    `m · 5^k < 2^{53+70} = 2^123 ≤ 2^124 ≤ 2^s`.  No number-theoretic
    distance bound is needed in this regime — the residue can be
    *adversarially worst* (gap `= 1`) and the condition still holds.
    Only `k > 30` (where `5^k` exceeds the slack) requires the genuine
    §9.7 / irrationality-measure bound. -/
theorem residueR20Cond_band2_elementary
    (m q k s : Nat)
    (hkle : k ≤ q)
    (hSlack : m * 5 ^ k ≤ 2 ^ s) :
    residueR20Cond m (10 ^ k) s (m * 2 ^ q) := by
  apply residueR20Cond_band2_of_fiveAdic m q k s hkle
  set j := q - k with hj
  have h5_pos : 0 < 5 ^ k := Nat.pow_pos (by omega)
  have hmod_lt : (m * 2 ^ j) % 5 ^ k < 5 ^ k := Nat.mod_lt _ h5_pos
  have hge1 : 1 ≤ 5 ^ k - (m * 2 ^ j) % 5 ^ k := by omega
  calc m * 5 ^ k ≤ 2 ^ s := hSlack
    _ = 1 * 2 ^ s := by grind
    _ ≤ (5 ^ k - (m * 2 ^ j) % 5 ^ k) * 2 ^ s := Nat.mul_le_mul_right _ hge1

/-- Elementary closure of the band-1 2-adic distance bound `(†)` in the
    *small-exponent* regime `m · 2^e ≤ 2^s`.  Since the residue
    `(m·5^kNeg) mod 2^e < 2^e`, the gap `2^e − residue ≥ 1`, so the slack
    `2^s` already dominates `m·2^e`.

    For binary64 this covers every band-1 input with `e ≤ 71`: there
    `m < 2^53` gives `m · 2^e < 2^{53+71} = 2^124 ≤ 2^s`.  Mirror of
    `residueR20Cond_band2_elementary`; only `e > 71` needs the genuine
    §9.7 / irrationality-measure (`log₂5`) bound. -/
theorem residueR20Cond_band1_elementary
    (m qNeg kNeg s : Nat)
    (hkle : kNeg ≤ qNeg)
    (hSlack : m * 2 ^ (qNeg - kNeg) ≤ 2 ^ s) :
    residueR20Cond m (2 ^ qNeg) s (m * 10 ^ kNeg) := by
  apply residueR20Cond_band1_of_twoAdic m qNeg kNeg s hkle
  set e := qNeg - kNeg with he
  have h2_pos : 0 < 2 ^ e := Nat.two_pow_pos e
  have hmod_lt : (m * 5 ^ kNeg) % 2 ^ e < 2 ^ e := Nat.mod_lt _ h2_pos
  have hge1 : 1 ≤ 2 ^ e - (m * 5 ^ kNeg) % 2 ^ e := by omega
  calc m * 2 ^ e ≤ 2 ^ s := hSlack
    _ = 1 * 2 ^ s := by grind
    _ ≤ (2 ^ e - (m * 5 ^ kNeg) % 2 ^ e) * 2 ^ s := Nat.mul_le_mul_right _ hge1

/-! ### The unified analytic core: a normalised "modular distance" bound

After the 5-adic (band 2) and 2-adic (band 1) reductions, *both* bands'
remaining obligation has the identical shape

    (M − (m · u) mod M) · 2^s ≥ m · M               (★)

with `M = 5^k, u = 2^(q−k)` (band 2) or `M = 2^e, u = 5^kNeg` (band 1),
`m < 2^53`, `s ≥ 124`.  `(★)` says the orbit point `m·u` stays a
definite distance *below* the next multiple of `M`.

`farFromMultipleBelow M u m a` is the normalised distance predicate:
the gap `M − (m·u mod M)` is at least `M · 2^{−a}`.  Given this with a
free `a` (any `a ≤ 71` for binary64), `farFromMultipleBelow_residue`
discharges `(★)` via `residueR20Cond_of_dist`.  This is the *single*
analytic statement future work must establish over the binary64 domain
(via continued-fraction best-approximation of `u/M`, equivalently the
irrationality measure of `log₂10` / `log₂5`); everything downstream of
it is already sorry-free. -/

/-- Normalised modular-distance predicate: `m · u` lies at least a
    factor `2^{−a}` of `M` below the next multiple of `M`.  Concretely
    `M ≤ (M − (m·u mod M)) · 2^a`, i.e. the gap up to the next multiple
    is `≥ M · 2^{−a}`.  This is the band-agnostic form of the §9.7
    distance bound; `a` plays the role of the irrationality-measure
    exponent (smaller `a` = stronger separation). -/
def farFromMultipleBelow (M u m a : Nat) : Prop :=
  M ≤ (M - (m * u) % M) * 2 ^ a

/-- The analytic core ⟹ the abstract distance bound `(★)`.  Given the
    normalised separation `farFromMultipleBelow M u m a` and the free
    slack `m · 2^a ≤ 2^s`, the bound `(M − (m·u mod M))·2^s ≥ m·M`
    holds.  Pure repackaging of `residueR20Cond_of_dist` with `B = M`,
    `N = m·u` (so `N mod B = (m·u) mod M`); separated out so both bands
    can consume one statement. -/
theorem farFromMultipleBelow_dist (M u m s a : Nat)
    (hFar : farFromMultipleBelow M u m a)
    (hSlack : m * 2 ^ a ≤ 2 ^ s) :
    (M - (m * u) % M) * 2 ^ s ≥ m * M := by
  have h := residueR20Cond_of_dist m M s (m * u) a hFar hSlack
  unfold residueR20Cond at h
  exact h

/-- The separation predicate holds *trivially with `a = 0`* whenever
    `m·u` is itself a multiple of `M` (residue 0, gap `= M`).  Covers the
    divisible sub-band (`5^k ∣ m·2^j` band 2 — i.e. `5^k ∣ m`; or
    `2^e ∣ m·5^kNeg` — i.e. `2^e ∣ m` — band 1) without any
    number-theoretic input.  Note this is the predicate-level analogue of
    `residueR20Cond_of_dvd`, exposed through `farFromMultipleBelow`. -/
theorem farFromMultipleBelow_of_dvd (M u m : Nat)
    (hDvd : M ∣ (m * u)) :
    farFromMultipleBelow M u m 0 := by
  unfold farFromMultipleBelow
  have hmod : (m * u) % M = 0 := Nat.mod_eq_zero_of_dvd hDvd
  rw [hmod, Nat.sub_zero, Nat.pow_zero, Nat.mul_one]
  exact Nat.le_refl M

/-- Band 2 closed *from the analytic core*: given the binary64 slack
    (`m < 2^53`, `s ≥ 124` ⟹ pick `a ≤ 71`) and the normalised
    separation of `m·2^(q−k)` from multiples of `5^k`, the band-2
    residue condition holds.  This is the drop-in the continued-fraction
    bound feeds once available. -/
theorem residueR20Cond_band2_of_far
    (m q k s a : Nat)
    (hkle : k ≤ q)
    (hFar : farFromMultipleBelow (5 ^ k) (2 ^ (q - k)) m a)
    (hSlack : m * 2 ^ a ≤ 2 ^ s) :
    residueR20Cond m (10 ^ k) s (m * 2 ^ q) :=
  residueR20Cond_band2_of_fiveAdic m q k s hkle
    (farFromMultipleBelow_dist (5 ^ k) (2 ^ (q - k)) m s a hFar hSlack)

/-- Band 1 closed *from the analytic core*: given the binary64 slack and
    the normalised separation of `m·5^kNeg` from multiples of `2^e`
    (`e = qNeg − kNeg`), the band-1 residue condition holds. -/
theorem residueR20Cond_band1_of_far
    (m qNeg kNeg s a : Nat)
    (hkle : kNeg ≤ qNeg)
    (hFar : farFromMultipleBelow (2 ^ (qNeg - kNeg)) (5 ^ kNeg) m a)
    (hSlack : m * 2 ^ a ≤ 2 ^ s) :
    residueR20Cond m (2 ^ qNeg) s (m * 10 ^ kNeg) :=
  residueR20Cond_band1_of_twoAdic m qNeg kNeg s hkle
    (farFromMultipleBelow_dist (2 ^ (qNeg - kNeg)) (5 ^ kNeg) m s a hFar hSlack)

/-- Floor extraction from the R20 residue condition.  Given the sandwich
    and `residueR20Cond`, the kernel floor equals the spec floor.  This is
    the sound bridge that turns R20 into an unconditional
    `K = ⌊N/B⌋` — no `m · B ≤ 2^s` (safe-regime) assumption needed. -/
theorem shiftedSig_floor_of_residue
    (m g B s N : Nat)
    (hB_pos : 0 < B)
    (hSandwich : N * 2 ^ s ≤ m * g * B ∧ m * g * B < N * 2 ^ s + m * B)
    (hResidue : residueR20Cond m B s N) :
    (m * g) / 2 ^ s = N / B := by
  obtain ⟨hLo, hHi⟩ := hSandwich
  have h2s_pos : 0 < 2 ^ s := Nat.two_pow_pos s
  set K := (m * g) / 2 ^ s with hK_def
  have hK_lo : K * 2 ^ s ≤ m * g := Nat.div_mul_le_self _ _
  -- K · B · 2^s ≤ m · g · B < N · 2^s + m · B.
  have hKBs : K * B * 2 ^ s < N * 2 ^ s + m * B := by
    calc K * B * 2 ^ s = K * 2 ^ s * B := by grind
      _ ≤ m * g * B := Nat.mul_le_mul_right B hK_lo
      _ < N * 2 ^ s + m * B := hHi
  -- Decompose N = B · Ks + ρ with ρ = N mod B < B.
  set Ks := N / B with hKs_def
  have hN_decomp : B * Ks + N % B = N := Nat.div_add_mod N B
  have hrho_lt : N % B < B := Nat.mod_lt N hB_pos
  -- Residue: m · B ≤ (B − ρ) · 2^s.
  have hres : m * B ≤ (B - N % B) * 2 ^ s := hResidue
  -- N + (B − ρ) = B · (Ks + 1).
  have hsum : N + (B - N % B) = B * (Ks + 1) := by
    have hexp : B * (Ks + 1) = B * Ks + B := by grind
    omega
  -- K · B · 2^s < B · (Ks + 1) · 2^s.
  have hKBs2 : K * B * 2 ^ s < B * (Ks + 1) * 2 ^ s := by
    have hstep : N * 2 ^ s + m * B ≤ N * 2 ^ s + (B - N % B) * 2 ^ s := by omega
    have hcomb : N * 2 ^ s + (B - N % B) * 2 ^ s = (N + (B - N % B)) * 2 ^ s := by grind
    rw [hcomb, hsum] at hstep
    omega
  -- Cancel 2^s: K · B < B · (Ks + 1).
  have hKB_lt : K * B < B * (Ks + 1) := Nat.lt_of_mul_lt_mul_right hKBs2
  -- Hence K ≤ Ks.
  have hK_le : K ≤ Ks := by
    rcases Nat.lt_or_ge K (Ks + 1) with h | h
    · omega
    · exfalso
      have hge : B * (Ks + 1) ≤ K * B := by
        calc B * (Ks + 1) = (Ks + 1) * B := by grind
          _ ≤ K * B := Nat.mul_le_mul_right B h
      omega
  -- And Ks ≤ K always (lower sandwich).
  have hKge : Ks ≤ K := shiftedSig_quotient_upper m g B s N hB_pos hLo
  omega

/-- R20-widened floor equality at the abstract `shiftedSig` layer.

    This is the direct analogue of the safe-regime closing step in
    `shiftedSig_eq_fast2`, but it replaces the `m · B ≤ 2^s` safety
    hypothesis (which forces the `B < 2^64` guard) by the R20 residue
    condition on the spec quotient.  Given the table invariant, the
    regrouping identity, and `residueR20Cond`, the kernel floor equals
    the spec floor `N / B` — with NO bound on `B`.

    Combining this with a proof of `residueR20Cond` over the binary64
    domain (the remaining analytic obligation) lets the `B < 2^64`
    accuracy guard be dropped from `shiftedSig_fast2`, widening the fast
    path to the full binary64 range. -/
theorem shiftedSig_floor_widened_of_residue
    (m g qPos qNeg kPos kNeg hPos hNeg s : Nat)
    (hm_pos : 0 < m)
    (hRegroup : 2 ^ s * 2 ^ qPos * 2 ^ hNeg = 2 ^ qNeg * 2 ^ hPos)
    (hInv : 10 ^ kNeg * 2 ^ hPos ≤ g * 10 ^ kPos * 2 ^ hNeg
              ∧ g * 10 ^ kPos * 2 ^ hNeg < 10 ^ kNeg * 2 ^ hPos + 10 ^ kPos * 2 ^ hNeg)
    (hResidue :
      residueR20Cond m (2 ^ qNeg * 10 ^ kPos) s (m * 2 ^ qPos * 10 ^ kNeg)) :
    (m * g) / 2 ^ s = (m * 2 ^ qPos * 10 ^ kNeg) / (2 ^ qNeg * 10 ^ kPos) := by
  set B : Nat := 2 ^ qNeg * 10 ^ kPos with hB_def
  set N : Nat := m * 2 ^ qPos * 10 ^ kNeg with hN_def
  have hB_pos : 0 < B :=
    Nat.mul_pos (Nat.two_pow_pos _) (Nat.pow_pos (by decide))
  have hSandwich := shiftedSig_sandwich m g qPos qNeg kPos kNeg hPos hNeg s
                      hm_pos hRegroup hInv
  exact shiftedSig_floor_of_residue m g B s N hB_pos hSandwich hResidue

/-! ### Table-precision-derived bound on the slack `m · B`

The table entries satisfy `g ≥ 2^127` (every `gHi` has its top bit
set), which combined with the table's upper invariant
`g · 10^kPos · 2^hNeg < 10^kNeg · 2^hPos + 10^kPos · 2^hNeg`
gives `(2^127 - 1) · 10^kPos · 2^hNeg < 10^kNeg · 2^hPos`, hence
`2^126 · 10^kPos · 2^hNeg ≤ 10^kNeg · 2^hPos` (the strict factor of 2
gives the room).  Multiplied through by `m` and rearranged via the
regroup identity, this yields the Schubfach §9 high-precision bound

    m · B · 2^126 ≤ N · 2^s

connecting the slack `m · B` (in the sandwich) to the spec numerator
`N · 2^s`.  This is the structural reason why the floor extraction can
succeed for `m · B > 2^s` cases as long as the §9.7 residue argument
goes through. -/

/-- Strict variant of the table's high-precision bound: given the
    invariant plus `g ≥ 2^127`, the LHS `2^127 · 10^kPos · 2^hNeg` is
    strictly less than `10^kNeg · 2^hPos`, with slack `10^kPos · 2^hNeg`. -/
theorem table_high_precision_strict
    (g kPos kNeg hPos hNeg : Nat)
    (hg : 2 ^ 127 ≤ g)
    (hInv : 10 ^ kNeg * 2 ^ hPos ≤ g * 10 ^ kPos * 2 ^ hNeg
              ∧ g * 10 ^ kPos * 2 ^ hNeg < 10 ^ kNeg * 2 ^ hPos + 10 ^ kPos * 2 ^ hNeg) :
    (2 ^ 127 - 1) * (10 ^ kPos * 2 ^ hNeg) < 10 ^ kNeg * 2 ^ hPos := by
  obtain ⟨_, hHi⟩ := hInv
  -- From `2^127 ≤ g`, `(2^127) · 10^kPos · 2^hNeg ≤ g · 10^kPos · 2^hNeg`.
  have h1 : 2 ^ 127 * (10 ^ kPos * 2 ^ hNeg) ≤ g * 10 ^ kPos * 2 ^ hNeg := by
    have := Nat.mul_le_mul_right (10 ^ kPos * 2 ^ hNeg) hg
    -- `this` : 2^127 * (10^kPos * 2^hNeg) ≤ g * (10^kPos * 2^hNeg)
    have hrw2 : g * (10 ^ kPos * 2 ^ hNeg) = g * 10 ^ kPos * 2 ^ hNeg := by grind
    rw [hrw2] at this
    exact this
  -- 2^127 · X ≤ g · X < 10^kNeg · 2^hPos + X.  Subtract X: (2^127 - 1) · X < 10^kNeg · 2^hPos.
  have h2 : 2 ^ 127 * (10 ^ kPos * 2 ^ hNeg) < 10 ^ kNeg * 2 ^ hPos + 10 ^ kPos * 2 ^ hNeg := by
    calc 2 ^ 127 * (10 ^ kPos * 2 ^ hNeg)
        ≤ g * 10 ^ kPos * 2 ^ hNeg := h1
      _ < 10 ^ kNeg * 2 ^ hPos + 10 ^ kPos * 2 ^ hNeg := hHi
  -- (2^127 - 1) · X = 2^127 · X - X < 10^kNeg · 2^hPos (Nat-subtraction).
  have h2_127_pos : (1 : Nat) ≤ 2 ^ 127 := Nat.one_le_two_pow
  have hExpand : (2 ^ 127 - 1) * (10 ^ kPos * 2 ^ hNeg)
                  = 2 ^ 127 * (10 ^ kPos * 2 ^ hNeg) - 10 ^ kPos * 2 ^ hNeg := by
    have := Nat.sub_mul (2 ^ 127) 1 (10 ^ kPos * 2 ^ hNeg)
    omega
  omega

/-- Weakened: `2^126 · 10^kPos · 2^hNeg ≤ 10^kNeg · 2^hPos`.

    Follows from the strict bound `(2^127 - 1) · _ < _` after halving. -/
theorem table_high_precision
    (g kPos kNeg hPos hNeg : Nat)
    (hg : 2 ^ 127 ≤ g)
    (hInv : 10 ^ kNeg * 2 ^ hPos ≤ g * 10 ^ kPos * 2 ^ hNeg
              ∧ g * 10 ^ kPos * 2 ^ hNeg < 10 ^ kNeg * 2 ^ hPos + 10 ^ kPos * 2 ^ hNeg) :
    2 ^ 126 * (10 ^ kPos * 2 ^ hNeg) ≤ 10 ^ kNeg * 2 ^ hPos := by
  have hStrict := table_high_precision_strict g kPos kNeg hPos hNeg hg hInv
  -- 2^126 · X · 2 = 2^127 · X ≤ (2^127 - 1) · X + X < 10^kNeg · 2^hPos + X.
  -- This direction doesn't quite work; let me try a cleaner argument:
  -- 2^126 · X · 2 = 2^127 · X = (2^127 - 1) · X + X.
  -- From hStrict: (2^127 - 1) · X < 10^kNeg · 2^hPos.
  -- So 2^127 · X = (2^127 - 1) · X + X < 10^kNeg · 2^hPos + X.
  -- Doesn't give 2^126 · X · 2 ≤ 10^kNeg · 2^hPos.
  -- Different route: use `2^126 ≤ 2^127 - 1` and Nat.mul_le_mul_right.
  have h1 : 2 ^ 126 ≤ 2 ^ 127 - 1 := by
    have : (2 : Nat) ^ 127 = 2 * 2 ^ 126 := by
      rw [show (127 : Nat) = 1 + 126 from rfl, Nat.pow_add, Nat.pow_one]
    omega
  have h2 : 2 ^ 126 * (10 ^ kPos * 2 ^ hNeg) ≤ (2 ^ 127 - 1) * (10 ^ kPos * 2 ^ hNeg) :=
    Nat.mul_le_mul_right _ h1
  omega

/-- The Schubfach §9 high-precision bound: `m · B · 2^126 ≤ N · 2^s`.

    Pure consequence of the table invariant plus `g ≥ 2^127` plus the
    regroup identity.  Bounds the sandwich's slack `m · B` strictly
    below the kernel's headroom `N · 2^s / 2^126`. -/
theorem shiftedSig_slack_bound
    (m g qPos qNeg kPos kNeg hPos hNeg s : Nat)
    (hg : 2 ^ 127 ≤ g)
    (hRegroup : 2 ^ s * 2 ^ qPos * 2 ^ hNeg = 2 ^ qNeg * 2 ^ hPos)
    (hInv : 10 ^ kNeg * 2 ^ hPos ≤ g * 10 ^ kPos * 2 ^ hNeg
              ∧ g * 10 ^ kPos * 2 ^ hNeg < 10 ^ kNeg * 2 ^ hPos + 10 ^ kPos * 2 ^ hNeg) :
    m * (2 ^ qNeg * 10 ^ kPos) * 2 ^ 126
      ≤ m * 2 ^ qPos * 10 ^ kNeg * 2 ^ s := by
  have hHP := table_high_precision g kPos kNeg hPos hNeg hg hInv
  -- 2^126 · 10^kPos · 2^hNeg ≤ 10^kNeg · 2^hPos.
  -- Multiply by m · 2^qNeg.
  have h1 : m * 2 ^ qNeg * (2 ^ 126 * (10 ^ kPos * 2 ^ hNeg))
              ≤ m * 2 ^ qNeg * (10 ^ kNeg * 2 ^ hPos) :=
    Nat.mul_le_mul_left _ hHP
  -- LHS = m · 2^qNeg · 2^126 · 10^kPos · 2^hNeg = m · B · 2^126 · 2^hNeg.
  have hLHS : m * 2 ^ qNeg * (2 ^ 126 * (10 ^ kPos * 2 ^ hNeg))
              = m * (2 ^ qNeg * 10 ^ kPos) * 2 ^ 126 * 2 ^ hNeg := by grind
  -- RHS = m · 2^qNeg · 10^kNeg · 2^hPos.  Using regroup
  -- 2^qNeg · 2^hPos = 2^s · 2^qPos · 2^hNeg:
  -- RHS = m · 10^kNeg · (2^qNeg · 2^hPos) = m · 10^kNeg · 2^s · 2^qPos · 2^hNeg
  --     = (m · 2^qPos · 10^kNeg) · 2^s · 2^hNeg = N · 2^s · 2^hNeg.
  have hRHS : m * 2 ^ qNeg * (10 ^ kNeg * 2 ^ hPos)
              = m * 2 ^ qPos * 10 ^ kNeg * 2 ^ s * 2 ^ hNeg := by
    have hR := hRegroup
    have hMul : m * 2 ^ qNeg * (10 ^ kNeg * 2 ^ hPos)
                  = m * 10 ^ kNeg * (2 ^ qNeg * 2 ^ hPos) := by grind
    rw [hMul, ← hR]; grind
  rw [hLHS, hRHS] at h1
  -- Cancel 2^hNeg.
  have h2hNeg_pos : 0 < 2 ^ hNeg := Nat.two_pow_pos _
  exact Nat.le_of_mul_le_mul_right h1 h2hNeg_pos

/-! ### Bounded floor disagreement from sandwich + slack bound

Combining the sandwich with the slack bound `m · B · 2^126 ≤ N · 2^s`
yields `K · B − N ≤ N / 2^126` (more precisely, in Nat, an analogous
divisibility statement).  This bounds how far the kernel's floor can
exceed the spec floor; the residue argument then closes by showing
the gap is in fact zero. -/

/-- Bounded floor disagreement.  Given the sandwich and slack bound,
    the kernel's `K · B` exceeds `N` by at most `⌊N / 2^126⌋`.

    For inputs with `N ≤ 2^126`, the bound forces `K · B ≤ N` and the
    proof closes immediately.  For larger `N`, the residue argument
    is needed to show the gap is zero. -/
theorem shiftedSig_floor_gap_bound
    (m g B s N : Nat)
    (_hB_pos : 0 < B)
    (hSandwich : N * 2 ^ s ≤ m * g * B ∧ m * g * B < N * 2 ^ s + m * B)
    (hSlack : m * B * 2 ^ 126 ≤ N * 2 ^ s) :
    let K := (m * g) / 2 ^ s
    K * B ≤ N + N / 2 ^ 126 := by
  obtain ⟨hLo, hHi⟩ := hSandwich
  have h2s_pos : 0 < 2 ^ s := Nat.two_pow_pos s
  have h2_126_pos : 0 < 2 ^ 126 := Nat.two_pow_pos 126
  set K := (m * g) / 2 ^ s with hK_def
  -- K · 2^s ≤ m · g.
  have hK_lo : K * 2 ^ s ≤ m * g := Nat.div_mul_le_self _ _
  -- K · B · 2^s ≤ m · g · B < N · 2^s + m · B.
  have h1 : K * B * 2 ^ s < N * 2 ^ s + m * B := by
    calc K * B * 2 ^ s
        = K * 2 ^ s * B := by grind
      _ ≤ m * g * B := Nat.mul_le_mul_right B hK_lo
      _ < N * 2 ^ s + m * B := hHi
  -- Multiply both sides by 2^126.
  -- K · B · 2^s · 2^126 < (N · 2^s + m · B) · 2^126
  --   = N · 2^s · 2^126 + m · B · 2^126
  --   ≤ N · 2^s · 2^126 + N · 2^s   (using slack bound m · B · 2^126 ≤ N · 2^s)
  --   = N · 2^s · (2^126 + 1).
  have h2 : K * B * 2 ^ s * 2 ^ 126 < N * 2 ^ s * (2 ^ 126 + 1) := by
    have hStep : (N * 2 ^ s + m * B) * 2 ^ 126 ≤ N * 2 ^ s * (2 ^ 126 + 1) := by
      have hExpand : (N * 2 ^ s + m * B) * 2 ^ 126
                      = N * 2 ^ s * 2 ^ 126 + m * B * 2 ^ 126 := by grind
      have hSlack' : m * B * 2 ^ 126 ≤ N * 2 ^ s := hSlack
      have hRHS : N * 2 ^ s * (2 ^ 126 + 1) = N * 2 ^ s * 2 ^ 126 + N * 2 ^ s := by grind
      grind
    calc K * B * 2 ^ s * 2 ^ 126
        < (N * 2 ^ s + m * B) * 2 ^ 126 := by
          have := Nat.mul_lt_mul_right h2_126_pos |>.mpr h1
          have hrw : (N * 2 ^ s + m * B) * 2 ^ 126
                      = N * 2 ^ s * 2 ^ 126 + m * B * 2 ^ 126 := by grind
          have hrw' : K * B * 2 ^ s * 2 ^ 126
                      = (K * B * 2 ^ s) * 2 ^ 126 := by grind
          omega
      _ ≤ N * 2 ^ s * (2 ^ 126 + 1) := hStep
  -- Divide both sides by 2^s · 2^126 in Nat.
  -- K · B · 2^126 < N · (2^126 + 1) (after cancelling 2^s).
  have hCancel_s : K * B * 2 ^ 126 < N * (2 ^ 126 + 1) := by
    -- From h2 with 2^s factored out.
    have hLHS : K * B * 2 ^ s * 2 ^ 126 = K * B * 2 ^ 126 * 2 ^ s := by grind
    have hRHS : N * 2 ^ s * (2 ^ 126 + 1) = N * (2 ^ 126 + 1) * 2 ^ s := by grind
    rw [hLHS, hRHS] at h2
    exact Nat.lt_of_mul_lt_mul_right h2
  -- N · (2^126 + 1) = N · 2^126 + N.  So K · B · 2^126 ≤ N · 2^126 + N - 1 ≤ N · 2^126 + N.
  -- Hence K · B ≤ (N · 2^126 + N) / 2^126 = N + N/2^126 (approx).
  -- More precisely: K · B ≤ N + N / 2^126 + 1 if N % 2^126 > 0, but we want strict.
  -- Cleaner: K · B · 2^126 < N · 2^126 + N ≤ (N + N/2^126 + 1) · 2^126 ... need care.
  -- Use:  K · B · 2^126 < N · 2^126 + N, so K · B · 2^126 ≤ N · 2^126 + N - 1.
  -- Then K · B ≤ N + (N - 1) / 2^126 ≤ N + N / 2^126.
  have hExpand : N * (2 ^ 126 + 1) = N * 2 ^ 126 + N := by grind
  rw [hExpand] at hCancel_s
  -- K · B · 2^126 < N · 2^126 + N.
  -- So K · B · 2^126 ≤ N · 2^126 + N - 1 (Nat).  Hence K · B ≤ N + (N-1)/2^126 ≤ N + N/2^126.
  have h3 : K * B * 2 ^ 126 ≤ N * 2 ^ 126 + N - 1 := by grind
  -- (K · B) ≤ (N · 2^126 + N - 1) / 2^126 ≤ N + (N-1)/2^126 ≤ N + N/2^126.
  -- Divide h3 by 2^126:
  have h4 : K * B ≤ (N * 2 ^ 126 + N - 1) / 2 ^ 126 := by
    have := Nat.div_le_div_right (c := 2 ^ 126) h3
    have hself : K * B * 2 ^ 126 / 2 ^ 126 = K * B :=
      Nat.mul_div_cancel _ h2_126_pos
    rw [hself] at this
    exact this
  -- (N · 2^126 + N - 1) / 2^126 = N + (N - 1) / 2^126.
  -- when N ≥ 1; for N = 0, both sides are 0.
  by_cases hN : N = 0
  · -- N = 0.  From hSlack: m · B · 2^126 ≤ 0, so m · B = 0.
    -- From h1 (post-N=0): K · B · 2^s < 0 + m · B = 0.  So K · B = 0.
    -- Goal: K · B ≤ 0 + 0/2^126 = 0.
    subst hN
    have hSlack' : m * B * 2 ^ 126 ≤ 0 := by simpa using hSlack
    have hmB_zero : m * B = 0 := by
      rcases Nat.mul_eq_zero.mp (by grind : m * B * 2 ^ 126 = 0) with h | h
      · exact h
      · exact absurd h (Nat.pos_iff_ne_zero.mp h2_126_pos)
    have hKB_zero : K * B = 0 := by
      have hh : K * B * 2 ^ s < 0 + m * B := by simpa using h1
      rw [hmB_zero] at hh
      have : K * B * 2 ^ s = 0 := by grind
      rcases Nat.mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd h (Nat.pos_iff_ne_zero.mp h2s_pos)
    show K * B ≤ 0 + 0 / 2 ^ 126
    rw [hKB_zero]; simp
  · -- N ≥ 1.
    have hN_pos : 0 < N := Nat.pos_of_ne_zero hN
    -- (N · 2^126 + N - 1) / 2^126 ≤ N + N/2^126.
    -- N · 2^126 / 2^126 = N.  (N - 1)/2^126 ≤ N/2^126 only if N - 1 < N, true.
    -- Actually we want: K · B ≤ (N · 2^126 + N - 1) / 2^126 ≤ N + N / 2^126.
    have hKey : (N * 2 ^ 126 + N - 1) / 2 ^ 126 ≤ N + N / 2 ^ 126 := by
      have h_sub_le : N * 2 ^ 126 + N - 1 ≤ N * 2 ^ 126 + N := by omega
      have h_div_le : (N * 2 ^ 126 + N - 1) / 2 ^ 126 ≤ (N * 2 ^ 126 + N) / 2 ^ 126 :=
        Nat.div_le_div_right h_sub_le
      have h_split : (N * 2 ^ 126 + N) / 2 ^ 126 = N + N / 2 ^ 126 := by
        -- (N · 2^126 + N) / 2^126: split via Nat.add_mul_div_right (a + b*c)/c = a/c + b.
        have hrw : N * 2 ^ 126 + N = N + N * 2 ^ 126 := by grind
        rw [hrw, Nat.add_mul_div_right N N h2_126_pos]
        omega
      omega
    omega

/-! ## Floor-extraction closing lemma for the kernel

Combining the sandwich + slack bound + analytic precision yields the
floor equality `(m·g) / 2^s = N / B` when the kernel guards hold.

The key argument: from the strict precision invariant (`g ≥ 2^127`,
yielding `(2^127 - 1) · 10^kPos · 2^hNeg < 10^kNeg · 2^hPos`),
we get `m · B · (2^127 - 1) < N · 2^s`.  Combined with the sandwich
`K · B · 2^s ≤ m · g · B < N · 2^s + m · B`, this forces
`(K · B - N) · (2^127 - 1) < N` (in rationals).

For `N < 2^127 - 1`, the strict inequality gives `K · B - N = 0`, i.e.,
`K · B ≤ N`, closing via `shiftedSig_floor_of_oracle`.  The cases
where `N ≥ 2^127 - 1` are bounded above by the kernel's `m < 2^60`
constraint combined with the table's specific `h(k)` values.
-/

/-- Floor equality via the strict precision bound.  Given the strict
    slack `m · B · (2^127 - 1) < N · 2^s` (provided by the table's
    `g ≥ 2^127` normality), the sandwich, and `K · B - N ≤ N / 2^126`
    from the gap bound, we close `(m · g) / 2^s = N / B`. -/
theorem shiftedSig_floor_strict_precision
    (m g B s N : Nat)
    (hB_pos : 0 < B)
    (hSandwich : N * 2 ^ s ≤ m * g * B ∧ m * g * B < N * 2 ^ s + m * B)
    (hStrictSlack : m * B * (2 ^ 127 - 1) < N * 2 ^ s)
    (hN_lt : N < 2 ^ 127 - 1) :
    (m * g) / 2 ^ s = N / B := by
  -- Establish K · B ≤ N from the strict bound.
  obtain ⟨hLo, hHi⟩ := hSandwich
  have h2s_pos : 0 < 2 ^ s := Nat.two_pow_pos s
  set K := (m * g) / 2 ^ s with hK_def
  have hK_lo : K * 2 ^ s ≤ m * g := Nat.div_mul_le_self _ _
  -- K · B · 2^s ≤ m · g · B < N · 2^s + m · B (strict).
  have h_sandwich' : K * B * 2 ^ s ≤ N * 2 ^ s + m * B - 1 := by
    calc K * B * 2 ^ s
        = K * 2 ^ s * B := by grind
      _ ≤ m * g * B := Nat.mul_le_mul_right B hK_lo
      _ ≤ N * 2 ^ s + m * B - 1 := by omega
  -- Suppose K · B > N (contradiction goal).
  -- Then K · B · 2^s ≥ (N + 1) · 2^s = N · 2^s + 2^s.
  -- So 2^s ≤ m · B - 1, i.e., m · B ≥ 2^s + 1.
  -- Combined with m · B · (2^127 - 1) < N · 2^s ≤ (N) · 2^s:
  -- (2^s + 1)(2^127 - 1) ≤ m · B · (2^127 - 1) < N · 2^s.
  -- So 2^s · 2^127 - 2^s + 2^127 - 1 < N · 2^s.
  -- I.e., N · 2^s > 2^s · 2^127 + 2^127 - 2^s - 1, so N > 2^127 + (2^127 - 2^s - 1)/2^s.
  -- For s ≤ 127: N > 2^127 - 1 (approx), so N ≥ 2^127 - 1 (Nat).
  -- This contradicts hN_lt: N < 2^127 - 1.
  have hKB_le_N : K * B ≤ N := by
    by_contra hContra
    push_neg at hContra
    -- K · B > N, so K · B ≥ N + 1.
    have hKB_ge : K * B * 2 ^ s ≥ (N + 1) * 2 ^ s :=
      Nat.mul_le_mul_right _ hContra
    -- (N + 1) · 2^s = N · 2^s + 2^s.
    have h1 : N * 2 ^ s + 2 ^ s ≤ N * 2 ^ s + m * B - 1 := by
      have : (N + 1) * 2 ^ s = N * 2 ^ s + 2 ^ s := by grind
      omega
    -- So 2^s ≤ m · B - 1, i.e., m · B ≥ 2^s + 1.
    have hmB_ge : 2 ^ s + 1 ≤ m * B := by omega
    -- (2^s + 1) · (2^127 - 1) ≤ m · B · (2^127 - 1) < N · 2^s.
    have h2 : (2 ^ s + 1) * (2 ^ 127 - 1) ≤ m * B * (2 ^ 127 - 1) :=
      Nat.mul_le_mul_right _ hmB_ge
    have h3 : (2 ^ s + 1) * (2 ^ 127 - 1) < N * 2 ^ s :=
      Nat.lt_of_le_of_lt h2 hStrictSlack
    -- Expand: (2^s + 1)(2^127 - 1) = 2^s · 2^127 - 2^s + 2^127 - 1.
    have hExpand : (2 ^ s + 1) * (2 ^ 127 - 1) = 2 ^ s * 2 ^ 127 + 2 ^ 127 - 2 ^ s - 1 := by
      have h2_127_pos : (1 : Nat) ≤ 2 ^ 127 := Nat.one_le_two_pow
      have h2_s_pos : (1 : Nat) ≤ 2 ^ s := Nat.one_le_two_pow
      have : (2 ^ s + 1) * (2 ^ 127 - 1) = 2 ^ s * (2 ^ 127 - 1) + (2 ^ 127 - 1) := by grind
      rw [this]
      have ha : 2 ^ s * (2 ^ 127 - 1) = 2 ^ s * 2 ^ 127 - 2 ^ s := by
        rw [Nat.mul_sub_one]
      rw [ha]
      have hBA : 2 ^ s ≤ 2 ^ s * 2 ^ 127 :=
        Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
      exact sub_add_sub_shuffle _ _ _ hBA h2_127_pos
    -- We have h3: 2^s · 2^127 + 2^127 - 2^s - 1 < N · 2^s.
    -- And hN_lt: N < 2^127 - 1, so N · 2^s < (2^127 - 1) · 2^s = 2^s · 2^127 - 2^s.
    have h2_127_pos : (1 : Nat) ≤ 2 ^ 127 := Nat.one_le_two_pow
    have h2_s_pos : (1 : Nat) ≤ 2 ^ s := Nat.one_le_two_pow
    have h4 : N * 2 ^ s ≤ (2 ^ 127 - 2) * 2 ^ s := by
      apply Nat.mul_le_mul_right; omega
    have hExpand2 : (2 ^ 127 - 2) * 2 ^ s = 2 ^ 127 * 2 ^ s - 2 * 2 ^ s := by
      rw [Nat.sub_mul]
    -- Combine: 2^s · 2^127 + 2^127 - 2^s - 1 < N · 2^s ≤ 2^127 · 2^s - 2 · 2^s.
    -- So 2^127 - 2^s - 1 < -2 · 2^s (in ℤ).  But LHS ≥ 0 in Nat — contradiction.
    -- Need to be careful with Nat subtraction.  Let me work with `+`-form.
    -- h3: 2^s · 2^127 + 2^127 - 2^s - 1 < N · 2^s.  Rewrite as:
    --   (2^127 - 2^s - 1) + 2^s · 2^127 < N · 2^s (since 2^s + 1 ≤ 2^127, the sub is positive).
    -- Wait: is 2^s + 1 ≤ 2^127?  s ≤ 191 doesn't bound 2^s ≤ 2^126.
    -- For our use, s ≥ 124, so 2^s ≥ 2^124.  Not necessarily ≤ 2^126.
    -- Actually for in-guard: s ∈ [124, 192).  So 2^s can be up to 2^191, > 2^127.
    -- Hmm, hExpand uses (2^127 - 1) - 2^s which could be negative in Nat.
    -- The Nat-sub `2^127 - 2^s` is 0 when s ≥ 127. So hExpand's RHS is 0 - 1 = 0 (no, 0 - 1 = 0 in Nat).
    -- I need to rethink.
    --
    -- Better strategy: cast to Int.
    -- Work in Nat throughout (avoid Int cast pain).
    -- Key relation: (2^s + 1)(2^127 - 1) < N · 2^s ≤ (2^127 - 2) · 2^s.
    -- Expansion: 2^s · 2^127 + 2^127 - 2^s - 1 < 2^127 · 2^s - 2 · 2^s.
    -- So 2^127 - 2^s - 1 < -2 · 2^s, i.e., 2^127 + 2^s < 1. Contradiction.
    -- Need care with Nat subtraction.  Use that 2 ^ 127 ≥ 1 + 2 * 2^s when ...
    -- Actually for s < 126: 2^s ≤ 2^125 < 2^127 / 2 < 2^127 / 2.  Then 2 · 2^s < 2^127.
    -- For s ≥ 126: 2^s ≥ 2^126, so (2^127 - 2) · 2^s ≥ ?
    --
    -- Cleaner formulation in Nat: directly compute.
    have hSum_Nat : 2 ^ s * (2 ^ 127 - 1) + (2 ^ 127 - 1) = (2 ^ s + 1) * (2 ^ 127 - 1) := by
      grind
    have hRHSbd_Nat : N * 2 ^ s + 2 ^ s ≤ (2 ^ 127 - 1) * 2 ^ s := by
      have : N + 1 ≤ 2 ^ 127 - 1 := by omega
      have h := Nat.mul_le_mul_right (2 ^ s) this
      have : (N + 1) * 2 ^ s = N * 2 ^ s + 2 ^ s := by grind
      omega
    have h2 : (2 ^ s + 1) * (2 ^ 127 - 1) ≤ m * B * (2 ^ 127 - 1) :=
      Nat.mul_le_mul_right _ hmB_ge
    have h3 : (2 ^ s + 1) * (2 ^ 127 - 1) < N * 2 ^ s :=
      Nat.lt_of_le_of_lt h2 hStrictSlack
    -- Expand: (2^s + 1)(2^127 - 1) = 2^s · (2^127 - 1) + (2^127 - 1).
    have h_expand : (2 ^ s + 1) * (2 ^ 127 - 1) = 2 ^ s * (2 ^ 127 - 1) + (2 ^ 127 - 1) := by grind
    rw [h_expand] at h3
    -- N * 2^s ≤ (2^127 - 2) · 2^s.
    have hN_le : N ≤ 2 ^ 127 - 2 := by omega
    have h4 : N * 2 ^ s ≤ (2 ^ 127 - 2) * 2 ^ s := Nat.mul_le_mul_right _ hN_le
    -- (2^127 - 2) · 2^s = 2^s · 2^127 - 2 · 2^s (Nat sub).
    have h2127_ge_2 : 2 ≤ 2 ^ 127 := by
      have : (2 : Nat) ^ 127 = 2 * 2 ^ 126 := by
        rw [show (127 : Nat) = 1 + 126 from rfl, Nat.pow_add, Nat.pow_one]
      have h2_126_pos : 1 ≤ 2 ^ 126 := Nat.one_le_two_pow
      omega
    have h5 : (2 ^ 127 - 2) * 2 ^ s = 2 ^ 127 * 2 ^ s - 2 * 2 ^ s := by
      rw [Nat.sub_mul]
    -- Combine to derive a Nat contradiction.
    -- From h3: 2^s · (2^127 - 1) + (2^127 - 1) < N · 2^s.
    -- From h4: N · 2^s ≤ 2^127 · 2^s - 2 · 2^s.
    -- 2^s · (2^127 - 1) = 2^s · 2^127 - 2^s.
    -- LHS' = (2^s · 2^127 - 2^s) + (2^127 - 1).
    -- N · 2^s ≤ 2^127 · 2^s - 2 · 2^s = 2^s · 2^127 - 2 · 2^s.
    -- So (2^s · 2^127 - 2^s) + (2^127 - 1) < 2^s · 2^127 - 2 · 2^s.
    -- I.e., 2^127 - 1 < (2^s · 2^127 - 2 · 2^s) - (2^s · 2^127 - 2^s) = -2 · 2^s + 2^s = -2^s.
    -- 2^127 - 1 < -2^s.  In Nat: LHS ≥ 0, RHS = 0 (since 2^s > 0).  So 0 < 0.  Contradiction.
    have h2s_pos_2 : 0 < 2 ^ s := Nat.two_pow_pos s
    have h_calc : 2 ^ s * (2 ^ 127 - 1) = 2 ^ s * 2 ^ 127 - 2 ^ s := by
      rw [Nat.mul_sub]; grind
    rw [h_calc] at h3
    rw [h5] at h4
    -- h3: 2^s · 2^127 - 2^s + (2^127 - 1) < N · 2^s
    -- h4: N · 2^s ≤ 2^127 · 2^s - 2 · 2^s
    -- So 2^s · 2^127 - 2^s + (2^127 - 1) < 2^127 · 2^s - 2 · 2^s.
    -- Simplify: 2^s · 2^127 = 2^127 · 2^s. Cancel.
    -- (2^127 - 1) - 2^s < -2 · 2^s, i.e., 2^127 - 1 < -2^s.  Contradiction.
    have h_comm : 2 ^ s * 2 ^ 127 = 2 ^ 127 * 2 ^ s := by grind
    -- Combine via Nat.add_lt_of_lt_sub_left or just omega.
    -- Need to ensure all subs are well-formed.
    -- 2^s · 2^127 ≥ 2^s, so 2^s · 2^127 - 2^s ≥ 0.
    have h_geq : 2 ^ s ≤ 2 ^ s * 2 ^ 127 := by
      have : 2 ^ s * 1 ≤ 2 ^ s * 2 ^ 127 := Nat.mul_le_mul_left _ (Nat.one_le_two_pow)
      omega
    -- 2^127 · 2^s ≥ 2 · 2^s, so the Nat sub on RHS is well-defined.
    have h_geq2 : 2 * 2 ^ s ≤ 2 ^ 127 * 2 ^ s := Nat.mul_le_mul_right _ h2127_ge_2
    omega
  -- K · B ≤ N closes via shiftedSig_floor_of_oracle.
  exact shiftedSig_floor_of_oracle m g B s N hB_pos hLo hKB_le_N

/-- Strict slack: from `g ≥ 2^127` plus the strict precision upper bound,
    `m · B · (2^127 - 1) < N · 2^s`.  Strictly tighter than
    `shiftedSig_slack_bound`. -/
theorem shiftedSig_slack_bound_strict
    (m g qPos qNeg kPos kNeg hPos hNeg s : Nat)
    (hm_pos : 0 < m)
    (hg : 2 ^ 127 ≤ g)
    (hRegroup : 2 ^ s * 2 ^ qPos * 2 ^ hNeg = 2 ^ qNeg * 2 ^ hPos)
    (hInv : 10 ^ kNeg * 2 ^ hPos ≤ g * 10 ^ kPos * 2 ^ hNeg
              ∧ g * 10 ^ kPos * 2 ^ hNeg < 10 ^ kNeg * 2 ^ hPos + 10 ^ kPos * 2 ^ hNeg) :
    m * (2 ^ qNeg * 10 ^ kPos) * (2 ^ 127 - 1) < m * 2 ^ qPos * 10 ^ kNeg * 2 ^ s := by
  obtain ⟨_, hHi⟩ := hInv
  -- From `g ≥ 2^127`: (g - 1) ≥ 2^127 - 1.
  -- Strict invariant: (g - 1) · 10^kPos · 2^hNeg < 10^kNeg · 2^hPos.
  -- So (2^127 - 1) · 10^kPos · 2^hNeg < 10^kNeg · 2^hPos.
  have hg_minus : 2 ^ 127 - 1 ≤ g - 1 := by omega
  have h_strict : (g - 1) * (10 ^ kPos * 2 ^ hNeg) < 10 ^ kNeg * 2 ^ hPos := by
    have hg_pos : 1 ≤ g := by
      have : (1 : Nat) ≤ 2 ^ 127 := Nat.one_le_two_pow
      omega
    have h1 : (g - 1) * (10 ^ kPos * 2 ^ hNeg) + 10 ^ kPos * 2 ^ hNeg
                = g * (10 ^ kPos * 2 ^ hNeg) := by
      have hsub : (g - 1) * (10 ^ kPos * 2 ^ hNeg)
                    = g * (10 ^ kPos * 2 ^ hNeg) - (10 ^ kPos * 2 ^ hNeg) := by
        rw [Nat.sub_mul]; grind
      have h10_pos : 0 < 10 ^ kPos := Nat.pow_pos (by decide)
      have hY_pos : 0 < 10 ^ kPos * 2 ^ hNeg :=
        Nat.mul_pos h10_pos (Nat.two_pow_pos _)
      have hgY_ge : 10 ^ kPos * 2 ^ hNeg ≤ g * (10 ^ kPos * 2 ^ hNeg) := by
        have : 1 ≤ g := hg_pos
        have h_mul : 1 * (10 ^ kPos * 2 ^ hNeg) ≤ g * (10 ^ kPos * 2 ^ hNeg) :=
          Nat.mul_le_mul_right _ this
        omega
      omega
    have h2 : g * (10 ^ kPos * 2 ^ hNeg) = g * 10 ^ kPos * 2 ^ hNeg := by grind
    have h3 : g * 10 ^ kPos * 2 ^ hNeg < 10 ^ kNeg * 2 ^ hPos + 10 ^ kPos * 2 ^ hNeg := hHi
    omega
  have h_127_strict : (2 ^ 127 - 1) * (10 ^ kPos * 2 ^ hNeg) < 10 ^ kNeg * 2 ^ hPos := by
    have h1 : (2 ^ 127 - 1) * (10 ^ kPos * 2 ^ hNeg) ≤ (g - 1) * (10 ^ kPos * 2 ^ hNeg) :=
      Nat.mul_le_mul_right _ hg_minus
    omega
  -- Multiply by m · 2^qNeg and use regroup.
  have hm_qNeg_pos : 0 < m * 2 ^ qNeg := Nat.mul_pos hm_pos (Nat.two_pow_pos _)
  have h_mul : m * 2 ^ qNeg * ((2 ^ 127 - 1) * (10 ^ kPos * 2 ^ hNeg))
                < m * 2 ^ qNeg * (10 ^ kNeg * 2 ^ hPos) :=
    (Nat.mul_lt_mul_left hm_qNeg_pos).mpr h_127_strict
  -- LHS = m · B · (2^127 - 1) · 2^hNeg.
  have hLHS_eq : m * 2 ^ qNeg * ((2 ^ 127 - 1) * (10 ^ kPos * 2 ^ hNeg))
                  = m * (2 ^ qNeg * 10 ^ kPos) * (2 ^ 127 - 1) * 2 ^ hNeg := by grind
  -- RHS = m · 2^qNeg · 10^kNeg · 2^hPos.  Use regroup to convert.
  have hRHS_eq : m * 2 ^ qNeg * (10 ^ kNeg * 2 ^ hPos)
                  = m * 2 ^ qPos * 10 ^ kNeg * 2 ^ s * 2 ^ hNeg := by
    have hMul : m * 2 ^ qNeg * (10 ^ kNeg * 2 ^ hPos)
                  = m * 10 ^ kNeg * (2 ^ qNeg * 2 ^ hPos) := by grind
    rw [hMul, ← hRegroup]; grind
  rw [hLHS_eq, hRHS_eq] at h_mul
  -- Cancel 2^hNeg.
  exact Nat.lt_of_mul_lt_mul_right h_mul

/-! ## Parametric strict precision lemma

A precision-parametric version of `shiftedSig_floor_strict_precision`.
Given `g ≥ 2^P` (implicit via `hStrictSlack` and the strict slack
chain), the floor agreement holds whenever `N < 2^P - 1` AND `P ≥ 2`. -/

/-- Parametric strict precision floor equality.

    Identical to `shiftedSig_floor_strict_precision` but with the
    precision exponent `P` as an explicit parameter, allowing the
    192-bit table (`P = 191`) to reuse the proof without duplication. -/
theorem shiftedSig_floor_strict_precision_param
    (m g B s N P : Nat)
    (hB_pos : 0 < B)
    (hP_ge : 2 ≤ P)
    (hSandwich : N * 2 ^ s ≤ m * g * B ∧ m * g * B < N * 2 ^ s + m * B)
    (hStrictSlack : m * B * (2 ^ P - 1) < N * 2 ^ s)
    (hN_lt : N < 2 ^ P - 1) :
    (m * g) / 2 ^ s = N / B := by
  obtain ⟨hLo, hHi⟩ := hSandwich
  have h2s_pos : 0 < 2 ^ s := Nat.two_pow_pos s
  set K := (m * g) / 2 ^ s with _hK_def
  have hK_lo : K * 2 ^ s ≤ m * g := Nat.div_mul_le_self _ _
  -- Key: identify 2^s · 2^P with 2^(s + P) so omega can use linear facts.
  set Q : Nat := 2 ^ (s + P) with hQ_def
  have hQ_eq : Q = 2 ^ s * 2 ^ P := by rw [hQ_def]; exact Nat.pow_add 2 s P
  have h2P_pos : 1 ≤ 2 ^ P := Nat.one_le_two_pow
  have h2P_ge_2 : 2 ≤ 2 ^ P := by
    have : (2 : Nat) ^ P = 2 ^ (P - 1) * 2 := by
      conv => lhs; rw [show P = (P - 1) + 1 from by omega]
      rw [Nat.pow_succ]
    have h_inner : 1 ≤ 2 ^ (P - 1) := Nat.one_le_two_pow
    omega
  have hKB_le_N : K * B ≤ N := by
    by_contra hContra
    push_neg at hContra
    have hKB_ge : K * B * 2 ^ s ≥ (N + 1) * 2 ^ s :=
      Nat.mul_le_mul_right _ hContra
    have hKBs_lt : K * B * 2 ^ s < N * 2 ^ s + m * B := by
      calc K * B * 2 ^ s = K * 2 ^ s * B := by grind
        _ ≤ m * g * B := Nat.mul_le_mul_right B hK_lo
        _ < N * 2 ^ s + m * B := hHi
    have hmB_ge : 2 ^ s + 1 ≤ m * B := by
      have : (N + 1) * 2 ^ s = N * 2 ^ s + 2 ^ s := by grind
      omega
    -- (2^s + 1) · (2^P - 1) ≤ m · B · (2^P - 1) < N · 2^s.
    have h2 : (2 ^ s + 1) * (2 ^ P - 1) ≤ m * B * (2 ^ P - 1) :=
      Nat.mul_le_mul_right _ hmB_ge
    have h3 : (2 ^ s + 1) * (2 ^ P - 1) < N * 2 ^ s :=
      Nat.lt_of_le_of_lt h2 hStrictSlack
    -- Open up the LHS via h_expand_nat: (2^s+1)*(2^P - 1) + 1 = Q + (2^P - 2^s).
    -- Plus N*2^s ≤ (2^P - 2)*2^s + 0 ≤ Q - 2*2^s (use 2 ≤ 2^P, hN_le).
    have hN_le : N ≤ 2 ^ P - 2 := by omega
    have h4 : N * 2 ^ s ≤ (2 ^ P - 2) * 2 ^ s := Nat.mul_le_mul_right _ hN_le
    -- (2^P - 2) · 2^s = 2^P · 2^s - 2 · 2^s = Q - 2 · 2^s.
    have h5 : (2 ^ P - 2) * 2 ^ s + 2 * 2 ^ s = Q := by
      have h_geq : 2 * 2 ^ s ≤ 2 ^ P * 2 ^ s := Nat.mul_le_mul_right _ h2P_ge_2
      have hsub : (2 ^ P - 2) * 2 ^ s = 2 ^ P * 2 ^ s - 2 * 2 ^ s := by
        rw [Nat.sub_mul]
      have hcomm : 2 ^ P * 2 ^ s = Q := by rw [hQ_eq]; grind
      omega
    -- Rewriting h3: (2^s + 1)(2^P - 1) = 2^s * 2^P - 2^s + 2^P - 1 = Q - 2^s + 2^P - 1.
    have h6 : (2 ^ s + 1) * (2 ^ P - 1) + 2 ^ s + 1 = Q + 2 ^ P := by
      rw [hQ_eq]
      have : (2 ^ s + 1) * (2 ^ P - 1) = (2 ^ s + 1) * 2 ^ P - (2 ^ s + 1) := by
        rw [Nat.mul_sub_one]
      have h_lhs_pos : 2 ^ s + 1 ≤ (2 ^ s + 1) * 2 ^ P := by
        have : (2 ^ s + 1) * 1 ≤ (2 ^ s + 1) * 2 ^ P := Nat.mul_le_mul_left _ h2P_pos
        omega
      have h_expand : (2 ^ s + 1) * 2 ^ P = 2 ^ s * 2 ^ P + 2 ^ P := by grind
      omega
    -- h3: 2^s * 2^P + 2^P - 2^s - 1 < N * 2^s. h4: N * 2^s + 2 * 2^s ≤ 2^P * 2^s = Q.
    -- Hence h3+h4: 2^s * 2^P + 2^P - 2^s - 1 + 2 * 2^s < Q + 0 = Q.
    -- I.e., Q + 2^P + 2^s - 1 < Q. So 2^P + 2^s ≤ 1, contradicting 2^P ≥ 2.
    have h2s_pos_2 : 1 ≤ 2 ^ s := Nat.one_le_two_pow
    omega
  exact shiftedSig_floor_of_oracle m g B s N hB_pos hLo hKB_le_N

/-- Parametric strict slack bound: from `g ≥ 2^P` plus the strict
    precision upper bound, `m · B · (2^P - 1) < N · 2^s`.  Generalises
    `shiftedSig_slack_bound_strict` (P = 127) to any P. -/
theorem shiftedSig_slack_bound_strict_param
    (m g qPos qNeg kPos kNeg hPos hNeg s P : Nat)
    (hm_pos : 0 < m)
    (hg : 2 ^ P ≤ g)
    (hRegroup : 2 ^ s * 2 ^ qPos * 2 ^ hNeg = 2 ^ qNeg * 2 ^ hPos)
    (hInv : 10 ^ kNeg * 2 ^ hPos ≤ g * 10 ^ kPos * 2 ^ hNeg
              ∧ g * 10 ^ kPos * 2 ^ hNeg < 10 ^ kNeg * 2 ^ hPos + 10 ^ kPos * 2 ^ hNeg) :
    m * (2 ^ qNeg * 10 ^ kPos) * (2 ^ P - 1) < m * 2 ^ qPos * 10 ^ kNeg * 2 ^ s := by
  obtain ⟨_, hHi⟩ := hInv
  have hg_minus : 2 ^ P - 1 ≤ g - 1 := by omega
  have hg_pos : 1 ≤ g := by
    have : (1 : Nat) ≤ 2 ^ P := Nat.one_le_two_pow
    omega
  have h_strict : (g - 1) * (10 ^ kPos * 2 ^ hNeg) < 10 ^ kNeg * 2 ^ hPos := by
    have h1 : (g - 1) * (10 ^ kPos * 2 ^ hNeg) + 10 ^ kPos * 2 ^ hNeg
                = g * (10 ^ kPos * 2 ^ hNeg) := by
      have hsub : (g - 1) * (10 ^ kPos * 2 ^ hNeg)
                    = g * (10 ^ kPos * 2 ^ hNeg) - (10 ^ kPos * 2 ^ hNeg) := by
        rw [Nat.sub_mul]; grind
      have hgY_ge : 10 ^ kPos * 2 ^ hNeg ≤ g * (10 ^ kPos * 2 ^ hNeg) := by
        have h_mul : 1 * (10 ^ kPos * 2 ^ hNeg) ≤ g * (10 ^ kPos * 2 ^ hNeg) :=
          Nat.mul_le_mul_right _ hg_pos
        omega
      omega
    have h2 : g * (10 ^ kPos * 2 ^ hNeg) = g * 10 ^ kPos * 2 ^ hNeg := by grind
    omega
  have h_P_strict : (2 ^ P - 1) * (10 ^ kPos * 2 ^ hNeg) < 10 ^ kNeg * 2 ^ hPos := by
    have h1 : (2 ^ P - 1) * (10 ^ kPos * 2 ^ hNeg) ≤ (g - 1) * (10 ^ kPos * 2 ^ hNeg) :=
      Nat.mul_le_mul_right _ hg_minus
    omega
  have hm_qNeg_pos : 0 < m * 2 ^ qNeg := Nat.mul_pos hm_pos (Nat.two_pow_pos _)
  have h_mul : m * 2 ^ qNeg * ((2 ^ P - 1) * (10 ^ kPos * 2 ^ hNeg))
                < m * 2 ^ qNeg * (10 ^ kNeg * 2 ^ hPos) :=
    (Nat.mul_lt_mul_left hm_qNeg_pos).mpr h_P_strict
  have hLHS_eq : m * 2 ^ qNeg * ((2 ^ P - 1) * (10 ^ kPos * 2 ^ hNeg))
                  = m * (2 ^ qNeg * 10 ^ kPos) * (2 ^ P - 1) * 2 ^ hNeg := by grind
  have hRHS_eq : m * 2 ^ qNeg * (10 ^ kNeg * 2 ^ hPos)
                  = m * 2 ^ qPos * 10 ^ kNeg * 2 ^ s * 2 ^ hNeg := by
    have hMul : m * 2 ^ qNeg * (10 ^ kNeg * 2 ^ hPos)
                  = m * 10 ^ kNeg * (2 ^ qNeg * 2 ^ hPos) := by grind
    rw [hMul, ← hRegroup]; grind
  rw [hLHS_eq, hRHS_eq] at h_mul
  exact Nat.lt_of_mul_lt_mul_right h_mul

end Srtfp.Schubfach

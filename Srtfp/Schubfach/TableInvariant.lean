/- Numerical invariant of the 128-bit pow10 table.

   For each entry `(gHi, gLo, h)` at index `i` (i.e., for `k = kMin + i`):
     `g · 10^max(-k,0) · 2^max(-h,0)
      ∈ [10^max(k,0) · 2^max(h,0),  10^max(k,0) · 2^max(h,0) + 10^max(-k,0) · 2^max(-h,0))`
   where `g = gHi · 2^64 + gLo`.

   Equivalently (in ℚ): `g · 2^{-h}` is the ceiling-rounded approximation
   of `10^k` to within `2^{-h}`.

   This file verifies the property via `decide +kernel` on the table data
   and exposes a per-lookup extraction theorem.  Downstream proofs
   (Schubfach §9.6–9.8 multiply-shift correctness) extract the invariant
   for the specific `(gHi, gLo, h) = pow10Lookup128 k` they need. -/
import Srtfp.Schubfach.Pow10Table128
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Srtfp.Schubfach

/-! ## Ceiling invariant as a `Bool` property -/

/-- Per-entry numerical invariant. `(k, gHi, gLo, h)` must satisfy:
    `g · 10^|min(k,0)| · 2^|min(h,0)| ∈ [10^max(k,0)·2^max(h,0), …+slack)`
    where `g = gHi·2^64+gLo` and the slack is `10^|min(k,0)|·2^|min(h,0)|`.

    This is the operational form of `g · 2^{-h} ∈ [10^k, 10^k + 2^{-h})`. -/
def entryInvBool (k : Int) (gHi gLo : UInt64) (h : Int) : Bool :=
  let g : Nat := gHi.toNat * 2^64 + gLo.toNat
  let kPos : Nat := if k ≥ 0 then k.toNat else 0
  let kNeg : Nat := if k < 0 then (-k).toNat else 0
  let hPos : Nat := if h ≥ 0 then h.toNat else 0
  let hNeg : Nat := if h < 0 then (-h).toNat else 0
  let lhs : Nat := g * 10^kNeg * 2^hNeg
  let rhs : Nat := 10^kPos * 2^hPos
  let slack : Nat := 10^kNeg * 2^hNeg
  decide (rhs ≤ lhs) && decide (lhs < rhs + slack)

/-- Boolean invariant aggregated over the whole table.

    Uses explicit `.1` / `.2` projections instead of pattern-matching `let`
    so the definition unfolds cleanly without triggering recursion-depth
    issues when extracting per-entry facts. -/
def tableInv128Bool : Bool :=
  (List.range pow10Table128.size).all fun i =>
    entryInvBool (pow10Table128_kMin + (i : Int))
      (pow10Table128[i]!).1 (pow10Table128[i]!).2.1 (pow10Table128[i]!).2.2

/-- The 128-bit pow10 table satisfies the ceiling invariant for all 649
    entries.  Verified by kernel reduction on the literal table data via
    `decide +kernel` (no `Lean.ofReduceBool` / `Lean.trustCompiler`). -/
theorem tableInv128 : tableInv128Bool = true := by decide +kernel

/-! ## Per-entry extraction

The aggregate invariant is unwieldy.  This section extracts the per-lookup
invariant in arithmetic form, ready for use by downstream proofs. -/

/-- Index of `k` in `pow10Table128` when `k ∈ [kMin, kMax]`. -/
@[inline]
def tableIdx (k : Int) : Nat := (k + 324).toNat

theorem pow10Table128_size_eq : pow10Table128.size = 649 := by decide +kernel

theorem pow10Table128_kMin_def : pow10Table128_kMin = -324 := rfl

theorem pow10Table128_kMax_def : pow10Table128_kMax = 324 := rfl

/-- When `k` is in the tabulated range, `pow10Lookup128` returns the
    `tableIdx k`-th entry. -/
theorem pow10Lookup128_in_range (k : Int)
    (hLo : pow10Table128_kMin ≤ k) (hHi : k ≤ pow10Table128_kMax) :
    pow10Lookup128 k = pow10Table128[tableIdx k]! := by
  unfold pow10Lookup128 tableIdx
  have hLo' : ¬ k < pow10Table128_kMin := not_lt.mpr hLo
  simp only [hLo', if_false]
  have hidx_lt : (k + 324).toNat < pow10Table128.size := by
    have : k + 324 ≤ 648 := by
      have h2 : pow10Table128_kMax = 324 := rfl
      omega
    have hk_nonneg : 0 ≤ k + 324 := by
      have h3 : pow10Table128_kMin = -324 := rfl
      omega
    rw [pow10Table128_size_eq]
    have := Int.toNat_of_nonneg hk_nonneg
    omega
  show pow10Table128.getD ((k + 324).toNat) pow10Table128_default
       = pow10Table128[(k + 324).toNat]!
  rw [(Array.getElem_eq_getD pow10Table128_default (h := hidx_lt)).symm,
      getElem!_pos pow10Table128 _ hidx_lt]

/-! ### Per-entry extraction from `tableInv128Bool` -/

/-- The boolean invariant is `(List.range n).all`-form; extract the entry. -/
theorem entryInvBool_of_tableInv128 (i : Nat) (hi : i < pow10Table128.size) :
    entryInvBool (pow10Table128_kMin + (i : Int))
      (pow10Table128[i]!).1 (pow10Table128[i]!).2.1 (pow10Table128[i]!).2.2 = true := by
  have hAll : tableInv128Bool = true := tableInv128
  unfold tableInv128Bool at hAll
  rw [List.all_eq_true] at hAll
  have hi_mem : i ∈ List.range pow10Table128.size := List.mem_range.mpr hi
  exact hAll i hi_mem

/-! ### Arithmetic invariant for a specific `k`

The `entryInvBool` packs the inequalities behind `&&` and `decide`.
Unpack to a clean `Prop`-level statement for downstream use. -/

/-- Helper: convert `entryInvBool` to its two inequalities. -/
theorem entryInvBool_iff (k : Int) (gHi gLo : UInt64) (h : Int) :
    entryInvBool k gHi gLo h = true ↔
      let g : Nat := gHi.toNat * 2^64 + gLo.toNat
      let kPos : Nat := if k ≥ 0 then k.toNat else 0
      let kNeg : Nat := if k < 0 then (-k).toNat else 0
      let hPos : Nat := if h ≥ 0 then h.toNat else 0
      let hNeg : Nat := if h < 0 then (-h).toNat else 0
      10^kPos * 2^hPos ≤ g * 10^kNeg * 2^hNeg
        ∧ g * 10^kNeg * 2^hNeg < 10^kPos * 2^hPos + 10^kNeg * 2^hNeg := by
  unfold entryInvBool
  simp [Bool.and_eq_true, decide_eq_true_eq]

/-- Final form: `pow10Lookup128 k` satisfies the ceiling invariant when
    `k ∈ [kMin, kMax]`.  The invariant is stated as a conjunction of
    arithmetic inequalities on Nat.  Uses `.1` / `.2.1` / `.2.2` projections
    on `pow10Lookup128 k` to avoid let-pattern recursion-depth issues. -/
theorem pow10Lookup128_invariant (k : Int)
    (hLo : pow10Table128_kMin ≤ k) (hHi : k ≤ pow10Table128_kMax) :
    let gHi := (pow10Lookup128 k).1
    let gLo := (pow10Lookup128 k).2.1
    let h := (pow10Lookup128 k).2.2
    let g : Nat := gHi.toNat * 2^64 + gLo.toNat
    let kPos : Nat := if k ≥ 0 then k.toNat else 0
    let kNeg : Nat := if k < 0 then (-k).toNat else 0
    let hPos : Nat := if h ≥ 0 then h.toNat else 0
    let hNeg : Nat := if h < 0 then (-h).toNat else 0
    10^kPos * 2^hPos ≤ g * 10^kNeg * 2^hNeg
      ∧ g * 10^kNeg * 2^hNeg < 10^kPos * 2^hPos + 10^kNeg * 2^hNeg := by
  have hLookup := pow10Lookup128_in_range k hLo hHi
  have hidx_lt : tableIdx k < pow10Table128.size := by
    unfold tableIdx
    have hk_nonneg : 0 ≤ k + 324 := by
      have : pow10Table128_kMin = -324 := rfl
      omega
    have hk_ub : k + 324 ≤ 648 := by
      have : pow10Table128_kMax = 324 := rfl
      omega
    rw [pow10Table128_size_eq]
    have := Int.toNat_of_nonneg hk_nonneg
    omega
  have hk_eq : pow10Table128_kMin + ((tableIdx k : Nat) : Int) = k := by
    unfold tableIdx
    have hk_nonneg : 0 ≤ k + 324 := by
      have : pow10Table128_kMin = -324 := rfl
      omega
    have h1 : ((k + 324).toNat : Int) = k + 324 := Int.toNat_of_nonneg hk_nonneg
    have h2 : pow10Table128_kMin = -324 := rfl
    omega
  have hEntry_inv := entryInvBool_of_tableInv128 (tableIdx k) hidx_lt
  rw [hk_eq] at hEntry_inv
  -- Rewrite the lookup to the table-indexed entry
  simp only [hLookup]
  exact (entryInvBool_iff k _ _ _).mp hEntry_inv

/-! ## Normality invariant: every `gHi` has its top bit set

Every table entry's `gHi` is in `[2^63, 2^64)`, hence the full 128-bit
`g = gHi · 2^64 + gLo ≥ 2^127`.  This is the §9 high-bit normality
assumption that drives the multiply-shift precision bound. -/

/-- Per-entry normality: `gHi.toNat ≥ 2^63`. -/
def entryNormBool (gHi : UInt64) : Bool :=
  decide ((2 ^ 63 : Nat) ≤ gHi.toNat)

/-- Aggregate normality over the entire table. -/
def tableNorm128Bool : Bool :=
  (List.range pow10Table128.size).all fun i =>
    entryNormBool (pow10Table128[i]!).1

/-- Every table entry's `gHi` has its top bit set.  Verified by
    `decide +kernel` on the literal table data. -/
theorem tableNorm128 : tableNorm128Bool = true := by decide +kernel

/-- Per-entry normality extraction. -/
theorem entryNormBool_of_tableNorm128 (i : Nat) (hi : i < pow10Table128.size) :
    entryNormBool (pow10Table128[i]!).1 = true := by
  have hAll : tableNorm128Bool = true := tableNorm128
  unfold tableNorm128Bool at hAll
  rw [List.all_eq_true] at hAll
  apply hAll
  rw [List.mem_range]
  exact hi

/-- Normality in arithmetic form: `2^63 ≤ gHi.toNat`. -/
theorem pow10Lookup128_gHi_top_bit (k : Int)
    (hLo : pow10Table128_kMin ≤ k) (hHi : k ≤ pow10Table128_kMax) :
    2 ^ 63 ≤ (pow10Lookup128 k).1.toNat := by
  have hLookup := pow10Lookup128_in_range k hLo hHi
  have hidx_lt : tableIdx k < pow10Table128.size := by
    unfold tableIdx
    have hk_nonneg : 0 ≤ k + 324 := by
      have : pow10Table128_kMin = -324 := rfl
      omega
    have hk_ub : k + 324 ≤ 648 := by
      have : pow10Table128_kMax = 324 := rfl
      omega
    rw [pow10Table128_size_eq]
    have := Int.toNat_of_nonneg hk_nonneg
    omega
  have hEntry := entryNormBool_of_tableNorm128 (tableIdx k) hidx_lt
  unfold entryNormBool at hEntry
  rw [decide_eq_true_eq] at hEntry
  rw [hLookup]
  exact hEntry

/-- The full 128-bit `g = gHi · 2^64 + gLo ≥ 2^127`. -/
theorem pow10Lookup128_g_ge (k : Int)
    (hLo : pow10Table128_kMin ≤ k) (hHi : k ≤ pow10Table128_kMax) :
    2 ^ 127 ≤ (pow10Lookup128 k).1.toNat * 2 ^ 64 + (pow10Lookup128 k).2.1.toNat := by
  have hgHi : 2 ^ 63 ≤ (pow10Lookup128 k).1.toNat :=
    pow10Lookup128_gHi_top_bit k hLo hHi
  have h127 : (2 : Nat) ^ 127 = 2 ^ 63 * 2 ^ 64 := by decide
  rw [h127]
  have h1 : 2 ^ 63 * 2 ^ 64 ≤ (pow10Lookup128 k).1.toNat * 2 ^ 64 := by
    exact Nat.mul_le_mul_right _ hgHi
  omega

end Srtfp.Schubfach

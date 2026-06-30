/- Numerical invariant of the 192-bit pow10 table.

   Mirrors `TableInvariant.lean` (128-bit) but for the wider 192-bit
   table.  For each entry `(gHi, gMid, gLo, h)` at index `i` (i.e.,
   for `k = kMin + i`):

     `g · 10^max(-k,0) · 2^max(-h,0)
      ∈ [10^max(k,0) · 2^max(h,0),  10^max(k,0) · 2^max(h,0) + 10^max(-k,0) · 2^max(-h,0))`

   where `g = gHi · 2^128 + gMid · 2^64 + gLo`.

   Equivalently (in ℚ): `g · 2^{-h}` is the ceiling-rounded approximation
   of `10^k` to within `2^{-h}` (relative error < `2^{-191}` post-
   normalization).

   This file verifies the property via `decide +kernel` on the table data
   and exposes a per-lookup extraction theorem (mirror of
   `pow10Lookup128_invariant`).
-/
import Srtfp.Numeric.Schubfach.Perf.Pow10Table192
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace PP.Numeric.Schubfach

set_option maxRecDepth 16384

/-! ## Ceiling invariant as a `Bool` property -/

/-- Per-entry numerical invariant. `(k, gHi, gMid, gLo, h)` must satisfy:
    `g · 10^|min(k,0)| · 2^|min(h,0)| ∈ [10^max(k,0)·2^max(h,0), …+slack)`
    where `g = gHi·2^128+gMid·2^64+gLo` and the slack is
    `10^|min(k,0)|·2^|min(h,0)|`. -/
def entryInvBool192 (k : Int) (gHi gMid gLo : UInt64) (h : Int) : Bool :=
  let g : Nat := gHi.toNat * 2^128 + gMid.toNat * 2^64 + gLo.toNat
  let kPos : Nat := if k ≥ 0 then k.toNat else 0
  let kNeg : Nat := if k < 0 then (-k).toNat else 0
  let hPos : Nat := if h ≥ 0 then h.toNat else 0
  let hNeg : Nat := if h < 0 then (-h).toNat else 0
  let lhs : Nat := g * 10^kNeg * 2^hNeg
  let rhs : Nat := 10^kPos * 2^hPos
  let slack : Nat := 10^kNeg * 2^hNeg
  decide (rhs ≤ lhs) && decide (lhs < rhs + slack)

/-- Boolean invariant aggregated over the whole table. -/
def tableInv192Bool : Bool :=
  (List.range pow10Table192.size).all fun i =>
    entryInvBool192 (pow10Table192_kMin + (i : Int))
      (pow10Table192[i]!).1 (pow10Table192[i]!).2.1
      (pow10Table192[i]!).2.2.1 (pow10Table192[i]!).2.2.2

/-- The 192-bit pow10 table satisfies the ceiling invariant for all 649
    entries.  Verified by kernel reduction on the literal table data via
    `decide +kernel` (no `Lean.ofReduceBool` / `Lean.trustCompiler`). -/
theorem tableInv192 : tableInv192Bool = true := by decide +kernel

/-! ## Per-entry extraction -/

/-- Index of `k` in `pow10Table192` when `k ∈ [kMin, kMax]`. -/
@[inline]
def tableIdx192 (k : Int) : Nat := (k + 324).toNat

theorem pow10Table192_size_eq : pow10Table192.size = 649 := by decide +kernel

theorem pow10Table192_kMin_def : pow10Table192_kMin = -324 := rfl

theorem pow10Table192_kMax_def : pow10Table192_kMax = 324 := rfl

/-- When `k` is in the tabulated range, `pow10Lookup192` returns the
    `tableIdx192 k`-th entry. -/
theorem pow10Lookup192_in_range (k : Int)
    (hLo : pow10Table192_kMin ≤ k) (hHi : k ≤ pow10Table192_kMax) :
    pow10Lookup192 k = pow10Table192[tableIdx192 k]! := by
  unfold pow10Lookup192 tableIdx192
  have hLo' : ¬ k < pow10Table192_kMin := not_lt.mpr hLo
  simp only [hLo', if_false]
  have hidx_lt : (k + 324).toNat < pow10Table192.size := by
    have : k + 324 ≤ 648 := by
      have h2 : pow10Table192_kMax = 324 := rfl
      omega
    have hk_nonneg : 0 ≤ k + 324 := by
      have h3 : pow10Table192_kMin = -324 := rfl
      omega
    rw [pow10Table192_size_eq]
    have := Int.toNat_of_nonneg hk_nonneg
    omega
  show pow10Table192.getD ((k + 324).toNat) pow10Table192_default
       = pow10Table192[(k + 324).toNat]!
  rw [(Array.getElem_eq_getD pow10Table192_default (h := hidx_lt)).symm,
      getElem!_pos pow10Table192 _ hidx_lt]

/-- The boolean invariant is `(List.range n).all`-form; extract the entry. -/
theorem entryInvBool192_of_tableInv192 (i : Nat) (hi : i < pow10Table192.size) :
    entryInvBool192 (pow10Table192_kMin + (i : Int))
      (pow10Table192[i]!).1 (pow10Table192[i]!).2.1
      (pow10Table192[i]!).2.2.1 (pow10Table192[i]!).2.2.2 = true := by
  have hAll : tableInv192Bool = true := tableInv192
  unfold tableInv192Bool at hAll
  rw [List.all_eq_true] at hAll
  have hi_mem : i ∈ List.range pow10Table192.size := List.mem_range.mpr hi
  exact hAll i hi_mem

/-- Helper: convert `entryInvBool192` to its two inequalities. -/
theorem entryInvBool192_iff (k : Int) (gHi gMid gLo : UInt64) (h : Int) :
    entryInvBool192 k gHi gMid gLo h = true ↔
      let g : Nat := gHi.toNat * 2^128 + gMid.toNat * 2^64 + gLo.toNat
      let kPos : Nat := if k ≥ 0 then k.toNat else 0
      let kNeg : Nat := if k < 0 then (-k).toNat else 0
      let hPos : Nat := if h ≥ 0 then h.toNat else 0
      let hNeg : Nat := if h < 0 then (-h).toNat else 0
      10^kPos * 2^hPos ≤ g * 10^kNeg * 2^hNeg
        ∧ g * 10^kNeg * 2^hNeg < 10^kPos * 2^hPos + 10^kNeg * 2^hNeg := by
  unfold entryInvBool192
  simp [Bool.and_eq_true, decide_eq_true_eq]

/-- Final form: `pow10Lookup192 k` satisfies the ceiling invariant when
    `k ∈ [kMin, kMax]`. -/
theorem pow10Lookup192_invariant (k : Int)
    (hLo : pow10Table192_kMin ≤ k) (hHi : k ≤ pow10Table192_kMax) :
    let gHi := (pow10Lookup192 k).1
    let gMid := (pow10Lookup192 k).2.1
    let gLo := (pow10Lookup192 k).2.2.1
    let h := (pow10Lookup192 k).2.2.2
    let g : Nat := gHi.toNat * 2^128 + gMid.toNat * 2^64 + gLo.toNat
    let kPos : Nat := if k ≥ 0 then k.toNat else 0
    let kNeg : Nat := if k < 0 then (-k).toNat else 0
    let hPos : Nat := if h ≥ 0 then h.toNat else 0
    let hNeg : Nat := if h < 0 then (-h).toNat else 0
    10^kPos * 2^hPos ≤ g * 10^kNeg * 2^hNeg
      ∧ g * 10^kNeg * 2^hNeg < 10^kPos * 2^hPos + 10^kNeg * 2^hNeg := by
  have hLookup := pow10Lookup192_in_range k hLo hHi
  have hidx_lt : tableIdx192 k < pow10Table192.size := by
    unfold tableIdx192
    have hk_nonneg : 0 ≤ k + 324 := by
      have : pow10Table192_kMin = -324 := rfl
      omega
    have hk_ub : k + 324 ≤ 648 := by
      have : pow10Table192_kMax = 324 := rfl
      omega
    rw [pow10Table192_size_eq]
    have := Int.toNat_of_nonneg hk_nonneg
    omega
  have hk_eq : pow10Table192_kMin + ((tableIdx192 k : Nat) : Int) = k := by
    unfold tableIdx192
    have hk_nonneg : 0 ≤ k + 324 := by
      have : pow10Table192_kMin = -324 := rfl
      omega
    have h1 : ((k + 324).toNat : Int) = k + 324 := Int.toNat_of_nonneg hk_nonneg
    have h2 : pow10Table192_kMin = -324 := rfl
    omega
  have hEntry_inv := entryInvBool192_of_tableInv192 (tableIdx192 k) hidx_lt
  rw [hk_eq] at hEntry_inv
  simp only [hLookup]
  exact (entryInvBool192_iff k _ _ _ _).mp hEntry_inv

/-! ## Normality invariant: every `gHi` has its top bit set

Every table entry's `gHi` is in `[2^63, 2^64)`, hence the full 192-bit
`g = gHi · 2^128 + gMid · 2^64 + gLo ≥ 2^191`.  This is the §9 high-bit
normality assumption that drives the multiply-shift precision bound. -/

/-- Per-entry normality: `gHi.toNat ≥ 2^63`. -/
def entryNormBool192 (gHi : UInt64) : Bool :=
  decide ((2 ^ 63 : Nat) ≤ gHi.toNat)

/-- Aggregate normality over the entire table. -/
def tableNorm192Bool : Bool :=
  (List.range pow10Table192.size).all fun i =>
    entryNormBool192 (pow10Table192[i]!).1

/-- Every table entry's `gHi` has its top bit set.  Verified by
    `decide +kernel` on the literal table data. -/
theorem tableNorm192 : tableNorm192Bool = true := by decide +kernel

/-- Per-entry normality extraction. -/
theorem entryNormBool192_of_tableNorm192 (i : Nat) (hi : i < pow10Table192.size) :
    entryNormBool192 (pow10Table192[i]!).1 = true := by
  have hAll : tableNorm192Bool = true := tableNorm192
  unfold tableNorm192Bool at hAll
  rw [List.all_eq_true] at hAll
  apply hAll
  rw [List.mem_range]
  exact hi

/-- Normality in arithmetic form: `2^63 ≤ gHi.toNat`. -/
theorem pow10Lookup192_gHi_top_bit (k : Int)
    (hLo : pow10Table192_kMin ≤ k) (hHi : k ≤ pow10Table192_kMax) :
    2 ^ 63 ≤ (pow10Lookup192 k).1.toNat := by
  have hLookup := pow10Lookup192_in_range k hLo hHi
  have hidx_lt : tableIdx192 k < pow10Table192.size := by
    unfold tableIdx192
    have hk_nonneg : 0 ≤ k + 324 := by
      have : pow10Table192_kMin = -324 := rfl
      omega
    have hk_ub : k + 324 ≤ 648 := by
      have : pow10Table192_kMax = 324 := rfl
      omega
    rw [pow10Table192_size_eq]
    have := Int.toNat_of_nonneg hk_nonneg
    omega
  have hEntry := entryNormBool192_of_tableNorm192 (tableIdx192 k) hidx_lt
  unfold entryNormBool192 at hEntry
  rw [decide_eq_true_eq] at hEntry
  rw [hLookup]
  exact hEntry

/-- The full 192-bit `g = gHi · 2^128 + gMid · 2^64 + gLo ≥ 2^191`. -/
theorem pow10Lookup192_g_ge (k : Int)
    (hLo : pow10Table192_kMin ≤ k) (hHi : k ≤ pow10Table192_kMax) :
    2 ^ 191 ≤ (pow10Lookup192 k).1.toNat * 2 ^ 128
                + (pow10Lookup192 k).2.1.toNat * 2 ^ 64
                + (pow10Lookup192 k).2.2.1.toNat := by
  have hgHi : 2 ^ 63 ≤ (pow10Lookup192 k).1.toNat :=
    pow10Lookup192_gHi_top_bit k hLo hHi
  have h191 : (2 : Nat) ^ 191 = 2 ^ 63 * 2 ^ 128 := by decide
  rw [h191]
  have h1 : 2 ^ 63 * 2 ^ 128 ≤ (pow10Lookup192 k).1.toNat * 2 ^ 128 := by
    exact Nat.mul_le_mul_right _ hgHi
  omega

end PP.Numeric.Schubfach

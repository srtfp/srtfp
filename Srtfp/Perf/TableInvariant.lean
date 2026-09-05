module
/- The ceiling invariant of the 128-bit power-of-ten table, read off its
   definition: every entry `(gHi, gLo, h)` for `k` satisfies

     10^k⁺ · 2^h⁺ ≤ g · 10^k⁻ · 2^h⁻ < 10^k⁺ · 2^h⁺ + 10^k⁻ · 2^h⁻,   g = gHi · 2^64 + gLo,

   the `Nat` form of `g · 2^{-h} ∈ [10^k, 10^k + 2^{-h})`. Downstream
   proofs (Schubfach §9.6–9.8 multiply-shift correctness) take it for the
   specific `pow10Lookup128 k` they need. -/
public import Srtfp.Perf.Pow10Table128

@[expose] public section

namespace Srtfp.Schubfach

/-! ## The table's shape -/

theorem pow10Table128_size_eq : pow10Table128.size = 649 := by
  simp [pow10Table128]

/-- Index of `k` in `pow10Table128` when `k ∈ [kMin, kMax]`. -/
@[inline]
def tableIdx (k : Int) : Nat := (k + 324).toNat

/-- When `k` is in the tabulated range, `pow10Lookup128` returns the
    `tableIdx k`-th entry. -/
theorem pow10Lookup128_in_range (k : Int)
    (hLo : pow10Table128_kMin ≤ k) (hHi : k ≤ pow10Table128_kMax) :
    pow10Lookup128 k = pow10Table128[tableIdx k]! := by
  unfold pow10Lookup128 tableIdx
  have hLo' : ¬ k < pow10Table128_kMin := Int.not_lt.mpr hLo
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

/-- The `i`-th entry is the computed entry for `k = i - 324`. -/
theorem pow10Table128_getElem! (i : Nat) (hi : i < 649) :
    pow10Table128[i]! = pow10Entry ((i : Int) - 324) := by
  rw [getElem!_pos pow10Table128 _ (by rw [pow10Table128_size_eq]; exact hi)]
  simp only [pow10Table128, Array.getElem_map, Array.getElem_range]

/-- In range, the lookup is the computed entry. -/
theorem pow10Lookup128_eq (k : Int)
    (hLo : pow10Table128_kMin ≤ k) (hHi : k ≤ pow10Table128_kMax) :
    pow10Lookup128 k = pow10Entry k := by
  have h3 : pow10Table128_kMin = -324 := rfl
  have h4 : pow10Table128_kMax = 324 := rfl
  rw [pow10Lookup128_in_range k hLo hHi, pow10Table128_getElem! _ (by unfold tableIdx; omega)]
  congr 1
  unfold tableIdx
  omega

/-! ## The ceiling -/

/-- `⌈n / d⌉ = (n + d - 1) / d` is bracketed by `n ≤ q · d < n + d`. -/
theorem ceil_bounds {n d : Nat} (hd : 0 < d) :
    n ≤ (n + d - 1) / d * d ∧ (n + d - 1) / d * d < n + d := by
  have h1 := Nat.div_add_mod (n + d - 1) d
  have h2 := Nat.mod_lt (n + d - 1) hd
  rw [Nat.mul_comm] at h1
  omega

theorem pow10Den_pos (k h : Int) : 0 < pow10Den k h :=
  Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos (by decide))

theorem pow10Ceil_bounds (k h : Int) :
    pow10Num k h ≤ pow10Ceil k h * pow10Den k h
      ∧ pow10Ceil k h * pow10Den k h < pow10Num k h + pow10Den k h :=
  ceil_bounds (pow10Den_pos k h)

/-! ## The shift keeps `g` a 128-bit word

`pow10Shift` puts `10^k · 2^h` in `[2^127, 2^128)`, so the ceiling stays
below `2^128` unless the top 128 bits of `5^|k|` are all ones; no
tabulated `k` comes close. Checked by kernel evaluation (`Nat.log2`,
`Nat.pow` and division are native there). -/

def ceilFitsBool : Bool :=
  (List.range 649).all fun i =>
    decide (pow10Ceil ((i : Int) - 324) (pow10Shift ((i : Int) - 324)) < 2 ^ 128)

theorem ceilFits : ceilFitsBool = true := by decide +kernel

theorem pow10Ceil_lt (k : Int) (hLo : pow10Table128_kMin ≤ k) (hHi : k ≤ pow10Table128_kMax) :
    pow10Ceil k (pow10Shift k) < 2 ^ 128 := by
  have hAll := ceilFits
  unfold ceilFitsBool at hAll
  rw [List.all_eq_true] at hAll
  have h3 : pow10Table128_kMin = -324 := rfl
  have h4 : pow10Table128_kMax = 324 := rfl
  have := hAll (k + 324).toNat (List.mem_range.mpr (by omega))
  rw [decide_eq_true_eq, show (((k + 324).toNat : Nat) : Int) - 324 = k by omega] at this
  exact this

/-- The shift lies in `[-2048, 2048)`, so the biased table `hB128` is exact. -/
theorem pow10Shift_bounds (k : Int)
    (hLo : pow10Table128_kMin ≤ k) (hHi : k ≤ pow10Table128_kMax) :
    -2048 ≤ pow10Shift k ∧ pow10Shift k < 2048 := by
  have h3 : pow10Table128_kMin = -324 := rfl
  have h4 : pow10Table128_kMax = 324 := rfl
  have hbig : (10 : Nat) ^ 324 < 2 ^ 1077 := by decide +kernel
  unfold pow10Shift
  split
  · have : Nat.log2 (10 ^ k.toNat) < 1077 := by
      rw [Nat.log2_lt (Nat.ne_of_gt (Nat.pow_pos (by decide)))]
      exact Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) (by omega)) hbig
    omega
  · have : Nat.log2 (10 ^ (-k).toNat) < 1077 := by
      rw [Nat.log2_lt (Nat.ne_of_gt (Nat.pow_pos (by decide)))]
      exact Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) (by omega)) hbig
    omega

/-! ## The invariant -/

/-- The 128-bit word `(gHi, gLo)` of `g < 2^128`, read back. -/
theorem word_of_lt {g : Nat} (hg : g < 2 ^ 128) :
    (UInt64.ofNat (g >>> 64)).toNat * 2 ^ 64 + (UInt64.ofNat g).toNat = g := by
  rw [UInt64.toNat_ofNat', UInt64.toNat_ofNat', Nat.shiftRight_eq_div_pow]
  have : g / 2 ^ 64 < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt this]
  omega

theorem pow10Entry_invariant (k : Int)
    (hLo : pow10Table128_kMin ≤ k) (hHi : k ≤ pow10Table128_kMax) :
    pow10Num k (pow10Entry k).2.2
        ≤ ((pow10Entry k).1.toNat * 2 ^ 64 + (pow10Entry k).2.1.toNat) * pow10Den k (pow10Entry k).2.2
      ∧ ((pow10Entry k).1.toNat * 2 ^ 64 + (pow10Entry k).2.1.toNat) * pow10Den k (pow10Entry k).2.2
        < pow10Num k (pow10Entry k).2.2 + pow10Den k (pow10Entry k).2.2 := by
  unfold pow10Entry
  simp only []
  rw [word_of_lt (pow10Ceil_lt k hLo hHi)]
  exact pow10Ceil_bounds k _

theorem toNat_of_if (x : Int) : (if x ≥ 0 then x.toNat else 0) = x.toNat := by
  split <;> omega

theorem toNat_neg_of_if (x : Int) : (if x < 0 then (-x).toNat else 0) = (-x).toNat := by
  split <;> omega

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
  have := pow10Entry_invariant k hLo hHi
  rw [← pow10Lookup128_eq k hLo hHi] at this
  simp only [pow10Num, pow10Den] at this
  simp only [toNat_of_if, toNat_neg_of_if, Nat.mul_assoc]
  exact this

end Srtfp.Schubfach

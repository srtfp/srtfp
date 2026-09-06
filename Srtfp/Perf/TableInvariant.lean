module
/- The ceiling invariant of the 128-bit power-of-ten table, read off its
   definition: every entry `(gHi, gLo, h)` for `k ∈ [-324, 324]` satisfies

     num ≤ g · den < num + den,   g = gHi · 2^64 + gLo,   10^k · 2^h = num / den,

   the `Nat` form of `g · 2^{-h} ∈ [10^k, 10^k + 2^{-h})`. The fast
   reader's proof (`Srtfp/Perf/ReadFast.lean`) takes it for the specific
   `pow10Lookup128 k` it needs. -/
public import Srtfp.Perf.Pow10Table128
public import Srtfp.Perf.Word

@[expose] public section

namespace Srtfp.Schubfach

/-! ## The table's shape -/

theorem pow10Table128_size_eq : pow10Table128.size = 649 := by
  simp [pow10Table128]

/-- Index of `k` in `pow10Table128` when `k ∈ [kMin, kMax]`. -/
@[inline]
def tableIdx (k : Int) : Nat := (k + 324).toNat

/-- In the tabulated range, `pow10Lookup128` returns the `tableIdx k`-th entry. -/
theorem pow10Lookup128_in_range (k : Int) (hLo : -324 ≤ k) (hHi : k ≤ 324) :
    pow10Lookup128 k = pow10Table128[tableIdx k]! := by
  have hidx : (k + 324).toNat < pow10Table128.size := by rw [pow10Table128_size_eq]; omega
  have hLo' : ¬ k < pow10Table128_kMin := Int.not_lt.mpr hLo
  unfold pow10Lookup128 tableIdx
  rw [if_neg hLo']
  exact (Array.getElem_eq_getD pow10Table128_default (h := hidx)).symm.trans (getElem!_pos pow10Table128 _ hidx).symm

/-- The `i`-th entry is the computed entry for `k = i - 324`. -/
theorem pow10Table128_getElem! (i : Nat) (hi : i < 649) :
    pow10Table128[i]! = pow10Entry ((i : Int) - 324) := by
  rw [getElem!_pos pow10Table128 _ (by rw [pow10Table128_size_eq]; exact hi)]
  simp only [pow10Table128, Array.getElem_map, Array.getElem_range]

/-- In range, the lookup is the computed entry. -/
theorem pow10Lookup128_eq (k : Int) (hLo : -324 ≤ k) (hHi : k ≤ 324) :
    pow10Lookup128 k = pow10Entry k := by
  rw [pow10Lookup128_in_range k hLo hHi, pow10Table128_getElem! _ (by unfold tableIdx; omega)]
  congr 1; unfold tableIdx; omega

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

theorem pow10Ceil_lt (k : Int) (hLo : -324 ≤ k) (hHi : k ≤ 324) :
    pow10Ceil k (pow10Shift k) < 2 ^ 128 := by
  have := List.all_eq_true.mp ceilFits (k + 324).toNat (List.mem_range.mpr (by omega))
  rwa [decide_eq_true_eq, show (((k + 324).toNat : Nat) : Int) - 324 = k by omega] at this

/-! ## The invariant -/

/-- The 128-bit word `(gHi, gLo)` of `g < 2^128`, read back. -/
theorem word_of_lt {g : Nat} (hg : g < 2 ^ 128) :
    (UInt64.ofNat (g >>> 64)).toNat * 2 ^ 64 + (UInt64.ofNat g).toNat = g := by word

/-- The ceiling invariant of the looked-up entry, `num ≤ g · den < num + den`
    with `10^k · 2^h = num / den`. -/
theorem pow10Lookup128_invariant (k : Int) (hLo : -324 ≤ k) (hHi : k ≤ 324) :
    pow10Num k (pow10Lookup128 k).2.2
        ≤ ((pow10Lookup128 k).1.toNat * 2 ^ 64 + (pow10Lookup128 k).2.1.toNat) * pow10Den k (pow10Lookup128 k).2.2
      ∧ ((pow10Lookup128 k).1.toNat * 2 ^ 64 + (pow10Lookup128 k).2.1.toNat) * pow10Den k (pow10Lookup128 k).2.2
        < pow10Num k (pow10Lookup128 k).2.2 + pow10Den k (pow10Lookup128 k).2.2 := by
  rw [pow10Lookup128_eq k hLo hHi]
  unfold pow10Entry
  simp only []
  rw [word_of_lt (pow10Ceil_lt k hLo hHi)]
  exact pow10Ceil_bounds k _

end Srtfp.Schubfach

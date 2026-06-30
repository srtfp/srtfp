/- R14/R15 magic-constant correctness on the binary64 range (M3.8.1).

   The Schubfach printer (`PP.Numeric.Schubfach`) uses two integer
   approximations of transcendental floor-log functions:

     floorLog10Pow2 e               = ⌊log₁₀(2^e)⌋          (R15)
     floorLog10ThreeQuartersPow2 e  = ⌊log₁₀(3/4 · 2^e)⌋   (R14)

   Both are implemented as `Int.fdiv (e * 2^41·log₁₀(2)) 2^41` (with
   constA = ⌊2^41·log₁₀(3/4)⌋ added for R14). Schubfach proves R15
   exact on `[-6432162, 6432162]` and R14 exact on `[-3606689,
   3150619]`, but the binary64 finite-Float domain only spans
   `q ∈ [-1074, 971]` — at most 2046 distinct exponents.

   Strategy. We characterise correctness as a *pure-integer* inequality
   that cross-multiplies away the rational 2^e and 10^k denominators,
   so the predicate is `Decidable` by ordinary `Nat` arithmetic. We
   then close `∀ e ∈ [-1074, 971], R15Holds e` by `decide` over an
   explicit `List.range`-indexed bounded universal. Because the largest
   single comparison is at e = 971 (involving 2^971 vs 10^292, both
   ≈300 digits), we bump `maxRecDepth` and `exponentiation.threshold`
   inside the `decide` block. The whole 2046-case sweep finishes in
   under five seconds at build time.

   No `native_decide`, no `sorry`, no custom axiom — the only axioms
   used are `propext` and `Quot.sound` (from `decide`'s use of `List`
   equational lemmas).

   We export the conclusions in a slightly cleaned-up form
   (`floorLog10Pow2_correct` / `floorLog10ThreeQuartersPow2_correct`),
   each producing the existentially-quantified statement of the form

       ∃ k, floorLog10⋯ e = k ∧ R⋯Holds e

   that downstream Schubfach correctness proofs (M3.8.2+) can consume. -/

import Srtfp.Numeric.Schubfach

namespace PP.Numeric.Schubfach

/-! ## Pure-integer correctness predicates

`R15HoldsAt e` is the cross-multiplied form of `10^k ≤ 2^e < 10^(k+1)`
where `k = floorLog10Pow2 e`. The expression is symmetric in the
treatment of negative `e` / negative `k`: each is split into a
numerator/denominator pair that places all `2^|·|` and `10^|·|`
factors as non-negative-exponent `Nat` powers.

For `2^e`, the rational is `p2e_n / p2e_d` where
  • `e ≥ 0` ⇒ `p2e_n = 2^e`, `p2e_d = 1`
  • `e < 0` ⇒ `p2e_n = 1`,    `p2e_d = 2^|e|`

The `10^k` and `10^(k+1)` halves are analogous. `R15HoldsAt e` then
asserts cross-multiplied inequalities

    p10k_n · p2e_d ≤ p2e_n · p10k_d
    p2e_n  · p10k1_d  <  p10k1_n  · p2e_d

equivalent to `10^k ≤ 2^e ∧ 2^e < 10^(k+1)` for any signs of `e, k`.

The `@[reducible]` attribute lets `decide` see through this definition
during kernel reduction; without it the `Decidable` instance synthesis
fails to unfold the `let`-bindings. -/

@[reducible] def R15HoldsAt (e : Int) : Prop :=
  let k := floorLog10Pow2 e
  let eAbs : Nat := e.natAbs
  let kAbs : Nat := k.natAbs
  let p2e_n  : Nat := if e ≥ 0 then 2 ^ eAbs else 1
  let p2e_d  : Nat := if e ≥ 0 then 1        else 2 ^ eAbs
  let p10k_n : Nat := if k ≥ 0 then 10 ^ kAbs else 1
  let p10k_d : Nat := if k ≥ 0 then 1         else 10 ^ kAbs
  let k1     : Int := k + 1
  let k1Abs  : Nat := k1.natAbs
  let p10k1_n : Nat := if k1 ≥ 0 then 10 ^ k1Abs else 1
  let p10k1_d : Nat := if k1 ≥ 0 then 1          else 10 ^ k1Abs
  (p10k_n * p2e_d ≤ p2e_n * p10k_d) ∧ (p2e_n * p10k1_d < p10k1_n * p2e_d)

/-- `R14HoldsAt e` is the cross-multiplied form of
    `10^k · 4 ≤ 3 · 2^e ∧ 3 · 2^e < 10^(k+1) · 4` where
    `k = floorLog10ThreeQuartersPow2 e`. -/
@[reducible] def R14HoldsAt (e : Int) : Prop :=
  let k := floorLog10ThreeQuartersPow2 e
  let eAbs : Nat := e.natAbs
  let kAbs : Nat := k.natAbs
  let p2e_n  : Nat := if e ≥ 0 then 2 ^ eAbs else 1
  let p2e_d  : Nat := if e ≥ 0 then 1        else 2 ^ eAbs
  let p10k_n : Nat := if k ≥ 0 then 10 ^ kAbs else 1
  let p10k_d : Nat := if k ≥ 0 then 1         else 10 ^ kAbs
  let k1     : Int := k + 1
  let k1Abs  : Nat := k1.natAbs
  let p10k1_n : Nat := if k1 ≥ 0 then 10 ^ k1Abs else 1
  let p10k1_d : Nat := if k1 ≥ 0 then 1          else 10 ^ k1Abs
  (4 * p10k_n * p2e_d ≤ 3 * p2e_n * p10k_d) ∧
    (3 * p2e_n * p10k1_d < 4 * p10k1_n * p2e_d)

/-! ## Range predicates

Each `R⋯ForRangeBool lo hi` is a `Bool`-form universal that `decide`
can verify in one batched kernel reduction (`List.range … |>.all …`).
The companion lemmas `allR⋯Range_iff_forall` translate between the
`Bool` witness and the surface `∀ e : Int` statement. -/

/-- Decidable bounded-universal witness for R15 on `[lo, hi]`. -/
def R15ForRange (lo hi : Int) : Prop :=
  (List.range (hi - lo + 1).toNat).all (fun i => decide (R15HoldsAt (lo + i))) = true

/-- Decidable bounded-universal witness for R14 on `[lo, hi]`. -/
def R14ForRange (lo hi : Int) : Prop :=
  (List.range (hi - lo + 1).toNat).all (fun i => decide (R14HoldsAt (lo + i))) = true

/-- Equivalence between the `Bool` form and the surface `∀ e` form for
R15. The non-empty-range hypothesis `lo ≤ hi + 1` is there so the
`(hi - lo + 1).toNat` truncation does not silently drop cases. -/
theorem R15ForRange_iff_forall (lo hi : Int) (hlh : lo ≤ hi + 1) :
    R15ForRange lo hi ↔ ∀ e : Int, lo ≤ e → e ≤ hi → R15HoldsAt e := by
  unfold R15ForRange
  have hnn : 0 ≤ hi - lo + 1 := by omega
  refine ⟨?_, ?_⟩
  · intro hall e hlo hhi
    have h0 : 0 ≤ e - lo := by omega
    have hlt : e - lo < hi - lo + 1 := by omega
    have hi_eq : (((e - lo).toNat : Nat) : Int) = e - lo := Int.toNat_of_nonneg h0
    have hi_lt : (e - lo).toNat < (hi - lo + 1).toNat := by
      have h1 : (((e - lo).toNat : Nat) : Int) < (((hi - lo + 1).toNat : Nat) : Int) := by
        rw [hi_eq, Int.toNat_of_nonneg hnn]; exact hlt
      exact_mod_cast h1
    rw [List.all_eq_true] at hall
    have hd := hall (e - lo).toNat (List.mem_range.mpr hi_lt)
    have hadd : lo + ((e - lo).toNat : Int) = e := by rw [hi_eq]; omega
    rw [hadd] at hd
    exact of_decide_eq_true hd
  · intro hall
    rw [List.all_eq_true]
    intro i hi_mem
    rw [List.mem_range] at hi_mem
    apply decide_eq_true
    have hi_lt_nat : (i : Int) < ((hi - lo + 1).toNat : Int) := by exact_mod_cast hi_mem
    rw [Int.toNat_of_nonneg hnn] at hi_lt_nat
    have hi_nn : (0 : Int) ≤ i := Int.natCast_nonneg _
    apply hall <;> omega

/-- Equivalence between the `Bool` form and the surface `∀ e` form for R14. -/
theorem R14ForRange_iff_forall (lo hi : Int) (hlh : lo ≤ hi + 1) :
    R14ForRange lo hi ↔ ∀ e : Int, lo ≤ e → e ≤ hi → R14HoldsAt e := by
  unfold R14ForRange
  have hnn : 0 ≤ hi - lo + 1 := by omega
  refine ⟨?_, ?_⟩
  · intro hall e hlo hhi
    have h0 : 0 ≤ e - lo := by omega
    have hlt : e - lo < hi - lo + 1 := by omega
    have hi_eq : (((e - lo).toNat : Nat) : Int) = e - lo := Int.toNat_of_nonneg h0
    have hi_lt : (e - lo).toNat < (hi - lo + 1).toNat := by
      have h1 : (((e - lo).toNat : Nat) : Int) < (((hi - lo + 1).toNat : Nat) : Int) := by
        rw [hi_eq, Int.toNat_of_nonneg hnn]; exact hlt
      exact_mod_cast h1
    rw [List.all_eq_true] at hall
    have hd := hall (e - lo).toNat (List.mem_range.mpr hi_lt)
    have hadd : lo + ((e - lo).toNat : Int) = e := by rw [hi_eq]; omega
    rw [hadd] at hd
    exact of_decide_eq_true hd
  · intro hall
    rw [List.all_eq_true]
    intro i hi_mem
    rw [List.mem_range] at hi_mem
    apply decide_eq_true
    have hi_lt_nat : (i : Int) < ((hi - lo + 1).toNat : Int) := by exact_mod_cast hi_mem
    rw [Int.toNat_of_nonneg hnn] at hi_lt_nat
    have hi_nn : (0 : Int) ≤ i := Int.natCast_nonneg _
    apply hall <;> omega

/-! ## Brute-force sweeps over the binary64 range

The 2046-case sweep is fast enough (~3–5 s) to run as a single
`decide` per side. The resulting theorems are normal `theorem`s,
already opaque by the elaborator's defaults — no further reducibility
annotation needed.

Should pre-commit build times become a problem, these can be split
into chunks (e.g. 200-element windows) by introducing intermediate
range theorems and stitching them with `omega`-driven case splits.
The current single-`decide` form is the simplest correct shape. -/

set_option exponentiation.threshold 4096 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- R15 sweep over the binary64 exponent range. Closed by a single
kernel `decide` reducing the explicit 2046-element `List.all`. -/
theorem R15_binary64_decidable : R15ForRange (-1074) 971 := by
  unfold R15ForRange; decide

set_option exponentiation.threshold 4096 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- R14 sweep over the binary64 exponent range. Closed by a single
kernel `decide` reducing the explicit 2046-element `List.all`. -/
theorem R14_binary64_decidable : R14ForRange (-1074) 971 := by
  unfold R14ForRange; decide

/-! ## Surface universal statements

These are the consumers' API: a clean `∀ e, -1074 ≤ e → e ≤ 971 →
R⋯HoldsAt e`. The proof just dispatches to the decided range and
applies the bridge lemma. -/

/-- R15 (cross-multiplied) holds for every binary64 exponent. -/
theorem R15HoldsAt_in_binary64_range :
    ∀ e : Int, -1074 ≤ e → e ≤ 971 → R15HoldsAt e :=
  (R15ForRange_iff_forall (-1074) 971 (by decide)).mp R15_binary64_decidable

/-- R14 (cross-multiplied) holds for every binary64 exponent. -/
theorem R14HoldsAt_in_binary64_range :
    ∀ e : Int, -1074 ≤ e → e ≤ 971 → R14HoldsAt e :=
  (R14ForRange_iff_forall (-1074) 971 (by decide)).mp R14_binary64_decidable

/-! ## Public correctness API

The Schubfach algorithm only consumes the *value* of `floorLog10Pow2`
together with the surrounding inequality; we pack both into a single
existential for ergonomic destructuring at the use site. -/

/-- The magic-constant approximation `floorLog10Pow2 e` returns the
exact value of `⌊log₁₀(2^e)⌋` over the binary64 exponent range,
witnessed by the cross-multiplied inequality `R15HoldsAt e`. -/
theorem floorLog10Pow2_correct (e : Int) (h1 : -1074 ≤ e) (h2 : e ≤ 971) :
    ∃ k : Int, floorLog10Pow2 e = k ∧ R15HoldsAt e := by
  refine ⟨floorLog10Pow2 e, rfl, ?_⟩
  exact R15HoldsAt_in_binary64_range e h1 h2

/-- The magic-constant approximation `floorLog10ThreeQuartersPow2 e`
returns the exact value of `⌊log₁₀(3/4 · 2^e)⌋` over the binary64
exponent range, witnessed by the cross-multiplied inequality
`R14HoldsAt e`. -/
theorem floorLog10ThreeQuartersPow2_correct (e : Int) (h1 : -1074 ≤ e) (h2 : e ≤ 971) :
    ∃ k : Int, floorLog10ThreeQuartersPow2 e = k ∧ R14HoldsAt e := by
  refine ⟨floorLog10ThreeQuartersPow2 e, rfl, ?_⟩
  exact R14HoldsAt_in_binary64_range e h1 h2

end PP.Numeric.Schubfach

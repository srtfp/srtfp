/- Clinger Decimal→Float correctness — base layer (M4).

   This module contains the structural foundation for the Clinger
   correctness theorem:

   * `roundNearestEven_*` shape lemmas (floor/ceil/tie characterisation).
   * `leBy2e` and `findBinaryExp` shape lemmas.
   * `scaleByPow2` shape lemmas.
   * The abstract decode `decodedAbs` and its zero/nonzero shape lemmas.
   * The runtime bridge predicate `DecodeOfDecimalBridge`.
   * The half-ULP bound `roundNearestEven_cleared_bound`.

   These are used by the per-branch correctness modules
   (`Regular`, `IrregularNoCarry`, `IrregularCarry`). The split lets
   each branch compile in parallel and keeps elaboration costs
   localized. -/

import Srtfp.Proofs.CorrectnessSpec
import Srtfp.Clinger
import Srtfp.Schubfach
import Srtfp.Float.Bits
import Srtfp.Float.Rep

namespace Srtfp.Clinger

open Srtfp.Float
open Srtfp.Schubfach
open Srtfp

/-! ## `roundNearestEven` shape lemmas -/

/-- `roundNearestEven a b` is either `a/b` or `a/b + 1`. -/
theorem roundNearestEven_eq_floor_or_ceil (a b : Nat) :
    roundNearestEven a b = a / b ∨ roundNearestEven a b = a / b + 1 := by
  unfold roundNearestEven
  by_cases h1 : 2 * (a - a / b * b) < b
  · left
    show (if 2 * (a - a / b * b) < b then a / b
       else if 2 * (a - a / b * b) > b then a / b + 1
       else if a / b % 2 = 0 then a / b else a / b + 1) = a / b
    rw [if_pos h1]
  · by_cases h2 : 2 * (a - a / b * b) > b
    · right
      show (if 2 * (a - a / b * b) < b then a / b
         else if 2 * (a - a / b * b) > b then a / b + 1
         else if a / b % 2 = 0 then a / b else a / b + 1) = a / b + 1
      rw [if_neg h1, if_pos h2]
    · by_cases h3 : a / b % 2 = 0
      · left
        show (if 2 * (a - a / b * b) < b then a / b
           else if 2 * (a - a / b * b) > b then a / b + 1
           else if a / b % 2 = 0 then a / b else a / b + 1) = a / b
        rw [if_neg h1, if_neg h2, if_pos h3]
      · right
        show (if 2 * (a - a / b * b) < b then a / b
           else if 2 * (a - a / b * b) > b then a / b + 1
           else if a / b % 2 = 0 then a / b else a / b + 1) = a / b + 1
        rw [if_neg h1, if_neg h2, if_neg h3]

theorem roundNearestEven_ge_floor (a b : Nat) :
    a / b ≤ roundNearestEven a b := by
  rcases roundNearestEven_eq_floor_or_ceil a b with h | h
  · omega
  · omega

theorem roundNearestEven_le_ceil (a b : Nat) :
    roundNearestEven a b ≤ a / b + 1 := by
  rcases roundNearestEven_eq_floor_or_ceil a b with h | h
  · omega
  · omega

/-! ## When does `roundNearestEven` pick floor vs ceil?

The rounding rule with `r = a - (a/b)·b = a % b`:
  * `2r < b`  → floor (`a / b`)
  * `2r > b`  → ceil  (`a / b + 1`)
  * `2r = b`  → tie  → ceil if `a/b` odd, floor if `a/b` even
-/

/-- Strict-below-midpoint: `roundNearestEven` picks the floor. -/
theorem roundNearestEven_eq_floor_of_below (a b : Nat)
    (h : 2 * (a - a / b * b) < b) :
    roundNearestEven a b = a / b := by
  show (if 2 * (a - a / b * b) < b then a / b
     else if 2 * (a - a / b * b) > b then a / b + 1
     else if a / b % 2 = 0 then a / b else a / b + 1) = a / b
  rw [if_pos h]

/-- Strict-above-midpoint: `roundNearestEven` picks the ceil. -/
theorem roundNearestEven_eq_ceil_of_above (a b : Nat)
    (h : 2 * (a - a / b * b) > b) :
    roundNearestEven a b = a / b + 1 := by
  show (if 2 * (a - a / b * b) < b then a / b
     else if 2 * (a - a / b * b) > b then a / b + 1
     else if a / b % 2 = 0 then a / b else a / b + 1) = a / b + 1
  have hnot : ¬ (2 * (a - a / b * b) < b) := by omega
  rw [if_neg hnot, if_pos h]

/-- Exactly-at-midpoint, floor even: pick the floor. -/
theorem roundNearestEven_eq_floor_of_tie_even (a b : Nat)
    (htie : 2 * (a - a / b * b) = b) (heven : a / b % 2 = 0) :
    roundNearestEven a b = a / b := by
  show (if 2 * (a - a / b * b) < b then a / b
     else if 2 * (a - a / b * b) > b then a / b + 1
     else if a / b % 2 = 0 then a / b else a / b + 1) = a / b
  have hnot1 : ¬ (2 * (a - a / b * b) < b) := by omega
  have hnot2 : ¬ (2 * (a - a / b * b) > b) := by omega
  rw [if_neg hnot1, if_neg hnot2, if_pos heven]

/-- Exactly-at-midpoint, floor odd: pick the ceil. -/
theorem roundNearestEven_eq_ceil_of_tie_odd (a b : Nat)
    (htie : 2 * (a - a / b * b) = b) (hodd : a / b % 2 ≠ 0) :
    roundNearestEven a b = a / b + 1 := by
  show (if 2 * (a - a / b * b) < b then a / b
     else if 2 * (a - a / b * b) > b then a / b + 1
     else if a / b % 2 = 0 then a / b else a / b + 1) = a / b + 1
  have hnot1 : ¬ (2 * (a - a / b * b) < b) := by omega
  have hnot2 : ¬ (2 * (a - a / b * b) > b) := by omega
  rw [if_neg hnot1, if_neg hnot2, if_neg hodd]

/-! ## Closest-integer characterisation of `roundNearestEven`

The contract: for `b > 0`, `roundNearestEven a b` is the integer `m` such
that `m·b` is *closest* to `a`, with ties broken to even.

We phrase this in cleared form (no rationals) as:
  `2·(a - m·b) ∈ [-b, b]` and the boundary is reached only at ties,
  which are decided by `m` being even.

Combined with the fact that the only candidate integers are `a/b` and
`a/b + 1`, this gives a clean closed-form midpoint relation. -/

/-- For `b > 0`, the rounding error in `roundNearestEven a b` satisfies:
either `m·b ≤ a ∧ 2·(a - m·b) ≤ b` (rounded down), or
`a ≤ m·b ∧ 2·(m·b - a) < b` (rounded up, strict). The boundary case
`2·(a - m·b) = b` is rounded down when `m` even, up when `m` odd. -/
theorem roundNearestEven_floor_bound (a b : Nat)
    (h_floor : roundNearestEven a b = a / b) :
    2 * (a - (roundNearestEven a b) * b) ≤ b := by
  rw [h_floor]
  have h_eq : a - a / b * b = a % b := by
    have h := Nat.div_add_mod a b
    have h' : a / b * b + a % b = a := by rw [Nat.mul_comm]; exact h
    omega
  rw [h_eq]
  show 2 * (a % b) ≤ b
  by_cases h1 : 2 * (a - a / b * b) < b
  · rw [h_eq] at h1; omega
  by_cases h2 : 2 * (a - a / b * b) > b
  · exfalso
    have hne : roundNearestEven a b = a / b + 1 :=
      roundNearestEven_eq_ceil_of_above a b h2
    rw [hne] at h_floor
    omega
  · have htie : 2 * (a - a / b * b) = b := by omega
    rw [h_eq] at htie
    omega

/-- For `b > 0`, when `roundNearestEven a b = a/b + 1`, the rounding
    overshoots by less than half a ULP. -/
theorem roundNearestEven_ceil_bound (a b : Nat) (hb : 0 < b)
    (h_ceil : roundNearestEven a b = a / b + 1) :
    2 * ((roundNearestEven a b) * b - a) ≤ b := by
  rw [h_ceil]
  have h_eq : a - a / b * b = a % b := by
    have h := Nat.div_add_mod a b
    have h' : a / b * b + a % b = a := by rw [Nat.mul_comm]; exact h
    omega
  have h_mod_lt : a % b < b := Nat.mod_lt _ hb
  have h_ab_eq : a / b * b + a % b = a := by
    rw [Nat.mul_comm]; exact Nat.div_add_mod a b
  have h_ge : a ≤ (a / b + 1) * b := by
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have h_sub : (a / b + 1) * b - a = b - a % b := by
    have hh : (a / b + 1) * b = a / b * b + b := by
      rw [Nat.add_mul, Nat.one_mul]
    omega
  rw [h_sub]
  by_cases h1 : 2 * (a - a / b * b) > b
  · rw [h_eq] at h1; omega
  by_cases h2 : 2 * (a - a / b * b) < b
  · exfalso
    have hne : roundNearestEven a b = a / b :=
      roundNearestEven_eq_floor_of_below a b h2
    rw [hne] at h_ceil
    omega
  · have htie : 2 * (a - a / b * b) = b := by omega
    rw [h_eq] at htie
    omega

/-! ## Unified "closest to a/b" characterisation -/

/-- `roundNearestEven a b · b` is within `b/2` of `a`, cleared form. -/
theorem roundNearestEven_within_half (a b : Nat) (hb : 0 < b) :
    let m := roundNearestEven a b
    (m * b ≤ a ∧ 2 * (a - m * b) ≤ b) ∨
    (a ≤ m * b ∧ 2 * (m * b - a) ≤ b) := by
  simp only
  rcases roundNearestEven_eq_floor_or_ceil a b with h_floor | h_ceil
  · left
    refine ⟨?_, ?_⟩
    · rw [h_floor]; exact Nat.div_mul_le_self _ _
    · exact roundNearestEven_floor_bound a b h_floor
  · right
    refine ⟨?_, ?_⟩
    · rw [h_ceil]
      have h_div_add_mod : a / b * b + a % b = a := by
        rw [Nat.mul_comm]; exact Nat.div_add_mod a b
      have h_mod_lt : a % b < b := Nat.mod_lt _ hb
      rw [Nat.add_mul, Nat.one_mul]
      omega
    · exact roundNearestEven_ceil_bound a b hb h_ceil

/-! ## `leBy2e` and `findBinaryExp` shape lemmas -/

theorem leBy2e_eq_true_iff (a b : Nat) (e : Int) :
    leBy2e a b e = true ↔
      (if e ≥ 0 then b * 2 ^ e.toNat ≤ a else b ≤ a * 2 ^ (-e).toNat) := by
  unfold leBy2e
  by_cases h : e ≥ 0
  · simp [h]
  · simp [h]

theorem findBinaryExp_eq_or (a b : Nat) :
    findBinaryExp a b = ((Nat.log2 a : Int) - Nat.log2 b) ∨
    findBinaryExp a b = ((Nat.log2 a : Int) - Nat.log2 b) - 1 := by
  unfold findBinaryExp
  by_cases h : leBy2e a b ((Nat.log2 a : Int) - Nat.log2 b) = true
  · left; simp [h]
  · right; simp [h]

/-! ## `scaleByPow2` shape lemmas -/

theorem scaleByPow2_nonneg {a b : Nat} {k : Int} (h : k ≥ 0) :
    scaleByPow2 a b k = (a * 2 ^ k.toNat, b) := by
  unfold scaleByPow2; simp [h]

theorem scaleByPow2_neg {a b : Nat} {k : Int} (h : ¬ k ≥ 0) :
    scaleByPow2 a b k = (a, b * 2 ^ (-k).toNat) := by
  unfold scaleByPow2; simp [h]

theorem scaleByPow2_num_eq (a b : Nat) (k : Int) :
    (scaleByPow2 a b k).1 =
      if k ≥ 0 then a * 2 ^ k.toNat else a := by
  unfold scaleByPow2
  by_cases h : k ≥ 0
  · simp [h]
  · simp [h]

theorem scaleByPow2_denom_eq (a b : Nat) (k : Int) :
    (scaleByPow2 a b k).2 =
      if k ≥ 0 then b else b * 2 ^ (-k).toNat := by
  unfold scaleByPow2
  by_cases h : k ≥ 0
  · simp [h]
  · simp [h]

theorem scaleByPow2_denom_pos {a b : Nat} {k : Int} (hb : 0 < b) :
    0 < (scaleByPow2 a b k).2 := by
  rw [scaleByPow2_denom_eq]
  by_cases hk : k ≥ 0
  · simp [hk]; exact hb
  · simp [hk]
    -- Goal shape depends on the simp normal form: `0 < b` or `0 < b * 2^n`.
    first
    | exact hb
    | exact Nat.mul_pos hb (Nat.two_pow_pos _)

/-! ## Abstract decoded form of `Clinger.ofDecimal`

`decodedAbs` is the abstract `Decoded` record produced by
`Clinger.ofDecimal ⟨sign, sig, exp⟩`; `IsFiniteAbs` says its biased
exponent stays in the finite binary64 range. They are *proof
vocabulary*: the public correctness statements no longer mention them
(`isFiniteAbs_of_roundtrip` in `Bridge.lean` derives `IsFiniteAbs` from
any bit-level round-trip to a finite float). -/

/-- Abstract decoded representation of `Clinger.ofDecimal (⟨sign, sig, exp⟩)`.
    Marker values for overflow/NaN: `m = 0, q = 1024` indicate `±∞`
    (the algorithm produces `infOfSign sign` whose decoded biased
    exponent would be 2047). -/
def decodedAbs (sign : Bool) (sig : Nat) (exp : Int) : Decoded :=
  if sig = 0 then
    ⟨sign, 0, -1074⟩
  else
    let (a, b) : Nat × Nat :=
      if exp ≥ 0 then (sig * 10 ^ exp.toNat, 1)
      else (sig, 10 ^ (-exp).toNat)
    let e := findBinaryExp a b
    if e > 1023 then
      ⟨sign, 0, 1024⟩
    else if e ≥ -1022 then
      let (num, denom) := scaleByPow2 a b (52 - e)
      let m := roundNearestEven num denom
      if m ≥ 2 ^ 53 then
        let e' := e + 1
        if e' > 1023 then ⟨sign, 0, 1024⟩
        else ⟨sign, 1 <<< 52, e' - 52⟩
      else
        ⟨sign, m, e - 52⟩
    else
      let (num, denom) := scaleByPow2 a b 1074
      let m := roundNearestEven num denom
      if m = 0 then
        ⟨sign, 0, -1074⟩
      else if m ≥ 2 ^ 52 then
        ⟨sign, m, -1074⟩
      else
        ⟨sign, m, -1074⟩

/-- `decodedAbs` produces a finite-range `Decoded` whenever the input
    isn't an overflow case. -/
def IsFiniteAbs (sign : Bool) (sig : Nat) (exp : Int) : Prop :=
  (decodedAbs sign sig exp).q ≤ 971

instance (sign : Bool) (sig : Nat) (exp : Int) :
    Decidable (IsFiniteAbs sign sig exp) := by
  unfold IsFiniteAbs; exact inferInstance

/-! ## Parameterised body of `decodedAbs` for the dispatch

The body of `decodedAbs` (after dispatching on `sig = 0`) is parameterised
on the inner `(a, b)` pair. We expose this as a separate definition to
simplify the dispatch proof: it eliminates the outer pair-match and
exposes the if-tree to direct case-split. -/

/-- Body of `decodedAbs sign sig exp` for `sig ≠ 0`, parameterised on
the inner `(a, b)` Nat values (which `decodedAbs` computes via
`if exp ≥ 0 then (sig * 10^exp, 1) else (sig, 10^(-exp))`).

Uses `.1`/`.2` projections instead of `let (num, denom) := ...` to
keep the if-tree free of pair-destructuring, which avoids elaboration
blow-up in the dispatch proof. -/
def decodedAbsAB (sign : Bool) (a b : Nat) : Decoded :=
  let e := findBinaryExp a b
  if e > 1023 then ⟨sign, 0, 1024⟩
  else if e ≥ -1022 then
    let m := roundNearestEven (scaleByPow2 a b (52 - e)).1
                               (scaleByPow2 a b (52 - e)).2
    if m ≥ 2 ^ 53 then
      let e' := e + 1
      if e' > 1023 then ⟨sign, 0, 1024⟩
      else ⟨sign, 1 <<< 52, e' - 52⟩
    else ⟨sign, m, e - 52⟩
  else
    let m := roundNearestEven (scaleByPow2 a b 1074).1
                               (scaleByPow2 a b 1074).2
    if m = 0 then ⟨sign, 0, -1074⟩
    else if m ≥ 2 ^ 52 then ⟨sign, m, -1074⟩
    else ⟨sign, m, -1074⟩

/-- For nonzero `sig`, `decodedAbs` equals `decodedAbsAB` for the
appropriate `(a, b)`. The split is on `exp ≥ 0`. -/
theorem decodedAbs_eq_decodedAbsAB_pos (sign : Bool) (sig : Nat) (exp : Int)
    (h_sig : sig ≠ 0) (hexp : exp ≥ 0) :
    decodedAbs sign sig exp = decodedAbsAB sign (sig * 10 ^ exp.toNat) 1 := by
  unfold decodedAbs decodedAbsAB
  rw [if_neg h_sig, if_pos hexp]

theorem decodedAbs_eq_decodedAbsAB_neg (sign : Bool) (sig : Nat) (exp : Int)
    (h_sig : sig ≠ 0) (hexp : ¬ exp ≥ 0) :
    decodedAbs sign sig exp = decodedAbsAB sign sig (10 ^ (-exp).toNat) := by
  unfold decodedAbs decodedAbsAB
  rw [if_neg h_sig, if_neg hexp]

/-! ## Predicates on the abstract decode -/

-- `IsFiniteAbs` and its `Decidable` instance now live on the audit
-- surface in `Srtfp.CorrectnessSpec` (imported above).

/-! ## Shape lemmas: each branch of `decodedAbs` -/

/-- Zero case. -/
theorem decodedAbs_zero (sign : Bool) (exp : Int) :
    decodedAbs sign 0 exp = ⟨sign, 0, -1074⟩ := by
  unfold decodedAbs; rfl

/-- For nonzero `sig`, we can name the intermediate `a, b, e`. -/
theorem decodedAbs_nonzero (sign : Bool) (sig : Nat) (exp : Int)
    (h_sig : sig ≠ 0) :
    decodedAbs sign sig exp =
      let (a, b) : Nat × Nat :=
        if exp ≥ 0 then (sig * 10 ^ exp.toNat, 1)
        else (sig, 10 ^ (-exp).toNat)
      let e := findBinaryExp a b
      if e > 1023 then ⟨sign, 0, 1024⟩
      else if e ≥ -1022 then
        let (num, denom) := scaleByPow2 a b (52 - e)
        let m := roundNearestEven num denom
        if m ≥ 2 ^ 53 then
          let e' := e + 1
          if e' > 1023 then ⟨sign, 0, 1024⟩
          else ⟨sign, 1 <<< 52, e' - 52⟩
        else ⟨sign, m, e - 52⟩
      else
        let (num, denom) := scaleByPow2 a b 1074
        let m := roundNearestEven num denom
        if m = 0 then ⟨sign, 0, -1074⟩
        else if m ≥ 2 ^ 52 then ⟨sign, m, -1074⟩
        else ⟨sign, m, -1074⟩ := by
  unfold decodedAbs
  rw [if_neg h_sig]

/-! ## Cleared-form midpoint inequality for `roundNearestEven` -/

/-- For `b > 0`, `2 * a - b ≤ 2 * m * b ≤ 2 * a + b`, in `Int`. -/
theorem roundNearestEven_cleared_bound (a b : Nat) (hb : 0 < b) :
    let m := roundNearestEven a b
    2 * (a : Int) - b ≤ 2 * (m : Int) * b ∧
    2 * (m : Int) * b ≤ 2 * (a : Int) + b := by
  simp only
  rcases roundNearestEven_within_half a b hb with ⟨h_le, h_diff⟩ | ⟨h_le, h_diff⟩
  · have h_le_int : ((roundNearestEven a b : Nat) : Int) * (b : Int) ≤ (a : Int) := by
      have := h_le
      have : ((roundNearestEven a b * b : Nat) : Int) ≤ (a : Int) := by
        exact_mod_cast this
      push_cast at this; exact this
    have h_diff_int :
        2 * ((a : Int) - (roundNearestEven a b : Int) * b) ≤ (b : Int) := by
      have : ((2 * (a - roundNearestEven a b * b) : Nat) : Int) ≤ (b : Int) := by
        exact_mod_cast h_diff
      push_cast at this
      have hsub :
          ((a - roundNearestEven a b * b : Nat) : Int)
            = (a : Int) - (roundNearestEven a b : Int) * b := by
        have : (roundNearestEven a b * b : Nat) ≤ a := h_le
        omega
      rw [hsub] at this
      exact this
    refine ⟨?_, ?_⟩
    · have h1 : 2 * (a : Int) - 2 * ((roundNearestEven a b : Int) * b) ≤ (b : Int) := by
        have : 2 * ((a : Int) - (roundNearestEven a b : Int) * b) ≤ (b : Int) := h_diff_int
        omega
      have h2 : 2 * ((roundNearestEven a b : Int)) * b
                  = 2 * ((roundNearestEven a b : Int) * b) := by
        rw [Int.mul_assoc]
      rw [h2]; omega
    · have h_b_nn : 0 ≤ (b : Int) := Int.natCast_nonneg _
      have h_2mb : 2 * ((roundNearestEven a b : Int) * b) ≤ 2 * (a : Int) := by
        have : (roundNearestEven a b : Int) * b ≤ (a : Int) := h_le_int
        omega
      have h2 : 2 * ((roundNearestEven a b : Int)) * b
                  = 2 * ((roundNearestEven a b : Int) * b) := by
        rw [Int.mul_assoc]
      rw [h2]; omega
  · have h_le_int : (a : Int) ≤ ((roundNearestEven a b : Nat) : Int) * (b : Int) := by
      have := h_le
      have : (a : Int) ≤ ((roundNearestEven a b * b : Nat) : Int) := by
        exact_mod_cast this
      push_cast at this; exact this
    have h_diff_int :
        2 * ((roundNearestEven a b : Int) * b - (a : Int)) ≤ (b : Int) := by
      have : ((2 * (roundNearestEven a b * b - a) : Nat) : Int) ≤ (b : Int) := by
        exact_mod_cast h_diff
      push_cast at this
      have hsub :
          ((roundNearestEven a b * b - a : Nat) : Int)
            = (roundNearestEven a b : Int) * b - (a : Int) := by
        have : a ≤ roundNearestEven a b * b := h_le
        omega
      rw [hsub] at this
      exact this
    refine ⟨?_, ?_⟩
    · have h_b_nn : 0 ≤ (b : Int) := Int.natCast_nonneg _
      have h1 : 2 * (a : Int) ≤ 2 * ((roundNearestEven a b : Int) * b) := by omega
      have h2 : 2 * ((roundNearestEven a b : Int)) * b
                  = 2 * ((roundNearestEven a b : Int) * b) := by
        rw [Int.mul_assoc]
      rw [h2]; omega
    · have h1 : 2 * ((roundNearestEven a b : Int) * b) - 2 * (a : Int) ≤ (b : Int) := by
        have : 2 * ((roundNearestEven a b : Int) * b - (a : Int)) ≤ (b : Int) :=
          h_diff_int
        omega
      have h2 : 2 * ((roundNearestEven a b : Int)) * b
                  = 2 * ((roundNearestEven a b : Int) * b) := by
        rw [Int.mul_assoc]
      rw [h2]; omega

/-! ## The runtime bridge -/

/-- **Bridge predicate.** For any `Decimal d`, `decode (Clinger.ofDecimal
d)` equals the abstract `decodedAbs d.sign d.significand d.exponent`,
modulo the IEEE-754 distinction between finite values and ±∞. -/
def DecodeOfDecimalBridge : Prop :=
  ∀ (d : Decimal),
    (decodedAbs d.sign d.significand d.exponent).q ≤ 971 →
    decode (ofDecimal d) = decodedAbs d.sign d.significand d.exponent

/-! ## Abstract correctness and dispatch obligations -/

/-- **Abstract correctness theorem.** For non-overflow nonzero
`(sig, exp)`, the abstract decode produces `(m, q)` such that
`inRoundingInterval sig exp m q (isIrregular m q) = true`. -/
def AbstractCorrectness : Prop :=
  ∀ (sign : Bool) (sig : Nat) (exp : Int),
    sig ≠ 0 →
    IsFiniteAbs sign sig exp →
    let d := decodedAbs sign sig exp
    inRoundingInterval sig exp d.m d.q (isIrregular d.m d.q) = true

/-- The dispatch residual: structurally equal to `AbstractCorrectness`.
This is the part of the proof that performs the case-split on
`decodedAbs`'s if-tree. The per-branch correctness is established
in `Clinger/{Regular,IrregularNoCarry,IrregularCarry}.lean`; the
case-split itself is discharged in `Clinger/Dispatch.lean`. -/
def BranchDispatch : Prop := AbstractCorrectness

/-- `AbstractCorrectness` reduces to `BranchDispatch` trivially. -/
theorem abstract_correctness_of_dispatch (h : BranchDispatch) :
    AbstractCorrectness := h

end Srtfp.Clinger

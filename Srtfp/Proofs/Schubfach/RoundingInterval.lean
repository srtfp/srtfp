/- Rounding-interval characterisation R_v (M3.8.2).

   For a positive non-zero finite binary64 value `v = m·2^q`, the
   *rounding interval* `R_v = [vℓ, vr]` is the closed interval of real
   numbers that round to `v` under round-to-nearest-ties-to-even.

   Schubfach §5 distinguishes two cases:

   **Regular spacing**: `vℓ = v - 2^(q-1)`, `vr = v + 2^(q-1)`.
   Width `2^q`. This is the typical case.

   **Irregular spacing**: `v` is a power of two strictly above the
   smallest normal, i.e. `m = 2^52 ∧ q > -1074`. Then the predecessor
   of `v` in binary64 is `(2^53 - 1) · 2^(q-1)`, which is closer to `v`
   than `2^(q-1)` would suggest. Hence `vℓ = v - 2^(q-2)`
   ( = `(3/4)·2^q` below `v` ) while `vr = v + 2^(q-1)` is unchanged.
   Width `(3/4)·2^q = 3·2^(q-2)`.

   The boundary points `vℓ` and `vr` themselves round-to-even — the
   tie behaviour is captured in M3.8.5 (`pickNearer`). This file just
   provides the structural definitions, the width formulas, and the
   membership `v ∈ R_v`.

   ## Representation

   No Mathlib means no `ℚ`. We carry rationals as `Midpoint`:
   `(num : Int, denPow2 : Int)` denoting the real `num · 2^(-denPow2)`.
   Equivalence is the standard cross-multiplied form lifted to allow
   either side to have the larger `denPow2`:

       a ~ b  ↔  a.num · 2^((b.denPow2 - a.denPow2)⁺)
                  = b.num · 2^((a.denPow2 - b.denPow2)⁺)

   where `x⁺ = max(x, 0)` (i.e. `(·).toNat` cast back to `Int`).
   This avoids splitting on the sign of `denPow2 - denPow2` at the
   spec level — exactly one of the two exponents is positive, and the
   other contributes a `2^0 = 1` factor.

   ## Out of scope (downstream milestones)

   - M3.8.3: `k = ⌊log_D(‖R_v‖)⌋` uses the width formulas here together
     with R14/R15 from M3.8.1.
   - M3.8.4/5/6: shifted significand, pickNearer, shortest-form check.
   - This file is *purely* about the binary-side rounding interval. -/

import Srtfp.Schubfach

namespace Srtfp.Schubfach

open Srtfp.Float

/-! ## `Midpoint` — exact rational `num · 2^(-denPow2)`

A small datatype for the rationals that arise in the binary-side
analysis: all endpoints are dyadic, so a single `Int` numerator and a
signed `denPow2` suffice. -/

/-- A dyadic rational `num · 2^(-denPow2)`. Negative `denPow2` is
allowed — it represents multiplication by a positive power of two,
as needed for values `m · 2^q` with `q ≥ 0`. -/
structure Midpoint where
  num     : Int
  denPow2 : Int
  deriving Repr, DecidableEq

namespace Midpoint

/-! ### Helpers: signed power of two as `Int` factor -/

/-- `2^(n⁺) : Int` — the positive-part power of two as an integer.
For `n ≤ 0`, equals `1`. Used to cross-multiply equivalence/order
without splitting on the sign of `n`. -/
def shiftFactor (n : Int) : Int := (2 : Int) ^ n.toNat

theorem shiftFactor_pos (n : Int) : 0 < shiftFactor n := by
  unfold shiftFactor
  induction n.toNat with
  | zero => decide
  | succ k ih =>
    rw [Int.pow_succ]
    exact Int.mul_pos ih (by decide)

theorem shiftFactor_nonneg (n : Int) : 0 ≤ shiftFactor n :=
  Int.le_of_lt (shiftFactor_pos n)

theorem shiftFactor_ne_zero (n : Int) : shiftFactor n ≠ 0 :=
  Int.ne_of_gt (shiftFactor_pos n)

theorem shiftFactor_nonpos {n : Int} (h : n ≤ 0) : shiftFactor n = 1 := by
  unfold shiftFactor
  have : n.toNat = 0 := Int.toNat_of_nonpos h
  rw [this]; rfl

theorem shiftFactor_of_nonneg {n : Int} (_h : 0 ≤ n) :
    shiftFactor n = (2 : Int) ^ n.toNat := rfl

theorem shiftFactor_zero : shiftFactor 0 = 1 := by
  unfold shiftFactor; rfl

/-! ### Equivalence: same real value -/

/-- Two midpoints denote the same real number, in cross-multiplied form.
The `shiftFactor` calls produce `1` on whichever side has the smaller
`denPow2`, so this captures the standard `a.num/2^a.denPow2 =
b.num/2^b.denPow2` equality regardless of signs. -/
def Equiv (a b : Midpoint) : Prop :=
  a.num * shiftFactor (b.denPow2 - a.denPow2)
    = b.num * shiftFactor (a.denPow2 - b.denPow2)

theorem Equiv.refl (a : Midpoint) : Equiv a a := by
  unfold Equiv; rfl

theorem Equiv.symm {a b : Midpoint} (h : Equiv a b) : Equiv b a := by
  unfold Equiv at h ⊢
  exact h.symm

/-! ### Constructors -/

/-- The midpoint representing the real `m · 2^q`. -/
def ofMQ (m : Int) (q : Int) : Midpoint := ⟨m, -q⟩

/-- The midpoint `0` (numerator zero, any `denPow2` works; we pick `0`). -/
def zero : Midpoint := ⟨0, 0⟩

instance : Inhabited Midpoint := ⟨zero⟩

theorem ofMQ_num (m q : Int) : (ofMQ m q).num = m := rfl
theorem ofMQ_denPow2 (m q : Int) : (ofMQ m q).denPow2 = -q := rfl

/-! ### Less-than relation

Order on midpoints, via cross-multiplied numerator comparison.
Because all `denPow2` values arise as `-q` for binary64 `q ∈ [-1074,
971]`, we never encounter degenerate cases where the cross-multiplied
form misbehaves: `shiftFactor` is always positive. -/

/-- Strict less-than on the real values. Equivalent to
`a.num/2^a.denPow2 < b.num/2^b.denPow2`. -/
def lt (a b : Midpoint) : Prop :=
  a.num * shiftFactor (b.denPow2 - a.denPow2)
    < b.num * shiftFactor (a.denPow2 - b.denPow2)

/-- Non-strict less-than. -/
def le (a b : Midpoint) : Prop :=
  a.num * shiftFactor (b.denPow2 - a.denPow2)
    ≤ b.num * shiftFactor (a.denPow2 - b.denPow2)

instance : LT Midpoint := ⟨lt⟩
instance : LE Midpoint := ⟨le⟩

theorem lt_iff (a b : Midpoint) :
    a < b ↔ a.num * shiftFactor (b.denPow2 - a.denPow2)
            < b.num * shiftFactor (a.denPow2 - b.denPow2) := Iff.rfl

theorem le_iff (a b : Midpoint) :
    a ≤ b ↔ a.num * shiftFactor (b.denPow2 - a.denPow2)
            ≤ b.num * shiftFactor (a.denPow2 - b.denPow2) := Iff.rfl

/-- When two midpoints share `denPow2`, equivalence reduces to
numerator equality. -/
theorem equiv_of_same_den {a b : Midpoint}
    (hden : a.denPow2 = b.denPow2) (hnum : a.num = b.num) : Equiv a b := by
  unfold Equiv
  rw [hden, hnum]

/-- When two midpoints share `denPow2`, `<` reduces to numerator `<`. -/
theorem lt_of_same_den {a b : Midpoint}
    (hden : a.denPow2 = b.denPow2) (hnum : a.num < b.num) : a < b := by
  show lt a b
  unfold lt
  have h1 : b.denPow2 - a.denPow2 = 0 := by omega
  have h2 : a.denPow2 - b.denPow2 = 0 := by omega
  rw [h1, h2, shiftFactor_zero]
  omega

/-- When two midpoints share `denPow2`, `≤` reduces to numerator `≤`. -/
theorem le_of_same_den {a b : Midpoint}
    (hden : a.denPow2 = b.denPow2) (hnum : a.num ≤ b.num) : a ≤ b := by
  show le a b
  unfold le
  have h1 : b.denPow2 - a.denPow2 = 0 := by omega
  have h2 : a.denPow2 - b.denPow2 = 0 := by omega
  rw [h1, h2, shiftFactor_zero]
  omega

end Midpoint

/-! ## §5 rounding interval `R_v`

For positive finite `v = m·2^q`, `R_v = [vℓ, vr]` where:

- regular case (default): `vℓ = v - 2^(q-1)`, `vr = v + 2^(q-1)`.
  Width `2^q`.
- irregular case (`m = 2^52 ∧ q > -1074`): `vℓ = v - 2^(q-2)`,
  `vr = v + 2^(q-1)`. Width `3·2^(q-2)`.

We multiply *both endpoints* through by `2^(-q+2)` so that all numerators
become integers regardless of the sign of `q`. The shared denominator
becomes `2^(-q+2)`, i.e. `denPow2 = -q + 2 = 2 - q`. -/

/-- The rounding interval `R_v = [vl, vr]` for a positive non-zero
finite binary64 value `v = m · 2^q`. Both endpoints are stored at the
common scale `denPow2 = -q + 2`, allowing a single subtraction for the
width. -/
structure RoundingInterval where
  /-- Lower endpoint `vℓ`. -/
  vl     : Midpoint
  /-- Upper endpoint `vr`. -/
  vr     : Midpoint
  /-- Width `vr - vl` as a midpoint at the shared scale. -/
  width  : Midpoint
  /-- The midpoint representation of `v` itself (numerator `m·2^2` at
  the same shared scale `-q + 2`). -/
  vMid   : Midpoint
  /-- Common scale shared by `vl`, `vr`, `width`, `vMid`. -/
  scale  : Int
  /-- All endpoints share `scale`. -/
  vl_den   : vl.denPow2 = scale
  vr_den   : vr.denPow2 = scale
  width_den : width.denPow2 = scale
  vMid_den : vMid.denPow2 = scale
  /-- Width is `vr.num - vl.num` at the shared scale. -/
  width_eq : width.num = vr.num - vl.num
  /-- `vl.num < vMid.num`: strict order of numerators (sufficient for
  `vl < v` since they share `denPow2`). -/
  vl_lt_v_num  : vl.num < vMid.num
  /-- `vMid.num < vr.num`: strict order of numerators. -/
  v_lt_vr_num  : vMid.num < vr.num
  deriving Repr

namespace RoundingInterval

/-! ### Construction

The constructor takes the binary64 invariants and the regular/irregular
classification (which is decided by `isIrregular m q`).

Numerator layout at scale `s = -q + 2`:

- `v = m · 2^q = (m · 2^2) · 2^(q-2) = (4m) / 2^s`. So `vMid.num = 4m`.
- Regular: `vℓ = v - 2^(q-1) = (4m - 2) / 2^s`,
           `vr = v + 2^(q-1) = (4m + 2) / 2^s`. Width = 4.
- Irregular: `vℓ = v - 2^(q-2) = (4m - 1) / 2^s`,
             `vr = v + 2^(q-1) = (4m + 2) / 2^s`. Width = 3.

(The factor 4 in regular width / 3 in irregular width is what the
ofMQ-level theorems below recover at the *value* level: width =
4·2^(q-2) = 2^q in regular, width = 3·2^(q-2) = (3/4)·2^q in
irregular.)

This matches `Schubfach.inRoundingInterval`'s `4·v_ℓ`, `4·v_r`
numerators verbatim. -/

/-- Construct `R_v` for a positive finite binary64 value `v = m·2^q`.
The preconditions enforce the binary64 invariants used in the
proofs. -/
def ofMQ (m : Nat) (q : Int)
    (_hm_pos : 1 ≤ m) (_hm_le : m < 2 ^ 53)
    (_hq_lo : -1074 ≤ q) (_hq_hi : q ≤ 971) : RoundingInterval :=
  let s : Int := -q + 2
  let mZ : Int := (m : Int)
  let vMidNum : Int := 4 * mZ
  let irreg : Bool := isIrregular m q
  let vlNum : Int := if irreg then 4 * mZ - 1 else 4 * mZ - 2
  let vrNum : Int := 4 * mZ + 2
  let widthNum : Int := vrNum - vlNum
  { vl := ⟨vlNum, s⟩,
    vr := ⟨vrNum, s⟩,
    width := ⟨widthNum, s⟩,
    vMid := ⟨vMidNum, s⟩,
    scale := s,
    vl_den := rfl,
    vr_den := rfl,
    width_den := rfl,
    vMid_den := rfl,
    width_eq := rfl,
    vl_lt_v_num := by
      show vlNum < vMidNum
      show (if irreg then 4 * mZ - 1 else 4 * mZ - 2) < 4 * mZ
      by_cases h : irreg = true
      · simp [h]; omega
      · have : irreg = false := Bool.eq_false_iff.mpr h
        simp [this]; omega
    v_lt_vr_num := by
      show vMidNum < vrNum
      show (4 * mZ) < 4 * mZ + 2
      omega }

/-! ### Projection lemmas: the constructor returns the expected shape -/

theorem ofMQ_scale (m : Nat) (q : Int)
    (hm_pos : 1 ≤ m) (hm_le : m < 2 ^ 53) (hq_lo : -1074 ≤ q) (hq_hi : q ≤ 971) :
    (ofMQ m q hm_pos hm_le hq_lo hq_hi).scale = -q + 2 := rfl

theorem ofMQ_vMid_num (m : Nat) (q : Int)
    (hm_pos : 1 ≤ m) (hm_le : m < 2 ^ 53) (hq_lo : -1074 ≤ q) (hq_hi : q ≤ 971) :
    (ofMQ m q hm_pos hm_le hq_lo hq_hi).vMid.num = 4 * (m : Int) := rfl

theorem ofMQ_vMid_denPow2 (m : Nat) (q : Int)
    (hm_pos : 1 ≤ m) (hm_le : m < 2 ^ 53) (hq_lo : -1074 ≤ q) (hq_hi : q ≤ 971) :
    (ofMQ m q hm_pos hm_le hq_lo hq_hi).vMid.denPow2 = -q + 2 := rfl

theorem ofMQ_vl_num_regular (m : Nat) (q : Int)
    (hm_pos : 1 ≤ m) (hm_le : m < 2 ^ 53) (hq_lo : -1074 ≤ q) (hq_hi : q ≤ 971)
    (h_reg : ¬ (isIrregular m q = true)) :
    (ofMQ m q hm_pos hm_le hq_lo hq_hi).vl.num = 4 * (m : Int) - 2 := by
  unfold ofMQ
  simp [h_reg]

theorem ofMQ_vl_num_irregular (m : Nat) (q : Int)
    (hm_pos : 1 ≤ m) (hm_le : m < 2 ^ 53) (hq_lo : -1074 ≤ q) (hq_hi : q ≤ 971)
    (h_irreg : isIrregular m q = true) :
    (ofMQ m q hm_pos hm_le hq_lo hq_hi).vl.num = 4 * (m : Int) - 1 := by
  unfold ofMQ
  simp [h_irreg]

theorem ofMQ_vr_num (m : Nat) (q : Int)
    (hm_pos : 1 ≤ m) (hm_le : m < 2 ^ 53) (hq_lo : -1074 ≤ q) (hq_hi : q ≤ 971) :
    (ofMQ m q hm_pos hm_le hq_lo hq_hi).vr.num = 4 * (m : Int) + 2 := rfl

theorem ofMQ_width_num_regular (m : Nat) (q : Int)
    (hm_pos : 1 ≤ m) (hm_le : m < 2 ^ 53) (hq_lo : -1074 ≤ q) (hq_hi : q ≤ 971)
    (h_reg : ¬ (isIrregular m q = true)) :
    (ofMQ m q hm_pos hm_le hq_lo hq_hi).width.num = 4 := by
  unfold ofMQ
  simp [h_reg]; omega

theorem ofMQ_width_num_irregular (m : Nat) (q : Int)
    (hm_pos : 1 ≤ m) (hm_le : m < 2 ^ 53) (hq_lo : -1074 ≤ q) (hq_hi : q ≤ 971)
    (h_irreg : isIrregular m q = true) :
    (ofMQ m q hm_pos hm_le hq_lo hq_hi).width.num = 3 := by
  unfold ofMQ
  simp [h_irreg]; omega

theorem ofMQ_width_denPow2 (m : Nat) (q : Int)
    (hm_pos : 1 ≤ m) (hm_le : m < 2 ^ 53) (hq_lo : -1074 ≤ q) (hq_hi : q ≤ 971) :
    (ofMQ m q hm_pos hm_le hq_lo hq_hi).width.denPow2 = -q + 2 := rfl

/-! ### Width-as-a-value theorems

The numerator analysis above gives `width.num = 4` (regular) or `3`
(irregular) at `denPow2 = -q + 2`. We translate this to the
"intuitive" form by `Midpoint.Equiv`:

- regular: `width ~ ⟨1, -q⟩` (= `2^q`)
- irregular: `width ~ ⟨3, -q + 2⟩` (= `3 · 2^(q-2) = (3/4) · 2^q`)

The regular equivalence rests on `4 · 2^(q-2) = 2^q`, i.e. `4 = 2^2`.
The irregular form is *already* `⟨3, -q + 2⟩` modulo definitional
unfolding — a one-line lemma. -/

/-- Width of `R_v` in regular spacing is `2^q`. Stated as
`Midpoint.Equiv width ⟨1, -q⟩`. -/
theorem width_regular (m : Nat) (q : Int)
    (hm_pos : 1 ≤ m) (hm_le : m < 2 ^ 53) (hq_lo : -1074 ≤ q) (hq_hi : q ≤ 971)
    (h_reg : ¬ (isIrregular m q = true)) :
    (ofMQ m q hm_pos hm_le hq_lo hq_hi).width.Equiv ⟨1, -q⟩ := by
  -- Width = ⟨4, -q + 2⟩, target = ⟨1, -q⟩.
  -- Cross-mul: 4 · 2^((-q) - (-q+2))⁺ = 1 · 2^((-q+2) - (-q))⁺
  --         ↔ 4 · 2^0 = 1 · 2^2 ↔ 4 = 4. ✓
  show Midpoint.Equiv _ _
  unfold Midpoint.Equiv
  have hwidth_num : (ofMQ m q hm_pos hm_le hq_lo hq_hi).width.num = 4 :=
    ofMQ_width_num_regular m q hm_pos hm_le hq_lo hq_hi h_reg
  have hwidth_den : (ofMQ m q hm_pos hm_le hq_lo hq_hi).width.denPow2 = -q + 2 := rfl
  show (ofMQ m q hm_pos hm_le hq_lo hq_hi).width.num *
        Midpoint.shiftFactor ((⟨1, -q⟩ : Midpoint).denPow2
          - (ofMQ m q hm_pos hm_le hq_lo hq_hi).width.denPow2)
        = (⟨1, -q⟩ : Midpoint).num *
            Midpoint.shiftFactor ((ofMQ m q hm_pos hm_le hq_lo hq_hi).width.denPow2
              - (⟨1, -q⟩ : Midpoint).denPow2)
  rw [hwidth_num, hwidth_den]
  -- Goal now: 4 * 2^((-q - (-q+2)).toNat) = 1 * 2^(((-q+2) - (-q)).toNat)
  show (4 : Int) * Midpoint.shiftFactor (-q - (-q + 2)) = 1 * Midpoint.shiftFactor (-q + 2 - -q)
  have h1 : (-q - (-q + 2) : Int) = -2 := by omega
  have h2 : (-q + 2 - -q : Int) = 2 := by omega
  rw [h1, h2]
  unfold Midpoint.shiftFactor
  decide

/-- Width of `R_v` in irregular spacing is `3 · 2^(q-2) = (3/4) · 2^q`.
Stated as `Midpoint.Equiv width ⟨3, -q + 2⟩`. -/
theorem width_irregular (m : Nat) (q : Int)
    (hm_pos : 1 ≤ m) (hm_le : m < 2 ^ 53) (hq_lo : -1074 ≤ q) (hq_hi : q ≤ 971)
    (h_irreg : isIrregular m q = true) :
    (ofMQ m q hm_pos hm_le hq_lo hq_hi).width.Equiv ⟨3, -q + 2⟩ := by
  -- Width = ⟨3, -q + 2⟩ already.
  apply Midpoint.equiv_of_same_den
  · exact ofMQ_width_denPow2 m q hm_pos hm_le hq_lo hq_hi
  · exact ofMQ_width_num_irregular m q hm_pos hm_le hq_lo hq_hi h_irreg

/-! ### `v ∈ R_v` and strict-order endpoints

Both endpoints share `denPow2` with `vMid`, so the strict numerator
orderings carried in the structure (`vl_lt_v_num`, `v_lt_vr_num`)
immediately give the value-level strict inequalities `vl < v < vr`. -/

/-- `vℓ < v` as `Midpoint` values. -/
theorem vl_lt_v (m : Nat) (q : Int)
    (hm_pos : 1 ≤ m) (hm_le : m < 2 ^ 53) (hq_lo : -1074 ≤ q) (hq_hi : q ≤ 971) :
    let R := ofMQ m q hm_pos hm_le hq_lo hq_hi
    R.vl < R.vMid := by
  intro R
  apply Midpoint.lt_of_same_den
  · rw [R.vl_den, R.vMid_den]
  · exact R.vl_lt_v_num

/-- `v < vr` as `Midpoint` values. -/
theorem v_lt_vr (m : Nat) (q : Int)
    (hm_pos : 1 ≤ m) (hm_le : m < 2 ^ 53) (hq_lo : -1074 ≤ q) (hq_hi : q ≤ 971) :
    let R := ofMQ m q hm_pos hm_le hq_lo hq_hi
    R.vMid < R.vr := by
  intro R
  apply Midpoint.lt_of_same_den
  · rw [R.vMid_den, R.vr_den]
  · exact R.v_lt_vr_num

/-- `v ∈ [vℓ, vr]` — non-strict version, the formal statement that `v`
itself lies in `R_v`. -/
theorem v_mem_rv (m : Nat) (q : Int)
    (hm_pos : 1 ≤ m) (hm_le : m < 2 ^ 53) (hq_lo : -1074 ≤ q) (hq_hi : q ≤ 971) :
    let R := ofMQ m q hm_pos hm_le hq_lo hq_hi
    R.vl ≤ R.vMid ∧ R.vMid ≤ R.vr := by
  intro R
  refine ⟨?_, ?_⟩
  · apply Midpoint.le_of_same_den
    · rw [R.vl_den, R.vMid_den]
    · exact Int.le_of_lt R.vl_lt_v_num
  · apply Midpoint.le_of_same_den
    · rw [R.vMid_den, R.vr_den]
    · exact Int.le_of_lt R.v_lt_vr_num

/-! ### Endpoint-vs-`v` value equalities

Useful for M3.8.3+ to talk about `v - vℓ` (the half-width on the lower
side) without unfolding the constructor every time. We expose the
numerator differences at the shared scale — the most ergonomic form
for downstream `omega`/`decide` arithmetic. -/

/-- `v - vℓ` numerator (regular): `4·m - (4·m - 2) = 2`. So the value
is `2 / 2^(-q+2) = 2^(q-1)`, the regular half-width. -/
theorem v_minus_vl_num_regular (m : Nat) (q : Int)
    (hm_pos : 1 ≤ m) (hm_le : m < 2 ^ 53) (hq_lo : -1074 ≤ q) (hq_hi : q ≤ 971)
    (h_reg : ¬ (isIrregular m q = true)) :
    let R := ofMQ m q hm_pos hm_le hq_lo hq_hi
    R.vMid.num - R.vl.num = 2 := by
  intro R
  rw [ofMQ_vMid_num, ofMQ_vl_num_regular m q hm_pos hm_le hq_lo hq_hi h_reg]
  omega

/-- `v - vℓ` numerator (irregular): `4·m - (4·m - 1) = 1`. So the
value is `1 / 2^(-q+2) = 2^(q-2)`, the irregular half-width on the
lower side. -/
theorem v_minus_vl_num_irregular (m : Nat) (q : Int)
    (hm_pos : 1 ≤ m) (hm_le : m < 2 ^ 53) (hq_lo : -1074 ≤ q) (hq_hi : q ≤ 971)
    (h_irreg : isIrregular m q = true) :
    let R := ofMQ m q hm_pos hm_le hq_lo hq_hi
    R.vMid.num - R.vl.num = 1 := by
  intro R
  rw [ofMQ_vMid_num, ofMQ_vl_num_irregular m q hm_pos hm_le hq_lo hq_hi h_irreg]
  omega

/-- `vr - v` numerator (always 2 in both cases): the upper half-width
is `2^(q-1)` whether spacing is regular or irregular. This is the
*key asymmetry* of the irregular case — the lower side shrinks but
the upper side is unchanged. -/
theorem vr_minus_v_num (m : Nat) (q : Int)
    (hm_pos : 1 ≤ m) (hm_le : m < 2 ^ 53) (hq_lo : -1074 ≤ q) (hq_hi : q ≤ 971) :
    let R := ofMQ m q hm_pos hm_le hq_lo hq_hi
    R.vr.num - R.vMid.num = 2 := by
  intro R
  rw [ofMQ_vr_num, ofMQ_vMid_num]
  omega

/-! ### Cross-check with `inRoundingInterval`

`Srtfp.Schubfach.inRoundingInterval` uses exactly the same scaled
endpoints: `leftN = 4m - 1` or `4m - 2`, `rightN = 4m + 2`. The
lemmas below witness that correspondence as plain equalities — useful
when M3.8.4+ needs to bridge between the `inRoundingInterval` boolean
and the `R_v` structural claim. -/

/-- `inRoundingInterval`'s left numerator matches `vl.num`. -/
theorem ofMQ_vl_matches_inRI_leftN (m : Nat) (q : Int)
    (hm_pos : 1 ≤ m) (hm_le : m < 2 ^ 53) (hq_lo : -1074 ≤ q) (hq_hi : q ≤ 971) :
    let R := ofMQ m q hm_pos hm_le hq_lo hq_hi
    let irreg := isIrregular m q
    R.vl.num = (if irreg then 4 * (m : Int) - 1 else 4 * (m : Int) - 2) := by
  intro R irreg
  by_cases h : irreg = true
  · have h_irreg : isIrregular m q = true := h
    rw [ofMQ_vl_num_irregular m q hm_pos hm_le hq_lo hq_hi h_irreg]
    simp [show irreg = true from h]
  · have h_reg : ¬ (isIrregular m q = true) := h
    rw [ofMQ_vl_num_regular m q hm_pos hm_le hq_lo hq_hi h_reg]
    have : irreg = false := Bool.eq_false_iff.mpr h
    simp [this]

/-- `inRoundingInterval`'s right numerator matches `vr.num`. -/
theorem ofMQ_vr_matches_inRI_rightN (m : Nat) (q : Int)
    (hm_pos : 1 ≤ m) (hm_le : m < 2 ^ 53) (hq_lo : -1074 ≤ q) (hq_hi : q ≤ 971) :
    let R := ofMQ m q hm_pos hm_le hq_lo hq_hi
    R.vr.num = 4 * (m : Int) + 2 := ofMQ_vr_num m q hm_pos hm_le hq_lo hq_hi

end RoundingInterval

end Srtfp.Schubfach

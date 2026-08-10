/- Correctness of `shiftedSig` (M3.8.4).

   `shiftedSig m q k` computes the integer floor of `m · 2^q · 10^(-k)`
   by clearing denominators and performing a single `Nat`-division:

       shiftedSig m q k = (m · 2^{max q 0} · 10^{max -k 0})
                          / (2^{max -q 0} · 10^{max k 0})

   The correctness statement is the integer-division algorithm,
   cross-multiplied so no rationals appear:

       s · 2^{max -q 0} · 10^{max k 0}  ≤  m · 2^{max q 0} · 10^{max -k 0}
       m · 2^{max q 0} · 10^{max -k 0}  <  (s + 1) · 2^{max -q 0} · 10^{max k 0}

   Proof is `Nat.div_mul_le_self` + `Nat.mod_lt` (`Nat.div_add_mod` packaged).
   No transcendentals, no decide, no native_decide.

   The only axioms used are `propext, Quot.sound, Classical.choice`. -/

import Srtfp.Schubfach

namespace Srtfp.Schubfach

/-! ## Sign-split power helpers

These mirror the let-bindings in `shiftedSig` and `cmpScaledMixed`.

NOTE: These are `def` (not `abbrev`) so they do NOT unfold automatically
during `rw`/`simp` chains. This is deliberate — earlier versions used
`abbrev`, but the resulting nested-if expressions caused exponential
elaboration blowups in the cast-heavy irregular-Clinger proofs
(5–9 min per file). Use the `*_nonneg` / `*_neg` lemmas below to
reduce the if-expression to its concrete branch, or `unfold` the
constant explicitly when needed. -/

/-- `2^{max q 0}`: the positive-side factor of `2^q`. -/
def twoPosPow (q : Int) : Nat := 2 ^ (if q ≥ 0 then q.toNat else 0)

/-- `2^{max -q 0}`: the negative-side factor of `2^q`. -/
def twoNegPow (q : Int) : Nat := 2 ^ (if q < 0 then (-q).toNat else 0)

/-- `10^{max k 0}`: the positive-side factor of `10^k`. -/
def tenPosPow (k : Int) : Nat := 10 ^ (if k ≥ 0 then k.toNat else 0)

/-- `10^{max -k 0}`: the negative-side factor of `10^k`. -/
def tenNegPow (k : Int) : Nat := 10 ^ (if k < 0 then (-k).toNat else 0)

/-! ## Branch characterising lemmas

These let callers reduce a power constant to its concrete form once
the sign of `q`/`k` is known, without unfolding the `def` and
re-traversing the if-expression. -/

@[simp] theorem twoPosPow_nonneg {q : Int} (h : 0 ≤ q) :
    twoPosPow q = 2 ^ q.toNat := by
  unfold twoPosPow; rw [if_pos h]

@[simp] theorem twoPosPow_neg {q : Int} (h : q < 0) :
    twoPosPow q = 1 := by
  unfold twoPosPow
  have : ¬ (0 ≤ q) := Int.not_le.mpr h
  rw [if_neg this]

@[simp] theorem twoNegPow_neg {q : Int} (h : q < 0) :
    twoNegPow q = 2 ^ (-q).toNat := by
  unfold twoNegPow; rw [if_pos h]

@[simp] theorem twoNegPow_nonneg {q : Int} (h : 0 ≤ q) :
    twoNegPow q = 1 := by
  unfold twoNegPow
  have : ¬ (q < 0) := Int.not_lt.mpr h
  rw [if_neg this]

@[simp] theorem tenPosPow_nonneg {k : Int} (h : 0 ≤ k) :
    tenPosPow k = 10 ^ k.toNat := by
  unfold tenPosPow; rw [if_pos h]

@[simp] theorem tenPosPow_neg {k : Int} (h : k < 0) :
    tenPosPow k = 1 := by
  unfold tenPosPow
  have : ¬ (0 ≤ k) := Int.not_le.mpr h
  rw [if_neg this]

@[simp] theorem tenNegPow_neg {k : Int} (h : k < 0) :
    tenNegPow k = 10 ^ (-k).toNat := by
  unfold tenNegPow; rw [if_pos h]

@[simp] theorem tenNegPow_nonneg {k : Int} (h : 0 ≤ k) :
    tenNegPow k = 1 := by
  unfold tenNegPow
  have : ¬ (k < 0) := Int.not_lt.mpr h
  rw [if_neg this]

/-- Positivity of any `twoPosPow` factor (always non-zero). -/
theorem twoPosPow_pos (q : Int) : 0 < twoPosPow q :=
  Nat.pow_pos (a := 2) (by decide)

/-- Positivity of any `twoNegPow` factor (always non-zero). -/
theorem twoNegPow_pos (q : Int) : 0 < twoNegPow q :=
  Nat.pow_pos (a := 2) (by decide)

/-- Positivity of any `tenPosPow` factor (always non-zero). -/
theorem tenPosPow_pos (k : Int) : 0 < tenPosPow k :=
  Nat.pow_pos (a := 10) (by decide)

/-- Positivity of any `tenNegPow` factor (always non-zero). -/
theorem tenNegPow_pos (k : Int) : 0 < tenNegPow k :=
  Nat.pow_pos (a := 10) (by decide)

/-- Positivity of the cleared denominator `2^{max -q 0} · 10^{max k 0}`. -/
theorem twoNeg_tenPos_pos (q k : Int) : 0 < twoNegPow q * tenPosPow k :=
  Nat.mul_pos (twoNegPow_pos q) (tenPosPow_pos k)

/-! ## Spec predicate

`IsShiftedSigOf s m q k` says `s = ⌊m · 2^q · 10^(-k)⌋`, expressed
purely in `Nat` via the cross-multiplied integer-division algorithm. -/

/-- `s` is the integer floor of `m · 2^q · 10^(-k)`, cross-multiplied
to remove rationals. The lower bound says `s · 2^{-q} · 10^{k} ≤ num`
and the strict upper bound says `num < (s+1) · 2^{-q} · 10^{k}`. -/
def IsShiftedSigOf (s m : Nat) (q k : Int) : Prop :=
  s * (twoNegPow q * tenPosPow k) ≤ m * (twoPosPow q * tenNegPow k) ∧
  m * (twoPosPow q * tenNegPow k) < (s + 1) * (twoNegPow q * tenPosPow k)

/-! ## Main theorem -/

/-- `shiftedSig m q k` is the integer floor of `m · 2^q · 10^(-k)`. -/
theorem shiftedSig_correct (m : Nat) (q k : Int) :
    IsShiftedSigOf (shiftedSig m q k) m q k := by
  -- Name numerator and denominator.
  let N : Nat := m * twoPosPow q * tenNegPow k
  let D : Nat := twoNegPow q * tenPosPow k
  have hD_pos : 0 < D := twoNeg_tenPos_pos q k
  -- `shiftedSig m q k = N / D` (just naming the let bindings).
  have hsig : shiftedSig m q k = N / D := by
    show shiftedSig m q k = (m * twoPosPow q * tenNegPow k) / (twoNegPow q * tenPosPow k)
    rfl
  -- Cross-reassociation helpers.
  have hN_eq : m * (twoPosPow q * tenNegPow k) = N := by
    show m * (twoPosPow q * tenNegPow k) = m * twoPosPow q * tenNegPow k
    rw [Nat.mul_assoc]
  have hD_eq : (twoNegPow q * tenPosPow k) = D := rfl
  refine ⟨?_, ?_⟩
  · rw [hsig, hN_eq, hD_eq]
    exact Nat.div_mul_le_self N D
  · rw [hsig, hN_eq, hD_eq]
    -- N < (N/D + 1) * D from Nat.div_add_mod + Nat.mod_lt.
    have hdm : N / D * D + N % D = N := by
      rw [Nat.mul_comm]; exact Nat.div_add_mod N D
    have hmod : N % D < D := Nat.mod_lt N hD_pos
    rw [Nat.add_mul, Nat.one_mul]
    omega

/-! ## Convenience extractors -/

/-- Lower bound projection of `shiftedSig_correct`. -/
theorem shiftedSig_le (m : Nat) (q k : Int) :
    shiftedSig m q k * (twoNegPow q * tenPosPow k)
      ≤ m * (twoPosPow q * tenNegPow k) :=
  (shiftedSig_correct m q k).1

/-- Strict upper bound projection of `shiftedSig_correct`. -/
theorem shiftedSig_lt_succ (m : Nat) (q k : Int) :
    m * (twoPosPow q * tenNegPow k)
      < (shiftedSig m q k + 1) * (twoNegPow q * tenPosPow k) :=
  (shiftedSig_correct m q k).2

end Srtfp.Schubfach

/- Precomputed power tables for the Schubfach multiply-shift kernel.

   `Schubfach.shiftedSig m q k` recomputes `2^|q|` and `10^|k|` from
   scratch on every call. For binary64 the operand sizes go up to
   `10^324 ≈ 2^1077`, and although `Nat.pow` is GMP-optimized, building
   the operand still dominates the per-call cost.

   This module precomputes both tables once at module load time and
   exposes total `pow2Lookup` / `pow10Lookup` wrappers that fall back to
   `Nat.pow` if the requested exponent is outside the precomputed range.

   The tables cover the full binary64 range:

     - `pow2Tab` : indices 0..1074  (`-qMin = 1074`)
     - `pow10Tab`: indices 0..324   (`-kMin = 324`)

   Phase 1 of the UInt64 refinement: this keeps the arithmetic in `Nat`
   (the GMP multiply / divide is the inner kernel) but eliminates the
   redundant `^` cost. A full UInt64 multiply-shift refinement is Phase 2.
-/

namespace Srtfp.Schubfach

/-! ## Generic builder -/

/-- Build the power table `[base^0, base^1, ..., base^n]`. -/
def buildPowTab (base : Nat) (n : Nat) : Array Nat :=
  ((List.range (n + 1)).map (base ^ ·)).toArray

theorem buildPowTab_size (base n : Nat) :
    (buildPowTab base n).size = n + 1 := by
  unfold buildPowTab
  simp

theorem buildPowTab_get (base n : Nat) (i : Nat)
    (h : i < (buildPowTab base n).size) :
    (buildPowTab base n)[i]'h = base ^ i := by
  unfold buildPowTab
  simp

/-! ## Concrete tables and lookups

`pow2Tab.size = 1075`, `pow10Tab.size = 325`. Index `i` holds `base^i`.
The tables are heap-shared `Nat` constants — built once at module init. -/

/-- Powers of 2: `pow2Tab[i] = 2^i` for `i ∈ [0, 1074]`. -/
def pow2Tab : Array Nat := buildPowTab 2 1074

/-- Powers of 10: `pow10Tab[i] = 10^i` for `i ∈ [0, 324]`. -/
def pow10Tab : Array Nat := buildPowTab 10 324

theorem pow2Tab_size : pow2Tab.size = 1075 := buildPowTab_size 2 1074

theorem pow10Tab_size : pow10Tab.size = 325 := buildPowTab_size 10 324

/-- Total `2^n` lookup with fallback. Inside the binary64 range
    (`n ≤ 1074`) this is an O(1) array lookup. -/
@[inline]
def pow2Lookup (n : Nat) : Nat :=
  pow2Tab.getD n (2 ^ n)

/-- Total `10^n` lookup with fallback. Inside the binary64 range
    (`n ≤ 324`) this is an O(1) array lookup. -/
@[inline]
def pow10Lookup (n : Nat) : Nat :=
  pow10Tab.getD n (10 ^ n)

/-! ## Correctness -/

theorem pow2Lookup_eq (n : Nat) : pow2Lookup n = 2 ^ n := by
  unfold pow2Lookup
  rw [show pow2Tab.getD n (2 ^ n) = (if h : n < pow2Tab.size then pow2Tab[n] else 2 ^ n) from rfl]
  split
  · next h => unfold pow2Tab; rw [buildPowTab_get]
  · rfl

theorem pow10Lookup_eq (n : Nat) : pow10Lookup n = 10 ^ n := by
  unfold pow10Lookup
  rw [show pow10Tab.getD n (10 ^ n) = (if h : n < pow10Tab.size then pow10Tab[n] else 10 ^ n) from rfl]
  split
  · next h => unfold pow10Tab; rw [buildPowTab_get]
  · rfl

end Srtfp.Schubfach

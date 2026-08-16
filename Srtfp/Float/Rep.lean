/- FloatRep — rational-valued model of IEEE-754 binary64.

   ## Why this file exists (M3.8.0)

   The Schubfach printer (`Srtfp.Schubfach`) and Clinger reader
   (`Srtfp.Clinger`) operate on raw `Float`s, which Lean exposes only
   through the opaque bit-level interface `Float.toBits` / `Float.ofBits`
   and (for arithmetic) the runtime intrinsics. To state and prove
   correctness theorems about either pipeline we need a *mathematical*
   model of finite binary64 — one we can reason about with ordinary
   `Nat`/`Int` arithmetic.

   `FloatRep` is that model. A `FloatRep` is a finite binary64 value
   represented exactly as

       (-1)^sign × m × 2^q       with  m < 2^53,  -1074 ≤ q ≤ 971.

   This is the same `(sign, m, q)` decomposition that `Float/Bits.lean`
   already produces via `decode`, but bundled with the binary64 range
   invariants. The point of separating it from `Decoded` is so that

     1. M3.8.1+ can reason about *finite* `Float` values without
        re-checking the bit-pattern bounds at every step;
     2. We get a clean carrier on which to define a real-valued semantics
        (`value`, `Equiv`) that downstream proofs (Schubfach round-trip,
        Clinger correct-rounding) can refer to;
     3. The bridge to the runtime `Float` type sits in one place
        (`toFloat`, `Float.toFloatRep`), and *nothing* in the M3.8.0
        layer depends on a `toBits ∘ ofBits = id` round-trip lemma.
        That lemma is a property of the Lean runtime intrinsics — we
        cannot prove it from first principles — and so it is deferred to
        downstream code (M3.8.x bridge / M4 correctness) where it can be
        introduced as a single named theorem and audited independently.

   ## Design choice: which canonical form?

   A given real number ±r has many `(sign, m, q)` representations:
   `(s, m, q) ∼ (s, 2m, q-1)` whenever `2m < 2^53` and `q-1 ≥ -1074`.
   Two reasonable canonicalisations are possible:

     A. "Odd-or-zero": insist either `m = 0` or `m` is odd. This is the
        *minimal-m* representation; useful for proofs about uniqueness
        of shortest decimals (Schubfach's invariant).
     B. "Maximal-m" / "IEEE-754 canonical": insist either `q = -1074 ∧
        m < 2^52` (subnormal/zero) or `2^52 ≤ m < 2^53` (normal). This
        is what the IEEE-754 biased-exponent encoding produces, and what
        `decode` returns.

   We do *not* impose either at the structure level — `FloatRep` is just
   "any triple in the binary64 rectangle". Both predicates are exposed
   as `Prop`s (`IsCanonicalRep` for form B, `IsOddOrZero` for form A).
   Reasoning is cleaner that way: the carrier is a trivial product, and
   real-value equality is captured by `Equiv` separately. Imposing a
   canonical form at the structure level would force two-way
   normalisation lemmas at every step.

   ## What this file does NOT contain

     - Bit-level round-trip lemmas about `Float.toBits` / `Float.ofBits`.
       Those need to be axiomatised or `native_decide`d at a single
       bridge point; M3.8.0 keeps the model first-principles.
     - Arithmetic on `FloatRep` (multiply, add, sqrt, etc.). Not needed
       for Schubfach/Clinger correctness statements — those only need
       order, equality, and the rational value. -/

import Srtfp.Float.Bits

namespace Srtfp.Float

/-! ## Small arithmetic lemmas

We don't have Mathlib, so we need to prove a handful of `Int`-power
facts from Lean-core lemmas. Kept `private` to avoid polluting the
namespace. -/

private theorem int_pow_two_ne_zero (n : Nat) : ((2 : Int) ^ n) ≠ 0 := by
  induction n with
  | zero => decide
  | succ k ih =>
    rw [Int.pow_succ]
    intro h
    cases Int.mul_eq_zero.mp h with
    | inl h2 => exact ih h2
    | inr h2 => exact absurd h2 (by decide)

private theorem int_pow_two_pos (n : Nat) : (0 : Int) < 2 ^ n := by
  induction n with
  | zero => decide
  | succ k ih =>
    rw [Int.pow_succ]
    exact Int.mul_pos ih (by decide)

/-! ## The `FloatRep` structure

A finite binary64 represented exactly. The invariants are the IEEE-754
binary64 *finite-domain* bounds: `m ∈ [0, 2^53)`, `q ∈ [-1074, 971]`.

Note that not every `(sign, m, q)` triple in this rectangle is reachable
by a real `Float`: representations with `q > -1074 ∧ m < 2^52` are
unreachable (they would be a subnormal in disguise — IEEE-754 forbids
those by definition, the encoding only admits `q = -1074` when the
significand lacks the implicit leading 1). We *allow* such triples in
the carrier and treat them as equivalent to their normalised form via
`Equiv`. Reasoning is cleaner that way: the invariant rectangle is
trivially a product, and IEEE reachability is recovered as a separate
predicate `IsCanonicalRep` when wanted. -/

/-- A finite binary64 value, in the form `(-1)^sign × m × 2^q`. The
bounds cover both normals (`2^52 ≤ m < 2^53`, `-1074 ≤ q ≤ 971`) and
subnormals/zero (`0 ≤ m < 2^52`, `q = -1074`). -/
structure FloatRep where
  sign : Bool
  m : Nat
  q : Int
  m_le : m < 2 ^ 53
  q_ge : -1074 ≤ q
  q_le : q ≤ 971
  deriving Repr

namespace FloatRep

/-! ## Sample constructors -/

/-- `+0` in the canonical (subnormal-zero) encoding. -/
def zero : FloatRep where
  sign := false
  m := 0
  q := -1074
  m_le := by decide
  q_ge := by decide
  q_le := by decide

/-- `-0` in the canonical (subnormal-zero) encoding. Distinct from `zero`
as a `FloatRep` but `Equiv`-equal (they share real value `0`). -/
def negZero : FloatRep where
  sign := true
  m := 0
  q := -1074
  m_le := by decide
  q_ge := by decide
  q_le := by decide

/-- `+1.0 = 1 · 2^52 · 2^{-52}` in IEEE-canonical (normalised) form. -/
def one : FloatRep where
  sign := false
  m := 1 <<< 52
  q := -52
  m_le := by decide
  q_ge := by decide
  q_le := by decide

instance : Inhabited FloatRep := ⟨zero⟩

/-! ## Canonicality predicates

A `FloatRep` is *IEEE-canonical* (matches what `decode` produces) when
either it is the subnormal/zero encoding (`q = -1074`, `m < 2^52`) or
it is the normal encoding (`2^52 ≤ m`). Any other `(m, q)` in the
rectangle is reachable only via `Equiv`. -/

/-- `r` is the canonical IEEE-754 encoding (normal or subnormal/zero
with no leading-1). -/
def IsCanonicalRep (r : FloatRep) : Prop :=
  (r.q = -1074 ∧ r.m < 2 ^ 52) ∨ (2 ^ 52 ≤ r.m ∧ r.m < 2 ^ 53)

instance (r : FloatRep) : Decidable (IsCanonicalRep r) := by
  unfold IsCanonicalRep
  exact inferInstance

/-- `r` represents a *normal* binary64. -/
def IsNormal (r : FloatRep) : Prop :=
  2 ^ 52 ≤ r.m ∧ r.m < 2 ^ 53

/-- `r` represents a *subnormal* or zero in canonical form. -/
def IsSubnormalOrZero (r : FloatRep) : Prop :=
  r.q = -1074 ∧ r.m < 2 ^ 52

instance (r : FloatRep) : Decidable (IsNormal r) := by
  unfold IsNormal; infer_instance
instance (r : FloatRep) : Decidable (IsSubnormalOrZero r) := by
  unfold IsSubnormalOrZero; infer_instance

/-- `r` represents zero (either sign). -/
def IsZero (r : FloatRep) : Prop := r.m = 0
instance (r : FloatRep) : Decidable (IsZero r) := by unfold IsZero; infer_instance

/-! ## Real value as a (signed numerator, denominator-power-of-2) pair

We cannot use `ℚ` (no Mathlib), so we represent the exact real value as
an `Int × Nat`: `(num, d)` denotes the rational `num / 2^d`. With this
encoding, sign is folded into `num`, and the power of two is split
between numerator and denominator depending on the sign of `q`:

  - `q ≥ 0`: `value = (±m · 2^q, 0)`. The real is the integer `±m·2^q`.
  - `q < 0`: `value = (±m, -q)`. The real is `±m / 2^{-q}`.

Two `FloatRep`s denote the same real iff their pairs are cross-product
equal (see `Equiv`). -/

/-- The exact real value of `r`, as `(numerator, denPow2)`. The real
denoted is `numerator / 2^denPow2`. -/
def value (r : FloatRep) : Int × Nat :=
  let signedM : Int := if r.sign then -(r.m : Int) else (r.m : Int)
  if r.q ≥ 0 then
    (signedM * (2 ^ r.q.toNat : Int), 0)
  else
    (signedM, (-r.q).toNat)

/-- The numerator of `value r` (signed). -/
def valueNum (r : FloatRep) : Int := (value r).1

/-- The denominator-power of `value r` (non-negative; `0` when `r.q ≥ 0`). -/
def valueDenPow (r : FloatRep) : Nat := (value r).2

/-- Convenience: signed-mantissa abbreviation. -/
private def signedMantissa (r : FloatRep) : Int :=
  if r.sign then -(r.m : Int) else (r.m : Int)

/-- `value` on the non-negative-`q` branch. -/
theorem value_of_q_nonneg
    {r : FloatRep} (h : 0 ≤ r.q) :
    value r = (signedMantissa r * (2 ^ r.q.toNat : Int), 0) := by
  unfold value signedMantissa
  simp [h]

/-- `value` on the negative-`q` branch. -/
theorem value_of_q_neg
    {r : FloatRep} (h : r.q < 0) :
    value r = (signedMantissa r, (-r.q).toNat) := by
  unfold value signedMantissa
  have : ¬ r.q ≥ 0 := by omega
  simp [this]

/-! ## Equivalence: two `FloatRep`s denote the same real

We use the cross-multiplied form: `(n1 / 2^d1) = (n2 / 2^d2)` iff
`n1 · 2^d2 = n2 · 2^d1`. This avoids needing a normal form. -/

/-- `a` and `b` denote the same real number. -/
def Equiv (a b : FloatRep) : Prop :=
  (value a).1 * (2 ^ (value b).2 : Int) = (value b).1 * (2 ^ (value a).2 : Int)

theorem Equiv.refl (a : FloatRep) : Equiv a a := by
  unfold Equiv; rfl

theorem Equiv.symm {a b : FloatRep} (h : Equiv a b) : Equiv b a := by
  unfold Equiv at h ⊢; exact h.symm

/-- Transitivity. The proof is a cancellation argument on `2 ^ d_b`:

      n_a · 2^d_b = n_b · 2^d_a            (hab)
      n_b · 2^d_c = n_c · 2^d_b            (hbc)
    ⇒ n_a · 2^d_c · 2^d_b = n_c · 2^d_a · 2^d_b
    ⇒ n_a · 2^d_c = n_c · 2^d_a            (cancel 2^d_b ≠ 0).

   Without `grind`, we chain the rearrangements as a `calc` block. -/
theorem Equiv.trans {a b c : FloatRep}
    (hab : Equiv a b) (hbc : Equiv b c) : Equiv a c := by
  unfold Equiv at hab hbc ⊢
  -- Abbreviate for readability. (`set` is unavailable in core Lean.)
  let na : Int := (value a).1
  let nb : Int := (value b).1
  let nc : Int := (value c).1
  let da : Nat := (value a).2
  let db : Nat := (value b).2
  let dc : Nat := (value c).2
  change na * (2 ^ dc : Int) = nc * (2 ^ da : Int)
  -- We have hab : na * 2^db = nb * 2^da, hbc : nb * 2^dc = nc * 2^db.
  have h1 : (na * (2 ^ db : Int)) * (2 ^ dc : Int)
              = (nb * (2 ^ da : Int)) * (2 ^ dc : Int) := by
    show (na * (2 ^ db : Int)) * (2 ^ dc : Int)
         = (nb * (2 ^ da : Int)) * (2 ^ dc : Int)
    rw [hab]
  have h2 : (nb * (2 ^ dc : Int)) * (2 ^ da : Int)
              = (nc * (2 ^ db : Int)) * (2 ^ da : Int) := by
    show (nb * (2 ^ dc : Int)) * (2 ^ da : Int)
         = (nc * (2 ^ db : Int)) * (2 ^ da : Int)
    rw [hbc]
  -- Reassociate / commute so we can chain h1 and h2.
  have h1' : na * (2 ^ dc : Int) * (2 ^ db : Int)
              = nb * (2 ^ dc : Int) * (2 ^ da : Int) := by
    calc na * (2 ^ dc : Int) * (2 ^ db : Int)
        = na * ((2 ^ dc : Int) * (2 ^ db : Int)) := by rw [Int.mul_assoc]
      _ = na * ((2 ^ db : Int) * (2 ^ dc : Int)) :=
            by rw [Int.mul_comm ((2 ^ dc : Int)) _]
      _ = na * (2 ^ db : Int) * (2 ^ dc : Int) := by rw [← Int.mul_assoc]
      _ = nb * (2 ^ da : Int) * (2 ^ dc : Int) := h1
      _ = nb * ((2 ^ da : Int) * (2 ^ dc : Int)) := by rw [Int.mul_assoc]
      _ = nb * ((2 ^ dc : Int) * (2 ^ da : Int)) :=
            by rw [Int.mul_comm ((2 ^ da : Int)) _]
      _ = nb * (2 ^ dc : Int) * (2 ^ da : Int) := by rw [← Int.mul_assoc]
  have h3 : na * (2 ^ dc : Int) * (2 ^ db : Int)
              = nc * (2 ^ db : Int) * (2 ^ da : Int) := by rw [h1', h2]
  have h3' : na * (2 ^ dc : Int) * (2 ^ db : Int)
              = nc * (2 ^ da : Int) * (2 ^ db : Int) := by
    calc na * (2 ^ dc : Int) * (2 ^ db : Int)
        = nc * (2 ^ db : Int) * (2 ^ da : Int) := h3
      _ = nc * ((2 ^ db : Int) * (2 ^ da : Int)) := by rw [Int.mul_assoc]
      _ = nc * ((2 ^ da : Int) * (2 ^ db : Int)) :=
            by rw [Int.mul_comm ((2 ^ db : Int)) _]
      _ = nc * (2 ^ da : Int) * (2 ^ db : Int) := by rw [← Int.mul_assoc]
  exact Int.eq_of_mul_eq_mul_right (int_pow_two_ne_zero db) h3'

instance : Trans (α := FloatRep) Equiv Equiv Equiv := ⟨Equiv.trans⟩

/-! ## Signed-zero handling

Both `zero` and `negZero` denote the real `0`, so they are `Equiv`. -/

theorem zero_equiv_negZero : Equiv zero negZero := by rfl

theorem negZero_equiv_zero : Equiv negZero zero :=
  Equiv.symm zero_equiv_negZero

/-! ## Bridge to the runtime `Float` type

Pure definitional bridge — both directions reuse `Float/Bits.lean`'s
`fromBits` / `decode`. No correctness lemma is proven here, by design:
`toBits ∘ ofBits = id` (and the inverse direction) is a runtime
property, not a derivable theorem in pure Lean 4. That round-trip is
the single (restricted) bridge axiom `Float.toBits_ofBits` in
`Srtfp/Float/RuntimeAxiom.lean`; this file stays first-principles. -/

/-- The biased-exponent encoding of `q`: `q + 1023 + 52` for normals,
`0` for subnormals/zero. -/
def biasedExpOf (r : FloatRep) : Nat :=
  if 2 ^ 52 ≤ r.m then
    -- Normal. biasedExp = q + 1023 + 52.
    (r.q + 1023 + 52).toNat
  else
    -- Subnormal / zero. biasedExp = 0.
    0

/-- The 52-bit raw mantissa field: `m - 2^52` for normals, `m` for
subnormals. -/
def mantissaFieldOf (r : FloatRep) : Nat :=
  if 2 ^ 52 ≤ r.m then r.m - 2 ^ 52 else r.m

/-- Embed `r : FloatRep` into the runtime `Float` type via the bit
fields. The bit pattern is the IEEE-754 canonical encoding of `r`'s
real value, *provided* `r` is itself in `IsCanonicalRep` form. For
non-canonical `r`, `toFloat` still returns *some* `Float`, but it
might not represent the same real (the encoding silently
re-interprets out-of-range exponents). Callers needing the
guaranteed-correct embedding should first normalise via the
upcoming `M3.8.1` `canonicalise` function. -/
def toFloat (r : FloatRep) : _root_.Float :=
  fromBits r.sign (biasedExpOf r) (mantissaFieldOf r)

/-! ## Decoding a finite `Float` to `FloatRep`

Mirrors `decode` from `Float/Bits.lean` but bundles the range
invariants. Returns `none` for NaN / Infinity (where the
`(sign, m, q)` decomposition has no real-value meaning). -/

/-- The raw mantissa field is bounded by `2^52`. -/
private theorem mantissaBits_lt (f : _root_.Float) :
    mantissaBits f < 2 ^ 52 := by
  unfold mantissaBits
  rw [UInt64.toNat_and]
  have hmask : ((0x000F_FFFF_FFFF_FFFF : UInt64).toNat) = 4503599627370495 := by decide
  rw [hmask]
  have hle : f.toBits.toNat &&& 4503599627370495 ≤ 4503599627370495 := Nat.and_le_right
  have hpow : (2 : Nat) ^ 52 = 4503599627370496 := by decide
  omega

/-- For finite `f` (biased-exp < 2047), `(decode f).q ≥ -1074`. -/
private theorem decode_q_ge_of_biasedExp
    {f : _root_.Float} (_h : biasedExpBits f < 2047) :
    -1074 ≤ (decode f).q := by
  unfold decode
  by_cases he : biasedExpBits f = 0
  · simp [he]
  · simp [he]
    have h1 : 1 ≤ biasedExpBits f := Nat.one_le_iff_ne_zero.mpr he
    omega

/-- For finite `f`, `(decode f).q ≤ 971`. -/
private theorem decode_q_le_of_biasedExp
    {f : _root_.Float} (h : biasedExpBits f < 2047) :
    (decode f).q ≤ 971 := by
  unfold decode
  by_cases he : biasedExpBits f = 0
  · simp [he]
  · simp [he]
    have hle : biasedExpBits f ≤ 2046 := Nat.lt_succ_iff.mp h
    omega

/-- For finite `f`, `(decode f).m < 2^53`. -/
private theorem decode_m_lt_of_biasedExp
    {f : _root_.Float} (_h : biasedExpBits f < 2047) :
    (decode f).m < 2 ^ 53 := by
  unfold decode
  by_cases he : biasedExpBits f = 0
  · simp [he]
    have h1 := mantissaBits_lt f
    have h2 : (2 : Nat) ^ 52 < 2 ^ 53 := by decide
    omega
  · simp [he]
    have hmb := mantissaBits_lt f
    have h52 : (2 : Nat) ^ 52 = 4503599627370496 := by decide
    have h53 : (2 : Nat) ^ 53 = 9007199254740992 := by decide
    omega

/-- Decode a finite `Float` into a `FloatRep`. Returns `none` for
NaN / Infinity. The qualified name is `Srtfp.Float.Float.toFloatRep`
(so it can be invoked as `Float.toFloatRep` from within the
`Srtfp.Float` namespace). -/
def _root_.Srtfp.Float.Float.toFloatRep
    (f : _root_.Float) : Option FloatRep :=
  if h : biasedExpBits f < 2047 then
    let d := decode f
    some ⟨d.sign, d.m, d.q,
          decode_m_lt_of_biasedExp h,
          decode_q_ge_of_biasedExp h,
          decode_q_le_of_biasedExp h⟩
  else
    none

/-- When `toFloatRep` succeeds, its payload fields project to `decode`'s. -/
theorem toFloatRep_eq_decode
    {f : _root_.Float} {r : FloatRep}
    (h : _root_.Srtfp.Float.Float.toFloatRep f = some r) :
    r.sign = (decode f).sign ∧ r.m = (decode f).m ∧ r.q = (decode f).q := by
  unfold _root_.Srtfp.Float.Float.toFloatRep at h
  split at h
  · simp at h
    -- h : ⟨..., ...⟩ = r (after Option.some.injEq simp).
    -- The structure constructed has fields decode f's projections.
    exact ⟨by rw [← h], by rw [← h], by rw [← h]⟩
  · simp at h

/-- `toFloatRep` returns `some` iff `f`'s biased exponent is in the
finite range `[0, 2046]`. -/
theorem toFloatRep_isSome_iff (f : _root_.Float) :
    (_root_.Srtfp.Float.Float.toFloatRep f).isSome ↔ biasedExpBits f < 2047 := by
  unfold _root_.Srtfp.Float.Float.toFloatRep
  by_cases h : biasedExpBits f < 2047
  · simp [h]
  · simp [h]

/-- Equivalent surface using `isFiniteBits`. -/
theorem toFloatRep_isSome_iff_finite (f : _root_.Float) :
    (_root_.Srtfp.Float.Float.toFloatRep f).isSome ↔ isFiniteBits f = true := by
  rw [toFloatRep_isSome_iff]
  unfold isFiniteBits
  simp

/-! ## Canonicality of the bridged value

When `toFloatRep` succeeds, the resulting `FloatRep` is `IsCanonicalRep`
by construction — this is just `decode`'s structure. -/

theorem toFloatRep_isCanonical
    {f : _root_.Float} {r : FloatRep}
    (h : _root_.Srtfp.Float.Float.toFloatRep f = some r) :
    IsCanonicalRep r := by
  obtain ⟨_, hm, hq⟩ := toFloatRep_eq_decode h
  unfold IsCanonicalRep
  unfold decode at hm hq
  by_cases he : biasedExpBits f = 0
  · -- Subnormal / zero branch.
    simp [he] at hm hq
    left
    refine ⟨by rw [hq], ?_⟩
    rw [hm]
    exact mantissaBits_lt f
  · -- Normal branch.
    simp [he] at hm hq
    right
    refine ⟨?_, ?_⟩
    · rw [hm]
      have h52 : (2 : Nat) ^ 52 = 4503599627370496 := by decide
      omega
    · exact r.m_le

/-! ## Odd-canonical form (alternative canonicaliser)

For proofs that prefer minimal-m representations, expose the "strip
trailing factors of 2 from the binary significand" map. Result: either
`m = 0` or `m` is odd. This stays at the value-pair level — we do *not*
construct a re-canonicalised `FloatRep` because the new `(m', q')` may
fall outside the binary64 rectangle even when the original was inside
(e.g. `m = 2, q = 971` would canonicalise to `m' = 1, q' = 972 > 971`).
The odd canonical form is therefore only useful for *equivalence*
reasoning, not as a re-encoding. -/

/-- 2-adic "odd part" of `(m, q)`: repeatedly halve `m` while it is even.
For `m = 0`, returns `(0, q)`. -/
def oddPart : Nat → Int → Nat × Int
  | 0, q => (0, q)
  | m+1, q =>
    if (m + 1) % 2 = 0 then
      have : (m + 1) / 2 < m + 1 :=
        Nat.div_lt_self (Nat.succ_pos _) (by decide)
      oddPart ((m + 1) / 2) (q + 1)
    else
      (m + 1, q)

/-- `r`'s `(m, q)` pair in odd-canonical form. -/
def oddCanonical (r : FloatRep) : Nat × Int := oddPart r.m r.q

/-- `IsOddOrZero`: the odd-canonical form invariant on a triple. -/
def IsOddOrZero (r : FloatRep) : Prop :=
  r.m = 0 ∨ r.m % 2 = 1

instance (r : FloatRep) : Decidable (IsOddOrZero r) := by
  unfold IsOddOrZero; infer_instance

/-! ## How downstream code uses this

  - The runtime bridge is the single restricted axiom
    `Float.toBits_ofBits` in `Srtfp/Float/RuntimeAxiom.lean`, stated on
    bit patterns rather than on `FloatRep` (the IEEE-754 behaviour of
    `Float.toBits`/`Float.ofBits` is not derivable in pure Lean 4).
  - The correctness stack (`Srtfp/Correctness.lean`,
    `Srtfp/Proofs/RoundTrip.lean`, `Srtfp/Proofs/Schubfach/`,
    `Srtfp/Proofs/Clinger/`) likewise works at the `decode`/bits level.
  - The alternative canonical forms defined here (`IsCanonicalRep`,
    `IsOddOrZero`) ended up unused by those proofs; they remain because
    nothing in this file commits to one canonical form — callers pick
    whichever suits their proof. -/

end FloatRep

end Srtfp.Float

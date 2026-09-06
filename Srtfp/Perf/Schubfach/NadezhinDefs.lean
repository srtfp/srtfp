module
/- Result 20 (Giulietti, after Nadezhin): the sweep.

   For every binary64 `v = c·2^q` with `k = kOfMQ c q`, the numbers
   `2V`, `2V_l`, `2V_r` (Definition 7, scaled by 2) are of the form
   `m'·2^{q'}·10^{-k}` with `m' < 2^54` and `q' ∈ {q, q−1}`. Result 20
   says each is an integer or at distance at least `ε = 2^{-64}` from
   the integers on both sides.

   Written as a fraction `N / M` with `M = 5^k` (band 2, `q' ≥ 0`) or
   `M = 2^{-q'+k}` (band 1, `q' < 0`) and `N = m'·u`, the two distances are
   the gaps of `m'·u mod M` down to `0` and up to `M`. For `M ≤ 2^64` any
   nonzero gap is at least `M / 2^64`. Otherwise `farAll_of_sweep`
   (`Keystone.lean`) decides the up-gap for every `m' < 2^54` from the
   convergent denominators of `u/M`, and the down-gap is the up-gap of
   `M − u`. This module defines the per-band checks and proves them
   sound; the checks themselves run in the kernel in the `NadezhinSweep`
   modules. -/

public import Srtfp.Perf.Schubfach.Keystone
public import Srtfp.Perf.Schubfach.RoundOdd
public import Srtfp.Perf.Schubfach.Table

@[expose] public section

open Srtfp.Compat

namespace Srtfp.Schubfach.R20

/-! ## Separation from the two gaps -/

/-- The two-sided gap condition on `N mod M` at `ε = 2^{-a}`. -/
def Gaps (N M a : Nat) : Prop :=
  N % M = 0 ∨ (M ≤ (N % M) * 2 ^ a ∧ M ≤ (M - N % M) * 2 ^ a)

/-- Any nonzero gap is at least `M / 2^a` once `M ≤ 2^a`. -/
theorem gaps_of_small (N M a : Nat) (hM : 0 < M) (hMa : M ≤ 2 ^ a) : Gaps N M a := by
  unfold Gaps
  by_cases h0 : N % M = 0
  · exact Or.inl h0
  · have := Nat.mod_lt N hM
    exact Or.inr ⟨Nat.le_trans hMa (by simpa using Nat.mul_le_mul_right (2 ^ a) (Nat.pos_of_ne_zero h0)),
      Nat.le_trans hMa (by simpa using Nat.mul_le_mul_right (2 ^ a) (show 1 ≤ M - N % M by omega))⟩

/-- `Separated (2^{-a}) (N / M)` from the gaps. -/
theorem separated_of_gaps (N M a : Nat) (hM : 0 < M) (h : Gaps N M a) :
    Separated ((2 : Rat) ^ (-(a : Int))) ((N : Rat) / (M : Rat)) := by
  have hMq : (0 : Rat) < M := by exact_mod_cast hM
  have h2a : (0 : Rat) < 2 ^ a := Rat.pow_pos (by decide)
  have hfrac := frac_natDiv N M hM
  unfold Separated
  rw [floor_natDiv N M hM, Rat.intCast_natCast, zpow_neg_natCast]
  rcases h with h0 | ⟨hlo, hhi⟩
  · left; rw [h0] at hfrac; push_cast at hfrac; grind
  · right
    have hmod := Nat.mod_lt N hM
    have hlo' : (M : Rat) ≤ ((N % M : Nat) : Rat) * 2 ^ a := by exact_mod_cast hlo
    have hhi' : (M : Rat) ≤ ((M - N % M : Nat) : Rat) * 2 ^ a := by exact_mod_cast hhi
    have hsub : ((M - N % M : Nat) : Rat) = (M : Rat) - ((N % M : Nat) : Rat) := by
      have h' : (((M - N % M) + N % M : Nat) : Rat) = (M : Rat) := by
        rw [Nat.sub_add_cancel (Nat.le_of_lt hmod)]
      push_cast at h'; grind
    rw [hsub] at hhi'
    -- `ε ≤ r/M` and `r/M ≤ 1 − ε` by cross-multiplication
    have e1 := mul_inv_le_mul_inv (p := 1) (r := ((N % M : Nat) : Rat)) h2a hMq (by grind)
    have e2 := mul_inv_le_mul_inv (p := ((N % M : Nat) : Rat)) (r := 2 ^ a - 1) hMq h2a (by grind)
    have e3 := Rat.mul_inv_cancel _ (Rat.ne_of_gt h2a)
    rw [Rat.div_def] at hfrac
    grind

/-! ## Both gaps from two one-sided sweeps -/

/-- The residue of the complementary multiplier: `m(M − u mod M) ≡ −mu`. -/
theorem mod_complement (M u m : Nat) (hM : 0 < M) :
    (m * (M - u % M)) % M = (M - (m * u) % M) % M := by
  have hu := Nat.mod_lt u hM
  rw [show (m * u) % M = (m * (u % M)) % M by rw [Nat.mul_mod, Nat.mul_mod m (u % M), Nat.mod_mod]]
  generalize u % M = r at *
  -- `m(M − r) = Mm − (Ma + b)` with `Ma + b = mr`
  have hdm := Nat.div_add_mod (m * r) M
  have hb := Nat.mod_lt (m * r) hM
  have hP : m * (M - r) + m * r = M * m := by
    rw [← Nat.mul_add, Nat.sub_add_cancel (Nat.le_of_lt hu), Nat.mul_comm]
  have hmr : m * r ≤ M * m := by rw [Nat.mul_comm M]; exact Nat.mul_le_mul_left m (Nat.le_of_lt hu)
  generalize m * r / M = a at *
  generalize m * r % M = b at *
  have ha : a ≤ m := Nat.le_of_mul_le_mul_left (by omega : M * a ≤ M * m) hM
  by_cases hb0 : b = 0
  · subst hb0
    rw [show m * (M - r) = M * (m - a) by rw [Nat.mul_sub, Nat.mul_sub, Nat.mul_comm m M]; omega,
      Nat.mul_mod_right, Nat.sub_zero, Nat.mod_self]
  · have ha' : a < m := Nat.lt_of_mul_lt_mul_left (by omega : M * a < M * m)
    have hMa : M * a + M ≤ M * m := by have := Nat.mul_le_mul_left M ha'; rwa [Nat.mul_succ] at this
    rw [show m * (M - r) = M * (m - a - 1) + (M - b) by
        rw [Nat.mul_sub, Nat.mul_sub, Nat.mul_sub, Nat.mul_one, Nat.mul_comm m M]; omega,
      Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]

theorem gaps_of_far (M u m a : Nat) (hM : 0 < M)
    (hup : farFromMultipleBelow M u m a) (hdown : farFromMultipleBelow M (M - u % M) m a) :
    Gaps (m * u) M a := by
  unfold farFromMultipleBelow at hup hdown
  unfold Gaps
  rw [mod_complement M u m hM] at hdown
  by_cases h0 : (m * u) % M = 0
  · exact Or.inl h0
  · right
    have hlt : (m * u) % M < M := Nat.mod_lt _ hM
    rw [Nat.mod_eq_of_lt (by omega : M - (m * u) % M < M)] at hdown
    refine ⟨?_, hup⟩
    have : M - (M - (m * u) % M) = (m * u) % M := by omega
    rw [this] at hdown
    exact hdown

/-! ## The checks -/

/-- One-sided check: every convergent denominator of `u/M` below the bound
    is far. -/
def sideCheck (M u bound : Nat) : Bool :=
  (convDenoms u M bound).all (fun Q => farB M u Q 64)

/-- Both sides, for the multipliers below `2^54`. -/
def bothCheck (M u : Nat) : Bool :=
  sideCheck M u (2 ^ 54) && sideCheck M (M - u % M) (2 ^ 54)

theorem sideCheck_sound (M u : Nat) (hM : 0 < M) (hco : Nat.Coprime u M) (hbM : 2 ^ 54 ≤ M)
    (h : sideCheck M u (2 ^ 54) = true) :
    ∀ m, 0 < m → m < 2 ^ 54 → farFromMultipleBelow M u m 64 :=
  farAll_of_sweep M u 64 (2 ^ 54) hM hco hbM (Nat.le_refl _) (by decide) h

/-- `M − u mod M` is coprime with `M` when `u` is. -/
theorem coprime_complement (M u : Nat) (hM : 0 < M) (hco : Nat.Coprime u M) :
    Nat.Coprime (M - u % M) M := by
  have hlt : u % M < M := Nat.mod_lt u hM
  have h1 : Nat.gcd (u % M) M = 1 := by rw [← Nat.gcd_rec, Nat.gcd_comm]; exact hco
  show Nat.gcd (M - u % M) M = 1
  have : Nat.gcd (M - u % M) M = Nat.gcd (M - u % M) (u % M + (M - u % M)) := by
    congr 1; omega
  rw [this, Nat.gcd_add_self_right, Nat.gcd_sub_self_left (Nat.le_of_lt hlt), Nat.gcd_comm]
  exact h1

theorem bothCheck_sound (M u : Nat) (hM : 0 < M) (hco : Nat.Coprime u M)
    (hbM : 2 ^ 54 ≤ M) (h : bothCheck M u = true) :
    ∀ m, 0 < m → m < 2 ^ 54 → Gaps (m * u) M 64 := by
  unfold bothCheck at h
  rw [Bool.and_eq_true] at h
  intro m hm hm54
  exact gaps_of_far M u m 64 hM (sideCheck_sound M u hM hco hbM h.1 m hm hm54)
    (sideCheck_sound M _ hM (coprime_complement M u hM hco) hbM h.2 m hm hm54)

/-! ## The two bands -/

/-- Band 2 (`q' ≥ 0`, `0 ≤ k ≤ q'`): `x = m'·2^{q'−k} / 5^k`. Elementary for
    `k ≤ 27` (`5^27 < 2^64`). -/
def check2 (q' k : Nat) : Bool :=
  if k ≤ 27 ∨ q' < k then true else bothCheck (5 ^ k) (2 ^ (q' - k))

/-- Band 1 (`q' < 0`, `k < 0`, `−k ≤ −q'`): `x = m'·5^{−k} / 2^{−q'+k}`, with
    `e = −q' + k`. Elementary for `e ≤ 64`. -/
def check1 (qNeg' kNeg : Nat) : Bool :=
  if qNeg' - kNeg ≤ 64 ∨ qNeg' < kNeg then true else bothCheck (2 ^ (qNeg' - kNeg)) (5 ^ kNeg)

theorem two_pow_54_le_five_pow (k : Nat) (hk : 28 ≤ k) : 2 ^ 54 ≤ 5 ^ k :=
  calc 2 ^ 54 ≤ 5 ^ 28 := by decide
    _ ≤ 5 ^ k := Nat.pow_le_pow_right (by decide) hk

theorem check2_sound (q' k : Nat) (hkq : k ≤ q') (h : check2 q' k = true) :
    ∀ m, 0 < m → m < 2 ^ 54 → Gaps (m * 2 ^ (q' - k)) (5 ^ k) 64 := by
  intro m hm hm54
  unfold check2 at h
  by_cases hk : k ≤ 27
  · exact gaps_of_small _ _ _ (Nat.pow_pos (by decide))
      (calc 5 ^ k ≤ 5 ^ 27 := Nat.pow_le_pow_right (by decide) hk
        _ ≤ 2 ^ 64 := by decide)
  · rw [if_neg (by omega)] at h
    have hM : 0 < 5 ^ k := Nat.pow_pos (by decide)
    have hco : Nat.Coprime (2 ^ (q' - k)) (5 ^ k) :=
      Nat.Coprime.pow _ _ (by decide : Nat.Coprime 2 5)
    exact bothCheck_sound _ _ hM hco (two_pow_54_le_five_pow k (by omega)) h m hm hm54

theorem check1_sound (qNeg' kNeg : Nat) (hkq : kNeg ≤ qNeg') (h : check1 qNeg' kNeg = true) :
    ∀ m, 0 < m → m < 2 ^ 54 → Gaps (m * 5 ^ kNeg) (2 ^ (qNeg' - kNeg)) 64 := by
  intro m hm hm54
  unfold check1 at h
  by_cases he : qNeg' - kNeg ≤ 64
  · exact gaps_of_small _ _ _ (Nat.pow_pos (by decide)) (Nat.pow_le_pow_right (by decide) he)
  · rw [if_neg (by omega)] at h
    have hM : 0 < 2 ^ (qNeg' - kNeg) := Nat.pow_pos (by decide)
    have hco : Nat.Coprime (5 ^ kNeg) (2 ^ (qNeg' - kNeg)) :=
      Nat.Coprime.pow _ _ (by decide : Nat.Coprime 5 2)
    exact bothCheck_sound _ _ hM hco (Nat.pow_le_pow_right (by decide) (by omega)) h m hm hm54

/-! ## Per exponent: both `k` candidates, both `q' ∈ {q, q−1}` -/

/-- The check for one `(q', k)`, dispatched by the band. -/
def checkAt (q' k : Int) : Bool :=
  if 0 ≤ q' ∧ 0 ≤ k then check2 q'.toNat k.toNat
  else if q' < 0 ∧ k < 0 then check1 (-q').toNat (-k).toNat
  else true

/-- The checks for the exponent `q`. -/
def checkQ (q : Int) : Bool :=
  checkAt q (floorLog10Pow2 q) && checkAt (q - 1) (floorLog10Pow2 q)
    && checkAt q (floorLog10ThreeQuartersPow2 q) && checkAt (q - 1) (floorLog10ThreeQuartersPow2 q)

/-- `checkQ` for the biased exponents `lo, …, lo + len − 1` (`q = i − 1074`),
    as a recursion the kernel unfolds one exponent at a time. -/
def rangeCheck : Nat → Nat → Bool
  | _, 0 => true
  | lo, len + 1 => checkQ ((lo : Int) - 1074) && rangeCheck (lo + 1) len

theorem rangeCheck_sound (lo len : Nat) (h : rangeCheck lo len = true) :
    ∀ i, lo ≤ i → i < lo + len → checkQ ((i : Int) - 1074) = true := by
  induction len generalizing lo with
  | zero => intro i h1 h2; omega
  | succ n ih =>
    intro i h1 h2
    unfold rangeCheck at h
    rw [Bool.and_eq_true] at h
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · exact h.1
    · exact ih (lo + 1) h.2 i (by omega) (by omega)

theorem rangeCheck_append (lo a b : Nat) (h1 : rangeCheck lo a = true)
    (h2 : rangeCheck (lo + a) b = true) : rangeCheck lo (a + b) = true := by
  induction a generalizing lo with
  | zero => simpa using h2
  | succ n ih =>
    unfold rangeCheck at h1
    rw [Bool.and_eq_true] at h1
    rw [show n + 1 + b = (n + b) + 1 by omega]
    unfold rangeCheck
    rw [Bool.and_eq_true]
    exact ⟨h1.1, ih (lo + 1) h1.2 (by rwa [show lo + 1 + n = lo + (n + 1) by omega])⟩

end Srtfp.Schubfach.R20

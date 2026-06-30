import Mathlib.Algebra.ContinuedFractions.Determinant
import Mathlib.Data.Rat.Floor
import Mathlib.RingTheory.Int.Basic
import Srtfp.Numeric.Schubfach.R20Sweep

/-!
# R20 keystone: rational convergent denominators are a fast `Nat` enumeration

This file is the *keystone* the sweep reduction (`R20Sweep.lean`) stops short
of.  `far_of_far_at_rat_convergents` reduces the R20 `farFromMultipleBelow`
obligation to a check at every `d < bound` whose ceiling rational
`approx M u d` is a rational convergent of `u/M`.  Mathlib's rational
convergents (`(GenContFract.of (u/M : ℚ)).convs n`) are computable but far too
slow to evaluate by `decide`/`native_decide` (they recompute a `Rat`-valued
`IntFractPair` stream, inverting `5^292`-sized fractions repeatedly).

The keystone bridges the (noncomputable-in-practice) rational convergents to a
*fast `Nat` Euclidean continuant recurrence*:

* `rem` — the Euclidean remainder sequence of `(u, M)`;
* `denI` / `numI` — the integer continuant numerators/denominators built from
  the Euclidean partial quotients `qt n = rem n / rem (n+1)`;
* `dens_eq_denI` / `nums_eq_numI` — `(of (u/M:ℚ)).dens/.nums n` equal these
  integer continuants (cast), while the remainders stay positive;
* `coprime_numI_denI` — `numI n, denI n` are coprime (the integer determinant);
* `convs_den_eq` — hence the *reduced* denominator `((of (u/M:ℚ)).convs n).den`
  equals `(denI u M n).natAbs`, a fast `Nat`;
* `pos_of_small_den` / `index_bound` — a convergent with reduced denominator
  `< M` is in the positive (pre-termination) regime, and `< 2^53` forces
  `n < 78` (since `Nat.fib 79 > 2^53` and `fib (n+1) ≤ dens n`).

Assembled in `hcheck_of_check`: in the sweep regime (`bound ≤ M`,
`gcd(u,M)=1`), the `hcheck` hypothesis of `far_of_far_at_rat_convergents`
reduces to a finite check over the computable list `convDenoms u M bound`
(`≤ 78` entries, each a fast `Nat` continuant).

All results are sorry-free (axioms: `propext`, `Quot.sound`,
`Classical.choice`).
-/

namespace PP.Numeric.Schubfach.R20Sweep

open GenContFract
open PP.Numeric.Schubfach (farFromMultipleBelow)
open PP.Numeric.Schubfach.R20Legendre (approx ceilNum)

/-! ## Euclidean remainders and the `fr`-invariant of the rational CF stream -/

/-- Euclidean remainder sequence of `(u, M)`: `rem 0 = M`, `rem 1 = u % M`,
`rem (n+2) = rem n % rem (n+1)`. -/
def rem (u M : Nat) : Nat → Nat
  | 0 => M
  | 1 => u % M
  | (n+2) => rem u M n % rem u M (n+1)

theorem rem_add_two (u M n : Nat) : rem u M (n+2) = rem u M n % rem u M (n+1) := rfl

/-- The fractional part of the `n`th term of the `IntFractPair` stream of
`u/M` is the Euclidean remainder ratio `rem (n+1) / rem n`, as long as the
remainders stay positive up to `n`. -/
theorem stream_fr_eq (u M : Nat) (_hM : 0 < M) :
    ∀ n, (∀ i, i ≤ n → 0 < rem u M i) →
      ∃ ifp, IntFractPair.stream ((u:ℚ)/M) n = some ifp ∧
        ifp.fr = ((rem u M (n+1) : Nat):ℚ) / ((rem u M n : Nat):ℚ) := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨IntFractPair.of ((u:ℚ)/M), IntFractPair.stream_zero _, ?_⟩
    show Int.fract ((u:ℚ)/M) = _
    rw [Int.fract_div_natCast_eq_div_natCast_mod]; rfl
  | succ n IH =>
    intro hpos
    obtain ⟨ifp, hstream, hfr⟩ := IH (fun i hi => hpos i (Nat.le_succ_of_le hi))
    have hrn1 : 0 < rem u M (n+1) := hpos (n+1) le_rfl
    have hrn : 0 < rem u M n := hpos n (Nat.le_succ n)
    have hrn1Q : ((rem u M (n+1) : Nat):ℚ) ≠ 0 := by exact_mod_cast hrn1.ne'
    have hrnQ : ((rem u M n : Nat):ℚ) ≠ 0 := by exact_mod_cast hrn.ne'
    have hfrne : ifp.fr ≠ 0 := by rw [hfr]; exact div_ne_zero hrn1Q hrnQ
    have hadv : IntFractPair.stream ((u:ℚ)/M) (n+1) = some (IntFractPair.of ifp.fr⁻¹) :=
      IntFractPair.stream_succ_of_some hstream hfrne
    refine ⟨IntFractPair.of ifp.fr⁻¹, hadv, ?_⟩
    show Int.fract ifp.fr⁻¹ = _
    rw [hfr, inv_div, Int.fract_div_natCast_eq_div_natCast_mod, rem_add_two]

/-- The `n`th partial denominator of `of (u/M)` is the Euclidean quotient
`rem n / rem (n+1)` (the partial numerator is always `1`). -/
theorem partDen_eq (u M : Nat) (hM : 0 < M) (n : Nat)
    (hpos : ∀ i, i ≤ n+1 → 0 < rem u M i) :
    (GenContFract.of ((u:ℚ)/M)).s.get? n
      = some ⟨1, ((rem u M n / rem u M (n+1) : Nat) : ℤ)⟩ := by
  obtain ⟨ifp1, hstream1, _⟩ := stream_fr_eq u M hM (n+1) hpos
  have hb : ifp1.b = ((rem u M n / rem u M (n+1) : Nat) : ℤ) := by
    obtain ⟨ifp0, hstream0, hfr0⟩ := stream_fr_eq u M hM n (fun i hi => hpos i (Nat.le_succ_of_le hi))
    have hrn : 0 < rem u M n := hpos n (Nat.le_succ _)
    have hrn1 : 0 < rem u M (n+1) := hpos (n+1) le_rfl
    have hfrne : ifp0.fr ≠ 0 := by
      rw [hfr0]; exact div_ne_zero (by exact_mod_cast hrn1.ne') (by exact_mod_cast hrn.ne')
    have hsucc : IntFractPair.stream ((u:ℚ)/M) (n+1) = some (IntFractPair.of ifp0.fr⁻¹) :=
      IntFractPair.stream_succ_of_some hstream0 hfrne
    rw [hsucc] at hstream1
    have hifp1 : ifp1 = IntFractPair.of ifp0.fr⁻¹ := by injection hstream1 with h; exact h.symm
    rw [hifp1]
    show ⌊ifp0.fr⁻¹⌋ = _
    rw [hfr0, inv_div, Int.floor_div_natCast]
    norm_cast
  rw [get?_of_eq_some_of_succ_get?_intFractPair_stream hstream1, hb]

/-! ## Integer continuants over the Euclidean partial quotients -/

/-- Euclidean partial quotient at continuant index `n`. -/
def qt (u M n : Nat) : Nat := rem u M n / rem u M (n+1)

/-- Integer continuant denominators, mirroring `GenContFract.dens` with the
partial numerator `= 1` of a `SimpContFract`. -/
def denI (u M : Nat) : Nat → ℤ
  | 0 => 1
  | 1 => (qt u M 0 : ℤ)
  | (n+2) => (qt u M (n+1) : ℤ) * denI u M (n+1) + denI u M n

/-- Integer continuant numerators. -/
def numI (u M : Nat) : Nat → ℤ
  | 0 => (u / M : Nat)
  | 1 => (qt u M 0 : ℤ) * (u / M : Nat) + 1
  | (n+2) => (qt u M (n+1) : ℤ) * numI u M (n+1) + numI u M n

/-- `dens n` of the rational CF equals the integer continuant `denI n`. -/
theorem dens_eq_denI (u M : Nat) (hM : 0 < M) :
    ∀ n, (∀ i, i ≤ n → 0 < rem u M i) →
      (GenContFract.of ((u:ℚ)/M)).dens n = ((denI u M n : ℤ):ℚ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro hpos
    match n with
    | 0 => simp [denI, zeroth_den_eq_one]
    | 1 =>
      rw [first_den_eq (partDen_eq u M hM 0 (fun i hi => hpos i hi))]
      simp [denI, qt]
    | (k+2) =>
      have hs : (GenContFract.of ((u:ℚ)/M)).s.get? (k+1)
          = some ⟨1, ((qt u M (k+1)) : ℤ)⟩ :=
        partDen_eq u M hM (k+1) (fun i hi => hpos i hi)
      have hrec := dens_recurrence (g := GenContFract.of ((u:ℚ)/M)) (n := k) hs
          (ppredB := (GenContFract.of ((u:ℚ)/M)).dens k)
          (predB := (GenContFract.of ((u:ℚ)/M)).dens (k+1)) rfl rfl
      rw [hrec, IH k (by omega) (fun i hi => hpos i (by omega)),
          IH (k+1) (by omega) (fun i hi => hpos i (by omega)),
          show denI u M (k+2) = (qt u M (k+1):ℤ) * denI u M (k+1) + denI u M k from rfl]
      push_cast; ring

theorem h_eq (u M : Nat) :
    (GenContFract.of ((u:ℚ)/M)).h = ((u / M : Nat) : ℚ) := by
  rw [of_h_eq_floor]
  show (⌊(u:ℚ)/M⌋ : ℚ) = _
  rw [Int.floor_div_natCast]; norm_cast

/-- `nums n` of the rational CF equals the integer continuant `numI n`. -/
theorem nums_eq_numI (u M : Nat) (hM : 0 < M) :
    ∀ n, (∀ i, i ≤ n → 0 < rem u M i) →
      (GenContFract.of ((u:ℚ)/M)).nums n = ((numI u M n : ℤ):ℚ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro hpos
    match n with
    | 0 => rw [zeroth_num_eq_h, h_eq u M]; simp only [numI]; norm_cast
    | 1 =>
      rw [first_num_eq (partDen_eq u M hM 0 (fun i hi => hpos i hi)), h_eq u M]
      show ((qt u M 0 : ℤ):ℚ) * ((u/M:Nat):ℚ) + 1 = ((numI u M 1 : ℤ):ℚ)
      rw [show numI u M 1 = (qt u M 0:ℤ) * (u/M:Nat) + 1 from rfl]
      push_cast [-Nat.cast_ofNat]; norm_cast
    | (k+2) =>
      have hs : (GenContFract.of ((u:ℚ)/M)).s.get? (k+1)
          = some ⟨1, ((qt u M (k+1)) : ℤ)⟩ :=
        partDen_eq u M hM (k+1) (fun i hi => hpos i hi)
      have hrec := nums_recurrence (g := GenContFract.of ((u:ℚ)/M)) (n := k) hs
          (ppredA := (GenContFract.of ((u:ℚ)/M)).nums k)
          (predA := (GenContFract.of ((u:ℚ)/M)).nums (k+1)) rfl rfl
      rw [hrec, IH k (by omega) (fun i hi => hpos i (by omega)),
          IH (k+1) (by omega) (fun i hi => hpos i (by omega)),
          show numI u M (k+2) = (qt u M (k+1):ℤ) * numI u M (k+1) + numI u M k from rfl]
      push_cast; ring

/-! ## Positivity, coprimality, and the reduced denominator -/

/-- The Euclidean remainder strictly decreases while positive. -/
theorem rem_succ_lt_rem (u M : Nat) (hM : 0 < M) (n : Nat) (h : 0 < rem u M n) :
    rem u M (n+1) < rem u M n := by
  match n with
  | 0 => exact Nat.mod_lt _ hM
  | (k+1) =>
    show rem u M k % rem u M (k+1) < rem u M (k+1)
    exact Nat.mod_lt _ h

theorem qt_pos (u M : Nat) (hM : 0 < M) (n : Nat)
    (h0 : 0 < rem u M n) (h1 : 0 < rem u M (n+1)) : 0 < qt u M n := by
  unfold qt
  exact Nat.div_pos (le_of_lt (rem_succ_lt_rem u M hM n h0)) h1

theorem denI_pos (u M : Nat) (hM : 0 < M) :
    ∀ n, (∀ i, i ≤ n → 0 < rem u M i) → 0 < denI u M n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro hpos
    match n with
    | 0 => simp [denI]
    | 1 =>
      simp only [denI]
      have : 0 < qt u M 0 := qt_pos u M hM 0 (hpos 0 (by omega)) (hpos 1 (by omega))
      positivity
    | (k+2) =>
      have hk := IH k (by omega) (fun i hi => hpos i (by omega))
      have hk1 := IH (k+1) (by omega) (fun i hi => hpos i (by omega))
      have hq : 0 ≤ (qt u M (k+1):ℤ) := by positivity
      rw [show denI u M (k+2) = (qt u M (k+1):ℤ)*denI u M (k+1) + denI u M k from rfl]
      nlinarith [hk, hk1, hq]

theorem not_term (u M : Nat) (hM : 0 < M) (n : Nat)
    (hpos : ∀ i, i ≤ n+1 → 0 < rem u M i) :
    ¬ (GenContFract.of ((u:ℚ)/M)).TerminatedAt n := by
  show (GenContFract.of ((u:ℚ)/M)).s.get? n ≠ none
  rw [partDen_eq u M hM n hpos]
  exact Option.some_ne_none _

/-- The integer continuants `numI n, denI n` are coprime — from the integer
determinant identity `numI n · denI (n+1) − denI n · numI (n+1) = ±1`. -/
theorem coprime_numI_denI (u M : Nat) (hM : 0 < M) (n : Nat)
    (hpos : ∀ i, i ≤ n+1 → 0 < rem u M i) :
    Nat.Coprime (numI u M n).natAbs (denI u M n).natAbs := by
  have hnt := not_term u M hM n hpos
  have hdet := (SimpContFract.of ((u:ℚ)/M)).determinant (n := n) hnt
  rw [show ((SimpContFract.of ((u:ℚ)/M)) : GenContFract ℚ) = GenContFract.of ((u:ℚ)/M) from rfl] at hdet
  have hposL : ∀ i, i ≤ n → 0 < rem u M i := fun i hi => hpos i (Nat.le_succ_of_le hi)
  rw [nums_eq_numI u M hM n hposL, dens_eq_denI u M hM (n+1) hpos,
      dens_eq_denI u M hM n hposL, nums_eq_numI u M hM (n+1) hpos] at hdet
  have hZ : numI u M n * denI u M (n+1) - denI u M n * numI u M (n+1) = (-1)^(n+1) := by
    have : ((numI u M n * denI u M (n+1) - denI u M n * numI u M (n+1) : ℤ):ℚ)
        = (((-1)^(n+1) : ℤ):ℚ) := by push_cast; linarith [hdet]
    exact_mod_cast this
  rw [Nat.coprime_iff_gcd_eq_one, ← Int.gcd_eq_natAbs]
  rw [← Int.isCoprime_iff_gcd_eq_one]
  refine ⟨(-1:ℤ)^(n+1) * denI u M (n+1), -((-1:ℤ)^(n+1) * numI u M (n+1)), ?_⟩
  have hsq : (-1:ℤ)^(n+1) * (-1:ℤ)^(n+1) = 1 := by rw [← pow_add, ← two_mul, pow_mul]; simp
  have hexp : ((-1:ℤ)^(n+1) * denI u M (n+1)) * numI u M n + -((-1:ℤ)^(n+1) * numI u M (n+1)) * denI u M n
      = (-1:ℤ)^(n+1) * (numI u M n * denI u M (n+1) - denI u M n * numI u M (n+1)) := by ring
  rw [hexp, hZ, hsq]

/-- **Keystone.**  The reduced denominator of the `n`th rational convergent of
`u/M` equals the fast integer continuant `(denI u M n).natAbs`, while the
remainders stay positive. -/
theorem convs_den_eq (u M : Nat) (hM : 0 < M) (n : Nat)
    (hpos : ∀ i, i ≤ n+1 → 0 < rem u M i) :
    ((GenContFract.of ((u:ℚ)/M)).convs n).den = (denI u M n).natAbs := by
  have hposL : ∀ i, i ≤ n → 0 < rem u M i := fun i hi => hpos i (Nat.le_succ_of_le hi)
  have hdenpos : 0 < denI u M n := denI_pos u M hM n hposL
  have hco := coprime_numI_denI u M hM n hpos
  have hconv : (GenContFract.of ((u:ℚ)/M)).convs n
      = ((numI u M n : ℤ):ℚ) / ((denI u M n : ℤ):ℚ) := by
    rw [conv_eq_num_div_den, nums_eq_numI u M hM n hposL, dens_eq_denI u M hM n hposL]
  rw [hconv]
  have hb : (0:ℤ) < denI u M n := hdenpos
  have heq : (((((numI u M n : ℤ):ℚ) / ((denI u M n : ℤ):ℚ)).den : ℤ)) = denI u M n :=
    Rat.den_div_eq_of_coprime hb hco
  omega

/-! ## Termination control: small reduced denominator ⟹ positive regime -/

/-- The full value `u/M` has reduced denominator `M` when `gcd(u,M)=1`. -/
theorem val_den (u M : Nat) (hM : 0 < M) (hco : Nat.Coprime u M) :
    ((u:ℚ)/M).den = M := by
  rw [show ((u:ℚ)/M) = ((u:ℤ):ℚ)/((M:ℤ):ℚ) by push_cast; ring]
  have := Rat.den_div_eq_of_coprime (a := (u:ℤ)) (b := (M:ℤ)) (by exact_mod_cast hM)
    (by simpa using hco)
  exact_mod_cast this

/-- A zero Euclidean remainder terminates the rational CF. -/
theorem terminated_of_rem_zero (u M : Nat) (hM : 0 < M) (n : Nat)
    (hpos : ∀ i, i ≤ n → 0 < rem u M i) (hz : rem u M (n+1) = 0) :
    (GenContFract.of ((u:ℚ)/M)).TerminatedAt n := by
  obtain ⟨ifp, hstream, hfr⟩ := stream_fr_eq u M hM n hpos
  have hfr0 : ifp.fr = 0 := by rw [hfr, hz]; simp
  rw [of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none]
  exact IntFractPair.stream_eq_none_of_fr_eq_zero hstream hfr0

/-- If the reduced denominator of `convs n` is `< M` (and `gcd(u,M)=1`), the CF
has not yet terminated by index `n`, i.e. all remainders up to `n+1` are
positive. -/
theorem pos_of_small_den (u M : Nat) (hM : 0 < M) (hco : Nat.Coprime u M) (n : Nat)
    (hsmall : ((GenContFract.of ((u:ℚ)/M)).convs n).den < M) :
    ∀ i, i ≤ n+1 → 0 < rem u M i := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨i, hile, hi0⟩ := hcon
  have hi0' : rem u M i = 0 := by omega
  have hex : ∃ j, rem u M j = 0 := ⟨i, hi0'⟩
  set j := Nat.find hex with hjdef
  have hjz : rem u M j = 0 := Nat.find_spec hex
  have hjle : j ≤ i := Nat.find_le hi0'
  have hjpos : 0 < j := by
    rcases Nat.eq_zero_or_pos j with h | h
    · rw [h] at hjz; simp [rem] at hjz; omega
    · exact h
  have hkpos : ∀ k, k < j → 0 < rem u M k := fun k hk => Nat.pos_of_ne_zero (Nat.find_min hex hk)
  obtain ⟨jp, hjp⟩ : ∃ jp, j = jp + 1 := ⟨j-1, by omega⟩
  have hterm : (GenContFract.of ((u:ℚ)/M)).TerminatedAt jp :=
    terminated_of_rem_zero u M hM jp (fun k hk => hkpos k (by omega)) (by rw [← hjp]; exact hjz)
  have hjpn : jp ≤ n := by omega
  have hstab : (GenContFract.of ((u:ℚ)/M)).convs n = (GenContFract.of ((u:ℚ)/M)).convs jp :=
    convs_stable_of_terminated hjpn hterm
  have hval : (GenContFract.of ((u:ℚ)/M)).convs jp = (u:ℚ)/M :=
    (of_correctness_of_terminatedAt hterm).symm
  rw [hstab, hval, val_den u M hM hco] at hsmall
  omega

/-- **Index bound.**  In the positive regime, a convergent with reduced
denominator `< 2^53` has index `n < 78`, since `Nat.fib (n+1) ≤ dens n` and
`Nat.fib 79 > 2^53`. -/
theorem index_bound (u M : Nat) (hM : 0 < M) (n : Nat)
    (hpos : ∀ i, i ≤ n+1 → 0 < rem u M i)
    (hden : ((GenContFract.of ((u:ℚ)/M)).convs n).den < 2^53) :
    n < 78 := by
  have hposL : ∀ i, i ≤ n → 0 < rem u M i := fun i hi => hpos i (Nat.le_succ_of_le hi)
  by_contra hge
  push_neg at hge
  have hfib : (Nat.fib (n+1) : ℚ) ≤ (GenContFract.of ((u:ℚ)/M)).dens n := by
    apply succ_nth_fib_le_of_nth_den
    exact Or.inr (not_term u M hM (n-1) (fun i hi => hpos i (by omega)))
  rw [dens_eq_denI u M hM n hposL] at hfib
  rw [convs_den_eq u M hM n hpos] at hden
  have hdpos : 0 < denI u M n := denI_pos u M hM n hposL
  have hnatabs : ((denI u M n).natAbs : ℤ) = denI u M n := Int.natAbs_of_nonneg (le_of_lt hdpos)
  have hfibN : Nat.fib (n+1) ≤ (denI u M n).natAbs := by
    have : ((Nat.fib (n+1) : ℤ)) ≤ ((denI u M n).natAbs : ℤ) := by
      rw [hnatabs]; exact_mod_cast hfib
    exact_mod_cast this
  have hmono : Nat.fib 79 ≤ Nat.fib (n+1) := Nat.fib_mono (by omega)
  have hfib79 : (2:Nat)^53 < Nat.fib 79 := by decide
  omega

/-! ## Computable candidate-denominator list and the `hcheck` discharge

The proof-side continuant `denI` is doubly-recursive (Fibonacci-many calls)
and so impractical to *evaluate*.  For the decidable sweep we use a single-pass
tail-recursive Euclidean continuant `fastDenoms` (linear, computes the
remainder and continuant chains together) that stops at the first zero
remainder, and prove it captures `(denI u M n).natAbs` for every pre-termination
index `n < 78` (`denN_mem_convDenoms`). -/

/-- `Nat`-valued continuant denominator `(denI u M n).natAbs`. -/
def denN (u M n : Nat) : Nat := (denI u M n).natAbs

theorem denN_zero (u M : Nat) : denN u M 0 = 1 := rfl
theorem denN_one (u M : Nat) : denN u M 1 = qt u M 0 := by unfold denN denI; simp

/-- The `Nat` continuant recurrence (positive regime). -/
theorem denN_rec (u M : Nat) (hM : 0 < M) (n : Nat) (hpos : ∀ i, i ≤ n+2 → 0 < rem u M i) :
    denN u M (n+2) = qt u M (n+1) * denN u M (n+1) + denN u M n := by
  unfold denN
  have h2 : denI u M (n+2) = (qt u M (n+1):ℤ) * denI u M (n+1) + denI u M n := rfl
  have hp1 : 0 < denI u M (n+1) := denI_pos u M hM (n+1) (fun i hi => hpos i (by omega))
  have hp0 : 0 < denI u M n := denI_pos u M hM n (fun i hi => hpos i (by omega))
  rw [h2]
  have e2 : (qt u M (n+1):ℤ) * denI u M (n+1) + denI u M n
      = ((qt u M (n+1) * (denI u M (n+1)).natAbs + (denI u M n).natAbs : Nat) : ℤ) := by
    rw [Nat.cast_add, Nat.cast_mul, Int.natAbs_of_nonneg (le_of_lt hp1),
        Int.natAbs_of_nonneg (le_of_lt hp0)]
  rw [e2, Int.natAbs_natCast]

/-- Single-pass Euclidean continuant denominators.  `fuel` bounds the index;
the run stops at the first zero remainder.  State `(rPrev, rCur)` are
consecutive remainders, `(bPrev, bCur)` consecutive continuant denominators. -/
def fastDenoms (fuel : Nat) (rPrev rCur bPrev bCur : Nat) (acc : List Nat) : List Nat :=
  match fuel with
  | 0 => acc.reverse
  | fuel+1 =>
    if rCur = 0 then acc.reverse
    else
      let a := rPrev / rCur
      let bNext := a * bCur + bPrev
      fastDenoms fuel rCur (rPrev % rCur) bCur bNext (bNext :: acc)

theorem fastDenoms_acc_subset (fuel : Nat) :
    ∀ rPrev rCur bPrev bCur (acc : List Nat) x, x ∈ acc →
      x ∈ fastDenoms fuel rPrev rCur bPrev bCur acc := by
  induction fuel with
  | zero => intro rp rc bp bc acc x hx; simp [fastDenoms, List.mem_reverse, hx]
  | succ f IH =>
    intro rp rc bp bc acc x hx
    unfold fastDenoms
    by_cases hrc : rc = 0
    · simp [hrc, List.mem_reverse, hx]
    · simp only [hrc, if_false]
      exact IH _ _ _ _ _ x (List.mem_cons_of_mem _ hx)

theorem fastDenoms_fuel_mono :
    ∀ fuel rPrev rCur bPrev bCur (acc : List Nat) x,
      x ∈ fastDenoms fuel rPrev rCur bPrev bCur acc →
      x ∈ fastDenoms (fuel+1) rPrev rCur bPrev bCur acc := by
  intro fuel
  induction fuel with
  | zero =>
    intro rp rc bp bc acc x hx
    simp only [fastDenoms, List.mem_reverse] at hx
    unfold fastDenoms
    by_cases hrc : rc = 0
    · simp [hrc, List.mem_reverse, hx]
    · simp only [hrc, if_false]
      exact fastDenoms_acc_subset 0 _ _ _ _ _ _ (List.mem_cons_of_mem _ hx)
  | succ f IH =>
    intro rp rc bp bc acc x hx
    rw [show fastDenoms (f+1) rp rc bp bc acc =
        (if rc = 0 then acc.reverse else
          fastDenoms f rc (rp % rc) bc (rp/rc*bc+bp) ((rp/rc*bc+bp)::acc)) from rfl] at hx
    rw [show fastDenoms (f+1+1) rp rc bp bc acc =
        (if rc = 0 then acc.reverse else
          fastDenoms (f+1) rc (rp % rc) bc (rp/rc*bc+bp) ((rp/rc*bc+bp)::acc)) from rfl]
    by_cases hrc : rc = 0
    · simp [hrc] at hx ⊢; exact hx
    · simp only [hrc, if_false] at hx ⊢
      exact IH _ _ _ _ _ x hx

theorem fastDenoms_fuel_mono_le :
    ∀ f g rPrev rCur bPrev bCur (acc : List Nat) x, f ≤ g →
      x ∈ fastDenoms f rPrev rCur bPrev bCur acc →
      x ∈ fastDenoms g rPrev rCur bPrev bCur acc := by
  intro f g
  induction g with
  | zero => intro rp rc bp bc acc x hfg hx; interval_cases f; exact hx
  | succ g IH =>
    intro rp rc bp bc acc x hfg hx
    rcases Nat.lt_or_ge f (g+1) with h | h
    · exact fastDenoms_fuel_mono g rp rc bp bc acc x (IH _ _ _ _ _ x (by omega) hx)
    · have : f = g+1 := by omega
      subst this; exact hx

/-- Aligned emission: a `fastDenoms` run whose state matches the continuant data
at index `t` emits `denN (t+s)` for every reachable `s`, while remainders stay
positive. -/
theorem fastDenoms_emit (u M : Nat) (hM : 0 < M) :
    ∀ fuel t bp acc,
      (∀ i, i ≤ t + fuel + 1 → 0 < rem u M i) →
      qt u M t * denN u M t + bp = denN u M (t+1) →
      ∀ j, t < j → j ≤ t + fuel →
        denN u M j ∈ fastDenoms fuel (rem u M t) (rem u M (t+1)) bp (denN u M t) acc := by
  intro fuel
  induction fuel with
  | zero => intro t bp acc _ _ j hj1 hj2; omega
  | succ f IH =>
    intro t bp acc hpos hbp j hj1 hj2
    have hrc : 0 < rem u M (t+1) := hpos (t+1) (by omega)
    unfold fastDenoms
    simp only [hrc.ne', if_false]
    have hqt : rem u M t / rem u M (t+1) = qt u M t := rfl
    have hbnext : (rem u M t / rem u M (t+1)) * denN u M t + bp = denN u M (t+1) := by
      rw [hqt]; exact hbp
    rw [hbnext]
    have hrem_next : rem u M t % rem u M (t+1) = rem u M (t+1+1) := (rem_add_two u M t).symm
    rw [hrem_next]
    by_cases hjt1 : j = t+1
    · subst hjt1
      exact fastDenoms_acc_subset f _ _ _ _ _ _ (List.mem_cons_self)
    · have hbp' : qt u M (t+1) * denN u M (t+1) + denN u M t = denN u M (t+1+1) := by
        rw [denN_rec u M hM t (fun i hi => hpos i (by omega))]
      exact IH (t+1) (denN u M t) _ (fun i hi => hpos i (by omega)) hbp' j (by omega) (by omega)

/-- Computable list of candidate reduced convergent denominators `< bound`,
via the single-pass Euclidean continuant. -/
def convDenoms (u M bound : Nat) : List Nat :=
  (1 :: fastDenoms 78 M (u % M) 0 1 []).filter (· < bound)

/-- The continuant denominator `denN u M n` is in the computable list for every
positive-regime index `n < 78` with `denN u M n < bound`. -/
theorem denN_mem_convDenoms (u M bound : Nat) (hM : 0 < M) (n : Nat)
    (hpos : ∀ i, i ≤ n+1 → 0 < rem u M i) (hn : n < 78) (hlt : denN u M n < bound) :
    denN u M n ∈ convDenoms u M bound := by
  unfold convDenoms
  rw [List.mem_filter]
  refine ⟨?_, by simp [hlt]⟩
  rcases Nat.eq_zero_or_pos n with h0 | hpos_n
  · rw [h0, denN_zero]; exact List.mem_cons_self
  · apply List.mem_cons_of_mem
    have hstart : qt u M 0 * denN u M 0 + 0 = denN u M 1 := by
      rw [denN_zero, denN_one]; ring
    have hmem_n : denN u M n
        ∈ fastDenoms n (rem u M 0) (rem u M 1) 0 (denN u M 0) [] :=
      fastDenoms_emit u M hM n 0 0 [] (by simpa using hpos) hstart n hpos_n (by omega)
    have hrem0 : rem u M 0 = M := rfl
    have hrem1 : rem u M 1 = u % M := rfl
    rw [hrem0, hrem1, denN_zero] at hmem_n
    exact fastDenoms_fuel_mono_le n 78 M (u % M) 0 1 [] _ (by omega) hmem_n

/-- **`hcheck` discharge.**  In the sweep regime (`bound ≤ M`, `gcd(u,M)=1`,
`bound ≤ 2^53`), the convergent-check hypothesis of
`far_of_far_at_rat_convergents` reduces to a finite check over the computable
list `convDenoms u M bound`. -/
theorem hcheck_of_check (M u a bound : Nat) (hM : 0 < M) (hco : Nat.Coprime u M)
    (hbM : bound ≤ M) (hb53 : bound ≤ 2^53)
    (hCheck : ∀ Q ∈ convDenoms u M bound, farFromMultipleBelow M u Q a) :
    ∀ d, 0 < d → d < bound →
      (∃ n, (GenContFract.of ((u : ℚ) / M)).convs n = approx M u d) →
      farFromMultipleBelow M u d a := by
  intro d hd hdb ⟨n, hn⟩
  by_cases hndm : (d * u) % M = 0
  · unfold farFromMultipleBelow
    rw [hndm, Nat.sub_zero]
    have : M ≤ M * 2 ^ a := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos a)
    omega
  · set d0 := (approx M u d).den with hd0
    have hd0pos : 0 < d0 := (approx M u d).pos
    have hden_eq : d0 = ((GenContFract.of ((u:ℚ)/M)).convs n).den := by rw [hd0, hn]
    have hd0_dvd : d0 ∣ d := by
      have hden := Rat.den_dvd (ceilNum M u d : Int) (d : Int)
      have heq : ((ceilNum M u d : ℚ) / (d : ℚ)) = Rat.divInt (ceilNum M u d) (d : Int) := by
        rw [Rat.divInt_eq_div]; push_cast; ring
      have hZ : (d0 : Int) ∣ (d : Int) := by
        have hc' : approx M u d = Rat.divInt (ceilNum M u d) (d : Int) := by
          unfold approx; exact heq
        rw [hd0, hc']; exact hden
      exact Int.natCast_dvd_natCast.mp hZ
    have hd0_le : d0 ≤ d := Nat.le_of_dvd hd hd0_dvd
    have hd0_lt_M : ((GenContFract.of ((u:ℚ)/M)).convs n).den < M := by rw [← hden_eq]; omega
    have hpos := pos_of_small_den u M hM hco n hd0_lt_M
    have hn78 : n < 78 := index_bound u M hM n hpos (by rw [← hden_eq]; omega)
    have hd0_denI : d0 = denN u M n := by
      rw [hden_eq]; exact convs_den_eq u M hM n hpos
    have hd0_mem : d0 ∈ convDenoms u M bound := by
      rw [hd0_denI]
      exact denN_mem_convDenoms u M bound hM n hpos hn78 (by rw [← hd0_denI]; omega)
    have hFar0 : farFromMultipleBelow M u d0 a := hCheck d0 hd0_mem
    have hfix : approx M u d0 = approx M u d := approx_den_fixed M u d hM hd hndm
    exact far_of_far_at_den M u d d0 a hM hd0pos hd0_dvd hd hfix.symm hFar0

/-! ## Decidable far-check Bool and the sweep-to-`far` bridge -/

/-- Decidable `Bool` mirror of `farFromMultipleBelow`. -/
def farB (M u m a : Nat) : Bool := decide (M ≤ (M - (m * u) % M) * 2 ^ a)

theorem farB_iff (M u m a : Nat) : farB M u m a = true ↔ farFromMultipleBelow M u m a := by
  unfold farB farFromMultipleBelow; rw [decide_eq_true_eq]

/-- **Sweep ⟹ universal `far`.**  In the sweep regime, a single decidable
`Bool` check over the computable list `convDenoms u M bound` (true iff every
candidate denominator is far) yields `farFromMultipleBelow M u m a` for *all*
`0 < m < bound`.  This is the decidable entry point for the binary64 range
sweep. -/
theorem farAll_of_sweep (M u a bound : Nat) (hM : 0 < M) (hco : Nat.Coprime u M)
    (hbM : bound ≤ M) (hb53 : bound ≤ 2^53) (hba : 2 * bound ≤ 2 ^ a)
    (hSweep : (convDenoms u M bound).all (fun Q => farB M u Q a) = true) :
    ∀ m, 0 < m → m < bound → farFromMultipleBelow M u m a := by
  apply far_of_far_at_rat_convergents M u a bound hM hba
  apply hcheck_of_check M u a bound hM hco hbM hb53
  intro Q hQ
  rw [List.all_eq_true] at hSweep
  exact (farB_iff M u Q a).mp (hSweep Q hQ)

end PP.Numeric.Schubfach.R20Sweep

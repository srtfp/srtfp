/- R20 keystone: the computable candidate-denominator sweep and its
   soundness (`farAll_of_sweep`).

   The continued-fraction mathematics — the Euclidean continuants and the
   rational Legendre theorem `small_den_is_denN` — lives in
   `R20Continuant.lean`, entirely in core `Nat`/`Int` arithmetic.  This
   file adds the single-pass computable continuant list `convDenoms`,
   proves it captures every regime continuant denominator below the
   bound, and assembles the decidable sweep-to-`far` bridge used by
   `R20BandSweep.lean`. -/

import Srtfp.Schubfach.R20Continuant
import Srtfp.Schubfach.R20Legendre
import Srtfp.Schubfach.KernelCorrectness
import Srtfp.Tactics

open Srtfp.Compat

namespace Srtfp.Schubfach.R20Sweep

open Srtfp.Schubfach (farFromMultipleBelow)
open Srtfp.Schubfach.R20Legendre (ceilNum gap ceilNum_mul_eq)

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
    rw [Int.natCast_add, Int.natCast_mul, Int.natAbs_of_nonneg (Int.le_of_lt hp1),
        Int.natAbs_of_nonneg (Int.le_of_lt hp0)]
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
  | zero =>
    intro rp rc bp bc acc x hfg hx
    have : f = 0 := by omega
    subst this; exact hx
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
    simp only [(Nat.ne_of_gt hrc), if_false]
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
      rw [denN_zero, denN_one]; grind
    have hmem_n : denN u M n
        ∈ fastDenoms n (rem u M 0) (rem u M 1) 0 (denN u M 0) [] :=
      fastDenoms_emit u M hM n 0 0 [] (by simpa using hpos) hstart n hpos_n (by omega)
    have hrem0 : rem u M 0 = M := rfl
    have hrem1 : rem u M 1 = u % M := rfl
    rw [hrem0, hrem1, denN_zero] at hmem_n
    exact fastDenoms_fuel_mono_le n 78 M (u % M) 0 1 [] _ (by omega) hmem_n
/-! ## Decidable far-check Bool and the sweep-to-`far` bridge -/

/-- Decidable `Bool` mirror of `farFromMultipleBelow`. -/
def farB (M u m a : Nat) : Bool := decide (M ≤ (M - (m * u) % M) * 2 ^ a)

theorem farB_iff (M u m a : Nat) : farB M u m a = true ↔ farFromMultipleBelow M u m a := by
  unfold farB farFromMultipleBelow; rw [decide_eq_true_eq]

/-- **Sweep ⟹ universal `far`.**  In the sweep regime, a single decidable
`Bool` check over the computable list `convDenoms u M bound` (true iff every
candidate denominator is far) yields `farFromMultipleBelow M u m a` for *all*
`0 < m < bound`.  This is the decidable entry point for the binary64 range
sweep.

Soundness runs through the native rational Legendre theorem
(`small_den_is_denN`): a bad `m` reduces (by dividing out
`g = gcd(ceilNum, m)`) to a coprime pair `(p, d)` with
`|u·d − M·p| · 2d < M`, so `d` is a continuant denominator in the swept
list; `far` at `d` scales back up to `far` at `m` because the gaps
divide out exactly (`gap d = gap m / g`). -/
theorem farAll_of_sweep (M u a bound : Nat) (hM : 0 < M) (hco : Nat.Coprime u M)
    (hbM : bound ≤ M) (hb53 : bound ≤ 2^53) (hba : 2 * bound ≤ 2 ^ a)
    (hSweep : (convDenoms u M bound).all (fun Q => farB M u Q a) = true) :
    ∀ m, 0 < m → m < bound → farFromMultipleBelow M u m a := by
  intro m hm hmb
  by_contra hbad
  unfold farFromMultipleBelow at hbad
  push_neg at hbad
  -- Divisible case: gap = M, trivially far — contradiction.
  by_cases hndm : (m * u) % M = 0
  · rw [hndm, Nat.sub_zero] at hbad
    have : M ≤ M * 2 ^ a := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos a)
    omega
  -- The reduced pair (p, d).
  have hceil := ceilNum_mul_eq M u m hM hndm
  set c := ceilNum M u m with hc_def
  set G := gap M u m with hG_def
  have hG_pos : 1 ≤ G := by
    rw [hG_def]; unfold gap
    have : (m * u) % M < M := Nat.mod_lt _ hM
    omega
  have hG_lt : G < M := by
    rw [hG_def]; unfold gap
    have h1 : 0 < (m * u) % M := Nat.pos_of_ne_zero hndm
    omega
  have hceil' : c * M = m * u + G := by
    rw [hc_def, hG_def]; exact hceil
  set g := Nat.gcd c m with hg_def
  have hc_pos : 0 < c := by
    -- c·M = m·u + G ≥ 1, so c ≥ 1
    by_contra hc0
    push_neg at hc0
    have : c = 0 := by omega
    rw [this] at hceil'
    omega
  have hg_pos : 0 < g := by
    rw [hg_def]; exact Nat.gcd_pos_of_pos_left _ hc_pos
  have hg_dvd_c : g ∣ c := by rw [hg_def]; exact Nat.gcd_dvd_left _ _
  have hg_dvd_m : g ∣ m := by rw [hg_def]; exact Nat.gcd_dvd_right _ _
  set d := m / g with hd_def
  set p := c / g with hp_def
  have hd_pos : 0 < d := by
    rw [hd_def]; exact Nat.div_pos (Nat.le_of_dvd hm hg_dvd_m) hg_pos
  have hd_le_m : d ≤ m := by rw [hd_def]; exact Nat.div_le_self _ _
  have hcop : Nat.gcd p d = 1 := by
    rw [hp_def, hd_def, hg_def]
    exact Nat.coprime_div_gcd_div_gcd (by rw [← hg_def]; omega)
  -- g divides the gap, and the scaled-down ceiling identity holds.
  have hg_dvd_G : g ∣ G := by
    have h1 : g ∣ c * M := Nat.dvd_trans hg_dvd_c (Nat.dvd_mul_right c M)
    have h2 : g ∣ m * u := Nat.dvd_trans hg_dvd_m (Nat.dvd_mul_right m u)
    have : G = c * M - m * u := by omega
    rw [this]
    exact Nat.dvd_sub h1 h2
  have hceil_d : p * M = d * u + G / g := by
    obtain ⟨c', hc'⟩ := hg_dvd_c
    obtain ⟨m', hm'⟩ := hg_dvd_m
    obtain ⟨G', hG'⟩ := hg_dvd_G
    have hp' : p = c' := by rw [hp_def, hc']; exact Nat.mul_div_cancel_left _ hg_pos
    have hd' : d = m' := by rw [hd_def, hm']; exact Nat.mul_div_cancel_left _ hg_pos
    have hGg : G / g = G' := by rw [hG']; exact Nat.mul_div_cancel_left _ hg_pos
    rw [hp', hd', hGg]
    -- g·c'·M = g·m'·u + g·G'  ⟹ cancel g
    have hbig : g * (c' * M) = g * (m' * u + G') := by
      have h1 : c * M = g * (c' * M) := by rw [hc']; grind
      have h2 : m * u = g * (m' * u) := by rw [hm']; grind
      have h3 : G = g * G' := hG'
      have hdist : g * (m' * u + G') = g * (m' * u) + g * G' := by grind
      omega
    have := Nat.eq_of_mul_eq_mul_left hg_pos hbig
    omega
  have hGg_pos : 1 ≤ G / g := Nat.one_le_div_iff hg_pos |>.mpr (Nat.le_of_dvd (by omega) hg_dvd_G)
  have hGg_lt : G / g < M := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hG_lt
  -- d·u mod M = M − G/g, i.e. gap at d is G/g.
  have hp_pos : 0 < p := by
    rcases Nat.eq_zero_or_pos p with h0 | h0
    · rw [h0, Nat.zero_mul] at hceil_d
      omega
    · exact h0
  have hmod_d : (d * u) % M = M - G / g := by
    obtain ⟨p', hp'⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
    have hdu : d * u = (p' * M) + (M - G / g) := by
      have hexp : (p' + 1) * M = p' * M + M := by grind
      rw [hp'] at hceil_d
      omega
    rw [hdu, Nat.add_comm, Nat.add_mul_mod_self_right]
    exact Nat.mod_eq_of_lt (by omega)
  -- Legendre smallness for (p, d): |u·d − M·p| = G/g and (G/g)·2d < M.
  have hGdef : G = M - (m * u) % M := by rw [hG_def]; rfl
  have hbad' : G * 2 ^ a < M := by rw [← hGdef] at hbad; exact hbad
  have habs : ((u : ℤ) * d - (M : ℤ) * p).natAbs = G / g := by
    have h1 : (p : ℤ) * M = (d : ℤ) * u + ((G / g : Nat) : ℤ) := by
      exact_mod_cast hceil_d
    have hc1 : (u : ℤ) * d = (d : ℤ) * u := by grind
    have hc2 : (M : ℤ) * p = (p : ℤ) * M := by grind
    omega
  have hsmall : ((u : ℤ) * d - (M : ℤ) * p).natAbs * (2 * d) < M := by
    rw [habs]
    have h2d : 2 * d ≤ 2 ^ a := by omega
    have hGg_le : G / g ≤ G := Nat.div_le_self _ _
    calc G / g * (2 * d) ≤ G * 2 ^ a := Nat.mul_le_mul hGg_le h2d
      _ < M := hbad'
  have hd_lt_M : d < M := by omega
  obtain ⟨n, hreg, hdenN⟩ := small_den_is_denN u M p d hM hco hcop hd_pos hd_lt_M hsmall
  have hn78 : n < 78 := bracket_index_lt_78 u M d n hM hreg hdenN (by omega)
  have hmem : denN u M n ∈ convDenoms u M bound :=
    denN_mem_convDenoms u M bound hM n hreg hn78 (by omega)
  rw [List.all_eq_true] at hSweep
  have hfar_d : farFromMultipleBelow M u (denN u M n) a :=
    (farB_iff M u _ a).mp (hSweep _ hmem)
  rw [hdenN] at hfar_d
  unfold farFromMultipleBelow at hfar_d
  rw [hmod_d] at hfar_d
  have hsimp : M - (M - G / g) = G / g := by omega
  rw [hsimp] at hfar_d
  have hmono : G / g * 2 ^ a ≤ G * 2 ^ a :=
    Nat.mul_le_mul_right _ (Nat.div_le_self _ _)
  omega

end Srtfp.Schubfach.R20Sweep

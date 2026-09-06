module
/- The keystone of Result 20: a computable sweep over convergent
   denominators decides separation from the multiples of `M` for every
   multiplier below the bound (`farAll_of_sweep`).

   `farFromMultipleBelow M u m a` says the gap from `m·u` up to the next
   multiple of `M` is at least `M / 2^a`. By Legendre (`small_den_is_denN`
   in `Continuant.lean`) a multiplier violating it, reduced to lowest
   terms, is a continuant denominator of `u/M`, so checking the finitely
   many continuant denominators below the bound (`convDenoms`) decides
   the property for all of them. -/

public import Srtfp.Perf.Schubfach.Continuant
public import Srtfp.Perf.Schubfach.Legendre
public import Srtfp.Perf.Tactics

@[expose] public section

open Srtfp.Compat

namespace Srtfp.Schubfach.R20

/-- `m·u` is at least `M / 2^a` below the next multiple of `M`. -/
def farFromMultipleBelow (M u m a : Nat) : Prop := M ≤ (M - (m * u) % M) * 2 ^ a

theorem denN_zero (u M : Nat) : denN u M 0 = 1 := rfl
theorem denN_one (u M : Nat) : denN u M 1 = qt u M 0 := by unfold denN denI; simp

/-- The `Nat` continuant recurrence (positive regime). -/
theorem denN_rec (u M : Nat) (hM : 0 < M) (n : Nat) (hpos : ∀ i, i ≤ n+2 → 0 < rem u M i) :
    denN u M (n+2) = qt u M (n+1) * denN u M (n+1) + denN u M n := by
  unfold denN
  have h2 : denI u M (n+2) = (qt u M (n+1):Int) * denI u M (n+1) + denI u M n := rfl
  have hp1 : 0 < denI u M (n+1) := denI_pos u M hM (n+1) (fun i hi => hpos i (by omega))
  have hp0 : 0 < denI u M n := denI_pos u M hM n (fun i hi => hpos i (by omega))
  rw [h2]
  have e2 : (qt u M (n+1):Int) * denI u M (n+1) + denI u M n
      = ((qt u M (n+1) * (denI u M (n+1)).natAbs + (denI u M n).natAbs : Nat) : Int) := by
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
  (1 :: fastDenoms 79 M (u % M) 0 1 []).filter (· < bound)

/-- The continuant denominator `denN u M n` is in the computable list for every
positive-regime index `n < 79` with `denN u M n < bound`. -/
theorem denN_mem_convDenoms (u M bound : Nat) (hM : 0 < M) (n : Nat)
    (hpos : ∀ i, i ≤ n+1 → 0 < rem u M i) (hn : n < 79) (hlt : denN u M n < bound) :
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
    exact fastDenoms_fuel_mono_le n 79 M (u % M) 0 1 [] _ (by omega) hmem_n
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
    (hbM : bound ≤ M) (hb54 : bound ≤ 2^54) (hba : 2 * bound ≤ 2 ^ a)
    (hSweep : (convDenoms u M bound).all (fun Q => farB M u Q a) = true) :
    ∀ m, 0 < m → m < bound → farFromMultipleBelow M u m a := by
  intro m hm hmb
  by_contra hbad
  unfold farFromMultipleBelow at hbad
  push_neg at hbad
  -- `m·u` is not a multiple of `M`: its gap `G` lies in `[1, M)`, and `c·M = m·u + G`
  have hndm : (m * u) % M ≠ 0 := fun h => by
    rw [h, Nat.sub_zero] at hbad
    exact absurd hbad (Nat.not_lt.mpr (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos a)))
  have hceil := ceilNum_mul_eq M u m hM hndm
  have hG : 1 ≤ gap M u m ∧ gap M u m < M := by
    unfold gap; have := Nat.mod_lt (m * u) hM; omega
  rw [show M - (m * u) % M = gap M u m from rfl] at hbad
  generalize gap M u m = G at *
  generalize ceilNum M u m = c at *
  have hc : 0 < c := Nat.pos_of_ne_zero (fun h => by subst h; omega)
  -- reduce `(c, m)` by their gcd `g` to the coprime `(p, d)`: `p·M = d·u + G/g`
  generalize hg : Nat.gcd c m = g
  have hgc : g ∣ c := hg ▸ Nat.gcd_dvd_left _ _
  have hgm : g ∣ m := hg ▸ Nat.gcd_dvd_right _ _
  have hg0 : 0 < g := hg ▸ Nat.gcd_pos_of_pos_left _ hc
  have hgG : g ∣ G := by
    rw [show G = c * M - m * u by omega]
    exact Nat.dvd_sub (Nat.dvd_trans hgc (Nat.dvd_mul_right c M))
      (Nat.dvd_trans hgm (Nat.dvd_mul_right m u))
  have hcop : Nat.gcd (c / g) (m / g) = 1 := by
    rw [← hg]; exact Nat.coprime_div_gcd_div_gcd (hg ▸ hg0)
  generalize hp : c / g = p at hcop
  generalize hd : m / g = d at hcop
  have hd0 : 0 < d := by rw [← hd]; exact Nat.div_pos (Nat.le_of_dvd hm hgm) hg0
  have hdm : d ≤ m := by rw [← hd]; exact Nat.div_le_self _ _
  have hceil_d : p * M = d * u + G / g := by
    apply Nat.eq_of_mul_eq_mul_left hg0
    rw [Nat.mul_add, ← Nat.mul_assoc, ← Nat.mul_assoc, ← hp, ← hd, Nat.mul_div_cancel' hgc,
      Nat.mul_div_cancel' hgm, Nat.mul_div_cancel' hgG]
    exact hceil
  have hGg : 1 ≤ G / g ∧ G / g < M :=
    ⟨(Nat.one_le_div_iff hg0).mpr (Nat.le_of_dvd (by omega) hgG),
      Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hG.2⟩
  have hp0 : 0 < p := Nat.pos_of_ne_zero (fun h => by subst h; omega)
  -- so the gap of `d` is `G/g`, and `(p, d)` approximates `u/M` to Legendre quality
  have hmod_d : (d * u) % M = M - G / g := by
    obtain ⟨p', hp'⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
    rw [hp', Nat.succ_mul] at hceil_d
    rw [show d * u = (M - G / g) + p' * M by omega, Nat.add_mul_mod_self_right]
    exact Nat.mod_eq_of_lt (by omega)
  have habs : ((u : Int) * d - (M : Int) * p).natAbs = G / g := by
    have h1 : (p : Int) * M = (d : Int) * u + ((G / g : Nat) : Int) := by exact_mod_cast hceil_d
    have hc1 : (u : Int) * d = (d : Int) * u := Int.mul_comm _ _
    have hc2 : (M : Int) * p = (p : Int) * M := Int.mul_comm _ _
    omega
  have hsmall : ((u : Int) * d - (M : Int) * p).natAbs * (2 * d) < M := by
    rw [habs]
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul (Nat.div_le_self _ _) (by omega : 2 * d ≤ 2 ^ a)) hbad
  -- Legendre: `d` is a swept continuant denominator, so it is far; but its gap is `≤ G`
  obtain ⟨n, hreg, hdenN⟩ := small_den_is_denN u M p d hM hco hcop hd0 (by omega) hsmall
  have hfar := (farB_iff M u _ a).mp ((List.all_eq_true.mp hSweep) _
    (denN_mem_convDenoms u M bound hM n hreg
      (bracket_index_lt_79 u M d n hM hreg hdenN (by omega)) (by omega)))
  unfold farFromMultipleBelow at hfar
  rw [hdenN, hmod_d, show M - (M - G / g) = G / g by omega] at hfar
  have := Nat.mul_le_mul_right (2 ^ a) (Nat.div_le_self G g)
  omega

end Srtfp.Schubfach.R20

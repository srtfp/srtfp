module
/- F7 with the integer tests of Results 18 and 19: the rounded-to-odd
   `v̄ = r_o(4V)`, `v̄_l = r_o(4V_l)`, `v̄_r = r_o(4V_r)` and `out = c mod 2`
   replace the rational comparisons of `Exact.shortest`. -/

public import Srtfp.Perf.Schubfach.RoundOdd

@[expose] public section

namespace Srtfp.Schubfach

open Srtfp.Printer Exact

variable {m : Nat} {q k : Int}

/-! ## R18 on naturals -/

theorem R18_left_nat (m : Nat) (a : Rat) (n : Nat) :
    leL m a (n : Rat) = decide (ro (4 * a) + out m ≤ 4 * (n : Int)) := by
  rw [← R18_left, Rat.intCast_natCast]

theorem R18_right_nat (m : Nat) (n : Nat) (a : Rat) :
    leR m (n : Rat) a = decide (4 * (n : Int) + out m ≤ ro (4 * a)) := by
  rw [← R18_right, Rat.intCast_natCast]

theorem R18_mid_lt_nat (x : Rat) (a b : Nat) :
    2 * x < (a : Rat) + (b : Rat) ↔ ro (4 * x) < 2 * ((a + b : Nat) : Int) := by
  rw [← R18_mid_lt]; push_cast; exact Iff.rfl

theorem R18_mid_gt_nat (x : Rat) (a b : Nat) :
    (a : Rat) + (b : Rat) < 2 * x ↔ 2 * ((a + b : Nat) : Int) < ro (4 * x) := by
  rw [← R18_mid_gt]; push_cast; exact Iff.rfl

/-! ## F7 on integers -/

/-- `pick` with the tests of R18. -/
def pickI (o vb vbl vbr : Int) (s : Nat) : Nat :=
  let t := s + 1
  let uIn := decide (vbl + o ≤ 4 * (s : Int))
  let wIn := decide (4 * (t : Int) + o ≤ vbr)
  if uIn && !wIn then s
  else if !uIn && wIn then t
  else if vb < 2 * ((s + t : Nat) : Int) then s
  else if 2 * ((s + t : Nat) : Int) < vb then t
  else if s % 2 = 0 then s
  else t

/-- `Exact.shortest` on the integers `v̄`, `v̄_l`, `v̄_r`. -/
def shortestI (m : Nat) (q : Int) : Nat × Int :=
  let k := kOfMQ m q
  let vb := ro (4 * V m q k)
  let vbl := ro (4 * Vl m q k)
  let vbr := ro (4 * Vr m q k)
  let o := out m
  let s := (vb / 4).toNat
  if s ≥ 10 then
    let s' := s / 10
    if vbl + o ≤ 4 * ((10 * s' : Nat) : Int) then (s', k + 1)
    else if 4 * ((10 * (s' + 1) : Nat) : Int) + o ≤ vbr then (s' + 1, k + 1)
    else (pickI o vb vbl vbr s, k)
  else (pickI o vb vbl vbr s, k)

theorem pickI_eq (s : Nat) :
    pickI (out m) (ro (4 * V m q k)) (ro (4 * Vl m q k)) (ro (4 * Vr m q k)) s
      = pick m q k s := by
  unfold pickI pick
  simp only [R18_left_nat, R18_right_nat, R18_mid_lt_nat, R18_mid_gt_nat]

/-- `s = ⌊V⌋ = v̄ ÷ 4` (R19). -/
theorem s_eq_ro : (ro (4 * V m q k) / 4).toNat = s m q k := by
  rw [R19]; rfl

theorem shortestI_eq : shortestI m q = Exact.shortest m q := by
  unfold shortestI Exact.shortest
  simp only [s_eq_ro, pickI_eq, R18_left_nat, R18_right_nat, decide_eq_true_eq]

end Srtfp.Schubfach

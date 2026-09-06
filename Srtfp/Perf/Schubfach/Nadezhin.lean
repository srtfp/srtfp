module
/- **Result 20** (Giulietti, after Nadezhin): for every binary64 `v` and
   `k` from R10, each of `2V`, `2V_l`, `2V_r` is an integer or at least
   `ε = 2^-64` away from the nearest integers on both sides. -/

public import Srtfp.Perf.Schubfach.NadezhinBands
public import Srtfp.Perf.Schubfach.NadezhinSweep1
public import Srtfp.Perf.Schubfach.NadezhinSweep2
public import Srtfp.Perf.Schubfach.NadezhinSweep3
public import Srtfp.Perf.Schubfach.NadezhinSweep4

@[expose] public section

namespace Srtfp.Schubfach

open Srtfp.Printer Srtfp.Schubfach.Exact R20

variable {m : Nat} {q : Int}

theorem rangeCheck_all : rangeCheck 0 2046 = true :=
  rangeCheck_append 0 512 1534 Sweep1.all
    (rangeCheck_append 512 512 1022 Sweep2.all
      (rangeCheck_append 1024 512 510 Sweep3.all Sweep4.all))

theorem checkQ_all (q : Int) (h1 : -1074 ≤ q) (h2 : q ≤ 971) : checkQ q = true := by
  have := rangeCheck_sound 0 2046 rangeCheck_all (q + 1074).toNat (by omega) (by omega)
  rwa [show (((q + 1074).toNat : Nat) : Int) - 1074 = q by omega] at this

theorem R20 (h : InRange m q) :
    Separated eps (2 * V m q (kOfMQ m q)) ∧ Separated eps (2 * Vl m q (kOfMQ m q))
    ∧ Separated eps (2 * Vr m q (kOfMQ m q)) :=
  R20_of_checkQ h (checkQ_all q h.2.2.1 h.2.2.2.1)

end Srtfp.Schubfach

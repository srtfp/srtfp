/- Minimized reproducer for an `omega` regression on Lean ≥ v4.32
   (still present on v4.33.0; absent on v4.27.0), hit throughout this
   repo's 128/192-bit kernel proofs when bumping the toolchain.

   `omega` exhausts any `maxRecDepth` (1024, 65536, …) whenever a
   hypothesis with a variable coefficient at `2^64` magnitude coexists
   with a goal whose constants reach `2^192` magnitude — even though the
   hypothesis is irrelevant to the (ground) goal, and even with the
   powers pre-expanded to numerals. Each ingredient alone is fine:
   dropping the hypothesis, or shrinking the goal below ~`2^128`, makes
   `omega` succeed instantly. On v4.27 the same call succeeds and even
   flags the hypothesis as unused.

   Run: `lean tools/omega_regression_repro.lean` on a ≥4.32 toolchain →
   "maximum recursion depth has been reached" at the `omega` line.

   Workarounds used in this repo: prove the ground fact in a clean
   context and `exact` it (`key192_bound`-style), swap the affected
   `omega`s for `grind`, or chain explicit `Nat.le_trans` steps. -/

set_option maxRecDepth 1024

example (m : Nat) (h : m * 2 ^ 64 ≤ (2 ^ 64 - 1) * 2 ^ 64) :
    (2 ^ 64 - 1) * (2 ^ 64 * 2 ^ 64) + (2 ^ 64 - 1) * 2 ^ 64 + 2 ^ 64
      ≤ 2 ^ 64 * (2 ^ 64 * 2 ^ 64) := by
  omega

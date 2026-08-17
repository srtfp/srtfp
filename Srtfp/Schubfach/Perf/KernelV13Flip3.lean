/- flip3 fast-path correctness: dispatch over the per-leg modules. -/

import Srtfp.Schubfach.Perf.KernelV13Flip3LegSlow
import Srtfp.Schubfach.Perf.KernelV13Flip3LegUV
import Srtfp.Schubfach.Perf.KernelV13Flip3LegWV
import Srtfp.Schubfach.Perf.KernelV13Flip3LegPick

namespace Srtfp.Schubfach

private theorem bool_eq_false {b : Bool} (h : ¬ b = true) : b = false := by
  cases b
  · rfl
  · exact absurd rfl h

set_option maxRecDepth 16384 in
/-- Fast-path correctness for flip3: a `some` result is the
    `shortestUnsigned_packed` (= spec) value. The `s` leg rides
    `sFromP_floor` instead of the 192-bit table chain.

    Elaboration memory is additive across a tactic proof's branches, so
    the four legs live in their own private lemmas above (dispatched on
    the spec-level rounding-interval predicates, which the kernel-side
    verdicts decide via `..._some_eq`); this bounds the module's peak at
    the largest single leg instead of their sum. -/
theorem shortestUnsigned_u64_opt_flip3_some_eq_packed
    (m : Nat) (q : Int) (sUo : UInt64) (ko : Int)
    (hopt : shortestUnsigned_u64_opt_flip3 m q = some (sUo, ko)) :
    shortestUnsigned_packed m q = (sUo.toNat, ko) := by
  rw [shortestUnsigned_packed_eq]
  by_cases hs10 : shiftedSig m q (kOfMQ m q) ≥ 10
  · by_cases hIn : inRoundingInterval (shiftedSig m q (kOfMQ m q) / 10)
        (kOfMQ m q + 1) m q (isIrregular m q) = true
    · exact flip3_some_eq_packed_uV m q sUo ko hopt hs10 hIn
    · by_cases hIn1 : inRoundingInterval (shiftedSig m q (kOfMQ m q) / 10 + 1)
          (kOfMQ m q + 1) m q (isIrregular m q) = true
      · exact flip3_some_eq_packed_wV m q sUo ko hopt hs10 (bool_eq_false hIn) hIn1
      · exact flip3_some_eq_packed_pick m q sUo ko hopt hs10
          (bool_eq_false hIn) (bool_eq_false hIn1)
  · exact flip3_some_eq_packed_slow m q sUo ko hopt hs10


end Srtfp.Schubfach

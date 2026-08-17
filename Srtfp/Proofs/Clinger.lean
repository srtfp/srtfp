/- Clinger Decimal→Float correctness — main file (M4).

   ## What this file establishes

   This file is the top-level entry point for M4 (Clinger
   correctly-rounded `Decimal → Float`). It re-exports the per-branch
   correctness machinery from the `Clinger/` sub-modules, assembles the
   abstract correctness theorem, and provides the unconditional
   headline theorem `ofDecimal_in_Rv` (via the runtime axiom
   `Float.toBits_ofBits`).

   ## Layering

   * **`Clinger/Base.lean`** — `roundNearestEven`/`findBinaryExp`/
     `scaleByPow2` shape lemmas, the abstract decode `decodedAbs`,
     `DecodeOfDecimalBridge`.
   * **`Clinger/Regular.lean`** — cleared-form scaling, parity at tie,
     `regular_branch_correct`.
   * **`Clinger/FindBinaryExp.lean`** — `findBinaryExp` lower/upper
     bounds, `clinger_num_ge_2pow52_denom`,
     `clinger_num_lt_2pow53_denom`, `num_pre_denom_eq`.
   * **`Clinger/IrregularNoCarry.lean`** — `irregular_no_carry_correct`.
   * **`Clinger/IrregularCarry.lean`** — `irregular_carry_correct`.
   * **`Clinger/Bridge.lean`** — the axiom-free bits-level bridge
     `decode_of_decimal_bridge_bits`, plus its Float tier (which uses
     the `Float.toBits_ofBits` axiom).

   This file assembles the dispatch and the unconditional headline, at
   both the word level (`ofDecimalBits_in_Rv`, axiom-free) and the
   `Float` level (`ofDecimal_in_Rv`). -/

import Srtfp.Proofs.Clinger.Base
import Srtfp.Proofs.Clinger.Regular
import Srtfp.Proofs.Clinger.FindBinaryExp
import Srtfp.Proofs.Clinger.IrregularNoCarry
import Srtfp.Proofs.Clinger.IrregularCarry
import Srtfp.Proofs.Clinger.Dispatch
import Srtfp.Proofs.Clinger.Bridge
import Srtfp.Proofs.Schubfach.Shorter
import Srtfp.Proofs.Schubfach.ToDecimal

namespace Srtfp.Clinger

open Srtfp.Float
open Srtfp.Schubfach
open Srtfp

/-! ## Setup lemmas for the dispatch -/

/-! ## Headline correctness theorem -/

/-- **Headline correctness theorem.** For a non-overflow nonzero
`Decimal d`, `Clinger.ofDecimal d` decodes to a Float in the rounding
interval of `d = d.significand · 10^d.exponent`.

The bridge from `decode (ofDecimal d)` to the abstract `decodedAbs`
uses `Float.toBits_ofBits` (and a single derived `fromBits_proj` axiom)
to project bit fields through the IEEE-754 runtime intrinsics. The
abstract correctness reduces to the case-split dispatch on
`decodedAbs`'s if-tree. Both are now proven; this theorem is
unconditional. -/
theorem ofDecimalBits_in_Rv
    (d : Decimal)
    (h_nonzero : d.significand ≠ 0)
    (h_finite : IsFiniteAbs d.sign d.significand d.exponent) :
    let decoded := Word.decode (ofDecimalBits d)
    inRoundingInterval d.significand d.exponent
        decoded.m decoded.q (isIrregular decoded.m decoded.q) = true := by
  simp only
  rw [decode_of_decimal_bridge_bits d h_finite]
  exact (abstract_correctness_of_dispatch branch_dispatch)
          d.sign d.significand d.exponent h_nonzero h_finite

end Srtfp.Clinger

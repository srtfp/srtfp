module
/- Clinger Decimal→Float correctness — main file (M4).

   ## What this file establishes

   This file is the top-level entry point for M4 (Clinger
   correctly-rounded `Decimal → Float`). It re-exports the per-branch
   correctness machinery from the `Reader/` sub-modules, assembles the
   abstract correctness theorem, and provides the unconditional
   headline theorem `ofDecimal_in_Rv` (via the runtime axiom
   `Float.toBits_ofBits`).

   ## Layering

   * **`Reader/Base.lean`** — `roundNearestEven`/`findBinaryExp`/
     `scaleByPow2` shape lemmas, the abstract decode `decodedAbs`,
     `DecodeOfDecimalBridge`.
   * **`Reader/Regular.lean`** — cleared-form scaling, parity at tie,
     `regular_branch_correct`.
   * **`Reader/FindBinaryExp.lean`** — `findBinaryExp` lower/upper
     bounds, `clinger_num_ge_2pow52_denom`,
     `clinger_num_lt_2pow53_denom`, `num_pre_denom_eq`.
   * **`Reader/IrregularNoCarry.lean`** — `irregular_no_carry_correct`.
   * **`Reader/IrregularCarry.lean`** — `irregular_carry_correct`.
   * **`Reader/Bridge.lean`** — the axiom-free bits-level bridge
     `decode_of_decimal_bridge_bits`, plus its Float tier (which uses
     the `Float.toBits_ofBits` axiom).

   This file assembles the dispatch and the unconditional headline, at
   both the word level (`ofDecimalBits_in_Rv`, axiom-free) and the
   `Float` level (`ofDecimal_in_Rv`). -/

public import Srtfp.Perf.Schubfach.Reader.Base
public import Srtfp.Perf.Schubfach.Reader.Regular
public import Srtfp.Perf.Schubfach.Reader.FindBinaryExp
public import Srtfp.Perf.Schubfach.Reader.IrregularNoCarry
public import Srtfp.Perf.Schubfach.Reader.IrregularCarry
public import Srtfp.Perf.Schubfach.Reader.Dispatch
public import Srtfp.Perf.Schubfach.Reader.Bridge
public import Srtfp.Perf.Schubfach.Reader.NatInterval

@[expose] public section

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

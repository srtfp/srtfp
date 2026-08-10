/- Phase C: `Schubfach.toStringFast` — fused Float → String fast path.

   Skips the `Except String Decimal` boxing on the success path and the
   `Decimal` constructor/destructor round-trip from `floatToStr`.

   `floatToStrRef` is the spec — verbatim shape of the prior bench code.
   `toStringFast` is the runtime form, proven equal pointwise and wired
   via `@[csimp]` so callers of `floatToStrRef` go through the fast path. -/

import Srtfp.Schubfach
import Srtfp.Schubfach.Perf.Orchestration
import Srtfp.Schubfach.Perf.Uint64Bridge
import Srtfp.Schubfach.Perf.Kernel192Correctness
import Srtfp.Schubfach.Perf.KernelV5
import Srtfp.Decimal.Perf.Fast

namespace Srtfp.Schubfach

open Srtfp.Float
open Srtfp.Decimal (canonicaliseAux)

/-! ## Reference: the bench's `floatToStr` shape, lifted as a verifiable spec. -/

/-- Reference `Int → String`.  Byte-identical to `toString : Int → String`
    (whose `ToString` instance routes through the OPAQUE
    `String.Internal.append`, making it unusable as a proof target);
    this spelling uses `++` so emitters can be proven against it. -/
def intToStrRef (e : Int) : String :=
  match e with
  | .ofNat m => toString m
  | .negSucc m => "-" ++ toString (m + 1)

/-- Reference Decimal → String emit (shape from `BenchFloatToString.lean`). -/
def decimalToStrRef (d : _root_.Srtfp.Decimal) : String :=
  if d.significand = 0 then (if d.sign then "-0" else "0")
  else
    let signStr := if d.sign then "-" else ""
    signStr ++ toString d.significand ++ "e" ++ intToStrRef d.exponent

/-- Reference `Float → String`: the body of `floatToStr` in `BenchFloatToString.lean`. -/
def floatToStrRef (f : _root_.Float) : String :=
  match toDecimal f with
  | .ok d => decimalToStrRef d
  | .error e => e

/-! ## Fast path: avoid Except + Decimal allocation. -/

/-- Fused `Float → String`. Mirrors `toDecimal_v4`'s control flow but
    inlines the `Except` and `Decimal` wrappers — the success path drops
    straight from `(sig, exp)` to the final `++` chain. -/
@[inline]
def toStringFast (f : _root_.Float) : String :=
  if isNaNBits f then "NaN"
  else if isInfBits f then (if signBit f then "-Infinity" else "Infinity")
  else
    let d := decode f
    if d.m = 0 then (if d.sign then "-0" else "0")
    else
      let (sig, exp) := shortestUnsigned_v5 d.m d.q
      -- Inline `Decimal.mk'_fast2` logic: derive the canonical (sig', exp').
      if sig = 0 then (if d.sign then "-0" else "0")
      else if sig % 10 ≠ 0 then
        -- No trailing zeros: skip canonicaliseAux entirely (common case for
        -- Schubfach outputs that don't end in 0).
        let signStr := if d.sign then "-" else ""
        signStr ++ toString sig ++ "e" ++ intToStrRef exp
      else
        let (sig', exp') := canonicaliseAux sig exp
        if sig' = 0 then (if d.sign then "-0" else "0")
        else
          let signStr := if d.sign then "-" else ""
          signStr ++ toString sig' ++ "e" ++ intToStrRef exp'

/-! ## Equivalence proof. -/

private theorem decimalToStrRef_mk' (sign : Bool) (sig : Nat) (exp : Int) :
    decimalToStrRef (_root_.Srtfp.Decimal.mk' sign sig exp)
      = (if sig = 0 then (if sign then "-0" else "0")
        else if sig % 10 ≠ 0 then
          let signStr := if sign then "-" else ""
          signStr ++ toString sig ++ "e" ++ intToStrRef exp
        else
          let (sig', exp') := canonicaliseAux sig exp
          if sig' = 0 then (if sign then "-0" else "0")
          else
            let signStr := if sign then "-" else ""
            signStr ++ toString sig' ++ "e" ++ intToStrRef exp') := by
  unfold decimalToStrRef _root_.Srtfp.Decimal.mk' _root_.Srtfp.Decimal.canonical
  by_cases hs0 : sig = 0
  · simp [hs0]
  simp only [hs0, if_false]
  by_cases hsmod : sig % 10 ≠ 0
  · have hCanon : canonicaliseAux sig exp = (sig, exp) := by
      unfold canonicaliseAux
      simp [hs0, hsmod]
    rw [hCanon, if_pos hsmod]
    simp [hs0]
  · rw [if_neg hsmod]

theorem toStringFast_eq_ref (f : _root_.Float) : toStringFast f = floatToStrRef f := by
  unfold toStringFast floatToStrRef toDecimal
  by_cases h1 : isNaNBits f = true
  · simp [h1]
  by_cases h2 : isInfBits f = true
  · simp [h1, h2]
  simp only [h1, h2, if_false, Bool.false_eq_true]
  by_cases h3 : (decode f).m = 0
  · simp [h3, decimalToStrRef]
  simp only [h3, if_false]
  rw [show shortestUnsigned (decode f).m (decode f).q
        = shortestUnsigned_v5 (decode f).m (decode f).q from
        (shortestUnsigned_v5_eq _ _).symm]
  -- pattern-match the prod
  obtain ⟨sig, exp⟩ : Nat × Int := shortestUnsigned_v5 (decode f).m (decode f).q
  show (if sig = 0 then (if (decode f).sign then "-0" else "0")
        else if sig % 10 ≠ 0 then
          let signStr := if (decode f).sign then "-" else ""
          signStr ++ toString sig ++ "e" ++ intToStrRef exp
        else
          let (sig', exp') := canonicaliseAux sig exp
          if sig' = 0 then (if (decode f).sign then "-0" else "0")
          else
            let signStr := if (decode f).sign then "-" else ""
            signStr ++ toString sig' ++ "e" ++ intToStrRef exp')
      = decimalToStrRef (_root_.Srtfp.Decimal.mk' (decode f).sign sig exp)
  rw [decimalToStrRef_mk']

-- Superseded registration: `floatToStrRef_eq_toStringFast4` (DigitsFast.lean)
-- is the live @[csimp].
theorem floatToStrRef_eq_toStringFast : @floatToStrRef = @toStringFast := by
  funext f
  exact (toStringFast_eq_ref f).symm

end Srtfp.Schubfach

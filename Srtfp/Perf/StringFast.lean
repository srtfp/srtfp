module
/- Phase C: `Schubfach.toStringFast` — fused Float → String fast path.

   Skips the `Option Decimal` boxing on the success path and the
   `Decimal` constructor/destructor round-trip from `floatToStr`.

   `floatToStrRef` is the spec — verbatim shape of the prior bench code.
   `toStringFast` is the runtime form, proven equal pointwise and wired
   via `@[csimp]` so callers of `floatToStrRef` go through the fast path. -/

public import Srtfp.Perf.Schubfach
public import Srtfp.Perf.Orchestration
public import Srtfp.Perf.Uint64Bridge
public import Srtfp.Perf.Kernel192Correctness
public import Srtfp.Perf.KernelV5
public import Srtfp.Perf.DecimalFast
public import Srtfp.Perf.SchubfachEq

@[expose] public section

open Float.Model.UnpackedFloat (Sign)

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
  if d.significand = 0 then withSign d.sign "0"
  else
    withSign d.sign (toString d.significand ++ "e" ++ intToStrRef d.exponent)

/-- Reference `Float → String`: the body of `floatToStr` in `BenchFloatToString.lean`. -/
def floatToStrRef (f : _root_.Float) : String :=
  match Printer.toDecimal f with
  | some d => decimalToStrRef d
  | none => if isNaNBits f then "NaN" else withSign (signBit f) "Infinity"

/-! ## Fast path: avoid Option + Decimal allocation. -/

/-- Fused `Float → String`. Mirrors `toDecimal`'s control flow but
    inlines the `Option` and `Decimal` wrappers — the success path drops
    straight from `(sig, exp)` to the final `++` chain. -/
@[inline]
def toStringFast (f : _root_.Float) : String :=
  if isNaNBits f then "NaN"
  else if isInfBits f then (withSign (signBit f) "Infinity")
  else
    let d := decode f
    if d.m = 0 then withSign d.sign "0"
    else
      let (sig, exp) := shortestUnsigned_v5 d.m d.q
      -- Inline `Decimal.mk'_fast2` logic: derive the canonical (sig', exp').
      if sig = 0 then withSign d.sign "0"
      else if sig % 10 ≠ 0 then
        -- No trailing zeros: skip canonicaliseAux entirely (common case for
        -- Schubfach outputs that don't end in 0).
        withSign d.sign (toString sig ++ "e" ++ intToStrRef exp)
      else
        let (sig', exp') := canonicaliseAux sig exp
        if sig' = 0 then withSign d.sign "0"
        else
          withSign d.sign (toString sig' ++ "e" ++ intToStrRef exp')

/-! ## Equivalence proof. -/

private theorem decimalToStrRef_mk' (sign : Sign) (sig : Nat) (exp : Int) :
    decimalToStrRef (_root_.Srtfp.Decimal.mk' sign sig exp)
      = (if sig = 0 then withSign sign "0"
        else if sig % 10 ≠ 0 then
          withSign sign (toString sig ++ "e" ++ intToStrRef exp)
        else
          let (sig', exp') := canonicaliseAux sig exp
          if sig' = 0 then withSign sign "0"
          else
            withSign sign (toString sig' ++ "e" ++ intToStrRef exp')) := by
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
  unfold toStringFast floatToStrRef
  rw [← congrFun toDecimal_eq_printer f]
  unfold toDecimal toDecimalBits
  simp only [← isNaNBits_word, ← isInfBits_word, ← signBit_word, ← decode_word]
  by_cases h1 : isNaNBits f = true
  · simp [h1]
  by_cases h2 : isInfBits f = true
  · simp [h1, h2] <;> split <;> simp [*]
  simp only [h1, h2, if_false, Bool.false_eq_true]
  by_cases h3 : (decode f).m = 0
  · simp [h3, decimalToStrRef]
  simp only [h3, if_false]
  rw [show shortestUnsigned (decode f).m (decode f).q
        = shortestUnsigned_v5 (decode f).m (decode f).q from
        (shortestUnsigned_v5_eq _ _).symm]
  -- pattern-match the prod
  obtain ⟨sig, exp⟩ : Nat × Int := shortestUnsigned_v5 (decode f).m (decode f).q
  show (if sig = 0 then withSign (decode f).sign "0"
        else if sig % 10 ≠ 0 then
          withSign (decode f).sign (toString sig ++ "e" ++ intToStrRef exp)
        else
          let (sig', exp') := canonicaliseAux sig exp
          if sig' = 0 then withSign (decode f).sign "0"
          else
            withSign (decode f).sign (toString sig' ++ "e" ++ intToStrRef exp'))
      = decimalToStrRef (_root_.Srtfp.Decimal.mk' (decode f).sign sig exp)
  rw [decimalToStrRef_mk']

end Srtfp.Schubfach

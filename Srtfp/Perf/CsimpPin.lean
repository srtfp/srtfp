module
/- Build-time pin of the LIVE `@[csimp]` kernel registrations.

   Each accelerated function must have exactly ONE registration
   (enforced by review), and this module asserts at compile time which
   replacement the compiler will actually use. An import reorder or a
   stray new registration that changes the live kernel FAILS THE BUILD
   here instead of silently reverting performance.

   The printer's proof path, for orientation: kernel 0
   (`Perf/Schubfach.lean`, equal to the reference by `SchubfachEq`)
   = the packed orchestration (`Orchestration`, 128-bit table product,
   R20 for the full binary64 range) = the flip3 boundary-digit kernel
   (`KernelV13Flip3*`) = v13 (`KernelV13`) = v14 (`KernelV14`, unboxed
   verdicts, biased exponent), the live kernel. An ambiguous 128-bit
   verdict falls back to `shortestUnsignedN` (`Fallback`), kernel 0's
   decision tree over `Nat` with an exact comparison where needed.

   Wired into `lake test` via AxiomCheck.lean. Not imported by `PP`
   (it pulls the Lean frontend, which library clients don't need). -/

public meta import Lean
public import Srtfp.Perf.KernelV14
public import Srtfp.Perf.ReadFast

@[expose] public section

open Lean Elab Command Lean.Compiler in
#eval show Lean.CoreM Unit from do
  let s := Lean.Compiler.CSimp.ext.getState (← Lean.getEnv)
  let check (src tgt : Lean.Name) : Lean.CoreM Unit := do
    match s.map.find? src with
    | some t =>
      unless t.toDeclName == tgt do
        throwError "csimp pin: {src} compiles to {t.toDeclName}, expected {tgt}"
    | none => throwError "csimp pin: {src} has no csimp replacement"
  check `Srtfp.Printer.toDecimal `Srtfp.Schubfach.toDecimal_v14
  check `Srtfp.Schubfach.toDecimal `Srtfp.Schubfach.toDecimal_v14
  check `Srtfp.Schubfach.floatToStrRef `Srtfp.Schubfach.toStringFast10
  check `Srtfp.Decimal.canonicaliseAux `Srtfp.Decimal.canonicaliseAux_fast2
  check `Srtfp.Decimal.mk' `Srtfp.Decimal.mk'_fast3
  check `Srtfp.Reader.ofDecimalBits `Srtfp.Reader.ofDecimalBits_fast
  check `Srtfp.Reader.ofDecimal `Srtfp.Reader.ofDecimal_fast

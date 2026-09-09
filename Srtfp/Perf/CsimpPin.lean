module
/- Build-time pin of the LIVE `@[csimp]` kernel registrations.

   Each accelerated function must have exactly ONE registration
   (enforced by review), and this module asserts at compile time which
   replacement the compiler will actually use. An import reorder or a
   stray new registration that changes the live kernel FAILS THE BUILD
   here instead of silently reverting performance.

   The printer's proof path, for orientation: the reference scan
   (`Srtfp/Printer.lean`) = Schubfach's F7 (`Perf/Schubfach/Exact.lean`)
   = its integer form (`Tests.lean`, R18/R19) = the word-level kernel
   (`Kernel.lean`, F9 with the estimates of R20–R25), the live kernel.

   Wired into `lake build` and `lake test` via SrtfpAudit.lean.
   Not imported by `Srtfp.Perf`
   (it pulls the Lean frontend, which library clients don't need). -/

public meta import Lean
public import Srtfp.Perf.Schubfach.Entry
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
  check `Srtfp.Printer.toDecimal `Srtfp.Schubfach.toDecimal
  check `Srtfp.Schubfach.floatToStrRef `Srtfp.Schubfach.floatToString
  check `Srtfp.Decimal.canonicaliseAux `Srtfp.Decimal.canonicaliseAuxFast
  check `Srtfp.Decimal.canonical `Srtfp.Decimal.canonicalFast
  check `Srtfp.Decimal.mk' `Srtfp.Decimal.mk'Fast
  check `Srtfp.Reader.ofDecimalBits `Srtfp.Reader.ofDecimalBits_fast
  check `Srtfp.Reader.ofDecimal `Srtfp.Reader.ofDecimal_fast

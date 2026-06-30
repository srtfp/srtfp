/- Build-time pin of the LIVE `@[csimp]` kernel registrations.

   The Schubfach optimization series replaced kernels via proven-equal
   `@[csimp]` swaps. Each function must have exactly ONE registration
   (enforced by review; superseded swaps keep their theorems but not the
   attribute), and this module asserts at compile time which replacement
   the compiler will actually use. An import reorder or a stray new
   registration that changes the live kernel FAILS THE BUILD here
   instead of silently reverting performance.

   Wired into `lake test` via AxiomCheck.lean. Not imported by `PP`
   (it pulls the Lean frontend, which library clients don't need). -/

import Lean
import Srtfp.Numeric.Schubfach.Perf.KernelV6
import Srtfp.Numeric.Schubfach.Perf.KernelV13

open Lean Lean.Compiler in
#eval show CoreM Unit from do
  let s := CSimp.ext.getState (← getEnv)
  let check (src tgt : Name) : CoreM Unit := do
    match s.map.find? src with
    | some t =>
      unless t == tgt do
        throwError "csimp pin: {src} compiles to {t}, expected {tgt}"
    | none => throwError "csimp pin: {src} has no csimp replacement"
  -- The two hot entry points of the verified printer.
  check `PP.Numeric.Schubfach.toDecimal `PP.Numeric.Schubfach.toDecimal_v7
  check `PP.Numeric.Schubfach.floatToStrRef `PP.Numeric.Schubfach.toStringFast9
  -- The kernel used by stage-level profiling (BenchProfile).
  check `PP.Numeric.Schubfach.shortestUnsigned `PP.Numeric.Schubfach.shortestUnsigned_v3

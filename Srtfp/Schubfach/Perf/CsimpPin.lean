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
import Srtfp.Schubfach.Perf.KernelV6
import Srtfp.Schubfach.Perf.KernelV13

/- The csimp extension's map values changed type across toolchains
   (`Name` before v4.29-ish, `CSimp.Entry` after), so the check is
   elaborated from syntax in an environment-dependent branch: only the
   applicable variant is ever type-checked. -/
open Lean Elab Command Lean.Compiler in
run_cmd do
  let mapInfo ← getConstInfo `Lean.Compiler.CSimp.State.map
  if mapInfo.type.getUsedConstants.contains `Lean.Compiler.CSimp.Entry then
    elabCommand (← `(#eval show Lean.CoreM Unit from do
      let s := Lean.Compiler.CSimp.ext.getState (← Lean.getEnv)
      let check (src tgt : Lean.Name) : Lean.CoreM Unit := do
        match s.map.find? src with
        | some t =>
          unless t.toDeclName == tgt do
            throwError "csimp pin: {src} compiles to {t.toDeclName}, expected {tgt}"
        | none => throwError "csimp pin: {src} has no csimp replacement"
      check `Srtfp.Schubfach.toDecimal `Srtfp.Schubfach.toDecimal_v7
      check `Srtfp.Schubfach.floatToStrRef `Srtfp.Schubfach.toStringFast9
      check `Srtfp.Schubfach.shortestUnsigned `Srtfp.Schubfach.shortestUnsigned_v3))
  else
    elabCommand (← `(#eval show Lean.CoreM Unit from do
      let s := Lean.Compiler.CSimp.ext.getState (← Lean.getEnv)
      let check (src tgt : Lean.Name) : Lean.CoreM Unit := do
        match s.map.find? src with
        | some t =>
          unless t == tgt do
            throwError "csimp pin: {src} compiles to {t}, expected {tgt}"
        | none => throwError "csimp pin: {src} has no csimp replacement"
      check `Srtfp.Schubfach.toDecimal `Srtfp.Schubfach.toDecimal_v7
      check `Srtfp.Schubfach.floatToStrRef `Srtfp.Schubfach.toStringFast9
      check `Srtfp.Schubfach.shortestUnsigned `Srtfp.Schubfach.shortestUnsigned_v3))

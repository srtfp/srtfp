/- Build-time axiom audit; never imported by the library itself.

   Lean's collector uses cached axiom dependencies for imported declarations.
   Keep the traversal upstream, and select declarations by their defining
   module so private helpers and declarations in other namespaces are covered.
   There are no exceptions for `sorryAx` or native proofs. Source definitions
   must be total and safe; the compiler's recursive helpers are handled below.
   Local runtime replacements must carry equality proofs (`@[csimp]`),
   rather than an unchecked `@[extern]` or `@[implemented_by]` contract. -/
import Srtfp
import Srtfp.Perf
import Srtfp.Perf.CsimpPin
import Lean.Elab.Command
import Lean.Util.CollectAxioms
import Lean.Compiler.ExternAttr
import Lean.Compiler.ImplementedByAttr
import Lean.Compiler.Old

open Lean Elab Command

namespace Test.Audit

/-- Check all declarations defined in the given modules or their submodules.
The only permitted axioms are Lean's standard logical axioms. -/
def checkModules (roots : Array Name) : CommandElabM Unit := do
  let env ← getEnv
  let names := env.constants.fold (init := #[]) fun names name _ =>
    let mod := match env.getModuleIdxFor? name with
      | some i => env.header.moduleNames[i.toNat]!
      | none => env.mainModule
    if roots.any (·.isPrefixOf mod) then names.push name else names
  if names.isEmpty then
    throwError "no declarations found in audit modules {roots}"
  for name in names do
    -- Lean compiles total recursive definitions through partial helpers.
    -- Their parent must be a kernel-checked safe definition, not an opaque
    -- `partial def`. This is part of trusting the upstream compiler.
    let totalRec := (Compiler.isUnsafeRecName? name).any env.isSafeDefinition
    if (env.find? name).any (fun c => c.isUnsafe || (c.isPartial && !totalRec)) then
      throwError "{name} is partial or unsafe"
    if isExtern env name || (Compiler.getImplementedBy? env name).isSome then
      throwError "{name} has an unchecked runtime replacement"
    for ax in ← collectAxioms name do
      unless #[`propext, `Quot.sound, `Classical.choice].contains ax do
        throwError "{name} depends on disallowed axiom {ax}"

end Test.Audit

-- One audit covers both implementations and their word and Float APIs.
run_cmd Test.Audit.checkModules #[`Srtfp]

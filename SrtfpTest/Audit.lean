/- Regression checks for the audit boundary. Each fixture is discarded after
   checking, so the deliberately invalid declarations never enter the library. -/
import SrtfpAudit
import Lean.Elab.Tactic.Decide

open Lean Elab Command

private def rejects (setup : CommandElabM Unit) (reason : String) : CommandElabM Unit :=
  withoutModifyingEnv do
    setup
    try
      SrtfpAudit.checkModules #[(← getEnv).mainModule]
    catch e =>
      if ((← e.toMessageData.toString).splitOn reason).length > 1 then return
      throw e
    throwError "audit accepted a fixture that should fail: {reason}"

-- Valid proofs, including uses of the standard logical axioms, pass.
run_cmd withoutModifyingEnv do
  elabCommand (← `(command| theorem AuditFixture.valid (p : Prop) : p ∨ ¬p := Classical.em p))
  elabCommand (← `(command| def AuditFixture.total : Nat → Nat
    | 0 => 0
    | n + 1 => AuditFixture.total n))
  SrtfpAudit.checkModules #[(← getEnv).mainModule]

-- Module ownership covers declarations outside the Srtfp namespace.
run_cmd rejects (do
  elabCommand (← `(command| axiom OutsideSrtfp.bad : False))) "disallowed axiom"

-- Unused private declarations must also be checked.
run_cmd rejects (do
  elabCommand (← `(command| private axiom AuditFixture.hidden : False))) "disallowed axiom"

#guard_msgs (drop warning) in
run_cmd rejects (do
  elabCommand (← `(command| def AuditFixture.hole : Nat := sorry))) "disallowed axiom sorryAx"

-- An unchecked implementation can disagree with an axiom-free definition.
run_cmd rejects (do
  elabCommand (← `(command| def AuditFixture.replacement : Nat := 1))
  elabCommand (← `(command| @[implemented_by AuditFixture.replacement]
    def AuditFixture.replaced : Nat := 0))) "unchecked runtime replacement"

run_cmd rejects (do
  elabCommand (← `(command| @[extern "srtfp_audit_fixture"]
    def AuditFixture.external : Nat := 0))) "unchecked runtime replacement"

run_cmd rejects (do
  elabCommand (← `(command| partial def AuditFixture.loop (n : Nat) : Nat := AuditFixture.loop n))) "partial or unsafe"

run_cmd rejects (do
  elabCommand (← `(command| unsafe def AuditFixture.unchecked : Nat := 0))) "partial or unsafe"

run_cmd rejects (do
  elabCommand (← `(command| theorem AuditFixture.native : (1 : Nat) = 1 := by native_decide))) "disallowed axiom"

-- None of the rejected fixtures leaked into the environment.
run_cmd SrtfpAudit.checkModules #[(← getEnv).mainModule]

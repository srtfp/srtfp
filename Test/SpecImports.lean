/- Specifications must depend only on upstream Lean and other specification modules. -/
import Srtfp.Text.Spec
import Lean.Elab.Command

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`Srtfp).isPrefixOf mod &&
        !#[`Srtfp.Spec, `Srtfp.DecimalSyntax, `Srtfp.Text.Spec].contains mod then
      throwError "specification imports implementation module: {mod}"

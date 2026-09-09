/- The reference and performance imports must keep the Float bridge optional.
   Check Lean's actual import closure, including indirect imports. -/
import Srtfp
import Srtfp.Perf
import Lean.Elab.Command

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`Srtfp.Bridge).isPrefixOf mod then
      throwError "reference/performance imports reach the optional bridge: {mod}"

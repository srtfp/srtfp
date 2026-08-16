import Srtfp.Schubfach.R20BandSweepDefs

/-! Band-2 kernel `decide` sweeps (parallel-build split). -/

namespace Srtfp.Schubfach.R20Sweep

open Srtfp.Schubfach
open Srtfp.Schubfach (farFromMultipleBelow)

set_option exponentiation.threshold 8192 in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 200000000 in
theorem band2_sweep_0_324 : band2ForRange 0 324 := by unfold band2ForRange; decide

set_option exponentiation.threshold 8192 in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 200000000 in
theorem band2_sweep_324_648 : band2ForRange 324 324 := by unfold band2ForRange; decide

set_option exponentiation.threshold 8192 in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 200000000 in
theorem band2_sweep_648_972 : band2ForRange 648 324 := by unfold band2ForRange; decide

end Srtfp.Schubfach.R20Sweep

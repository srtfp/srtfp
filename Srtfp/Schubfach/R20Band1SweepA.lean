import Srtfp.Schubfach.R20BandSweepDefs

/-! Band-1 kernel `decide` sweeps, first half (parallel-build split). -/

namespace Srtfp.Schubfach.R20Sweep

open Srtfp.Schubfach
open Srtfp.Schubfach (farFromMultipleBelow)

set_option exponentiation.threshold 8192 in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 400000000 in
theorem band1_sweep_1_269 : band1ForRange 1 269 := by unfold band1ForRange; decide

set_option exponentiation.threshold 8192 in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 400000000 in
theorem band1_sweep_270_538 : band1ForRange 270 269 := by unfold band1ForRange; decide


end Srtfp.Schubfach.R20Sweep

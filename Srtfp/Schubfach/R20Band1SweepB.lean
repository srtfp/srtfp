import Srtfp.Schubfach.R20BandSweepDefs

/-! Band-1 kernel `decide` sweeps, second half (parallel-build split). -/

namespace Srtfp.Schubfach.R20Sweep

open Srtfp.Schubfach
open Srtfp.Schubfach (farFromMultipleBelow)

set_option exponentiation.threshold 8192 in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 400000000 in
theorem band1_sweep_539_806 : band1ForRange 539 268 := by unfold band1ForRange; decide

set_option exponentiation.threshold 8192 in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 400000000 in
theorem band1_sweep_807_1074 : band1ForRange 807 268 := by unfold band1ForRange; decide


end Srtfp.Schubfach.R20Sweep

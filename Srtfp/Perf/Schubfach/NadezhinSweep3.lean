module
/- Result 20: kernel sweep over biased exponents 1024..1535
   (one of four modules so they build in parallel). -/
public import Srtfp.Perf.Schubfach.NadezhinDefs

@[expose] public section

namespace Srtfp.Schubfach.R20.Sweep3

set_option exponentiation.threshold 8192 in
set_option maxRecDepth 1000000 in
theorem chunk0 : rangeCheck 1024 64 = true := by decide +kernel

set_option exponentiation.threshold 8192 in
set_option maxRecDepth 1000000 in
theorem chunk1 : rangeCheck 1088 64 = true := by decide +kernel

set_option exponentiation.threshold 8192 in
set_option maxRecDepth 1000000 in
theorem chunk2 : rangeCheck 1152 64 = true := by decide +kernel

set_option exponentiation.threshold 8192 in
set_option maxRecDepth 1000000 in
theorem chunk3 : rangeCheck 1216 64 = true := by decide +kernel

set_option exponentiation.threshold 8192 in
set_option maxRecDepth 1000000 in
theorem chunk4 : rangeCheck 1280 64 = true := by decide +kernel

set_option exponentiation.threshold 8192 in
set_option maxRecDepth 1000000 in
theorem chunk5 : rangeCheck 1344 64 = true := by decide +kernel

set_option exponentiation.threshold 8192 in
set_option maxRecDepth 1000000 in
theorem chunk6 : rangeCheck 1408 64 = true := by decide +kernel

set_option exponentiation.threshold 8192 in
set_option maxRecDepth 1000000 in
theorem chunk7 : rangeCheck 1472 64 = true := by decide +kernel

theorem all : rangeCheck 1024 512 = true :=
  rangeCheck_append 1024 64 448 chunk0 (rangeCheck_append 1088 64 384 chunk1 (rangeCheck_append 1152 64 320 chunk2 (rangeCheck_append 1216 64 256 chunk3 (rangeCheck_append 1280 64 192 chunk4 (rangeCheck_append 1344 64 128 chunk5 (rangeCheck_append 1408 64 64 chunk6 (chunk7)))))))

end Srtfp.Schubfach.R20.Sweep3

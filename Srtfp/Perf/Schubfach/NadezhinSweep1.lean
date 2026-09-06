module
/- Result 20: kernel sweep over biased exponents 0..511
   (one of four modules so they build in parallel). -/
public import Srtfp.Perf.Schubfach.NadezhinDefs

@[expose] public section

namespace Srtfp.Schubfach.R20.Sweep1

set_option exponentiation.threshold 8192 in
set_option maxRecDepth 1000000 in
theorem chunk0 : rangeCheck 0 64 = true := by decide +kernel

set_option exponentiation.threshold 8192 in
set_option maxRecDepth 1000000 in
theorem chunk1 : rangeCheck 64 64 = true := by decide +kernel

set_option exponentiation.threshold 8192 in
set_option maxRecDepth 1000000 in
theorem chunk2 : rangeCheck 128 64 = true := by decide +kernel

set_option exponentiation.threshold 8192 in
set_option maxRecDepth 1000000 in
theorem chunk3 : rangeCheck 192 64 = true := by decide +kernel

set_option exponentiation.threshold 8192 in
set_option maxRecDepth 1000000 in
theorem chunk4 : rangeCheck 256 64 = true := by decide +kernel

set_option exponentiation.threshold 8192 in
set_option maxRecDepth 1000000 in
theorem chunk5 : rangeCheck 320 64 = true := by decide +kernel

set_option exponentiation.threshold 8192 in
set_option maxRecDepth 1000000 in
theorem chunk6 : rangeCheck 384 64 = true := by decide +kernel

set_option exponentiation.threshold 8192 in
set_option maxRecDepth 1000000 in
theorem chunk7 : rangeCheck 448 64 = true := by decide +kernel

theorem all : rangeCheck 0 512 = true :=
  rangeCheck_append 0 64 448 chunk0 (rangeCheck_append 64 64 384 chunk1 (rangeCheck_append 128 64 320 chunk2 (rangeCheck_append 192 64 256 chunk3 (rangeCheck_append 256 64 192 chunk4 (rangeCheck_append 320 64 128 chunk5 (rangeCheck_append 384 64 64 chunk6 (chunk7)))))))

end Srtfp.Schubfach.R20.Sweep1

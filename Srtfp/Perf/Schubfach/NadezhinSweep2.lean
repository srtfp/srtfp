module
/- Result 20: kernel sweep over biased exponents 512..1023
   (one of four modules so they build in parallel). -/
public import Srtfp.Perf.Schubfach.NadezhinDefs

@[expose] public section

namespace Srtfp.Schubfach.R20.Sweep2

set_option exponentiation.threshold 8192 in
set_option maxRecDepth 1000000 in
theorem chunk0 : rangeCheck 512 64 = true := by decide +kernel

set_option exponentiation.threshold 8192 in
set_option maxRecDepth 1000000 in
theorem chunk1 : rangeCheck 576 64 = true := by decide +kernel

set_option exponentiation.threshold 8192 in
set_option maxRecDepth 1000000 in
theorem chunk2 : rangeCheck 640 64 = true := by decide +kernel

set_option exponentiation.threshold 8192 in
set_option maxRecDepth 1000000 in
theorem chunk3 : rangeCheck 704 64 = true := by decide +kernel

set_option exponentiation.threshold 8192 in
set_option maxRecDepth 1000000 in
theorem chunk4 : rangeCheck 768 64 = true := by decide +kernel

set_option exponentiation.threshold 8192 in
set_option maxRecDepth 1000000 in
theorem chunk5 : rangeCheck 832 64 = true := by decide +kernel

set_option exponentiation.threshold 8192 in
set_option maxRecDepth 1000000 in
theorem chunk6 : rangeCheck 896 64 = true := by decide +kernel

set_option exponentiation.threshold 8192 in
set_option maxRecDepth 1000000 in
theorem chunk7 : rangeCheck 960 64 = true := by decide +kernel

theorem all : rangeCheck 512 512 = true :=
  rangeCheck_append 512 64 448 chunk0 (rangeCheck_append 576 64 384 chunk1 (rangeCheck_append 640 64 320 chunk2 (rangeCheck_append 704 64 256 chunk3 (rangeCheck_append 768 64 192 chunk4 (rangeCheck_append 832 64 128 chunk5 (rangeCheck_append 896 64 64 chunk6 (chunk7)))))))

end Srtfp.Schubfach.R20.Sweep2

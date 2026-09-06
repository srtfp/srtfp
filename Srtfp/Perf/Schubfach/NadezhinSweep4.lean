module
/- Result 20: kernel sweep over biased exponents 1536..2045
   (one of four modules so they build in parallel). -/
public import Srtfp.Perf.Schubfach.NadezhinDefs

@[expose] public section

namespace Srtfp.Schubfach.R20.Sweep4

set_option exponentiation.threshold 8192 in
set_option maxRecDepth 1000000 in
theorem chunk0 : rangeCheck 1536 64 = true := by decide +kernel

set_option exponentiation.threshold 8192 in
set_option maxRecDepth 1000000 in
theorem chunk1 : rangeCheck 1600 64 = true := by decide +kernel

set_option exponentiation.threshold 8192 in
set_option maxRecDepth 1000000 in
theorem chunk2 : rangeCheck 1664 64 = true := by decide +kernel

set_option exponentiation.threshold 8192 in
set_option maxRecDepth 1000000 in
theorem chunk3 : rangeCheck 1728 64 = true := by decide +kernel

set_option exponentiation.threshold 8192 in
set_option maxRecDepth 1000000 in
theorem chunk4 : rangeCheck 1792 64 = true := by decide +kernel

set_option exponentiation.threshold 8192 in
set_option maxRecDepth 1000000 in
theorem chunk5 : rangeCheck 1856 64 = true := by decide +kernel

set_option exponentiation.threshold 8192 in
set_option maxRecDepth 1000000 in
theorem chunk6 : rangeCheck 1920 64 = true := by decide +kernel

set_option exponentiation.threshold 8192 in
set_option maxRecDepth 1000000 in
theorem chunk7 : rangeCheck 1984 62 = true := by decide +kernel

theorem all : rangeCheck 1536 510 = true :=
  rangeCheck_append 1536 64 446 chunk0 (rangeCheck_append 1600 64 382 chunk1 (rangeCheck_append 1664 64 318 chunk2 (rangeCheck_append 1728 64 254 chunk3 (rangeCheck_append 1792 64 190 chunk4 (rangeCheck_append 1856 64 126 chunk5 (rangeCheck_append 1920 64 62 chunk6 (chunk7)))))))

end Srtfp.Schubfach.R20.Sweep4

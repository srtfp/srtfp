import LSpec
import Srtfp
import SrtfpAxiomCheck
import SrtfpTest.Ryu
import SrtfpTest.Uint64Kernel
import SrtfpTest.Uint64Kernel192
import SrtfpTest.KernelV13

open LSpec

def main : IO UInt32 :=
  lspecIO (.ofList [
    ("ryu d2s + f2s edge cases", [PP.Numeric.Tests.Ryu.ryuTests]),
    ("schubfach UInt64 kernel runtime cross-check",
      [PP.Numeric.Tests.Uint64Kernel.runTests]),
    ("schubfach kOfMQ_fast / floorLog10_fast runtime cross-check",
      [PP.Numeric.Tests.Uint64Kernel.runFloorLogTests]),
    ("schubfach 192-bit shiftedSig runtime cross-check",
      [PP.Numeric.Tests.Uint64Kernel192.runTests]),
    ("schubfach 192-bit end-to-end shortestUnsigned cross-check",
      [PP.Numeric.Tests.Uint64Kernel192.runEndToEndTests]),
    ("schubfach v13 live-kernel shortestUnsigned cross-check",
      [PP.Numeric.Tests.KernelV13.runTests])
  ]) []

import SrtfpTest.Spec
import Srtfp
import SrtfpAxiomCheck
import SrtfpTest.Ryu
import SrtfpTest.Uint64Kernel
import SrtfpTest.Uint64Kernel192
import SrtfpTest.KernelV13

open SrtfpSpec

def main : IO UInt32 :=
  lspecIO (.ofList [
    ("ryu d2s + f2s edge cases", [Srtfp.Tests.Ryu.ryuTests]),
    ("schubfach UInt64 kernel runtime cross-check",
      [Srtfp.Tests.Uint64Kernel.runTests]),
    ("schubfach kOfMQ_fast / floorLog10_fast runtime cross-check",
      [Srtfp.Tests.Uint64Kernel.runFloorLogTests]),
    ("schubfach 192-bit shiftedSig runtime cross-check",
      [Srtfp.Tests.Uint64Kernel192.runTests]),
    ("schubfach 192-bit end-to-end shortestUnsigned cross-check",
      [Srtfp.Tests.Uint64Kernel192.runEndToEndTests]),
    ("schubfach v13 live-kernel shortestUnsigned cross-check",
      [Srtfp.Tests.KernelV13.runTests])
  ]) []

import SrtfpTest.Spec
import Srtfp
import SrtfpAxiomCheck
import SrtfpTest.Ryu
import SrtfpTest.Kernel
import SrtfpTest.Text
import SrtfpTest.Printer
import SrtfpTest.Reader

open SrtfpSpec

def main : IO UInt32 :=
  lspecIO (.ofList [
    ("ryu d2s + f2s edge cases", [Srtfp.Tests.Ryu.ryuTests]),
    ("live printer kernel, fallback and emitter vs reference scan",
      [Srtfp.Tests.Kernel.runTests]),
    ("text layer round-trip and dialect cross-check",
      [Srtfp.Tests.Text.runRoundTripTests, Srtfp.Tests.Text.runDialectTests]),
    ("reference printer vs live printer", [Srtfp.Tests.Printer.runTests]),
    ("reader: fast kernel and exact fallback vs reference", [Srtfp.Tests.Reader.runTests])
  ]) []

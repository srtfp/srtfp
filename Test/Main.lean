import Test.Harness
import Srtfp
import Test.SpecImports
import Test.Audit
import Test.AuditTests
import Test.FloatRuntime
import Test.Ryu
import Test.Kernel
import Test.Text
import Test.Printer
import Test.Reader

open Test.Harness

def main : IO UInt32 :=
  Suite.run (.ofList [
    ("ryu d2s + f2s edge cases", [Srtfp.Tests.Ryu.ryuTests]),
    ("live printer kernel and emitter vs reference scan",
      [Srtfp.Tests.Kernel.runTests]),
    ("text layer round-trip and dialect cross-check",
      [Srtfp.Tests.Text.runRoundTripTests, Srtfp.Tests.Text.runDialectTests]),
    ("reference printer vs live printer", [Srtfp.Tests.Printer.runTests]),
    ("reader: fast kernel and exact fallback vs reference", [Srtfp.Tests.Reader.runTests])
  ])

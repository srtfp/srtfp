/- Runtime cross-checks for `Srtfp.Text`: the verified round trip
   exercised on a real corpus for every compatible (printer, dialect)
   pair, plus per-dialect accept/reject spot checks mirroring the
   grammar deltas (JSON vs MLIR vs YAML). -/

import Test.Harness
import Test.Ryu
import Srtfp.Text
import Srtfp.Perf.Schubfach
import Srtfp.Perf

namespace Srtfp.Tests.Text

open Test.Harness Srtfp Srtfp.Text

open Srtfp.Tests.Ryu in
private def corpusFloats : Array Float :=
  (d2sBasic ++ d2sSwitchToSubnormal ++ d2sMinAndMax ++ d2sLotsOfTrailingZeros
    ++ d2sRegression ++ d2sLooksLikePow5 ++ d2sOutputLength ++ d2sMinMaxShift
    ++ d2sSmallIntegers).map (fun c => c.2.1)

/-- Canonical decimals: the shortest-printer outputs for the Ryu corpus
    plus hand-picked edges (signed zero, extreme exponents, window
    boundaries). -/
private def corpusDecimals : Array Decimal :=
  corpusFloats.filterMap (fun f =>
    Printer.toDecimal f)
  ++ #[⟨.negative, 0, 0⟩, ⟨.positive, 0, 0⟩, ⟨.positive, 1, 0⟩, ⟨.negative, 15, -1⟩,
       ⟨.positive, 12345678901234567, 100⟩, ⟨.positive, 5, -324⟩, ⟨.negative, 1, 16⟩,
       ⟨.positive, 1, -5⟩, ⟨.positive, 9007199254740993, -22⟩]

/-- A consumer-defined preset (the pattern downstream repos use):
    shortest form with a forced decimal point, suiting dot-requiring
    grammars such as MLIR float literals. -/
private def dotted : FormatOptions := { minFracDigits := 1, sciMinFracDigits := 1 }

private def fmts : Array (String × FormatOptions) :=
  #[("dotted", dotted), ("python", .python), ("js", .js), ("java", .java),
    ("cScientific", .cScientific)]

private def dialects : Array (String × DecimalSyntax) :=
  #[("json", .jsonStrict), ("mlir", .mlir), ("yamlCore", .yamlCore)]

/-- Runtime mirror of `FormatOptions.CompatibleWith`. -/
private def compatB (f : FormatOptions) (p : DecimalSyntax) : Bool :=
  !p.requireDot || (1 ≤ f.minFracDigits && 1 ≤ f.sciMinFracDigits)

def runRoundTripTests : TestSeq := Id.run do
  let mut t : TestSeq := .done
  for (fn, fo) in fmts do
    for (pn, po) in dialects do
      if compatB fo po then
        let ok := corpusDecimals.all (fun d => parse po (format fo d) == some d)
        t := t ++ test s!"{fn} prints, {pn} reparses ({corpusDecimals.size} decimals)" ok
  return t

def runDialectTests : TestSeq :=
  test "dotted format shapes (MLIR-parseable)"
      (format dotted ⟨.positive, 15, -1⟩ == "1.5"
        && format dotted ⟨.positive, 2, 0⟩ == "2.0"
        && format dotted ⟨.positive, 15, 2⟩ == "1500.0"
        && format dotted ⟨.positive, 5, -4⟩ == "0.0005"
        && format dotted ⟨.negative, 0, 0⟩ == "-0.0"
        && format dotted ⟨.positive, 15, 300⟩ == "1.5e301"
        && format dotted ⟨.positive, 1, -7⟩ == "1.0e-7")
    ++ test "python/js/java/C shapes"
      (format .python ⟨.positive, 1, 21⟩ == "1e+21"
        && format .python ⟨.positive, 1, -5⟩ == "1e-05"
        && format .js ⟨.positive, 2, 0⟩ == "2"
        && format .js ⟨.positive, 1, -7⟩ == "1e-7"
        && format .java ⟨.positive, 1, 7⟩ == "1.0E7"
        && format .cScientific ⟨.positive, 2, 0⟩ == "2.000000e+00")
    ++ test "mlir accepts '2.' / '007.5', rejects bare '2'"
      (parse .mlir "2." == some ⟨.positive, 2, 0⟩
        && parse .mlir "007.5" == some ⟨.positive, 75, -1⟩
        && parse .mlir "2" == none)
    ++ test "json rejects '2.' / '00.5' / '.5' / '+1.5'"
      (parse .jsonStrict "2." == none
        && parse .jsonStrict "00.5" == none
        && parse .jsonStrict ".5" == none
        && parse .jsonStrict "+1.5" == none
        && parse .jsonStrict "-0.5" == some ⟨.negative, 5, -1⟩)
    ++ test "yaml accepts '.5' / '+1.5'"
      (parse .yamlCore ".5" == some ⟨.positive, 5, -1⟩
        && parse .yamlCore "+1.5" == some ⟨.positive, 15, -1⟩)
    ++ test "parse canonicalises padding and uppercase exponents"
      (parse .jsonStrict "1.500E2" == some ⟨.positive, 15, 1⟩
        && parse .mlir "2.000000e+00" == some ⟨.positive, 2, 0⟩)
    ++ test "formatting uses the exact notation-window boundaries"
      (format {} ⟨.positive, 1, -5⟩ == "1e-5"
        && format {} ⟨.positive, 1, -4⟩ == "0.0001"
        && format {} ⟨.positive, 1, 15⟩ == "1000000000000000"
        && format {} ⟨.positive, 1, 16⟩ == "1e16")
    ++ test "formatting retains the supplied noncanonical digits and exponent"
      (format {} ⟨.positive, 1500, -3⟩ == "1.500"
        && format {} ⟨.negative, 0, -3⟩ == "-0.000"
        && format {} ⟨.positive, 0, 23⟩ == "0e23")

end Srtfp.Tests.Text

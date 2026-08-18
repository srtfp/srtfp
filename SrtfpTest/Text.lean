/- Runtime cross-checks for `Srtfp.Text`: the verified round trip
   exercised on a real corpus for every compatible (printer, dialect)
   pair, plus per-dialect accept/reject spot checks mirroring the
   grammar deltas (JSON vs MLIR vs YAML). -/

import SrtfpTest.Spec
import SrtfpTest.Ryu
import Srtfp.Text
import Srtfp.Schubfach

namespace Srtfp.Tests.Text

open SrtfpSpec Srtfp Srtfp.Text

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
    match Schubfach.toDecimal f with | .ok d => some d | .error _ => none)
  ++ #[⟨true, 0, 0⟩, ⟨false, 0, 0⟩, ⟨false, 1, 0⟩, ⟨true, 15, -1⟩,
       ⟨false, 12345678901234567, 100⟩, ⟨false, 5, -324⟩, ⟨true, 1, 16⟩,
       ⟨false, 1, -5⟩, ⟨false, 9007199254740993, -22⟩]

private def fmts : Array (String × FormatOptions) :=
  #[("veir", .veir), ("python", .python), ("js", .js), ("java", .java),
    ("cScientific", .cScientific)]

private def dialects : Array (String × DecimalSyntax) :=
  #[("json", .jsonStrict), ("mlir", .mlir), ("yamlCore", .yamlCore),
    ("yaml11", .yaml11)]

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
  test "veir format matches the FloatPrinter shapes"
      (format .veir ⟨false, 15, -1⟩ == "1.5"
        && format .veir ⟨false, 2, 0⟩ == "2.0"
        && format .veir ⟨false, 15, 2⟩ == "1500.0"
        && format .veir ⟨false, 5, -4⟩ == "0.0005"
        && format .veir ⟨true, 0, 0⟩ == "-0.0"
        && format .veir ⟨false, 15, 300⟩ == "1.5e301"
        && format .veir ⟨false, 1, -7⟩ == "1.0e-7")
    ++ test "python/js/java/C shapes"
      (format .python ⟨false, 1, 21⟩ == "1e+21"
        && format .python ⟨false, 1, -5⟩ == "1e-05"
        && format .js ⟨false, 2, 0⟩ == "2"
        && format .js ⟨false, 1, -7⟩ == "1e-7"
        && format .java ⟨false, 1, 7⟩ == "1.0E7"
        && format .cScientific ⟨false, 2, 0⟩ == "2.000000e+00")
    ++ test "mlir accepts '2.' / '007.5', rejects bare '2'"
      (parse .mlir "2." == some ⟨false, 2, 0⟩
        && parse .mlir "007.5" == some ⟨false, 75, -1⟩
        && parse .mlir "2" == none)
    ++ test "json rejects '2.' / '00.5' / '.5' / '+1.5'"
      (parse .jsonStrict "2." == none
        && parse .jsonStrict "00.5" == none
        && parse .jsonStrict ".5" == none
        && parse .jsonStrict "+1.5" == none
        && parse .jsonStrict "-0.5" == some ⟨true, 5, -1⟩)
    ++ test "yaml accepts '.5' / '+1.5'"
      (parse .yamlCore ".5" == some ⟨false, 5, -1⟩
        && parse .yamlCore "+1.5" == some ⟨false, 15, -1⟩)
    ++ test "parse canonicalises padding and uppercase exponents"
      (parse .jsonStrict "1.500E2" == some ⟨false, 15, 1⟩
        && parse .mlir "2.000000e+00" == some ⟨false, 2, 0⟩)

end Srtfp.Tests.Text

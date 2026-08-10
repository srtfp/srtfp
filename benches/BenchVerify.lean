/- Verify cmpScaledMixed_fast2 and shiftedSig_fast2 agree with reference paths. -/

import Srtfp.Schubfach
import Srtfp.Float.Bits
open Srtfp.Schubfach
open Srtfp.Float

def testInputs : Array Float :=
  #[
    1.0, 2.0, 0.1, 0.2, 0.3, 0.1 + 0.2,
    1e10, 1e-10, 1.7976931348623157e308, 5e-324,
    3.14159265358979, 2.718281828459045,
    1.0/3.0, 1.0/7.0, 1.0/11.0,
    42.0, 100.0, 1000.0, 999999.999999,
    1.5, 2.5, 3.5, 4.5
  ]

def main : IO Unit := do
  let mut nCmpMatch : Nat := 0
  let mut nCmpFail : Nat := 0
  let mut nSigMatch : Nat := 0
  let mut nSigFail : Nat := 0
  for f in testInputs do
    let d := decode f
    if d.m = 0 then continue
    let k := kOfMQ d.m d.q
    let sRef := shiftedSig_fast d.m d.q k
    let sNew := shiftedSig_fast2 d.m d.q k
    if sRef == sNew then
      nSigMatch := nSigMatch + 1
    else
      nSigFail := nSigFail + 1
      IO.println s!"sig MISMATCH f={f}: m={d.m} q={d.q} k={k}, ref={sRef}, new={sNew}"
    let s := sRef
    let calls : Array (Int × Int × Int × Int) := #[
      (4 * (d.m : Int) - 2, d.q, 4 * (s : Int), k),
      (4 * (d.m : Int) + 2, d.q, 4 * (s : Int), k),
      (2 * (d.m : Int), d.q, 2 * (s : Int) + 1, k),
      -- Also try with k+1 (the shorter-form path).
      (4 * (d.m : Int) - 2, d.q, 4 * ((s / 10) : Int), k + 1),
      (4 * (d.m : Int) + 2, d.q, 4 * ((s / 10) : Int), k + 1)
    ]
    for (a, q, b, k) in calls do
      let ref := cmpScaledMixed_fast a q b k
      let new := cmpScaledMixed_fast2 a q b k
      if ref == new then
        nCmpMatch := nCmpMatch + 1
      else
        nCmpFail := nCmpFail + 1
        IO.println s!"cmp MISMATCH f={f}: a={a} q={q} b={b} k={k}, ref={ref}, new={new}"
  IO.println s!"cmp: {nCmpMatch} match, {nCmpFail} mismatch"
  IO.println s!"sig: {nSigMatch} match, {nSigFail} mismatch"

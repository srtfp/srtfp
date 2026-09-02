/- Our-printer dumper for differential testing against Ryu.

   Reads decimal `UInt64` bit patterns (one per line) from stdin; for each,
   reconstructs the binary64 via `Float.ofBits` and prints
   "<bits> <floatToStrRef output>".  `floatToStrRef` is the live verified
   Schubfach string printer (the `@[csimp]` chain selects the v13 kernel via
   `KernelV13`).  Paired with `benches/difftest_ryu.cpp` by
   `benches/difftest_ryu.py`. -/
import Srtfp.Perf.KernelV13  -- live floatToStrRef @[csimp] (v13)

open Srtfp.Schubfach (floatToStrRef)

partial def loop (stdin : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return ()          -- EOF
  let t := line.trimAscii
  if t.isEmpty then loop stdin
  else
    match t.toNat? with
    | some n =>
      let bits : UInt64 := UInt64.ofNat n
      IO.println s!"{bits.toNat} {floatToStrRef (Float.ofBits bits)}"
      loop stdin
    | none => loop stdin

def main : IO Unit := do
  loop (← IO.getStdin)

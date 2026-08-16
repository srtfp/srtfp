/- Minimal in-repo test harness.

   Replaces the LSpec dependency: srtfp's suites only ever used
   `TestSeq`, `++`, `test`, and `lspecIO`, and pinning an external
   package across the toolchain matrix (4.27 … 4.33) proved impossible
   (the pinned rev fails to elaborate on ≥4.32). This shim reproduces
   exactly that surface with the same call syntax, so the corpus
   modules are oblivious to the swap — and srtfp now depends on nothing
   beyond the Lean toolchain, test suite included. -/

namespace SrtfpSpec

/-- A flat sequence of labelled boolean checks. -/
inductive TestSeq where
  | done
  | more (label : String) (pass : Bool) (rest : TestSeq)

namespace TestSeq

def append : TestSeq → TestSeq → TestSeq
  | .done, t => t
  | .more l p r, t => .more l p (r.append t)

instance : Append TestSeq := ⟨append⟩

/-- Run a sequence: print one line per check, return `(passed, failed)`. -/
def run (indent : String) : TestSeq → IO (Nat × Nat)
  | .done => pure (0, 0)
  | .more label pass rest => do
    IO.println s!"{indent}{if pass then "✓" else "✗"} {label}"
    let (p, f) ← rest.run indent
    pure (if pass then (p + 1, f) else (p, f + 1))

end TestSeq

/-- A labelled check. Accepts any decidable proposition (`Bool`s coerce). -/
def test (label : String) (p : Prop) [inst : Decidable p] : TestSeq :=
  .more label (decide p) .done

/-- Named groups of test sequences. -/
structure Suite where
  groups : List (String × List TestSeq)

def Suite.ofList (groups : List (String × List TestSeq)) : Suite := ⟨groups⟩

/-- Run every group; exit code 1 iff any check failed. -/
def lspecIO (s : Suite) (_args : List String) : IO UInt32 := do
  let mut passed := 0
  let mut failed := 0
  for (name, seqs) in s.groups do
    IO.println s!"{name}"
    for seq in seqs do
      let (p, f) ← seq.run "  "
      passed := passed + p
      failed := failed + f
    IO.println ""
  IO.println s!"{passed} passed, {failed} failed"
  pure (if failed == 0 then 0 else 1)

end SrtfpSpec

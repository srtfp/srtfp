/- Write the bench corpora as `benches/corpora/<name>.u64`, one decimal
   IEEE-754 word per line, for the C++, Python and Java harnesses. Run
   from the repository root: `lake exe genCorpora`. -/
import Corpora

def main : IO Unit := do
  IO.FS.createDirAll "benches/corpora"
  for (name, xs) in [("adversarial", Corpora.adversarial), ("nice", Corpora.nice),
                     ("uniform", Corpora.uniform)] do
    let lines := xs.toList.map fun f => toString f.toBits
    IO.FS.writeFile s!"benches/corpora/{name}.u64" (String.intercalate "\n" lines ++ "\n")
    IO.println s!"benches/corpora/{name}.u64: {xs.size} entries"

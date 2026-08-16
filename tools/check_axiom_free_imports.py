#!/usr/bin/env python3
"""Fast source-level guard for the two-tier axiom split.

Fails (exit 1) if the default umbrella `Srtfp.lean` — or anything it
transitively imports — reaches `Srtfp.Float.RuntimeAxiom` (the module
declaring the runtime axiom) or any `Srtfp.Bridge.*` module (its
consumers). The environment-level ground truth is
`SrtfpBitsAxiomCheck.lean`; this walk just catches a stray import before
a full build.
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
FORBIDDEN = re.compile(r"^Srtfp\.(Float\.RuntimeAxiom$|Bridge($|\.))")
IMPORT_RE = re.compile(r"^import (Srtfp[\w.]*)", re.M)


def module_path(mod: str) -> Path:
    return ROOT / (mod.replace(".", "/") + ".lean")


def imports_of(mod: str) -> list[str]:
    p = module_path(mod)
    if not p.exists():
        sys.exit(f"error: module {mod} has no file at {p}")
    return IMPORT_RE.findall(p.read_text(encoding="utf-8"))


def main() -> int:
    seen: set[str] = set()
    stack = ["Srtfp"]
    parent: dict[str, str] = {}
    while stack:
        mod = stack.pop()
        if mod in seen:
            continue
        seen.add(mod)
        for dep in imports_of(mod):
            if FORBIDDEN.match(dep):
                chain, cur = [dep, mod], mod
                while cur in parent:
                    cur = parent[cur]
                    chain.append(cur)
                print("AXIOM TIER LEAK: the default umbrella reaches "
                      f"{dep}\n  via: {' <- '.join(chain)}")
                return 1
            if dep not in seen:
                parent[dep] = mod
                stack.append(dep)
    print(f"ok: Srtfp's import closure ({len(seen)} modules) stays clear "
          "of Srtfp.Float.RuntimeAxiom and Srtfp.Bridge.*")
    return 0


if __name__ == "__main__":
    sys.exit(main())

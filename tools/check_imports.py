#!/usr/bin/env python3
"""Fast source-level guard for the optional Float bridge import boundary.

Fails (exit 1) if the default umbrella `Srtfp.lean` or the performance
umbrella `Srtfp/Perf.lean` — or anything they transitively import —
reaches any `Srtfp.Bridge.*` module (the bit round-trip to the runtime
`Float` and its consumers). This walk keeps the Float-quantified API
optional and catches a stray import before a full build. The separate
axiom and runtime-replacement audit lives in `SrtfpAudit.lean`.
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
FORBIDDEN = re.compile(r"^Srtfp\.Bridge(\.|$)")
IMPORT_RE = re.compile(r"^(?:public |meta |public meta )?import (Srtfp[\w.]*)", re.M)


def module_path(mod: str) -> Path:
    return ROOT / (mod.replace(".", "/") + ".lean")


def imports_of(mod: str) -> list[str]:
    p = module_path(mod)
    if not p.exists():
        sys.exit(f"error: module {mod} has no file at {p}")
    return IMPORT_RE.findall(p.read_text(encoding="utf-8"))


def main() -> int:
    seen: set[str] = set()
    stack = ["Srtfp", "Srtfp.Perf"]
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
                print("IMPORT TIER LEAK: a reference/performance umbrella reaches "
                      f"{dep}\n  via: {' <- '.join(chain)}")
                return 1
            if dep not in seen:
                parent[dep] = mod
                stack.append(dep)
    print(f"ok: the Srtfp and Srtfp.Perf import closure ({len(seen)} modules) "
          "stays clear of Srtfp.Bridge.*")
    return 0


if __name__ == "__main__":
    sys.exit(main())

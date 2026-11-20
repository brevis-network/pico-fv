#!/usr/bin/env python3
"""Prints, one per line and sorted, the source path of every PicoFV module that PicoFV64.lean
imports, directly or through other PicoFV modules.

Files under PicoFV/ that nothing imports (parked work, such as the equivalence files while the
CPU chip moves) are left out, so a job that walks this list never asks for a module the build
did not produce.
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
IMPORT = re.compile(r"^import\s+(PicoFV\.[A-Za-z0-9_.]+)", re.MULTILINE)


def main() -> int:
    seen: set[str] = set()
    queue = ["PicoFV64.lean"]
    while queue:
        source = queue.pop()
        for module in IMPORT.findall((ROOT / source).read_text()):
            path = module.replace(".", "/") + ".lean"
            if path in seen:
                continue
            if not (ROOT / path).is_file():
                print(f"imported but missing: {path} (from {source})", file=sys.stderr)
                return 1
            seen.add(path)
            queue.append(path)
    sys.stdout.write("".join(f"{p}\n" for p in sorted(seen)))
    return 0


if __name__ == "__main__":
    sys.exit(main())

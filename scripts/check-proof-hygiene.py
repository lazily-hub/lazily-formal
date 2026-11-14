#!/usr/bin/env python3
"""Proof-hygiene gate for lazily-formal.

`lake build` only elaborates modules reachable from the root `LazilyFormal.lean`,
and a cached build does not re-report `sorry` warnings. This gate makes both
explicit so a green `make check` means every proof file was checked and closed:

* every `LazilyFormal/**/*.lean` module is imported by `LazilyFormal.lean`;
* no source contains `sorry` or `native_decide` (a fast textual pre-check; the
  authoritative check is `scripts/AxiomAudit.lean`, which `make proof-hygiene`
  runs next and which also catches the `admit` tactic and declared axioms).
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
FORBIDDEN = re.compile(r"\b(sorry|native_decide)\b")


def strip_comments(text: str) -> str:
    """Drop `--` line comments and (nested) `/- ... -/` block comments."""
    out: list[str] = []
    depth = 0
    i = 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth:
            out.append("\n" if text[i] == "\n" else " ")
            i += 1
        elif text.startswith("--", i):
            while i < len(text) and text[i] != "\n":
                i += 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def main() -> int:
    root_imports = set(re.findall(r"^import\s+(\S+)", (ROOT / "LazilyFormal.lean").read_text(), re.M))
    failures: list[str] = []
    modules = sorted((ROOT / "LazilyFormal").rglob("*.lean"))
    for path in modules:
        module = ".".join(path.relative_to(ROOT).with_suffix("").parts)
        if module not in root_imports:
            failures.append(f"{path.relative_to(ROOT)}: not imported by LazilyFormal.lean, so `lake build` never checks it")
        code = strip_comments(path.read_text())
        for match in FORBIDDEN.finditer(code):
            line = code.count("\n", 0, match.start()) + 1
            failures.append(f"{path.relative_to(ROOT)}:{line}: forbidden `{match.group(0).strip()}`")
    if failures:
        print("\n".join(failures), file=sys.stderr)
        return 1
    print(f"proof hygiene ok: {len(modules)} modules reachable from the root, no sorry/native_decide")
    return 0


if __name__ == "__main__":
    sys.exit(main())

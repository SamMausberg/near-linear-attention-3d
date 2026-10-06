#!/usr/bin/env python3
"""Build the Lean development and audit its axioms.

Run from this directory after `lake exe cache get`. The script
1. scans the sources for forbidden tokens,
2. runs `lake build` (warnings are errors, see lakefile.toml),
3. runs `AxiomAudit.lean` and checks that every listed theorem depends only on
   `propext`, `Classical.choice`, and `Quot.sound`.
It writes the results to lean-verification.json.
"""
from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = [r"\bsorry\b", r"\badmit\b", r"\baxiom\b", r"\bnative_decide\b",
             r"\bimplemented_by\b", r"\bunsafe\b", r"@\[extern"]


def strip_comments(text: str) -> str:
    """Remove Lean comments and keep every newline, so line numbers are preserved.

    Block comments `/- ... -/` (including `/--` and `/-!`) nest. Line comments run from `--`
    to the end of the line. String literals are copied unchanged.
    """
    out: list[str] = []
    i, n, depth = 0, len(text), 0
    while i < n:
        if depth > 0:
            if text.startswith("/-", i):
                depth, i = depth + 1, i + 2
            elif text.startswith("-/", i):
                depth, i = depth - 1, i + 2
            else:
                if text[i] == "\n":
                    out.append("\n")
                i += 1
        elif text.startswith("/-", i):
            depth, i = 1, i + 2
        elif text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j < 0 else j
        elif text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            out.append(text[i:j + 1])
            i = j + 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def scan() -> list[str]:
    hits = []
    for path in sorted((ROOT / "Attention3D").rglob("*.lean")) + [ROOT / "Attention3D.lean"]:
        text = path.read_text()
        raw = text.splitlines()
        code = strip_comments(text).splitlines()
        for lineno, line in enumerate(code, 1):
            for pattern in FORBIDDEN:
                if re.search(pattern, line):
                    hits.append(f"{path.relative_to(ROOT)}:{lineno}: {raw[lineno - 1].strip()}")
    return hits


def run(cmd: list[str]) -> subprocess.CompletedProcess:
    return subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)


def audit(output: str) -> dict[str, list[str]]:
    result: dict[str, list[str]] = {}
    pattern = re.compile(r"'([^']+)' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)", re.S)
    for name, axioms in pattern.findall(output):
        result[name] = sorted(a.strip() for a in axioms.split(",") if a.strip())
    return result


def main() -> int:
    hits = scan()
    build = run(["lake", "build"])
    audit_run = run(["lake", "env", "lean", "AxiomAudit.lean"])
    axioms = audit(audit_run.stdout)
    listed = len(re.findall(r"^#print axioms", (ROOT / "AxiomAudit.lean").read_text(), re.M))
    bad = {k: v for k, v in axioms.items() if not set(v) <= ALLOWED}
    ok = (not hits and build.returncode == 0 and audit_run.returncode == 0
          and len(axioms) == listed and not bad)
    report = {
        "status": "passed" if ok else "failed",
        "forbidden_tokens": hits,
        "build_returncode": build.returncode,
        "audited_theorems": len(axioms),
        "listed_theorems": listed,
        "axioms": axioms,
        "non_standard": bad,
    }
    (ROOT / "lean-verification.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: report[k] for k in ("status", "audited_theorems", "listed_theorems",
                                              "forbidden_tokens", "non_standard")}, indent=2))
    if build.returncode != 0:
        print(build.stdout[-4000:], file=sys.stderr)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())

#!/usr/bin/env python3
"""Verify final latexmk logs, not transient first-pass warnings.

This is a layout/reference gate, not a proof of mathematical correctness.
"""
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
LOGS = (
    "proposal/proposal.log",
    "slides/topic.log",
    "slides/final.log",
    "paper/paper.log",
)
BAD = {
    "LaTeX error": re.compile(r"!\s+LaTeX Error:|LaTeX Error:"),
    "unresolved reference": re.compile(
        r"There were undefined references|Reference .+ undefined"),
    "unresolved citation": re.compile(
        r"There were undefined citations|Citation .+ undefined"),
    "overfull box": re.compile(r"Overfull \\hbox"),
}
bad = False
for rel in LOGS:
    p = ROOT / rel
    if not p.is_file():
        print(f"FAIL {rel}: final .log missing")
        bad = True
        continue
    content = p.read_text(encoding="utf-8", errors="replace")
    errs = [(name, len(pattern.findall(content)))
            for name, pattern in BAD.items()]
    errs = [(name, n) for name, n in errs if n > 0]
    under = len(re.findall(r"Underfull \\hbox", content))
    if errs:
        print(f"FAIL {rel}: {errs} (underfull informational={under})")
        bad = True
    else:
        print(f"PASS {rel}: no unresolved references, citations, errors or overfull boxes"
              f" (underfull informational={under})")
if bad:
    sys.exit(1)

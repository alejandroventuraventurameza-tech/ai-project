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
# Official issue #7: the body must occupy 8--20 pages, title to conclusion.
# The source emits a marker only AFTER a clearpage flushes pending figures,
# and BEFORE bibliography, so neither references nor appendices are counted.
paper_log = ROOT / "paper/paper.log"
if paper_log.is_file():
    source = paper_log.read_text(encoding="utf-8", errors="replace")
    page_markers = re.findall(r"IE_COMPACT_BODY_PAGES=(\d+)", source)
    if not page_markers:
        print("FAIL paper: compact body page marker missing")
        bad = True
    else:
        body_pages = int(page_markers[-1])
        if not 8 <= body_pages <= 20:
            print(f"FAIL paper: compact body has {body_pages} pages (required: 8--20)")
            bad = True
        else:
            print(f"PASS paper: compact body has {body_pages} pages (required: 8--20)")
if bad:
    sys.exit(1)

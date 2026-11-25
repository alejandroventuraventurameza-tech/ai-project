#!/usr/bin/env bash
# Build only the eight-result final-paper candidate.
# Does not execute Lean or all numerical IRF checks.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT/paper"

for src in paper.tex body_compact_intro.tex body_compact_after.tex \
           appendix_eight_results.tex references.bib irf_impact_table.tex \
           irf_mechanism_table.tex figures/irf_transmission.pdf \
           figures/irf_real_allocation.pdf; do
  if [ ! -s "$src" ]; then
    printf 'ERROR: missing or empty source %s\n' "$src" >&2
    exit 2
  fi
done

pdflatex -interaction=nonstopmode -halt-on-error -file-line-error paper.tex
bibtex paper
pdflatex -interaction=nonstopmode -halt-on-error -file-line-error paper.tex
pdflatex -interaction=nonstopmode -halt-on-error -file-line-error paper.tex

printf '\n=== COMPACT BODY PAGE COUNT ===\n'
grep 'IE_COMPACT_BODY_PAGES=' paper.log | tail -n 1

printf '\n=== HARD WARNINGS TO REVIEW ===\n'
grep -Ei 'undefined references|undefined citation|citation.*undefined|overfull \\hbox|LaTeX Error' paper.log || true

printf '\n=== PDF INFORMATION ===\n'
pdfinfo paper.pdf | grep -E 'Pages:|Page size:|File size:' || true

printf '\nIMPORTANT: a successful compile is not a complete Lean or economic-equilibrium proof.\n'

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
if command -v bibtex >/dev/null 2>&1; then
  bibtex paper
elif command -v bibtex8 >/dev/null 2>&1; then
  bibtex8 paper
else
  echo 'ERROR: neither bibtex nor bibtex8 found' >&2
  exit 3
fi
pdflatex -interaction=nonstopmode -halt-on-error -file-line-error paper.tex
pdflatex -interaction=nonstopmode -halt-on-error -file-line-error paper.tex

printf '\n=== COMPACT BODY PAGE COUNT ===\n'
body_pages="$(sed -n 's/.*IE_COMPACT_BODY_PAGES=\([0-9][0-9]*\).*/\1/p' paper.log | tail -n 1)"
if [ -z "$body_pages" ]; then
  echo 'ERROR: missing IE_COMPACT_BODY_PAGES in paper.log' >&2
  exit 4
fi
if [ "$body_pages" -lt 8 ] || [ "$body_pages" -gt 20 ]; then
  printf 'ERROR: %s body pages (allowed 8..20)\n' "$body_pages" >&2
  exit 4
fi
printf 'Body pages: %s (required 8..20)\n' "$body_pages"

printf '\n=== UNRESOLVED REFERENCES AND OVERFULL BOXES ===\n'
if grep -Ei 'undefined references|Citation.*undefined|overfull \\hbox|LaTeX Error' paper.log; then
  echo 'ERROR: blocking warning in final LaTeX log' >&2
  exit 5
fi
echo 'No blocking warnings.'

printf '\n=== PDF INFORMATION ===\n'
if command -v pdfinfo >/dev/null 2>&1; then
  pdfinfo paper.pdf | grep -E 'Pages:|Page size:|File size:'
else
  echo 'pdfinfo unavailable; body page count verified via TeX log'
fi
printf '\n=== PDF SHA-256 ===\n'
sha256sum paper.pdf

echo 'Important: LaTeX compilation is not a proof of economic equilibrium.'

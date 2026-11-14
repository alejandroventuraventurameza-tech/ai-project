#!/usr/bin/env python3
"""Audit scientific scope of the two main conditional IRF propositions.

Checks consistency between the current LaTeX manuscript, slides, the
versioned result ledger and the formal counterexample to literal
Allocation uniqueness. It does not certify the propositions themselves.
No third-party packages or data are needed.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PAPER = ROOT / "paper/paper.tex"
SLIDES = ROOT / "slides/final.tex"
LEDGER = ROOT / "paper/result_ledger.json"
LEAN_REFUTATION = ROOT / (
    "lean/candidates/Ventura26LiquidityAllocation/"
    "Proposition42RefutationCandidate.lean"
)
LEAN_REPAIR = ROOT / (
    "lean/candidates/Ventura26LiquidityAllocation/"
    "Proposition42PrimalRepairCandidate.lean"
)
LEAN_SCALAR = ROOT / (
    "lean/candidates/Ventura26LiquidityAllocation/"
    "ScalarComplementarityMultiplicityCandidate.lean"
)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def raw_claim(paper: str, label: str, title: str) -> str:
    begin = "\\begin{proposition}[" + title + "]\\label{" + label + "}"
    require(paper.count(begin) == 1, f"Missing/duplicate proposition: {label}")
    start = paper.index(begin)
    ending = "\\end{proof}"
    finish = paper.index(ending, start) + len(ending)
    require(finish - start < 5000, f"Unexpected proposition length: {label}")
    return paper[start:finish]


def main() -> None:
    paper = PAPER.read_text(encoding="utf-8")
    slides = SLIDES.read_text(encoding="utf-8")
    ledger = json.loads(LEDGER.read_text(encoding="utf-8"))
    require(ledger["paper_sha256"] == hashlib.sha256(PAPER.read_bytes()).hexdigest(),
            "Stale paper SHA256 in result ledger")
    results = ledger["results"]
    require(len(results) == 57, "57-result ledger cardinality changed")
    rows = {row["label"]: row for row in results}
    require(len(rows) == len(results), "Duplicate result labels")
    expected = {
        "prop:local_macro_multiplicity":
            "Dos soluciones locales de la complementariedad reducida",
        "prop:risky_branch_persistence":
            "Persistencia condicional de ramas reducidas bajo riesgo",
    }
    for label, title in expected.items():
        require(label in rows, f"Result disappeared: {label}")
        row = rows[label]
        raw = raw_claim(paper, label, title)
        digest = hashlib.sha256(raw.encode("utf-8")).hexdigest()
        require(row.get("current_proposition_and_proof_raw_tex_sha256") == digest,
                f"Revised proposition/proof SHA256 drift: {label}")
        require(row.get("scope_review") ==
                "conditional_reduced_not_full_competitive_equilibrium",
                f"Scope flag changed: {label}")
        require(row["formalization_status"] == "not_run",
                f"Unsupported Lean coverage claim: {label}")
        require("reducid" in raw.lower(), f"Reduced scope missing: {label}")
        require("condicional" in raw.lower() or "suponga" in raw.lower(),
                f"Conditional hypotheses missing: {label}")
        require("existen exactamente dos equilibrios" not in raw.lower(),
                f"Full equilibrium claimed without proof: {label}")

    require("BoundaryWorkerLaborPackage" in paper,
            "Missing the explicit unresolved date-zero labor FOC")
    require("collateralDual" in paper,
            "Missing the formal uniqueness obstruction")
    require("localMacroMultiplicitySpec_false" in LEAN_REFUTATION.read_text(),
            "Lean refutation source not found")
    require("localMacroMultiplicityPrimalSpec" in LEAN_REPAIR.read_text(),
            "Primal repair interface not found")
    require("scalar_complementarity_exactly_two" in LEAN_SCALAR.read_text(),
            "Conditional scalar lemma not found")
    require("La objeción formal a la unicidad literal" in slides,
            "Lean scope slide removed")
    require("exactamente dos soluciones escalares" in slides,
            "Complementarity proof slide removed")
    require(slides.count("\\begin{frame}") == slides.count("\\end{frame}"),
            "Slides frames mismatched")
    require(ledger.get("editorial_scope_revision", {}).get("status") ==
            "conditional_reduced",
            "Ledger no longer distinguishes reduced from full equilibrium")

    out = {
        "status": "pass_editorial_scope_consistency_only",
        "revision_note": "No theorem certification: compiled kernel and full economic correspondence require independent checking.",
        "numbered_claims": len(results),
        "conditional_scoped_claims": list(expected),
        "paper_sha256": ledger["paper_sha256"],
        "lean_literal_spec_refuted_not_economic_claim": True,
        "full_infinite_equilibrium_proved": False,
    }
    print(json.dumps(out, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Audit a 57-row *scope* crosswalk. Not a formal theorem-equivalence checker.

This gate catches missing paper claims, stale paper/ledger hashes, dangling
Lean declaration references, and false promotion of evidence status.
A present Lean `theorem` declaration is only a syntactic link; the exact
economic statement, its hypotheses, and its mathlib proof must be reviewed
independently before promoting any claim to integrated formal coverage.
"""
from __future__ import annotations

import hashlib
import json
import re
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LEDGER = ROOT / "paper" / "result_ledger.json"
CROSSWALK = ROOT / "paper" / "lean_crosswalk_57.json"
PAPER = ROOT / "paper" / "paper.tex"
ALLOWED_REVIEW_STATES = {
    "targeted_semantic_comparison",
    "not_yet_semantically_reviewed",
}
ALLOWED_RELATIONS = {
    "auxiliary_or_conditional_only",
    "counterexample_to_stronger_literal_interface",
    "source_financial_proof_related",
    "unproved_source_specification",
    "exact_interface_claim_candidate_ci_pending",
    "corrected_economic_claim_ci_pending",
    "counterexample_to_malformed_literal_interface",
}
EXPECTED_EXACT_CANDIDATES = {
    "lem:repayment": "exact_repaymentSpec",
    "lem:v0m_original_6_2": "exact_noSimultaneousSavingBorrowingSpec",
    "prop:v0m_original_6_3": "exact_financingCapacityComparativeSpec",
}


def require(ok: bool, why: str) -> None:
    if not ok:
        raise AssertionError(why)


def main() -> None:
    ledger = json.loads(LEDGER.read_text(encoding="utf-8"))
    data = json.loads(CROSSWALK.read_text(encoding="utf-8"))
    paper_hash = hashlib.sha256(PAPER.read_bytes()).hexdigest()
    require(ledger["paper_sha256"] == paper_hash,
            "Source manuscript drifted from result ledger.")
    require(data["paper_sha256"] == paper_hash,
            "Lean crosswalk stale: update after paper changes.")
    require(data["schema"] == "ie-paper-lean-crosswalk-v1",
            "Unexpected crosswalk version.")
    require(data["claim_count"] == 57, "Crosswalk metadata count changed.")
    require(len(ledger["results"]) == len(data["entries"]) == 57,
            "Missing/added numbered claims.")
    labels = [row["label"] for row in data["entries"]]
    require(len(set(labels)) == 57, "Duplicate crosswalk label.")
    original = {row["label"]: row for row in ledger["results"]}
    require(set(labels) == set(original), "Crosswalk label set differs from paper.")
    reviewed = 0
    related = 0
    refutations = 0
    exact_candidates = {}
    source_specifications = 0
    corrected_candidates = {}
    malformed_interface_refutations = {}
    for row in data["entries"]:
        label = row["label"]
        old = original[label]
        for key in ("paper_number", "title"):
            require(row[key] == old[key], f"{label}: stale {key}")
        require(row["paper_statement_sha256"] == old["statement_sha256"],
                f"{label}: source proposition changed, review required")
        require(row["source_ledger_formalization_status"] ==
                old["formalization_status"] == "not_run",
                f"{label}: formalization status unsupported by current audit")
        require(row["paper_proof_equivalent_in_lean"] == "not_established",
                f"{label}: unverified equivalence asserted")
        state = row["review_state"]
        require(state in ALLOWED_REVIEW_STATES, f"{label}: invalid review state")
        evidence = row["related_lean_declarations"]
        require(isinstance(evidence, list), f"{label}: related links must be list")
        require(bool(row.get("semantic_gap")), f"{label}: no semantic gap note")
        if state == "not_yet_semantically_reviewed":
            require(not evidence, f"{label}: evidence without semantic review")
        else:
            reviewed += 1
            require(evidence, f"{label}: reviewed but no referenced theorem")
        for item in evidence:
            related += 1
            rel = item.get("relationship")
            require(rel in ALLOWED_RELATIONS,
                    f"{label}: invalid theorem relation {rel}")
            if rel == "counterexample_to_stronger_literal_interface":
                refutations += 1
            if rel == "exact_interface_claim_candidate_ci_pending":
                require(label in EXPECTED_EXACT_CANDIDATES,
                        f"{label}: cannot self-designate an exact proof candidate")
                require(item["declaration"] == EXPECTED_EXACT_CANDIDATES[label],
                        f"{label}: wrong literal PaperInterface theorem")
                require(label not in exact_candidates,
                        f"{label}: multiple exact proof candidates")
                exact_candidates[label] = item["declaration"]
            if rel == "corrected_economic_claim_ci_pending":
                require(label == "lem:funding_supergradient",
                        "Wrong corrected claim mapping")
                require(item["declaration"] == "corrected_fundingSupergradientSpec",
                        "Wrong corrected 3.5 theorem reference")
                require(label not in corrected_candidates,
                        "Duplicate corrected 3.5 theorem")
                corrected_candidates[label] = item["declaration"]
            if rel == "counterexample_to_malformed_literal_interface":
                require(label == "lem:funding_supergradient",
                        "Malformed Spec counterexample on wrong result")
                require(item["declaration"] == "original_fundingSupergradientSpec_false",
                        "Wrong 3.5 counterexample")
                require(label not in malformed_interface_refutations,
                        "Duplicate malformed interface refutation")
                malformed_interface_refutations[label] = item["declaration"]
            if rel == "unproved_source_specification":
                source_specifications += 1
            require(bool(item.get("note")), f"{label}: no evidence scope note")
            p = ROOT / item["relative_path"]
            permitted_roots = (
                ROOT / "lean" / "candidates" / "Ventura26LiquidityAllocation",
                ROOT / "lean" / "checkpoint" / "modules"
                / "Ventura26LiquidityAllocation",
            )
            require(p.is_file() and p.suffix == ".lean"
                    and p.parent in permitted_roots,
                    f"{label}: missing or untrusted Lean file {p}")
            decl = item["declaration"]
            require(re.fullmatch(r"[a-zA-Z][A-Za-z0-9_']*", decl) is not None,
                    f"{label}: invalid theorem name")
            src = p.read_text(encoding="utf-8")
            require(re.search(r"^\s*(?:theorem|lemma|def|noncomputable def)\s+"
                              + re.escape(decl) + r"\b", src, re.M) is not None,
                    f"{label}: theorem name not found in {p}")
        for target in row.get("numerical_context", []):
            require((ROOT / target).is_file(),
                    f"{label}: missing numerical evidence {target}")
    require(refutations == 1, "Expected exactly one literal specification refutation.")
    require(exact_candidates == EXPECTED_EXACT_CANDIDATES,
            f"Wrong set of pending literal proof candidates: {exact_candidates}")
    require(corrected_candidates == {
        "lem:funding_supergradient": "corrected_fundingSupergradientSpec"
    }, f"Wrong corrected 3.5 theorem: {corrected_candidates}")
    require(malformed_interface_refutations == {
        "lem:funding_supergradient": "original_fundingSupergradientSpec_false"
    }, f"Wrong malformed interface counterexample: {malformed_interface_refutations}")
    require(original["prop:local_macro_multiplicity"].get("scope_review") ==
            "conditional_reduced_not_full_competitive_equilibrium",
            "Proposition 4.2 must remain explicitly reduced/conditional")
    require(data["entries"][labels.index("prop:local_macro_multiplicity")]
            ["paper_proof_equivalent_in_lean"] == "not_established",
            "Proposition 4.2 is not formally matched yet.")
    print(json.dumps({
        "status": "PASS_SYNTAX_AND_SCOPE_ONLY_NOT_EQUIVALENCE",
        "numbered_paper_claims": len(labels),
        "targeted_semantic_comparisons": reviewed,
        "not_yet_reviewed": len(labels) - reviewed,
        "related_declaration_pointers": related,
        "literal_spec_refutations": refutations,
        "exact_paper_interface_candidates_still_pending_lean_ci": len(exact_candidates),
        "corrected_economic_financial_theorems_pending_ci": len(corrected_candidates),
        "malformed_pinned_interface_refutations_pending_ci": len(malformed_interface_refutations),
        "unproved_source_specifications": source_specifications,
        "complete_paper_theorems_proved_in_lean_by_this_audit": 0,
        "full_equilibrium_confirmed": False,
    }, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()

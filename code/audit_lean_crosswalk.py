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
    "exact_interface_claim_kernel_verified",
    "corrected_economic_claim_kernel_verified",
    "counterexample_malformed_interface_kernel_verified",
    "auxiliary_claim_kernel_verified",
    "efficiency_support_kernel_verified",
    "source_algebra_kernel_verified",
    "source_labor_kernel_verified",
    "original_labor_kernel_verified",
}
GREEN_SOURCE_FINANCIAL_RUN = 42457259796
GREEN_SOURCE_FINANCIAL_SHA = "c006e00c437243c3f6f44ec3c102df4286c545e0"
GREEN_REPAYMENT_RUN = 42458034938
GREEN_REPAYMENT_SHA = "acc4263a2c60c6ec3a90c3331aef9cb522e4427a"
GREEN_LOSS_AUX_RUN = 42458449121
GREEN_LOSS_AUX_SHA = "1e797f886dea03a6fdea135338e6408a3e8ab91b"
GREEN_EFFICIENCY_RUN = 42459394970
GREEN_EFFICIENCY_SHA = "8e883b7993f39d29ae431c44a6a14e45ca55707d"
GREEN_SOURCE_BRIDGE_RUN = 42459648021
GREEN_SOURCE_BRIDGE_SHA = "aef180ba9595e426c32236a2941731837151fdcc"
GREEN_SOURCE_LABOR_RUN = 42500091118
GREEN_SOURCE_LABOR_SHA = "e9ec2024da991768115ecb70e39acdfb647f8b9a"
GREEN_ORIGINAL_LABOR_RUN = 42500721984
GREEN_ORIGINAL_LABOR_SHA = "548911a4b763f8d75ad635338d27752253d71231"
EXPECTED_VERIFIED_ORIGINAL_LABOR = {
    "original_two_type_labor_global_bound",
    "original_labor_candidate_attains_global_bound",
}
EXPECTED_VERIFIED_SOURCE_LABOR = {
    "source_weight_pow_identity",
    "source_output_at_weighted_labor",
    "positive_labor_aggregate_power",
    "source_two_type_output_at_optimal_labor",
    "source_labor_candidate_clears_resources",
    "normalized_labor_global_bound",
    "source_output_with_scaled_labor",
    "source_two_type_global_labor_optimality",
    "source_labor_global_bound_attained",
}
EXPECTED_VERIFIED_SOURCE_BRIDGE = {
    "productivity_weight_recovers_A",
    "positive_aggregate_loss_log_formula",
}
EXPECTED_VERIFIED_EFFICIENCY = {
    "normalized_two_type_output_le_benchmark",
    "normalized_benchmark_attained",
    "normalized_log_loss_nonneg",
    "efficient_candidate_clears_resources",
}
EXPECTED_VERIFIED_LOSS_AUX = {
    "allocation_loss_log_differential_algebra",
    "output_share_gt_capital_share_iff_productivity",
    "loss_direction_negative_of_reallocation",
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
    green_exact = {}
    green_corrected = {}
    green_refutations = {}
    green_loss_aux = set()
    green_efficiency_aux = set()
    green_source_bridge = set()
    green_source_labor = set()
    green_original_labor = set()
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
            if rel == "source_algebra_kernel_verified":
                require(label == "lem:allocation_loss_identity",
                        "Source power/log bridge attached to wrong paper lemma")
                require(item["declaration"] in EXPECTED_VERIFIED_SOURCE_BRIDGE,
                        "Unknown source power/log bridge theorem")
                require(item["declaration"] not in green_source_bridge,
                        "Duplicate power/log source bridge theorem")
                require(item.get("lean_ci_run_id") == GREEN_SOURCE_BRIDGE_RUN
                        and item.get("lean_ci_commit") == GREEN_SOURCE_BRIDGE_SHA
                        and item.get("lean_axiom_audit") == "passed_no_sorryAx",
                        "Power/log source theorem not pinned to green kernel run")
                green_source_bridge.add(item["declaration"])
            if rel == "source_labor_kernel_verified":
                require(label == "lem:allocation_loss_identity",
                        "Original micro-output/labor theorem attached to wrong claim")
                require(item["declaration"] in EXPECTED_VERIFIED_SOURCE_LABOR,
                        "Unknown physical production/labor theorem")
                require(item["declaration"] not in green_source_labor,
                        "Duplicate verified source labor theorem")
                require(item.get("lean_ci_run_id") == GREEN_SOURCE_LABOR_RUN
                        and item.get("lean_ci_commit") == GREEN_SOURCE_LABOR_SHA
                        and item.get("lean_axiom_audit") == "passed_no_sorryAx",
                        "Physical production/labor theorem not pinned to exact green run")
                green_source_labor.add(item["declaration"])
            if rel == "original_labor_kernel_verified":
                require(label == "lem:allocation_loss_identity",
                        "Arbitrary original labor theorem attached to wrong claim")
                require(item["declaration"] in EXPECTED_VERIFIED_ORIGINAL_LABOR,
                        "Unknown arbitrary original labor theorem")
                require(item["declaration"] not in green_original_labor,
                        "Duplicate original labor theorem")
                require(item.get("lean_ci_run_id") == GREEN_ORIGINAL_LABOR_RUN
                        and item.get("lean_ci_commit") == GREEN_ORIGINAL_LABOR_SHA
                        and item.get("lean_axiom_audit") == "passed_no_sorryAx",
                        "Original labor theorem not pinned to the exact green run")
                green_original_labor.add(item["declaration"])
            if rel == "efficiency_support_kernel_verified":
                require(label == "lem:allocation_loss_identity",
                        "Efficiency support theorem mapped to wrong source claim")
                require(item["declaration"] in EXPECTED_VERIFIED_EFFICIENCY,
                        "Unexpected normalized efficiency theorem promoted")
                require(item["declaration"] not in green_efficiency_aux,
                        "Duplicate verified efficiency-support theorem")
                require(item.get("lean_ci_run_id") == GREEN_EFFICIENCY_RUN
                        and item.get("lean_ci_commit") == GREEN_EFFICIENCY_SHA
                        and item.get("lean_axiom_audit") == "passed_no_sorryAx",
                        "Efficiency theorem missing its exact green Lean run")
                green_efficiency_aux.add(item["declaration"])
            if rel == "auxiliary_claim_kernel_verified":
                require(label == "lem:allocation_loss_identity",
                        "Loss auxiliary theorem attached to wrong claim")
                require(item["declaration"] in EXPECTED_VERIFIED_LOSS_AUX,
                        "Unexpected loss auxiliary theorem promoted")
                require(item["declaration"] not in green_loss_aux,
                        "Duplicate verified loss auxiliary theorem")
                require(item.get("lean_ci_run_id") == GREEN_LOSS_AUX_RUN
                        and item.get("lean_ci_commit") == GREEN_LOSS_AUX_SHA
                        and item.get("lean_axiom_audit") == "passed_no_sorryAx",
                        "Loss auxiliary theorem not pinned to verified Lean run")
                green_loss_aux.add(item["declaration"])
            if rel in ("exact_interface_claim_candidate_ci_pending",
                       "exact_interface_claim_kernel_verified"):
                require(label in EXPECTED_EXACT_CANDIDATES,
                        f"{label}: cannot self-designate an exact proof candidate")
                require(item["declaration"] == EXPECTED_EXACT_CANDIDATES[label],
                        f"{label}: wrong literal PaperInterface theorem")
                require(label not in exact_candidates,
                        f"{label}: multiple exact proof candidates")
                exact_candidates[label] = item["declaration"]
                if rel == "exact_interface_claim_kernel_verified":
                    green_exact[label] = item["declaration"]
            if rel in ("corrected_economic_claim_ci_pending",
                       "corrected_economic_claim_kernel_verified"):
                require(label == "lem:funding_supergradient",
                        "Wrong corrected claim mapping")
                require(item["declaration"] == "corrected_fundingSupergradientSpec",
                        "Wrong corrected 3.5 theorem reference")
                require(label not in corrected_candidates,
                        "Duplicate corrected 3.5 theorem")
                corrected_candidates[label] = item["declaration"]
                if rel == "corrected_economic_claim_kernel_verified":
                    green_corrected[label] = item["declaration"]
            if rel in ("counterexample_to_malformed_literal_interface",
                       "counterexample_malformed_interface_kernel_verified"):
                require(label == "lem:funding_supergradient",
                        "Malformed Spec counterexample on wrong result")
                require(item["declaration"] == "original_fundingSupergradientSpec_false",
                        "Wrong 3.5 counterexample")
                require(label not in malformed_interface_refutations,
                        "Duplicate malformed interface refutation")
                malformed_interface_refutations[label] = item["declaration"]
                if rel == "counterexample_malformed_interface_kernel_verified":
                    green_refutations[label] = item["declaration"]
            if rel in (
                "exact_interface_claim_kernel_verified",
                "corrected_economic_claim_kernel_verified",
                "counterexample_malformed_interface_kernel_verified",
            ):
                expected_run, expected_sha = (
                    (GREEN_REPAYMENT_RUN, GREEN_REPAYMENT_SHA)
                    if label == "lem:repayment"
                    else (GREEN_SOURCE_FINANCIAL_RUN, GREEN_SOURCE_FINANCIAL_SHA)
                )
                require(item.get("lean_ci_run_id") == expected_run,
                        f"{label}: unrecognized green Lean run")
                require(item.get("lean_ci_commit") == expected_sha,
                        f"{label}: pinned theorem commit mismatch")
                require(item.get("lean_axiom_audit") == "passed_no_sorryAx",
                        f"{label}: source proof not shown axiom-audited")
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
    require(green_loss_aux == EXPECTED_VERIFIED_LOSS_AUX,
            f"Loss auxiliary proof set incomplete: {green_loss_aux}")
    require(green_efficiency_aux == EXPECTED_VERIFIED_EFFICIENCY,
            f"Global efficiency proof set incomplete: {green_efficiency_aux}")
    require(green_source_bridge == EXPECTED_VERIFIED_SOURCE_BRIDGE,
            f"Source power/log proof set incomplete: {green_source_bridge}")
    require(green_source_labor == EXPECTED_VERIFIED_SOURCE_LABOR,
            f"Physical production/conditional labor proof set incomplete: {green_source_labor}")
    require(green_original_labor == EXPECTED_VERIFIED_ORIGINAL_LABOR,
            f"Arbitrary original labor proof set incomplete: {green_original_labor}")
    require(green_exact == {
        "lem:repayment": "exact_repaymentSpec",
        "lem:v0m_original_6_2": "exact_noSimultaneousSavingBorrowingSpec",
        "prop:v0m_original_6_3": "exact_financingCapacityComparativeSpec",
    }, f"Wrong kernel-verified exact source claims: {green_exact}")
    require(green_corrected == {
        "lem:funding_supergradient": "corrected_fundingSupergradientSpec"
    }, f"Wrong verified corrected funding theorem: {green_corrected}")
    require(green_refutations == {
        "lem:funding_supergradient": "original_fundingSupergradientSpec_false"
    }, f"Wrong verified refutation: {green_refutations}")
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
        "exact_source_interfaces_kernel_verified": len(green_exact),
        "exact_source_interfaces_pending_lean_ci": len(exact_candidates) - len(green_exact),
        "corrected_economic_financial_theorems_kernel_verified": len(green_corrected),
        "malformed_source_specifications_kernel_refuted": len(green_refutations),
        "verified_financial_run": GREEN_SOURCE_FINANCIAL_RUN,
        "verified_repayment_run": GREEN_REPAYMENT_RUN,
        "verified_loss_auxiliary_run": GREEN_LOSS_AUX_RUN,
        "verified_loss_auxiliary_lemmas": len(green_loss_aux),
        "verified_global_efficiency_run": GREEN_EFFICIENCY_RUN,
        "verified_global_efficiency_lemmas": len(green_efficiency_aux),
        "verified_source_power_log_run": GREEN_SOURCE_BRIDGE_RUN,
        "verified_source_power_log_lemmas": len(green_source_bridge),
        "verified_source_labor_run": GREEN_SOURCE_LABOR_RUN,
        "verified_source_labor_lemmas": len(green_source_labor),
        "verified_original_labor_run": GREEN_ORIGINAL_LABOR_RUN,
        "verified_original_labor_lemmas": len(green_original_labor),
        "unproved_source_specifications": source_specifications,
        "complete_paper_theorems_proved_in_lean_by_this_audit": 0,
        "full_equilibrium_confirmed": False,
    }, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()

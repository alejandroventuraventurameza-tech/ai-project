#!/usr/bin/env python3
"""Create an official schema-v1 source statement spec for the compact IE paper.

This builder pins the original 16-page PDF by Git blob and SHA-256, and locates
all eight exact original LaTeX statements in frozen Git blobs. Its Lean types
are extracted without modification from the independently kernel-tested
provisional PaperInterface, except for implicit universe syntax in A.1.2.

A successful source-byte/structure check is NOT a completed semantic audit:
dependent definitions still require atom-by-atom source-to-Spec review.
"""
from __future__ import annotations

import hashlib
import json
import pathlib
import re
import subprocess
import sys

from stage_eight_paper_interface import EXPECTED, PAPER, SOURCE_SHA

PDF_PATH = "paper/paper.pdf"
PDF_GIT_BLOB = "45207cd36ab8a316b4fa4f157f62e2610311ead5"
PDF_SHA256 = "923b766624491e7f7b290c4302332140cd5636fe421ab27c7d4024377db7d2e3"
PDF_BYTES = 519368
VERSION = f"compact-8-results-2026-11-26@{SOURCE_SHA}"

TYPES = (
    ("p31", "Proposition 3.1", "proposition", "theorem"),
    ("p51", "Proposition 5.1", "proposition", "theorem"),
    ("l52", "Lemma 5.2", "lemma", "lemma"),
    ("p53", "Proposition 5.3", "proposition", "theorem"),
    ("a11", "Lemma A.1.1", "lemma", "lemma"),
    ("a12", "Lemma A.1.2", "lemma", "lemma"),
    ("a13", "Proposition A.1.3", "proposition", "theorem"),
    ("a14", "Lemma A.1.4", "lemma", "lemma"),
)

SCOPE_CAVEATS = {
    "prop:local_macro_multiplicity":
        "C1 scalar complementarity is proven; no SOURCE-33 recovery or infinite-equilibrium theorem",
    "prop:compact_exact_tail_power":
        "Exact decay applies to pinned 6x6 decimal F0; no SOURCE Jacobian identity",
    "lem:compact_robust_tail_power":
        "Uniform bound applies to matrices within the explicit 1e-4 radius; no SOURCE proximity",
    "prop:compact_source_collateral_effective_wedge":
        "Conditional effective-price identity; no equilibrium branch or welfare statement",
    "lem:repayment":
        "Statewise robust collateral and nonnegative net worth; not bank solvency",
    "lem:v0m_original_6_2":
        "Finite-support expectation and necessary interior FOCs; not arbitrary probability spaces",
    "prop:v0m_original_6_3":
        "Attainable feasible capacity and partial interest-rate derivative; not optimal investment",
    "lem:allocation_loss_identity":
        "Physical two-firm allocation with optimal labor and pathwise derivative; not DSGE equilibrium",
}


def git_text(root: pathlib.Path, *args: str) -> str:
    return subprocess.check_output(["git", *args], cwd=root, text=True)


def git_bytes(root: pathlib.Path, *args: str) -> bytes:
    return subprocess.check_output(["git", *args], cwd=root)


def lean_type(name: str) -> tuple[str, bool]:
    """Read the transparent type verbatim from the proven provisional interface."""
    regex = r"(?m)^def " + re.escape(name) + r"Spec(?:\.\{u\})? : Prop :=\s*"
    occurrences = list(re.finditer(regex, PAPER))
    if len(occurrences) != 1:
        raise ValueError(f"{name}: expected one transparent Spec, got {len(occurrences)}")
    tail = PAPER[occurrences[0].end():]
    boundaries = [i for term in ("\n\n/--", "\n\nend Ventura26LiquidityAllocation")
                  if (i := tail.find(term)) >= 0]
    if not boundaries:
        raise ValueError(f"{name}: missing next declaration boundary")
    typ = tail[:min(boundaries)].strip()
    # The official source-spec renderer generates a def without an explicit
    # universe binder. The underlying finite-support Prop is polymorphic.
    generalized = name == "a12"
    if generalized:
        assert typ == "CurrentCompact.noSimultaneousInteriorCurrentSpec.{u}"
        typ = "CurrentCompact.noSimultaneousInteriorCurrentSpec"
    if not typ or "/-" in typ or "-/" in typ or "sorry" in typ:
        raise ValueError(f"{name}: unsafe Lean type")
    return typ, generalized


def main() -> None:
    if len(sys.argv) != 3:
        raise SystemExit("usage: build_eight_statement_spec.py AI_PROJECT OUTPUT_DIR")
    project, output = (pathlib.Path(a).resolve() for a in sys.argv[1:])
    if not (project / ".git").exists():
        raise SystemExit("project must be a Git checkout")
    output.mkdir(parents=True, exist_ok=True)
    inventory = json.loads(
        (project / "lean/current_paper_source_inventory_8.json").read_text(encoding="utf-8"))
    if inventory["source_main_sha"] != SOURCE_SHA:
        raise ValueError("paper snapshot SHA changed")
    labels = tuple(c["label"] for c in inventory["claims"])
    if labels != EXPECTED or len(set(labels)) != 8:
        raise ValueError("wrong paper source labels")

    blob = git_text(project, "rev-parse", f"{SOURCE_SHA}:{PDF_PATH}").strip()
    if blob != PDF_GIT_BLOB:
        raise ValueError(f"frozen original PDF Git blob changed: {blob}")
    pdf = git_bytes(project, "show", f"{SOURCE_SHA}:{PDF_PATH}")
    actual_sha = hashlib.sha256(pdf).hexdigest()
    if actual_sha != PDF_SHA256 or len(pdf) != PDF_BYTES:
        raise ValueError("frozen source PDF SHA256 or byte length differs")
    if not pdf.startswith(b"%PDF-") or b"%%EOF" not in pdf[-64:]:
        raise ValueError("invalid PDF header or footer")
    pdf_output = output / "source-paper-8.pdf"
    pdf_output.write_bytes(pdf)
    print(f"SOURCE_PDF_GIT_BLOB_SHA256_BYTES_OK:{blob}:{actual_sha}:{len(pdf)}")

    targets = []
    provenance = []
    for c, (name, title, source_kind, kind) in zip(inventory["claims"], TYPES, strict=True):
        path = c["source_path"]
        latex = c["statement_latex"]
        original = git_text(project, "show", f"{SOURCE_SHA}:{path}")
        frozen_blob = git_text(project, "rev-parse", f"{SOURCE_SHA}:{path}").strip()
        if frozen_blob != c["source_git_blob"]:
            raise ValueError(f"frozen source blob changed for {c['label']}")
        if original.count(latex) != 1:
            raise ValueError(f"exact LaTeX statement not uniquely found for {c['label']}")
        start_line = original[:original.index(latex)].count("\n") + 1
        typ, generalized = lean_type(name)
        # Upstream new_paper.py uses an IGNORECASE placeholder regex for
        # English TODO, which accidentally matches ordinary Spanish "todo".
        # Keep every original byte and its digest in the independent ledger.
        # Only the official parser-facing field receives a declared, strictly
        # meaning-preserving normalization ("Para todo" -> "Para cada").
        parser_text = latex
        normalized = False
        if c["label"] == "prop:compact_exact_tail_power":
            if latex.count("Para todo") != 1:
                raise ValueError("unexpected Proposicion 5.1 source phrase")
            parser_text = latex.replace("Para todo", "Para cada", 1)
            normalized = True
        if parser_text.count("Para cada") > 1 and normalized:
            raise ValueError("unexpected repeated normalization")
        targets.append({
            "source_item": title,
            "source_kind": source_kind,
            "source_location": f"{path}:{start_line}",
            "source_statement": parser_text,
            "lean_name": name,
            "lean_type": typ,
            "kind": kind,
        })
        provenance.append({
            "label": c["label"],
            "parser_text_normalized_for_upstream_false_positive": normalized,
            "parser_normalization": "Para todo -> Para cada" if normalized else None,
            "original_statement_verbatim": latex,
            "original_statement_matches_spec_field": not normalized,
            "git_source_path": path,
            "git_source_blob": frozen_blob,
            "source_first_line": start_line,
            "latex_sha256": hashlib.sha256(latex.encode("utf-8")).hexdigest(),
            "lean_spec_type_sha256": hashlib.sha256(typ.encode("utf-8")).hexdigest(),
            "current_scope": SCOPE_CAVEATS[c["label"]],
            "source_to_spec_independent_semantic_audit": "PENDING",
            "universe_implicit_generalization": generalized,
        })
    spec = {
        "schema": 1,
        "source_artifact_path": "source-paper-8.pdf",
        "source_artifact_sha256": PDF_SHA256,
        "source_version": VERSION,
        "targets": targets,
    }
    (output / "statement-spec-8.json").write_text(
        json.dumps(spec, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    record = {
        "schema": 1,
        "status": "source-and-type-structural-check-only",
        "source_pdf_git_sha1": PDF_GIT_BLOB,
        "source_pdf_sha256": PDF_SHA256,
        "source_main_sha": SOURCE_SHA,
        "target_count": len(targets),
        "targets": provenance,
        "certifies_equilibrium": False,
        "passed_independent_source_to_spec_audit": False,
        "official_full_closeout_passed": False,
    }
    (output / "statement-spec-provenance.json").write_text(
        json.dumps(record, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print("EIGHT_EXACT_LATEX_STATEMENTS_AND_GIT_BLOBS_OK")
    print("EIGHT_SOURCE_STATEMENT_SPEC_SCHEMA_V1_EMITTED")
    print("UPSTREAM_TODO_SPANISH_FALSE_POSITIVE_NORMALIZATION_DOCUMENTED")
    print("SEMANTIC_SOURCE_TO_SPEC_AUDIT_PENDING")


if __name__ == "__main__":
    main()

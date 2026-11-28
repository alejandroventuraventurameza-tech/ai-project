#!/usr/bin/env python3
"""Generate a Lean *definitional-equivalence* audit of three compatibility aliases.

Inputs: frozen 8-statement explicit types, independent existing source proof
modules and the literal finite-support lemma body. A success certifies the
EXACT Lean-definitional equality in the current formal language; it does NOT
establish the independent source-to-model semantic correspondence.

This script generates proof obligations but NEVER certifies their success.
Only the pinned GitHub Actions Lean kernel can do that.
"""
from __future__ import annotations

import hashlib
import json
import pathlib
import sys
import textwrap

from build_eight_statement_spec import (
    PDF_SHA256,
    SOURCE_SHA,
    lean_type,
)

ROOTS = {
    "p51": "CurrentPaperSource.prop51AllSourceClauses",
    "l52": "CurrentCompact.lemma52_decimal_current_spec",
    "a12": "CurrentCompact.noSimultaneousInteriorCurrentSpec.{0}",
}

LEAN_HEADER = """import Ventura26LiquidityAllocation.CurrentPaperSourceCompleteProp51
import Ventura26LiquidityAllocation.CurrentCompactRobustFiniteCertificate
import Ventura26LiquidityAllocation.PostDeadlineCurrentPaperFive

/-!
Postdeadline, proof-carrying type-expansion audit for the three aliases
admitted by the upstream official-new compatibility interface.

Source scientific text: ai-project@bac3c6255da39cd1169a965df35bb5e9a230e6e8.
The finite-support W : Type 0 specialization MUST NOT be interpreted as
proving the article's claim on general probability spaces.
-/

open scoped NNReal Matrix Matrix.Norms.Operator Topology

namespace Ventura26LiquidityAllocation
namespace SourceToSpecDefeqAudit
"""


def indent_expr(expr: str) -> str:
    return textwrap.indent(expr.rstrip(), "  ")


def lemma_a12_body(project: pathlib.Path) -> tuple[str, str]:
    path = project / (
        "lean/candidates/Ventura26LiquidityAllocation/"
        "CurrentCompactInteriorKKT.lean"
    )
    source = path.read_text(encoding="utf-8")
    marker = "def noSimultaneousInteriorCurrentSpec : Prop :=\n"
    if source.count(marker) != 1:
        raise AssertionError("finite-support source definition not unique")
    body = source.split(marker, 1)[1].split("\n\n/--", 1)[0].rstrip()
    assert body.count("∀ {W : Type*} [Fintype W]") == 1
    assert "∑ w : W, probability w" in body
    assert "0 < probability w → 0 < marginalValue w" in body
    assert "lambda = entrepreneurDiscount *" in body
    assert body.endswith("False")
    return body.replace("∀ {W : Type*} [Fintype W]",
                        "∀ {W : Type 0} [Fintype W]", 1), hashlib.sha256(
                            body.encode("utf-8")).hexdigest()


def main() -> None:
    if len(sys.argv) != 3:
        raise SystemExit("usage: audit_eight_expanded_aliases.py AI_PROJECT OUTPUT_DIR")
    project, output = (pathlib.Path(x).resolve() for x in sys.argv[1:])
    output.mkdir(parents=True, exist_ok=True)
    inventory = json.loads(
        (project / "lean/current_paper_source_inventory_8.json").read_text(
            encoding="utf-8"))
    assert inventory["source_main_sha"] == SOURCE_SHA
    assert len(inventory["claims"]) == 8
    assert inventory["claims"][1]["label"] == "prop:compact_exact_tail_power"
    assert inventory["claims"][2]["label"] == "lem:compact_robust_tail_power"
    assert inventory["claims"][5]["label"] == "lem:v0m_original_6_2"

    p51, p51_generalized = lean_type("p51")
    l52, l52_generalized = lean_type("l52")
    a12, a12_generalized = lean_type("a12")
    assert not p51_generalized and not l52_generalized and a12_generalized
    assert "exactDecimalF0 ^ 48" in p51 and "r < 48" in p51
    assert "‖A - CurrentCompact.exactDecimalF0‖" in l52
    assert a12 == "CurrentCompact.noSimultaneousInteriorCurrentSpec"
    a12_finite, a12_original_sha = lemma_a12_body(project)
    assert "Type 0" in a12_finite and "Fintype W" in a12_finite
    assert not any(s in a12_finite for s in ("sorry", "admit", "axiom"))

    lean_text = LEAN_HEADER + (
        "\n/-- All 3 original mathematical clauses of Proposition 5.1. -/\n"
        "def p51Explicit : Prop :=\n" + indent_expr(p51) + "\n\n"
        "/-- Full 6x6 matrix-radius and transient clauses of Lemma 5.2. -/\n"
        "def l52Explicit : Prop :=\n" + indent_expr(l52) + "\n\n"
        "/-- Expansion of the finite-support FOC hypothesis in A.1.2.\n"
        "This deliberately DOES NOT claim arbitrary probability spaces. -/\n"
        "def a12FiniteExplicit : Prop :=\n" + indent_expr(a12_finite) + "\n\n"
        "/-- Definitional, not merely logically deduced, equality: P5.1. -/\n"
        "theorem p51_expanded_defeq :\n"
        "    p51Explicit = CurrentPaperSource.prop51AllSourceClauses := by\n"
        "  rfl\n\n"
        "/-- Definitional equality between L5.2 explicit and compatibility spec. -/\n"
        "theorem l52_expanded_defeq :\n"
        "    l52Explicit = CurrentCompact.lemma52_decimal_current_spec := by\n"
        "  rfl\n\n"
        "/-- A1.2 definitional equality at universe 0: finite state support. -/\n"
        "theorem a12_finite_expanded_defeq :\n"
        "    a12FiniteExplicit = CurrentCompact.noSimultaneousInteriorCurrentSpec.{0} := by\n"
        "  rfl\n\n"
        "/-- Original explicit P5.1 conclusion directly closed by existing proof. -/\n"
        "theorem p51_explicit_proved : p51Explicit := by\n"
        "  exact CurrentPaperSource.prop51AllSourceClauses_proved\n\n"
        "/-- Original explicit L5.2 conclusion directly closed by existing proof. -/\n"
        "theorem l52_explicit_proved : l52Explicit := by\n"
        "  exact CurrentCompact.lemma52_decimal_current_exact\n\n"
        "/-- Finite-support A1.2, specialized to ordinary Type 0. -/\n"
        "theorem a12_finite_explicit_proved : a12FiniteExplicit := by\n"
        "  exact PostDeadlineCurrentPaperFive.lemma_A12_interior_FOC_paper.{0}\n\n"
        "#print axioms p51_expanded_defeq\n"
        "#print axioms l52_expanded_defeq\n"
        "#print axioms a12_finite_expanded_defeq\n"
        "#print axioms p51_explicit_proved\n"
        "#print axioms l52_explicit_proved\n"
        "#print axioms a12_finite_explicit_proved\n\n"
        "end SourceToSpecDefeqAudit\n"
        "end Ventura26LiquidityAllocation\n"
    )
    lean = output / "SourceToSpecDefeqAudit.lean"
    lean.write_text(lean_text, encoding="utf-8")
    receipt = {
        "schema": "ie-eight-transparent-alias-defeq-test-v1",
        "status": "proof-obligations-generated-not-executed",
        "scientific_source_commit": SOURCE_SHA,
        "source_pdf_sha256": PDF_SHA256,
        "a12_finite_def_source_sha256": a12_original_sha,
        "targets": {
            "p51": {"literal_source_type_sha256": hashlib.sha256(
                p51.encode("utf-8")).hexdigest(),
                "alias": ROOTS["p51"], "proof": "p51_expanded_defeq"},
            "l52": {"literal_source_type_sha256": hashlib.sha256(
                l52.encode("utf-8")).hexdigest(),
                "alias": ROOTS["l52"], "proof": "l52_expanded_defeq"},
            "a12": {"finite_support_source_type_sha256": a12_original_sha,
                "alias": ROOTS["a12"], "proof": "a12_finite_expanded_defeq",
                "restriction": "finite-support Type 0, not arbitrary probability spaces"},
        },
        "formal_proofs_kernel_verified": False,
        "independent_source_to_expanded_spec_semantic_certification": False,
        "source33_equilibrium_recovery_proved": False,
    }
    (output / "defeq-proof-obligations.json").write_text(
        json.dumps(receipt, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8")
    print("THREE_LITERAL_COMPATIBILITY_ALIAS_PROOFS_GENERATED")
    print("A12_FINITE_SUPPORT_ORIGINAL_BODY_EXPANDED_WITH_UNIVERSE_ZERO")
    print("SOURCE_TO_LIBRARY_SEMANTIC_AUDIT_STILL_PENDING")


if __name__ == "__main__":
    main()

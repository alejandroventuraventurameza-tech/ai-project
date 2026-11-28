#!/usr/bin/env python3
"""Promote the provisional eight-paper package through OFFICIAL new --statement-spec.

Run only in an isolated checkout of pinned AppliedModelingLib. This script
uses its public new_paper.py schema/Lean renderer and then replaces GENERATED
sorry draft endpoints with the eight previously kernel-proved theorems.

This is structural source/Lean elaboration, NOT an independent v11 semantic
audit, a full closeout, or a proof of the SOURCE-33 equilibrium.
"""
from __future__ import annotations

import hashlib
import json
import pathlib
import re
import subprocess
import sys

from build_eight_statement_spec import PDF_SHA256, VERSION
from stage_eight_paper_interface import PROOFS, REPO

OFFICIAL_FOLDER = "Ventura26LiquidityAllocationEight"

SOURCE_NAMES = ("p31", "p51", "l52", "p53", "a11", "a12", "a13", "a14")

ROOT_IMPORTS = """import Ventura26LiquidityAllocation.CurrentCompactProp31C1Bridge
import Ventura26LiquidityAllocation.CurrentPaperSourceCompleteProp51
import Ventura26LiquidityAllocation.CurrentCompactRobustFiniteCertificate
import Ventura26LiquidityAllocation.PostDeadlineCurrentPaperFive
"""


def run(argv: list[str], cwd: pathlib.Path) -> None:
    print("+", " ".join(argv), flush=True)
    subprocess.run(argv, cwd=cwd, check=True)


def main() -> None:
    if len(sys.argv) != 4:
        raise SystemExit(
            "usage: stage_official_eight_statement_spec.py AI_PROJECT UPSTREAM SPEC_DIR")
    project, upstream, specdir = (pathlib.Path(p).resolve() for p in sys.argv[1:])
    if not (upstream / "papers" / REPO / "ProofInterface.lean").exists():
        raise ValueError("first run the provisional stage_eight_paper_interface.py")
    spec_path = specdir / "statement-spec-8.json"
    source_path = specdir / "source-paper-8.pdf"
    if not spec_path.exists() or not source_path.exists():
        raise ValueError("missing frozen PDF / schema-v1 statement spec")
    if hashlib.sha256(source_path.read_bytes()).hexdigest() != PDF_SHA256:
        raise ValueError("wrong original PDF bytes")

    # Preserve the exact, explicit source-facing types in statement-spec-8.json.
    # The stock upstream renderer validates isolated spec fragments without
    # inheriting the Matrix.Norms.Operator / Matrix notation scopes, and cannot
    # infer a Type* universe level from a bare reference in a Prop definition.
    # For this *compatibility-only* generator smoke test, replace those three
    # opaque-in-isolation type spellings with transparent, kernel-proved source
    # declarations. This is NOT a v11 source-to-expanded-Spec audit receipt.
    original_spec = json.loads(spec_path.read_text(encoding="utf-8"))
    targets = original_spec["targets"]
    assert len(targets) == 8
    assert [t["lean_name"] for t in targets] == list(SOURCE_NAMES)
    assert "exactDecimalF0 ^ 48" in targets[1]["lean_type"]
    assert "r < 48" in targets[1]["lean_type"]
    assert "‖A - CurrentCompact.exactDecimalF0‖" in targets[2]["lean_type"]
    assert targets[5]["lean_type"] == (
        "CurrentCompact.noSimultaneousInteriorCurrentSpec"
    )
    compatibility_aliases = {
        "p51": "CurrentPaperSource.prop51AllSourceClauses",
        "l52": "CurrentCompact.lemma52_decimal_current_spec",
        "a12": "CurrentCompact.noSimultaneousInteriorCurrentSpec.{0}",
    }
    for target in targets:
        if target["lean_name"] in compatibility_aliases:
            target["lean_type"] = compatibility_aliases[target["lean_name"]]
    compat_path = specdir / "statement-spec-8-official-compat.json"
    compat_path.write_text(
        json.dumps(original_spec, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )
    (specdir / "official-compatibility-aliases.json").write_text(
        json.dumps(
            {
                "status": "experimental-generator-compatibility-only",
                "exact_literal_types_preserved_at": spec_path.name,
                "stock_upstream_scoped_instance_gap": True,
                "stock_upstream_universe_generalization_gap": True,
                "aliases": compatibility_aliases,
                "independent_source_to_expanded_spec_certification": False,
                "full_closeout": False,
            },
            indent=2,
        ) + "\n",
        encoding="utf-8",
    )
    print("SOURCE_EXPLICIT_TYPE_SNAPSHOT_PRESERVED_UNCHANGED", flush=True)
    print("OFFICIAL_GENERATOR_THREE_ALIAS_COMPATIBILITY_DECLARED", flush=True)

    root = upstream / "AppliedModelingLib.lean"
    original_root = root.read_text(encoding="utf-8")
    if ROOT_IMPORTS.strip().splitlines()[0] in original_root:
        raise ValueError("temporary upstream root has already been patched")
    # Fast, isolated type-check shim: the original broad upstream root is
    # intentionally not compiled; all paper dependencies are imported here.
    # The pinned upstream Git checkout itself remains unchanged on disk.
    assert "import AppliedModelingLib.Basic" in original_root
    root.write_text(ROOT_IMPORTS + "\n", encoding="utf-8")
    print("PINNED_UPSTREAM_ROOT_EXPOSES_SOURCE_PROOF_TYPES", flush=True)

    # The official generator checks its proof-spec surface by compiling
    # import AppliedModelingLib; its pinned upstream compatibility root
    # does not normally import paper-specific candidate definitions.
    # Add only these imports in the ephemeral checkout and compile the root.
    run(["lake", "build", "AppliedModelingLib"], upstream)
    print("UPSTREAM_ROOT_WITH_TEMPORARY_PAPER_TYPE_IMPORTS_BUILT", flush=True)

    # The upstream CLI condenses Lean errors to the FIRST four lines.
    # If warnings precede a real error, that hides the actionable message.
    # Expand error reporting in this disposable checkout ONLY; do not
    # change the verifier, generated types, or success criteria.
    upstream_generator = upstream / "scripts/new_paper.py"
    generator_text = upstream_generator.read_text(encoding="utf-8")
    old_excerpt = 'excerpt = " ".join(details[:4])[:800]'
    assert generator_text.count(old_excerpt) == 1
    upstream_generator.write_text(
        generator_text.replace(
            old_excerpt, 'excerpt = " ".join(details[-60:])[:10000]', 1
        ), encoding="utf-8"
    )
    print("UPSTREAM_GENERATOR_ERROR_DIAGNOSTICS_ONLY_EXPANDED", flush=True)

    url = (
        "https://github.com/alejandroventuraventurameza-tech/ai-project/blob/"
        "bac3c6255da39cd1169a965df35bb5e9a230e6e8/paper/paper.pdf"
    )
    run([
        "python3", "scripts/paper_contribution.py", "new", url,
        "--folder", OFFICIAL_FOLDER,
        "--namespace", REPO,
        "--title", "Financial frictions, policy corridor, and capital allocation",
        "--authors", "Alejandro Ventura",
        "--version", VERSION,
        "--statement-spec", str(compat_path),
        "--no-download"
    ], upstream)

    out = upstream / "papers" / OFFICIAL_FOLDER
    exact_source = out / "source-audited.pdf"
    if not exact_source.is_file():
        raise AssertionError("official generated source-audited.pdf missing")
    if hashlib.sha256(exact_source.read_bytes()).hexdigest() != PDF_SHA256:
        raise AssertionError("official generated source PDF not byte-pinned")

    paper = (out / "PaperInterface.lean").read_text(encoding="utf-8")
    proof = (out / "ProofInterface.lean").read_text(encoding="utf-8")
    for name in SOURCE_NAMES:
        if paper.count("def " + name + "Spec : Prop :=") != 1:
            raise AssertionError(f"official-generated missing or duplicate {name}Spec")
        if not re.search(
            rf"\b(?:theorem|lemma)\s+{re.escape(name)}\s*:\s*"
            rf"{re.escape(name)}Spec\s*:=\s*by\s+sorry\b", proof
        ):
            raise AssertionError(
                f"official-generated draft proof endpoint {name} missing"
            )
    for alias in compatibility_aliases.values():
        if alias not in paper:
            raise AssertionError(f"official-generated compatibility alias missing: {alias}")
    print("OFFICIAL_GENERATED_ALIASES_REQUIRE_INDEPENDENT_EXPANSION_REVIEW", flush=True)

    # Generated MainTheorems initially imports Mathlib only; the eight
    # pinned source definitions are imported from this ephemeral supporting
    # module so the generated human-facing PaperInterface stays unchanged.
    main_path = out / "MainTheorems.lean"
    main_original = main_path.read_text(encoding="utf-8")
    assert main_original.startswith("import Mathlib\n")
    main_path.write_text(ROOT_IMPORTS + "\n" + main_original, encoding="utf-8")
    print("GENERATED_SUPPORT_IMPORTS_OF_PINNED_THEOREMS_RELINKED", flush=True)

    closed_proofs = PROOFS.replace(
        f"import {REPO}.PaperInterface",
        f"import {OFFICIAL_FOLDER}.PaperInterface", 1)
    if closed_proofs == PROOFS:
        raise AssertionError("proof interface import path was not rewritten")

    # The compatibility interface fixes the finite state universe at 0
    # (ordinary Type0), so this one endpoint must specialize the already
    # polymorphic theorem without changing its mathematical proof.
    old_a12 = "theorem a12.{u} : a12Spec.{u} :="
    assert closed_proofs.count(old_a12) == 1
    closed_proofs = closed_proofs.replace(
        old_a12, "theorem a12 : a12Spec :=", 1
    )
    (out / "ProofInterface.lean").write_text(closed_proofs.lstrip(), encoding="utf-8")
    print(f"OFFICIAL_FRESH_FOLDER:{OFFICIAL_FOLDER}", flush=True)
    print("OFFICIAL_GENERATED_PAPER_INTERFACE_PRESERVED", flush=True)
    print("OFFICIAL_GENERATED_SORRY_ENDPOINTS_REPLACED_BY_EIGHT_ACTUAL_PROOFS", flush=True)
    print("OFFICIAL_NEW_STATEMENT_SPEC_EIGHT_SUCCEEDED", flush=True)
    print("CAVEAT: no independent v11 source-to-Spec realization audit; no full closeout",
          flush=True)


if __name__ == "__main__":
    main()

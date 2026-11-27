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
import pathlib
import subprocess
import sys

from build_eight_statement_spec import PDF_SHA256, VERSION
from stage_eight_paper_interface import MAIN, PROOFS, REPO

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

    root = upstream / "AppliedModelingLib.lean"
    original_root = root.read_text(encoding="utf-8")
    if ROOT_IMPORTS.strip().splitlines()[0] in original_root:
        raise ValueError("temporary upstream root has already been patched")
    root.write_text(ROOT_IMPORTS + "\n" + original_root, encoding="utf-8")
    print("PINNED_UPSTREAM_ROOT_EXPOSES_SOURCE_PROOF_TYPES", flush=True)

    # The official generator checks its proof-spec surface by compiling
    # import AppliedModelingLib; its pinned upstream compatibility root
    # does not normally import paper-specific candidate definitions.
    # Add only these imports in the ephemeral checkout and compile the root.
    run(["lake", "build", "AppliedModelingLib"], upstream)
    print("UPSTREAM_ROOT_WITH_TEMPORARY_PAPER_TYPE_IMPORTS_BUILT", flush=True)

    url = (
        "https://github.com/alejandroventuraventurameza-tech/ai-project/blob/"
        "bac3c6255da39cd1169a965df35bb5e9a230e6e8/paper/paper.pdf"
    )
    run([
        "python3", "scripts/paper_contribution.py", "new", url,
        "--folder", REPO,
        "--namespace", REPO,
        "--title", "Financial frictions, policy corridor, and capital allocation",
        "--authors", "Alejandro Ventura",
        "--version", VERSION,
        "--statement-spec", str(spec_path),
        "--no-download", "--force"
    ], upstream)

    out = upstream / "papers" / REPO
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
        if name + "Spec := by sorry" not in proof:
            raise AssertionError(f"official-generated draft proof endpoint {name} missing")
    if "exactDecimalF0 ^ 48" not in paper or "r < 48" not in paper:
        raise AssertionError("official-generated Proposition 5.1 omitted source bounds")

    (out / "MainTheorems.lean").write_text(MAIN.lstrip(), encoding="utf-8")
    (out / "ProofInterface.lean").write_text(PROOFS.lstrip(), encoding="utf-8")
    print("OFFICIAL_GENERATED_PAPER_INTERFACE_PRESERVED", flush=True)
    print("OFFICIAL_GENERATED_SORRY_ENDPOINTS_REPLACED_BY_EIGHT_ACTUAL_PROOFS", flush=True)
    print("OFFICIAL_NEW_STATEMENT_SPEC_EIGHT_SUCCEEDED", flush=True)
    print("CAVEAT: no independent v11 source-to-Spec realization audit; no full closeout",
          flush=True)


if __name__ == "__main__":
    main()

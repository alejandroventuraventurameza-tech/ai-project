#!/usr/bin/env python3
"""Stage an isolated *provisional* 8-result paper interface in a pinned upstream clone.

This smoke-test generator does not assert full paper-source semantic closeout.
Four derived Specs currently refer to transparent CurrentCompact definitions,
pending independent source-atom review. Never replace a public submission with
this temporary stage or report --fast as full AppliedModelingLib certification.
"""
from __future__ import annotations

import json
import pathlib
import shutil
import subprocess
import sys

REPO = "Ventura26LiquidityAllocation"
SOURCE_SHA = "bac3c6255da39cd1169a965df35bb5e9a230e6e8"
EXPECTED = (
    "prop:local_macro_multiplicity",
    "prop:compact_exact_tail_power",
    "lem:compact_robust_tail_power",
    "prop:compact_source_collateral_effective_wedge",
    "lem:repayment",
    "lem:v0m_original_6_2",
    "prop:v0m_original_6_3",
    "lem:allocation_loss_identity",
)

MAIN = r"""
import Ventura26LiquidityAllocation.CurrentCompactProp31C1Bridge
import Ventura26LiquidityAllocation.CurrentCompactBlock48Tail
import Ventura26LiquidityAllocation.CurrentCompactRobustFiniteCertificate
import Ventura26LiquidityAllocation.PostDeadlineCurrentPaperFive

/-! Existing source-pinned mathematical definitions and proof modules.
No new economic equation or assumption is introduced in this staging shim. -/
"""

PAPER = r"""
import Ventura26LiquidityAllocation.MainTheorems
import Ventura26LiquidityAllocation.Assumptions

/-!
Provisional human-facing 8-result interface, 27 Nov 2026.
Source paper: ai-project@bac3c6255da39cd1169a965df35bb5e9a230e6e8.

The expressions below are proof-obligation types, NOT a completed source-atom
semantic audit. In particular, the last five except A.1.4 refer to transparent
Core/CurrentCompact Specs; their formulas and paper-source matching still
require independent source-to-Spec review.
-/

open scoped NNReal Matrix Matrix.Norms.Operator Topology

namespace Ventura26LiquidityAllocation

/-- Proposition 3.1, conditional SCALAR C1 result; no recovered SOURCE economy. -/
def p31Spec : Prop :=
  ∀ (M : ℝ → ℝ → ℝ)
    (hzero : M 0 0 = 0)
    (hC1 : ContDiffAt ℝ 1
      (fun z : ℝ × ℝ => M z.1 z.2) ((0 : ℝ), (0 : ℝ)))
    (hb : fderiv ℝ (fun z : ℝ × ℝ => M z.1 z.2)
      ((0 : ℝ), (0 : ℝ)) ((1 : ℝ), (0 : ℝ)) < 0)
    (ha : fderiv ℝ (fun z : ℝ × ℝ => M z.1 z.2)
      ((0 : ℝ), (0 : ℝ)) ((0 : ℝ), (1 : ℝ)) < 0),
    ∃ K : ℝ, 0 < K ∧
      ∃ delta : ℝ, 0 < delta ∧
        (∀ h : ℝ, -delta < h → h < 0 →
          ∃ r : ℝ, 0 < r ∧ r < -K * h ∧ M r h = 0 ∧
            (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) (-K * h) →
              (ProposedScalarComplementarityMultiplicity.ScalarComplementarity
                (fun x => M x h) s ↔ s = 0 ∨ s = r))) ∧
        (∃ eps : ℝ, 0 < eps ∧
          ∀ h : ℝ, 0 < h → h < delta →
            ¬ ∃ s : ℝ, s ∈ Set.Icc (0 : ℝ) eps ∧
              ProposedScalarComplementarityMultiplicity.ScalarComplementarity
                (fun x => M x h) s)

/-- Proposition 5.1: exact fixed rational matrix; not a SOURCE Jacobian. -/
def p51Spec : Prop :=
  ∀ (k : ℕ) (x : Fin 6 → ℝ),
    ‖(CurrentCompact.exactDecimalF0 ^ k) *ᵥ x‖ ≤
      (61 / 10 : ℝ) * (24 / 25 : ℝ) ^ (k / 48) * ‖x‖

/-- Lemma 5.2: all 6x6 real matrices in an explicitly specified ball. -/
def l52Spec : Prop :=
  ∀ A : Matrix (Fin 6) (Fin 6) ℝ,
    ‖A - CurrentCompact.exactDecimalF0‖ ≤ (1 / 10000 : ℝ) →
      ‖A ^ 48‖ < (49 / 50 : ℝ) ∧
      (∀ r : ℕ, r < 48 → ‖A ^ r‖ < (7 : ℝ)) ∧
      (∀ (k : ℕ) (x : Fin 6 → ℝ),
        ‖(A ^ k) *ᵥ x‖ ≤
          (7 : ℝ) * (49 / 50 : ℝ) ^ (k / 48) * ‖x‖)

/-- Proposition 5.3: conditional effective-price financial wedge. -/
def p53Spec : Prop := CurrentCompact.effectiveWedgeCurrentSpec

/-- Appendix Lemma A.1.1: robust collateral coverage in each state. -/
def a11Spec : Prop := CurrentCompact.repaymentCurrentSpec

/-- Appendix Lemma A.1.2: finite support and strictly positive states. -/
def a12Spec.{u} : Prop := CurrentCompact.noSimultaneousInteriorCurrentSpec.{u}

/-- Appendix Proposition A.1.3: feasible capital-capacity bound and rate derivative. -/
def a13Spec : Prop := CurrentCompact.financingCapacityCurrentSpec

/-- Appendix Lemma A.1.4: physical allocation and pathwise log-loss. -/
def a14Spec : Prop :=
  ∀ (vH vL AH AL L alpha beta d : ℝ)
      (kH kL : ℝ → ℝ) (t dkH dkL : ℝ),
    0 < vH → 0 < vL →
    0 < AH → 0 < AL →
    0 < L →
    0 < alpha → 0 < beta → 0 < d →
    alpha + beta + d = 1 →
    0 < kH t → 0 < kL t →
    HasDerivAt kH dkH t →
    HasDerivAt kL dkL t →
    CurrentCompact.compactLemmaA14CurrentFullSpec
      vH vL AH AL L alpha beta d kH kL t dkH dkL

end Ventura26LiquidityAllocation
"""

PROOFS = r"""
import Ventura26LiquidityAllocation.PaperInterface

/-! Eight proofs by kernel-checked source-specific lemmas; no sorry. -/
namespace Ventura26LiquidityAllocation

theorem p31 : p31Spec := by
  intro M hzero hC1 hb ha
  exact CurrentCompactProp31C1.prop31_scalar_from_only_C1_hypotheses
    M hzero hC1 hb ha

theorem p51 : p51Spec := by
  intro k x
  exact CurrentCompact.prop51_unconditional_exact k x

theorem l52 : l52Spec := by
  exact CurrentCompact.lemma52_decimal_current_exact

theorem p53 : p53Spec :=
  PostDeadlineCurrentPaperFive.proposition_53_effective_price_wedge_paper

theorem a11 : a11Spec :=
  PostDeadlineCurrentPaperFive.lemma_A11_repayment_paper

theorem a12.{u} : a12Spec.{u} :=
  PostDeadlineCurrentPaperFive.lemma_A12_interior_FOC_paper

theorem a13 : a13Spec :=
  PostDeadlineCurrentPaperFive.proposition_A13_financing_capacity_paper

theorem a14 : a14Spec := by
  intro vH vL AH AL L alpha beta d kH kL t dkH dkL
    hvH hvL hAH hAL hL ha hb hd hsum hkH hkL hH hLL
  exact PostDeadlineCurrentPaperFive.lemma_A14_physical_allocation_and_log_loss_paper
    vH vL AH AL L alpha beta d kH kL t dkH dkL
    hvH hvL hAH hAL hL ha hb hd hsum hkH hkL hH hLL

#print axioms p31
#print axioms p51
#print axioms l52
#print axioms p53
#print axioms a11
#print axioms a12
#print axioms a13
#print axioms a14

end Ventura26LiquidityAllocation
"""

def run(argv: list[str], cwd: pathlib.Path) -> None:
    print("+", " ".join(argv), flush=True)
    subprocess.run(argv, cwd=cwd, check=True)

def main() -> None:
    if len(sys.argv) != 3:
        raise SystemExit("usage: stage_eight_paper_interface.py AI_PROJECT UPSTREAM")
    project, upstream = (pathlib.Path(v).resolve() for v in sys.argv[1:])
    inv = json.loads((project / "lean/current_paper_source_inventory_8.json").read_text())
    assert inv["source_main_sha"] == SOURCE_SHA
    assert tuple(c["label"] for c in inv["claims"]) == EXPECTED
    for c in inv["claims"]:
        orig = subprocess.check_output(
            ["git", "show", SOURCE_SHA + ":" + c["source_path"]],
            cwd=project, text=True)
        blob = subprocess.check_output(
            ["git", "rev-parse", SOURCE_SHA + ":" + c["source_path"]],
            cwd=project, text=True).strip()
        assert c["statement_latex"] in orig and c["source_git_blob"] == blob, c["label"]
    print("PAPER_EIGHT_SOURCE_STATEMENTS_GIT_BLOBS_OK", flush=True)

    assert not (upstream / "papers" / REPO).exists()
    run(["python3", "scripts/paper_contribution.py", "new",
         "https://github.com/alejandroventuraventurameza-tech/ai-project/blob/"
         + SOURCE_SHA + "/paper/paper.pdf",
         "--folder", REPO,
         "--title", "Financial frictions, policy corridor, and capital allocation",
         "--authors", "Alejandro Ventura",
         "--version", "compact-8-results-2026-11-26",
         "--namespace", REPO,
         "--no-download"], upstream)

    dst = upstream / "papers" / REPO
    checkpoint = project / "lean/checkpoint/modules" / REPO
    for p in checkpoint.glob("*.lean"):
        shutil.copyfile(p, dst / p.name)
    for p in (project / "lean/candidates" / REPO).glob("*.lean"):
        shutil.copyfile(p, dst / p.name)
    for p in (project / "lean/current").glob("*.lean"):
        shutil.copyfile(p, dst / p.name)
    for filename, contents in (
        ("MainTheorems.lean", MAIN),
        ("PaperInterface.lean", PAPER),
        ("ProofInterface.lean", PROOFS),
    ):
        (dst / filename).write_text(contents.lstrip(), encoding="utf-8")
    for filename in ("PaperInterface.lean", "ProofInterface.lean"):
        s = (dst / filename).read_text(encoding="utf-8")
        assert "sorry" not in "\n".join(line for line in s.splitlines() if not line.strip().startswith("/-!"))
    print("PAPER_SCOPED_EIGHT_STAGING_READY_NO_PROOF_HOLES", flush=True)
    print("CAVEAT: generated without official source statement-spec; run --fast only", flush=True)

if __name__ == "__main__":
    main()

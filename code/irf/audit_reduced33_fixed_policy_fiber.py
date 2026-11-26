#!/usr/bin/env python3
"""Fail-closed separation of a free-h Python boundary root and fixed-shock IRFs.

The reduced 33x33 Newton boundary solve treats reserve-remuneration innovation
h as UNKNOWN alongside 32 economic log coordinates. The actual IRF experiment
uses an EXOGENOUSLY FIXED policy innovation v_R. A small boundary residual
at hStar says nothing by itself about the SOURCE root at v_R.

This report checks the two REAL on-disk JSON witnesses produced by
code/verify.py in one Git revision. It does NOT invoke Lean or prove any
SOURCE-to-Python semantic identity, interval enclosure or equilibrium.
"""
from __future__ import annotations

import hashlib
import json
import math
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
BOUNDARY = HERE / "output/frozen_python_reduced33_dual_eliminated_search.json"
IRF = HERE / "output/main/finite_irf_validation.json"
SOURCE = ROOT / "lean/checkpoint/modules/Ventura26LiquidityAllocation/EconomicModel.lean"
PYTHON = HERE / "finite_irf.py"
OUT = HERE / "output/frozen_reduced33_fixed_policy_fiber_gate.json"

def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)

def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main() -> None:
    require(BOUNDARY.is_file(), "Reduced33 boundary root report missing")
    require(IRF.is_file(), "Main fixed-policy IRF report missing")
    require(SOURCE.is_file() and PYTHON.is_file(), "SOURCE/Python provenance missing")

    boundary = json.loads(BOUNDARY.read_text(encoding="utf-8"))
    irf = json.loads(IRF.read_text(encoding="utf-8"))

    require(boundary.get("status") ==
            "NUMERICAL_PYTHON_REDUCED33_DUAL_ELIMINATION_CANDIDATE",
            "Boundary report is not the expected reduced33 Newton candidate")
    require(boundary.get("all_regime_checks_pass") is True,
            "Boundary regime diagnostics changed")
    require(boundary.get("source_34_equations_formally_validated") is False
            and boundary.get("true_SOURCE_34_equation_root_certified") is False,
            "Boundary report falsely claims genuine SOURCE validation")
    require(boundary.get("solve_error") is None,
            "Boundary Newton routine did not reach its candidate")
    require(boundary["final_reduced33_max_residual"] < 1e-10,
            "Boundary numerical residual drift")

    shock = irf.get("shock", {})
    require(shock.get("instrument") ==
            "date-0 log reserve-remuneration-rule innovation v_R",
            "IRF instrument changed; the policy-fiber comparison needs review")
    h_star = float(boundary["final_innovation_h"])
    h_irf = float(shock["value"])
    require(math.isfinite(h_star) and math.isfinite(h_irf),
            "Policy innovations must be finite")

    # A regression on the PINNED illustration. If a later revision changes
    # these signs or brings the two policy innovations together, review the
    # economic interpretation rather than silently relabeling the root.
    require(h_star > 0 and h_irf < 0,
            "Current positive boundary vs negative IRF sign separation changed")
    separation = abs(h_star - h_irf)
    require(separation > 1e-3,
            "Free-h boundary root now near fixed-policy IRF: re-audit validity")

    report = {
        "status": "FREE_H_BOUNDARY_ROOT_IS_NOT_THE_FIXED_NEGATIVE_IRF_SHOCK",
        "free_h_boundary_reduced33_unknowns": "32 economic logs plus solved h",
        "fixed_h_irf_reduced33_unknowns": "32 economic logs with h prescribed",
        "free_h_boundary_reduced33_equations": 33,
        "fixed_h_irf_reduced33_equations": 33,
        "free_h_boundary_python_h": h_star,
        "fixed_negative_irf_h": h_irf,
        "policy_innovation_absolute_separation": separation,
        "same_policy_innovation": False,
        "irf_shock_instrument": shock["instrument"],
        "free_h_boundary_float_residual": boundary["final_reduced33_max_residual"],
        "free_h_boundary_regime_diagnostics_passed": True,
        "full_SOURCE_Python_semantic_identity_certified": False,
        "true_SOURCE_root_at_free_h_certified": False,
        "true_SOURCE_root_at_fixed_irf_h_certified": False,
        "fixed_policy_IRF_certified_from_free_h_root": False,
        "full_infinite_horizon_equilibrium_certified": False,
        "inputs_sha256": {
            str(p.relative_to(ROOT)): sha256(p)
            for p in (BOUNDARY, IRF, SOURCE, PYTHON)
        },
        "note": (
            "A boundary root with endogenous positive h cannot be "
            "substituted for the fixed negative IRF shock. This is a "
            "numerical-provenance firewall, not a SOURCE existence theorem."
        ),
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n",
                   encoding="utf-8")
    print(json.dumps({
        "status": report["status"],
        "boundary_h": h_star,
        "irf_h": h_irf,
        "absolute_gap": separation,
        "source_fixed_irf_root_certified": False,
        "report": str(OUT),
    }, indent=2))

if __name__ == "__main__":
    main()

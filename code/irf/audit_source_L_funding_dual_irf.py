#!/usr/bin/env python3
"""Numerical audit of SOURCE augmented row 34, not a 34-row equivalence proof.

Lean SOURCE defines the normalized firm-L funding dual as
    1/R^L_t - beta_E * [c_L,t+1^(-sigma_E)/c_L,t^(-sigma_E)] / Pi_t+1.
The Python illustrative case has sigma_E=1 and reports collateral_dual_L.

Reconstruct that SOURCE expression from the generated CSV for every
finite t and branch S/B, baseline and shock. This checks a PARTICULAR
function/coordinate projection numerically and cannot certify an actual
Lean economic continuation, the 33 other rows, or any infinite TVC.
"""
from __future__ import annotations

import csv
import hashlib
import json
import math
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
LEAN = ROOT / "lean/checkpoint/modules/Ventura26LiquidityAllocation/EconomicModel.lean"
PATHS = HERE / "output/main/finite_irf_paths.csv"
META = HERE / "output/main/finite_irf_validation.json"
OUT = HERE / "output/source_L_funding_dual_irf_audit.json"


def require(ok, message):
    if not ok:
        raise AssertionError(message)


def fingerprint(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    source = LEAN.read_text(encoding="utf-8").replace("\r\n", "\n")
    require(
        "noncomputable def crraMarginal (sigma c : ℝ) : ℝ := c ^ (-sigma)"
        in source, "SOURCE CRRA marginal utility definition has changed"
    )
    start = source.index("noncomputable def localNormalizedCollateralDualL")
    end = source.index("def LocalScalarComplementarityL", start)
    block = source[start:end]
    for anchor in (
        "1 / Z.controlsZero.loanRate -",
        "P.entrepreneurDiscount *",
        "crraMarginal P.entrepreneurRiskAversion Z.controlsOne.consumptionL",
        "crraMarginal P.entrepreneurRiskAversion Z.controlsZero.consumptionL",
        "Z.controlsOne.inflation",
    ):
        require(anchor in block, f"SOURCE augmented row 34 changed: {anchor}")
    require(PATHS.is_file() and META.is_file(),
            "Run the finite IRF reproduction before this independent audit")
    meta = json.loads(META.read_text(encoding="utf-8"))
    require(meta["shock"]["instrument"] ==
            "date-0 log reserve-remuneration-rule innovation v_R",
            "Instrument misidentified: not a reserve-requirement shock")
    beta = float(meta["parameters"]["beta_entrepreneur"])
    sigma = float(meta["parameters"]["risk_aversion_entrepreneur"])
    require(beta > 0 and sigma == 1.0,
            "The illustrative Python projection requires CRRA sigma_E=1")
    with PATHS.open(newline="", encoding="utf-8") as handle:
        rows = list(csv.DictReader(handle))
    indexed = {}
    for row in rows:
        branch, t = row["branch"], int(row["period"])
        require((branch, t) not in indexed, "Duplicate branch and time")
        indexed[(branch, t)] = row
    require({b for b, _ in indexed} == {"slack", "binding"},
            "Expected two conditional S/B branches")
    tol = 2e-12
    results = {}
    max_err = 0.0
    for branch in ("slack", "binding"):
        times = sorted(t for b, t in indexed if b == branch)
        require(times == list(range(len(times))) and len(times) >= 2,
                "Noncontiguous or insufficient transition dates")
        impact = {}
        branch_max = 0.0
        for t in times[:-1]:
            current, following = indexed[(branch, t)], indexed[(branch, t+1)]
            for suffix, label in (("", "shocked"), ("_baseline", "baseline")):
                loan = float(current["loan_rate" + suffix])
                c_current = float(current["consumption_L" + suffix])
                c_next = float(following["consumption_L" + suffix])
                pi_next = float(following["inflation" + suffix])
                printed = float(current["collateral_dual_L" + suffix])
                require(all(math.isfinite(v) and v > 0 for v in
                            (loan, c_current, c_next, pi_next)),
                        "SOURCE-dual positivity domain violated")
                source_projection = (
                    1.0 / loan - beta * (c_current/c_next)**sigma / pi_next
                )
                err = abs(source_projection-printed)
                branch_max = max(branch_max, err)
                max_err = max(max_err, err)
                if t == 0:
                    impact[label] = {
                        "source_formula": source_projection,
                        "python_diagnostic": printed,
                        "abs_difference": err,
                    }
        results[branch] = {
            "periods_audited": len(times)-1,
            "maximum_abs_equation_34_projection_error": branch_max,
            "date_zero": impact,
            "regime_L_at_impact": (
                "slack, hence funding dual required to vanish"
                if branch == "slack" else
                "binding, funding dual is nonnegative and can be positive"
            ),
        }
    require(max_err < tol, "Numerical SOURCE row-34 dual projection mismatch")
    require(abs(results["slack"]["date_zero"]["shocked"]["python_diagnostic"])
            < 1e-9, "S impact violates zero funding dual")
    report = {
        "status": "NUMERICAL_SOURCE_ROW34_FUNDING_DUAL_PROJECTION_MATCH",
        "source_lean_definition": "localNormalizedCollateralDualL",
        "source_marginal_utility": "crraMarginal sigma c = c^(-sigma)",
        "equation": (
            "dual_L=1/Rloan-betaE*(c_L_t/c_L_t+1)^sigmaE/Pi_t+1"
        ),
        "input_sha256": {
            str(p.relative_to(ROOT)): fingerprint(p) for p in
            (LEAN, HERE/"finite_irf.py", PATHS, META)
        },
        "shock": meta["shock"],
        "beta_E": beta,
        "sigma_E": sigma,
        "source_34th_row_is_not_an_extra_shock": True,
        "numerical_error_threshold": tol,
        "max_absolute_error": max_err,
        "branches": results,
        "important_limitations": [
            "Numerical evaluation of one selected SOURCE-equation formula",
            "NOT a proof that the 33-row surrogate equals all Lean SOURCE rows",
            "NOT proof of 34-row augmented zero for shocked branch B",
            "NOT global firm/bank optimality, stochastic bank OTC or infinite TVC",
            "Not an independent causal decomposition of the reserve-rate shock",
        ],
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(report, indent=2, sort_keys=True)+"\n",
                   encoding="utf-8")
    print(json.dumps({
        "status": report["status"],
        "max_abs_error": max_err,
        "S_shock_date_zero_dual": (
            results["slack"]["date_zero"]["shocked"]["python_diagnostic"]
        ),
        "B_shock_date_zero_dual": (
            results["binding"]["date_zero"]["shocked"]["python_diagnostic"]
        ),
        "output": str(OUT),
    }, indent=2))


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Numerical diagnostic for eliminating the single Python L-dual row.

Uses the *already independently interval-enclosed* stationary unit-CRRA
SOURCE-shaped dual formula to set its loan-rate log coordinate to an
analytic zero, while holding all other Python frozen-frontier log
coordinates and the remuneration-rule innovation unchanged.

This is a float64 DIAGNOSTIC on finite_irf.py's prefix_residual. It does
not prove that the other 33 true Lean SOURCE rows vanish, nor certify
an exact 34-vector root, valid KKT branch or long-run equilibrium.
"""
from __future__ import annotations
import json
import math
from fractions import Fraction
from pathlib import Path

from finite_irf import prefix_residual, max_abs, steady_case
from frozen_stationary_prefix_audit import frozen_stationary_seed
from audit_frozen_python_augmented34_basepoint import exact_shape_dual
from audit_frozen_frontier_source_dual_scalar_root import (
    FRONTIER, OUT as ROOT_BRACKET,
)
from audit_frozen_frontier_source_dual_interval import require, digest

HERE = Path(__file__).resolve().parent
PRE = HERE / "inputs/rational_preconditioners.json"
OUT = HERE / "output/frozen_python_34_analytic_dual_elimination_diagnostic.json"

def main():
    data=json.loads(FRONTIER.read_text(encoding="utf-8"))
    bracket=json.loads(ROOT_BRACKET.read_text(encoding="utf-8"))
    require(bracket["status"] ==
            "EXACT_RATIONAL_CONDITIONAL_SOURCE_FORMULA_SCALAR_ZERO_BRACKET",
            "Scalar interval sign certificate not present")
    require(bracket["frontier_report_sha256"] == digest(FRONTIER),
            "Frontier candidate drifted after scalar proof")
    s=steady_case()
    seed=frozen_stationary_seed(s)
    pdata=json.loads(PRE.read_text(encoding="utf-8"))
    p0=[[float(v) for v in row] for row in pdata["P0"]]
    cand=data["numerical_candidate"]
    z=list(cand["baseline_33_unknowns"])
    h=cand["innovation_h"]
    require(len(z)==33 and all(math.isfinite(v) for v in z),
            "Invalid finite 33-coordinate frontier")
    old=z[15]
    new_rate_log=-(math.log(s.rate)+math.log(s.be))-z[8]+z[24]+z[28]
    require(math.isfinite(new_rate_log),
            "Analytic scalar correction is not finite")
    # The exact Fraction/Taylor bracket is separate from this double log.
    inside = (
        Fraction(bracket["root_z15_lower_exact"]) <
        Fraction.from_float(new_rate_log) <
        Fraction(bracket["root_z15_upper_exact"])
    )
    require(inside,
            "Binary64 analytic correction left the independent rational bracket")
    updated=list(z)
    updated[15]=new_rate_log
    policy=(h,0.0,0.0,0.0)
    before=prefix_residual(seed,p0,"binding",policy,z)
    after=prefix_residual(seed,p0,"binding",policy,updated)
    old_dual=exact_shape_dual(s,seed,z)[0]
    new_dual=exact_shape_dual(s,seed,updated)[0]
    require(len(before)==33 and len(after)==33,
            "Reduced prefix residual dimension drift")
    require(all(math.isfinite(t) for t in after),
            "Analytic elimination produced nonfinite residuals")
    require(abs(new_dual)<1e-13,
            "The Python dual did not vanish to binary64 accuracy")
    require(max_abs(after)<1e-6,
            "The 33 other rows became numerically remote")
    report={
        "status":"NUMERICAL_PYTHON_34_DUAL_ANALYTIC_ELIMINATION_NOT_SOURCE_ROOT",
        "frontier_sha256":digest(FRONTIER),
        "exact_scalar_bracket_sha256":digest(ROOT_BRACKET),
        "log_loan_rate_before":old,
        "log_loan_rate_after":new_rate_log,
        "log_loan_rate_delta":new_rate_log-old,
        "analytic_new_z15_in_exact_rational_scalar_bracket":inside,
        "max_33_python_residual_before":max_abs(before),
        "max_33_python_residual_after":max_abs(after),
        "max_34_python_residual_after":max(max_abs(after),abs(new_dual)),
        "funding_dual_before":old_dual,
        "funding_dual_after":new_dual,
        "only_coordinate_15_changed":all(
            z[i]==updated[i] for i in range(33) if i!=15),
        "innovation_h_preserved":h,
        "same_inherited_state":list(seed.X0),
        "other_33_SOURCE_rows_formally_identified":False,
        "validated_SOURCE_interval_derivative_enclosure":False,
        "certified_SOURCE_34_root":False,
        "full_dynamic_equilibrium":False,
    }
    OUT.parent.mkdir(parents=True,exist_ok=True)
    OUT.write_text(json.dumps(report,sort_keys=True,indent=2)+"\n",
                   encoding="utf-8")
    print(json.dumps({k:report[k] for k in (
        "status","log_loan_rate_delta",
        "max_33_python_residual_before",
        "max_33_python_residual_after",
        "funding_dual_before","funding_dual_after",
        "analytic_new_z15_in_exact_rational_scalar_bracket",
        "certified_SOURCE_34_root")},indent=2))

if __name__=="__main__":
    main()

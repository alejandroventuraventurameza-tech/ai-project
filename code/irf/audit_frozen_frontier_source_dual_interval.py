#!/usr/bin/env python3
"""Rational interval of literal SOURCE L-dual formula at Python 34 frontier.

Uses the SOURCE-proved four-log-coordinate identity and stationarity of
the Python frozen U0,U1 controls to simplify to
nu = R0^(-1)*exp(-z15) - betaE*exp(z8-z24-z28), for sigmaE = 1.
Bounds are EXACT Fraction intervals using a Taylor remainder bound
and exact rational stationary-loan-rate enclosure. Numeric coordinates
are interpreted as exact binary64 rationals, not as SOURCE Lean values.

NO SOURCE/Python semantics, SOURCE root, or SOURCE 33-row derivative
certificate is asserted by this arithmetic evaluation.
"""
from __future__ import annotations
import hashlib
import json
import math
from fractions import Fraction as Q
from math import factorial
from pathlib import Path

from audit_frozen_stationary_dual_rational import Box, bounds
from frozen_stationary_prefix_audit import frozen_stationary_seed
from finite_irf import steady_case

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
SOURCE = ROOT / "lean/checkpoint/modules/Ventura26LiquidityAllocation/EconomicModel.lean"
ENGINE = HERE / "finite_irf.py"
FRONTIER = HERE / "output/frozen_python_augmented34_boundary_search.json"
OUT = HERE / "output/frozen_frontier_source_dual_rational_interval.json"
TAYLOR_N = 20

def require(ok, msg):
    if not ok:
        raise AssertionError(msg)

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def exp_rational_interval(x: Q, order=TAYLOR_N):
    """Taylor+Lagrange interval with |remainder| <= 3*|x|^(N+1)/(N+1)!
    for |x| <= 1; this follows from exp(|x|) <= exp(1) < 3.
    All arithmetic in this function is exact Fraction arithmetic.
    """
    require(isinstance(x, Q) and abs(x) <= 1 and order >= 2,
            "Taylor series requested outside certified domain")
    s = sum((x**k)/factorial(k) for k in range(order+1))
    err = 3*abs(x)**(order+1)/factorial(order+1)
    require(s-err > 0, "Positive exp interval not established")
    return Box(s-err,s+err)

def main():
    require(FRONTIER.is_file(), "Missing frozen Python frontier")
    data = json.loads(FRONTIER.read_text(encoding="utf-8"))
    require(data["status"] ==
            "NUMERICAL_PYTHON_34_BOUNDARY_CANDIDATE_FOUND_NOT_SOURCE_PROOF",
            "Not the expected Python 34 candidate")
    require(data["source_sha256"] == digest(SOURCE) and
            data["python_engine_sha256"] == digest(ENGINE),
            "Pinned SOURCE/Python code drift")
    s = steady_case()
    seed = frozen_stationary_seed(s)
    require(s.sigmaE == 1.0 and s.be == float(Q(24,25)),
            "The pinned risk-aversion/discount simplification changed")
    require(seed.U0[1] > 0 and seed.U0[1] == seed.U1[1]
            and seed.U1[5] == 1.0,
            "Stationary C0/C1 or Pi1 normalization not valid")
    rate = bounds()["rate"]
    require(rate.lo > 0 and rate.lo < Q.from_float(s.rate) < rate.hi,
            "Rational exact-rate interval does not contain Python rate")
    cand = data["numerical_candidate"]
    z = cand["baseline_33_unknowns"]
    require(len(z) == 33 and all(math.isfinite(v) for v in z),
            "Nonfinite 33-log-coordinate Python candidate")
    z8,z15,z24,z28 = [Q.from_float(z[i]) for i in (8,15,24,28)]
    first = exp_rational_interval(-z15) / rate
    second = Box(Q(24,25)) * exp_rational_interval(z8-z24-z28)
    dual = first-second
    require(dual.lo > 0 and dual.hi > dual.lo,
            "Pinned frontier dual not strictly positive in rational bounds")
    reported = Q.from_float(cand["funding_dual_L"])
    require(dual.lo < reported < dual.hi,
            "Python displayed dual lies outside rational SOURCE-formula bound")
    assert cand["max_34_residual"] >= abs(cand["funding_dual_L"])
    report = {
        "status": "EXACT_RATIONAL_FRONTIER_SOURCE_FORMULA_L_DUAL_POSITIVE_CONDITIONAL_INPUTS",
        "source_formula_proven_in_lean":
            "sourceFundingDual_four_log_coordinate_formula",
        "formula_after_sigma1_stationary_normalization":
            "R0^-1 * exp(-z15) - (24/25)*exp(z8-z24-z28)",
        "frontier_report_sha256": digest(FRONTIER),
        "source_sha256": digest(SOURCE),
        "python_engine_sha256": digest(ENGINE),
        "exact_log_coordinate_interpretation":
            "exact Fraction.from_float on the four Python binary64 values",
        "loan_rate_lower_exact": str(rate.lo),
        "loan_rate_upper_exact": str(rate.hi),
        "taylor_order": TAYLOR_N,
        "taylor_remainder_bound": "3*abs(x)^(N+1)/(N+1)! for abs(x)<=1",
        "dual_lower_exact": str(dual.lo),
        "dual_upper_exact": str(dual.hi),
        "dual_lower_float": float(dual.lo),
        "dual_upper_float": float(dual.hi),
        "interval_width_float": float(dual.hi-dual.lo),
        "python_candidate_dual": cand["funding_dual_L"],
        "rigorous_positive_for_this_formula_and_exact_binary_chart": True,
        "exact_candidate_is_zero_of_this_scalar": False,
        "source_primitives_and_Z0_identified_in_Lean_with_python": False,
        "source_33_residual_enclosed": False,
        "source_34_root_certified": False,
        "full_equilibrium_certified": False,
        "caveat": "An exact interval of the SOURCE formula with pinned Python values"
                  " does not identify a full SOURCE instance, its continuation,"
                  " or the other 33 true SOURCE residuals.",
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(report, indent=2, sort_keys=True)+"\n",
                   encoding="utf-8")
    print(json.dumps({k:report[k] for k in (
        "status","dual_lower_float","dual_upper_float",
        "interval_width_float","python_candidate_dual",
        "source_primitives_and_Z0_identified_in_Lean_with_python"
    )},indent=2))

if __name__ == "__main__":
    main()

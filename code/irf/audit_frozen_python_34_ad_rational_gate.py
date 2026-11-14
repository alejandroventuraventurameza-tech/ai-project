#!/usr/bin/env python3
"""Exact rational Neumann/Schur test for the forward-AD Python Jacobian.

The 34x34 AD matrix is computed by differentiating finite_irf.py, then
its float values are rounded to decimal fractions. All subsequent
Neumann, Schur and perturbation-budget inequalities use Fraction EXACTLY.
This still does NOT enclose the genuine Python or Lean SOURCE derivatives.
"""
from __future__ import annotations

import hashlib
import json
from fractions import Fraction
from pathlib import Path

from audit_frozen_python_34_rational_preconditioner import (
    N, FULL, approximate_inverse, flt_solve, norm_inf, q, require,
    witness,
)

HERE = Path(__file__).resolve().parent
AD = HERE / "output/frozen_python_augmented34_forward_ad.json"
FD_BASE = HERE / "output/frozen_python_augmented34_boundary_search.json"
FD_GATE = HERE / "output/frozen_python_augmented34_rational_preconditioner.json"
OUT = HERE / "output/frozen_python_augmented34_ad_rational_gate.json"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    require(all(path.is_file() for path in (AD, FD_BASE, FD_GATE)),
            "Regenerate AD/FD boundary and previous rational gate first")
    data = json.loads(AD.read_text(encoding="utf-8"))
    prior = json.loads(FD_GATE.read_text(encoding="utf-8"))
    base = json.loads(FD_BASE.read_text(encoding="utf-8"))
    require(data["status"] == "FLOAT64_FORWARD_AD_PYTHON_34_JACOBIAN_NOT_SOURCE",
            "Invalid AD input scope")
    require(prior["status"] ==
            "EXACT_RATIONAL_ROUNDED_PYTHON_34_MATRIX_CERTIFICATE_ONLY",
            "Previous independent FD rational test missing")
    require(data["parent_boundary_report_sha256"] == sha(FD_BASE)
            and prior["parent_report_sha256"] == sha(FD_BASE)
            and data["source_sha256"] == base["source_sha256"],
            "AD/FD point or economic SOURCE fingerprints disagree")

    J = data["forward_ad_jacobian_34"]
    require(len(J) == FULL and all(len(row) == FULL for row in J),
            "Forward AD Jacobian not 34x34")
    A = [list(row[:N]) for row in J[:N]]
    C33f, _pivot33 = approximate_inverse(A)
    C34f, _pivot34 = approximate_inverse(J)
    Aq, C33q, q33, n33, K33 = witness(A, C33f)
    Jq, C34q, q34, n34, K34 = witness(J, C34f)

    # Exact negativity of Schur for the RATIONALIZED forward-AD matrix.
    b_float = [J[i][-1] for i in range(N)]
    c_float = J[-1][:N]
    u_float, _ = flt_solve(A, [-v for v in b_float])
    u = [q(v) for v in u_float]
    bq = [q(v) for v in b_float]
    cq = [q(v) for v in c_float]
    residual = [
        sum(Aq[i][k]*u[k] for k in range(N)) + bq[i]
        for i in range(N)
    ]
    rn = max(abs(v) for v in residual)
    s = sum(cq[i]*u[i] for i in range(N))
    s_err = sum(abs(v) for v in cq)*K33*rn
    require(s+s_err < 0,
            "AD rationalized Schur scalar negative sign not certified")

    eps33 = (1-q33)/(4*N*n33)
    eps34 = (1-q34)/(4*FULL*n34)
    eps = min(eps33, eps34)
    require(eps > 0, "No uniform rational entrywise tolerance")

    # A second algebraically exact cross-comparison: rationalized
    # forward-AD matrix sits strictly within the independently certified
    # finite-difference *rounded* Jacobian perturbation budget.
    old = base["numerical_candidate"]["float_jacobian_probe"]
    oldA = old["first33_jacobian"]
    oldb = old["policy_forcing_column_b"]
    oldc = old["sparse_funding_dual_gradient_c"]
    oldJ = [
        list(oldA[i]) + [oldb[i]] for i in range(N)
    ] + [[float(oldc.get(str(i),0.)) for i in range(N)] + [0.]]
    difference = max(abs(Jq[i][j] - q(oldJ[i][j]))
                     for i in range(FULL) for j in range(FULL))
    old_eps = Fraction(prior["conditional_per_entry_error_tolerance"])
    require(difference < old_eps,
            "AD rounded Jacobian is outside old FD Neumann budget")
    require(data["last_row_policy_derivative"] == 0,
            "AD SOURCE-shaped dual directly depends on h")

    report = {
        "status": "EXACT_RATIONAL_ROUNDED_FORWARD_AD_PYTHON_34_GATE_ONLY",
        "input_AD_sha256": sha(AD),
        "input_FD_boundary_sha256": sha(FD_BASE),
        "input_FD_rational_gate_sha256": sha(FD_GATE),
        "rounded_matrix_order_33": N,
        "rounded_matrix_order_34": FULL,
        "exact_rational_33_defect": str(q33),
        "exact_rational_34_defect": str(q34),
        "approx_33_defect_float": float(q33),
        "approx_34_defect_float": float(q34),
        "exact_rational_schur_lower": str(s-s_err),
        "exact_rational_schur_upper": str(s+s_err),
        "rational_schur_lower_float": float(s-s_err),
        "rational_schur_upper_float": float(s+s_err),
        "rational_33_inverse_upper": str(K33),
        "rational_34_inverse_upper": str(K34),
        "conditional_34_entry_error_tolerance": str(eps),
        "conditional_34_entry_error_tolerance_float": float(eps),
        "AD_FD_rounded_max_entry_difference_exact": str(difference),
        "AD_FD_rounded_max_entry_difference_float": float(difference),
        "old_FD_entry_tolerance_exact": str(old_eps),
        "both_rationalized_33_matrices_invertible": True,
        "both_rationalized_34_matrices_invertible": True,
        "AD_rounded_schur_sign_negative": True,
        "same_point_same_inherited_state": True,
        "source_python_equality_proved": False,
        "true_SOURCE_derivative_enclosed": False,
        "true_Python_derivative_enclosed": False,
        "IFT_existence_proved": False,
        "full_dynamic_equilibrium_proved": False,
        "notes": [
            "Forward AD eliminates finite-difference truncation, but still uses float64.",
            "An exact Neumann test of rounded AD coefficients is NOT a directed-rounding derivative certificate.",
            "Both matrices are evaluated at the frozen-predecessor Python boundary h*.",
            "The actual SOURCE 34-row derivative and nonlinear root require separate proof.",
        ],
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(report,indent=2,sort_keys=True)+"\n",encoding="utf-8")
    print(json.dumps({k:report[k] for k in (
        "status","approx_33_defect_float","approx_34_defect_float",
        "rational_schur_lower_float","rational_schur_upper_float",
        "conditional_34_entry_error_tolerance_float",
        "AD_FD_rounded_max_entry_difference_float",
    )}, indent=2))


if __name__ == "__main__":
    main()

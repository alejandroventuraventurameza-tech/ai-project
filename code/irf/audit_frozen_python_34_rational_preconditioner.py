#!/usr/bin/env python3
"""Exact rational matrix test for the ROUNDING of the Python 34-row Jacobian.

This program does NOT enclose the true SOURCE or Python derivative. It
certifies the 33x33 and 34x34 *decimal-rationalized* matrices and provides
an exact conditional per-entry error budget for future SOURCE interval work.
"""
from __future__ import annotations

import hashlib
import json
import math
from decimal import Decimal
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
INPUT = HERE / "output/frozen_python_augmented34_boundary_search.json"
OUT = HERE / "output/frozen_python_augmented34_rational_preconditioner.json"
SOURCE = ROOT / "lean/checkpoint/modules/Ventura26LiquidityAllocation/EconomicModel.lean"
ENGINE = HERE / "finite_irf.py"
PRE = HERE / "inputs/rational_preconditioners.json"
N = 33
FULL = 34
DIGITS = 12


def require(test, message):
    if not test:
        raise AssertionError(message)


def q(x):
    require(isinstance(x, (int, float)) and math.isfinite(float(x)),
            "Nonfinite matrix input")
    return Fraction(Decimal(format(float(x), f".{DIGITS}f")))


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def flt_solve(matrix, rhs):
    n = len(matrix)
    a = [[float(t) for t in row] for row in matrix]
    b = [float(t) for t in rhs]
    min_pivot = math.inf
    for k in range(n):
        j = max(range(k, n), key=lambda i: abs(a[i][k]))
        require(abs(a[j][k]) > 1e-14, "Unstable float preconditioner pivot")
        a[k], a[j] = a[j], a[k]
        b[k], b[j] = b[j], b[k]
        pk = a[k][k]
        min_pivot = min(min_pivot, abs(pk))
        for col in range(k, n):
            a[k][col] /= pk
        b[k] /= pk
        for row in range(n):
            if row == k:
                continue
            factor = a[row][k]
            if factor == 0:
                continue
            for col in range(k, n):
                a[row][col] -= factor * a[k][col]
            b[row] -= factor * b[k]
    require(all(math.isfinite(x) for x in b), "Nonfinite float solve")
    return b, min_pivot


def approximate_inverse(matrix):
    n = len(matrix)
    columns = []
    min_pivot = math.inf
    for k in range(n):
        rhs = [float(i == k) for i in range(n)]
        col, pivot = flt_solve(matrix, rhs)
        columns.append(col)
        min_pivot = min(min_pivot, pivot)
    return [[columns[j][i] for j in range(n)]
            for i in range(n)], min_pivot


def norm_inf(mat):
    return max(sum(abs(t) for t in row) for row in mat)


def exact_defect(C, M):
    n = len(M)
    return max(sum(abs(Fraction(int(i == j)) -
                   sum(C[i][k]*M[k][j] for k in range(n)))
                   for j in range(n)) for i in range(n))


def witness(matrix, preconditioner):
    n = len(matrix)
    require(n == len(preconditioner)
            and all(len(row) == n for row in matrix)
            and all(len(row) == n for row in preconditioner),
            "Non-square matrix or mismatched preconditioner")
    M = [[q(v) for v in row] for row in matrix]
    C = [[q(v) for v in row] for row in preconditioner]
    defect = exact_defect(C, M)
    require(defect < 1, "Exact Neumann defect is not < 1")
    cnorm = norm_inf(C)
    require(cnorm > 0, "Zero preconditioner")
    # M^-1 = (CM)^-1 C and ||M^-1|| <= ||C||/(1-||I-CM||).
    return M, C, defect, cnorm, cnorm/(1-defect)


def main():
    require(INPUT.exists(), "Run 34-row Python boundary search before this audit")
    payload = json.loads(INPUT.read_text(encoding="utf-8"))
    require(payload["status"] ==
            "NUMERICAL_PYTHON_34_BOUNDARY_CANDIDATE_FOUND_NOT_SOURCE_PROOF",
            "No 34-row Python candidate")
    require(payload["source_sha256"] == sha(SOURCE)
            and payload["python_engine_sha256"] == sha(ENGINE)
            and payload["preconditioner_sha256"] == sha(PRE),
            "SOURCE / Python / pinned-tail input hash drift")
    root = payload["numerical_candidate"]
    require(root["max_34_residual"] < 1e-9
            and root["all_local_regime_checks_pass"],
            "Regime or residual invalid at numerical boundary")
    p = root["float_jacobian_probe"]
    require(p["true_SOURCE_Jacobian_evaluated"] is False
            and p["directed_interval_inverse_proved"] is False,
            "Unjustified SOURCE certificate in input")
    a = p["first33_jacobian"]
    b = p["policy_forcing_column_b"]
    cdict = p["sparse_funding_dual_gradient_c"]
    c = [float(cdict.get(str(i), 0)) for i in range(N)]
    require(len(a) == N and all(len(row) == N for row in a)
            and len(b) == N and len(c) == N, "Bad 33-block dimensions")
    require(set(map(int, cdict)) == {8, 15, 24, 28},
            "Unexpected SOURCE-shaped sparse dual indices")
    aug = [list(a[i]) + [b[i]] for i in range(N)] + [c+[0.0]]
    c33_float = p["first33_inverse_approximation"]
    c34_float, pivot34 = approximate_inverse(aug)
    A, C33, q33, c33norm, inv33bound = witness(a, c33_float)
    M, C34, q34, c34norm, inv34bound = witness(aug, c34_float)

    # Exact Schur sign for the ROUNDED A,b,c, using a rational
    # approximate tangent u and a rational residual norm.
    ufloat, pivot33 = flt_solve(a, [-x for x in b])
    u = [q(v) for v in ufloat]
    bq, cq = [q(x) for x in b], [q(x) for x in c]
    r = [sum(A[i][k]*u[k] for k in range(N))+bq[i]
         for i in range(N)]
    rn = max(abs(x) for x in r)
    schur_center = sum(cq[i]*u[i] for i in range(N))
    schur_error = sum(abs(x) for x in cq)*inv33bound*rn
    require(schur_center+schur_error < 0,
            "Rounded rational Schur strict negativity not established")

    # The SOURCE/Python derivative is NOT currently enclosed by this
    # budget. Only a future rigorous interval entry bound can use it.
    epsilon33 = (1-q33)/(4*N*c33norm)
    epsilon34 = (1-q34)/(4*FULL*c34norm)
    epsilon = min(epsilon33, epsilon34)
    require(epsilon > 0, "No strict entrywise tolerance budget")
    report = {
        "status": "EXACT_RATIONAL_ROUNDED_PYTHON_34_MATRIX_CERTIFICATE_ONLY",
        "parent_report_sha256": sha(INPUT),
        "source_sha256": sha(SOURCE),
        "python_engine_sha256": sha(ENGINE),
        "matrix_order_33": N,
        "matrix_order_34": FULL,
        "rounded_decimal_places": DIGITS,
        "rounding_rule": "format(x,.12f) then exact Decimal-to-Fraction",
        "rational_33_neumann_defect": str(q33),
        "rational_34_neumann_defect": str(q34),
        "rational_33_inverse_norm_upper": str(inv33bound),
        "rational_34_inverse_norm_upper": str(inv34bound),
        "rationalized_schur_center": str(schur_center),
        "rationalized_schur_error_bound": str(schur_error),
        "rationalized_schur_upper": str(schur_center+schur_error),
        "rationalized_schur_lower": str(schur_center-schur_error),
        "rational_schur_negative_for_rounded_matrix": True,
        "conditional_per_entry_error_tolerance": str(epsilon),
        "conditional_per_entry_error_tolerance_float": float(epsilon),
        "rounded_33_matrix_invertible_exact": True,
        "rounded_34_matrix_invertible_exact": True,
        "rational_33_defect_float": float(q33),
        "rational_34_defect_float": float(q34),
        "rationalized_schur_lower_float": float(schur_center-schur_error),
        "rationalized_schur_upper_float": float(schur_center+schur_error),
        "source_true_derivative_within_tolerance_proved": False,
        "python_true_derivative_within_tolerance_proved": False,
        "source_python_semantic_equivalence_proved": False,
        "source_exact_root_proved": False,
        "source_economic_ift_proved": False,
        "source_full_dynamic_equilibrium_proved": False,
        "conditional_claim": (
            "IF the 34x34 SOURCE Jacobian is enclosed entrywise "
            "within the strict rational tolerance of this rounded "
            "34x34 matrix, and the SOURCE 34th row has the asserted "
            "block form, then 33x33 and 34x34 blocks are invertible "
            "and the Schur scalar remains strictly negative. "
            "This SOURCE enclosure is NOT yet established."),
        "float_preconditioner_min_abs_pivot": min(pivot33, pivot34),
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(report, indent=2, sort_keys=True)+"\n",
                   encoding="utf-8")
    print(json.dumps({key: report[key] for key in (
        "status", "rational_33_defect_float", "rational_34_defect_float",
        "rationalized_schur_lower_float", "rationalized_schur_upper_float",
        "conditional_per_entry_error_tolerance_float",
        "source_true_derivative_within_tolerance_proved",
    )}, indent=2))


if __name__ == "__main__":
    main()

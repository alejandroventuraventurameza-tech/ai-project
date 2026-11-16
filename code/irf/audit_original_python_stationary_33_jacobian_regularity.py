#!/usr/bin/env python3
"""Numerical conditioning audit of the ORIGINAL 33x33 Python Jacobian.

Construct the genuine finite_irf.prefix_residual Jacobian on the
frozen binding stationary seed with several symmetric-difference
steps. Report pivot magnitudes, inverse infinity norm, and inverse
residuals. Check sensitivity of J and the solved policy-direction
linear responses across step sizes.

This is a reproducible floating-point NONSINGULARITY DIAGNOSTIC for a
finite-difference matrix, NOT a mathematically certified inverse of
the true derivative, not interval enclosure, and not a SOURCE root.
"""

from __future__ import annotations
import hashlib
import json
import math
from pathlib import Path

import finite_irf as model
from frozen_stationary_prefix_audit import frozen_stationary_seed

HERE = Path(__file__).resolve().parent
P0 = HERE / "inputs/rational_preconditioners.json"
OUT = HERE / "output/original_python_stationary_33_jacobian_regularity_diagnostic.json"
N = 33


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def norminf(a):
    return max(sum(abs(value) for value in row) for row in a)


def max_abs(a):
    return max(abs(v) for row in a for v in row)


def jacobian(f, x, step):
    ans = [[0.0] * N for _ in range(N)]
    for j in range(N):
        a, b = list(x), list(x)
        a[j] += step
        b[j] -= step
        fa, fb = f(a), f(b)
        for i in range(N):
            ans[i][j] = (fa[i] - fb[i]) / (2 * step)
    return ans


def inverse_with_pivots(a):
    cols = []
    lowest = math.inf
    for k in range(N):
        rhs = [0.0] * N
        rhs[k] = 1.0
        col, pivots = model.solve_linear(a, rhs)
        cols.append(col)
        lowest = min(lowest, *pivots)
    inv = [[cols[j][i] for j in range(N)] for i in range(N)]
    return inv, lowest


def identity_residual(a, inv):
    return max(abs(sum(a[i][k] * inv[k][j] for k in range(N)) -
                   (1.0 if i == j else 0.0))
               for i in range(N) for j in range(N))


def main():
    s = model.steady_case()
    base = frozen_stationary_seed(s)
    p0 = [[float(x) for x in row] for row in
          json.loads(P0.read_text(encoding="utf-8"))["P0"]]
    require(len(p0) == 16 and all(len(r) == 6 for r in p0),
            "Pinned continuation drift")
    zero = [0.0] * N
    def f(x):
        return model.prefix_residual(base, p0, "binding",
                                     (0.0, 0.0, 0.0, 0.0), x)
    residual = f(zero)
    root_error = max(abs(v) for v in residual)
    require(root_error < 1e-9, "Frozen 33-row seed no longer root-like")

    steps = [4e-6, 2e-6, 1e-6]
    results = []
    main_jac = None
    main_inv = None
    for step in steps:
        j = jacobian(f, zero, step)
        inv, min_pivot = inverse_with_pivots(j)
        right_residual = identity_residual(j, inv)
        left_residual = identity_residual(inv, j)
        cond_inf = norminf(j) * norminf(inv)
        require(all(math.isfinite(t) for t in
                    (min_pivot, right_residual, left_residual, cond_inf)),
                "Nonfinite inverse diagnostic")
        require(min_pivot > 1e-13, "Numerical pivot too small")
        require(max(right_residual, left_residual) < 1e-5,
                "Matrix-inverse consistency check failed")
        results.append({
            "finite_difference_step": step,
            "jacobian_inf_norm": norminf(j),
            "inverse_inf_norm": norminf(inv),
            "condition_inf_estimate": cond_inf,
            "min_gauss_jordan_abs_pivot": min_pivot,
            "max_abs_matrix_inverse_identity_residual": right_residual,
            "max_abs_inverse_matrix_identity_residual": left_residual,
        })
        if step == 2e-6:
            main_jac, main_inv = j, inv

    require(main_jac is not None, "Reference jacobian missing")
    deviation = []
    response_diffs = []
    for step in (4e-6, 1e-6):
        alternative = jacobian(f, zero, step)
        deviation.append(max_abs([
            [alternative[i][j] - main_jac[i][j] for j in range(N)]
            for i in range(N)]))
        # This is a probe of generic unit right-hand sides in the
        # 33-row coordinate space, NOT an economic IRF to policy tools.
        for idx in (12, 13, 21, 28, 29):
            rhs = [0.0] * N
            rhs[idx] = 1.0
            ref_response, _ = model.solve_linear(main_jac, rhs)
            alt_response, _ = model.solve_linear(alternative, rhs)
            response_diffs.append(max(abs(x-y) for x,y in
                                      zip(ref_response, alt_response)))
    max_jac_discrepancy = max(deviation)
    max_response_discrepancy = max(response_diffs)
    require(max_jac_discrepancy < 3e-5,
            f"Jacobian finite-difference step instability: {max_jac_discrepancy}")
    require(max_response_discrepancy < 3e-3,
            f"Linear response finite-difference instability: {max_response_discrepancy}")

    report = {
        "status": "NUMERICAL_FINITE_DIFFERENCE_PYTHON_33_JACOBIAN_REGULARITY_DIAGNOSTIC",
        "matrix_rows": N,
        "matrix_columns": N,
        "frozen_root_max_abs_residual": root_error,
        "step_experiments": results,
        "max_abs_jacobian_step_discrepancy": max_jac_discrepancy,
        "max_abs_linear_solve_step_discrepancy": max_response_discrepancy,
        "unit_rhs_rows_probed": [12, 13, 21, 28, 29],
        "original_true_derivative_invertibility_proved": False,
        "interval_condition_bound_proved": False,
        "actual_Lean_SOURCE_jacobian_evaluated": False,
        "economic_policy_IRFs_computed_in_this_audit": False,
        "model_sha256": hashlib.sha256(
            (HERE / "finite_irf.py").read_bytes()).hexdigest(),
        "preconditioner_sha256": hashlib.sha256(P0.read_bytes()).hexdigest(),
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()

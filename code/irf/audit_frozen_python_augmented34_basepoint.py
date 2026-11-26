#!/usr/bin/env python3
"""Numerical obstruction to using the frozen Python B seed as a 34-row boundary.

The frozen binding prefix solves the 33 equations in finite_irf.py, but the
SOURCE-shaped additional equation requires the normalized firm-L funding dual
to be ZERO.  This regression computes that scalar on the same Python log chart,
checks its four-coordinate gradient, and tests a local policy tangent.

It NEVER executes EconomicModel.lean, proves SOURCE/Python equality, produces
a directed-rounding interval Jacobian, or certifies a competitive equilibrium.
"""
from __future__ import annotations

import hashlib
import json
import math
from pathlib import Path

from finite_irf import (
    max_abs, newton, numerical_jacobian, prefix_residual, solve_linear,
    steady_case,
)
from frozen_stationary_prefix_audit import frozen_stationary_seed
from frozen_four_tool_impact_audit import unpack_solution
from frozen_four_tool_local_derivative_audit import analytic_forcing


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
SOURCE = ROOT / "lean/checkpoint/modules/Ventura26LiquidityAllocation/EconomicModel.lean"
ENGINE = HERE / "finite_irf.py"
P0 = HERE / "inputs/rational_preconditioners.json"
OUTPUT = HERE / "output/frozen_python_augmented34_basepoint_obstruction.json"
N = 33
H = 2e-6


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def exact_shape_dual(s, seed, z):
    """SOURCE-formula projection, evaluated on frozen Python coordinates."""
    _, u0, u1, metrics = unpack_solution(s, seed, z, (0., 0., 0., 0.))
    R, c0, c1, pi1 = u0[8], u0[1], u1[1], u1[5]
    require(all(math.isfinite(v) and v > 0 for v in (R, c0, c1, pi1)),
            "Positive SOURCE-shaped log chart violated")
    G = s.be * (c0 / c1) ** s.sigmaE / pi1
    nu = 1.0 / R - G
    require(abs(nu - metrics["collateral_dual_L"]) < 1e-12,
            "Original frozen Python funding dual projection changed")
    return nu, G, R


def numerical_gradient(s, seed, z, step=2e-6):
    result = []
    for j in range(N):
        zp, zm = list(z), list(z)
        zp[j] += step
        zm[j] -= step
        result.append(
            (exact_shape_dual(s, seed, zp)[0] -
             exact_shape_dual(s, seed, zm)[0]) / (2.0 * step)
        )
    return result


def main():
    # Semantic guard: check the SOURCE dual body against the same anchors
    # used by the independent source_L_funding_dual_irf audit.
    source = SOURCE.read_text(encoding="utf-8").replace("\r\n", "\n")
    i = source.index("noncomputable def localNormalizedCollateralDualL")
    j = source.index("def LocalScalarComplementarityL", i)
    body = source[i:j]
    for anchor in (
        "1 / Z.controlsZero.loanRate -",
        "P.entrepreneurDiscount *",
        "crraMarginal P.entrepreneurRiskAversion Z.controlsOne.consumptionL",
        "crraMarginal P.entrepreneurRiskAversion Z.controlsZero.consumptionL",
        "Z.controlsOne.inflation",
    ):
        require(anchor in body, "SOURCE normalized L dual changed: " + anchor)

    s = steady_case()
    seed = frozen_stationary_seed(s)
    pins = json.loads(P0.read_text(encoding="utf-8"))
    p0 = [[float(v) for v in row] for row in pins["P0"]]
    require(len(p0) == 16 and all(len(row) == 6 for row in p0),
            "Pinned 16x6 continuation candidate changed")
    z0 = [0.] * N
    policy0 = (0., 0., 0., 0.)
    f0 = lambda z: prefix_residual(seed, p0, "binding", policy0, z)
    res33 = max_abs(f0(z0))
    require(res33 < 1e-9, "Frozen binding predecessor no longer solves 33 Python rows")

    nu0, G, R = exact_shape_dual(s, seed, z0)
    require(s.sigmaE == 1.0 and abs(G - s.be) < 1e-12,
            "The claimed stationary CRRA reduction is not valid")
    require(abs(nu0 - (1.0 / s.rate - s.be)) < 1e-12,
            "Stationary funding-dual identity changed")
    require(nu0 > 1e-4, "Frozen B seed unexpectedly approaches funding boundary")

    # Exact four support indices in the 33-dimensional Python log chart.
    # This is the SOURCE formula's coordinate structure, not a proof of
    # functional identity for all 33 real SOURCE residuals.
    c = [0.0] * N
    c[8], c[15], c[24], c[28] = (
        -s.sigmaE * G, -1.0 / R, s.sigmaE * G, G
    )
    numeric_c = numerical_gradient(s, seed, z0)
    gradient_error = max_abs([a - b for a, b in zip(c, numeric_c)])
    require(gradient_error < 1e-7,
            "Four-coordinate funding-dual log-gradient projection failed")

    # Floating point only: compare direct forcing to the implicit
    # policy derivative for the frozen Python 33-row binding map.
    A = numerical_jacobian(f0, z0, step=2e-6)
    b = analytic_forcing(s, seed)["reserve_rate_rule_innovation"]
    dz, pivots = solve_linear(A, [-x for x in b])
    residual_linear = max_abs([
        sum(A[i][j] * dz[j] for j in range(N)) + b[i]
        for i in range(N)
    ])
    require(min(pivots) > 1e-15 and residual_linear < 1e-7,
            "Python floating-point linear tangent check failed")
    schur_float = sum(c[j] * dz[j] for j in range(N))

    checked = []
    for sign in (-1, 1):
        h = sign * H
        intervention = (h, 0., 0., 0.)
        f = lambda z: prefix_residual(seed, p0, "binding", intervention, z)
        root, _history, _ = newton(
            f, [h * x for x in dz], tolerance=2e-12
        )
        residual = max_abs(f(root))
        require(residual < 1e-9, "Nonlinear frozen policy root failed")
        nu = exact_shape_dual(s, seed, root)[0]
        require(nu > 0., "Small policy experiment left the binding-dual regime")
        checked.append({
            "innovation": h,
            "dual_L": nu,
            "max_33_row_residual": residual,
        })
    centered = (checked[1]["dual_L"] - checked[0]["dual_L"]) / (2.0 * H)
    tangent_error = abs(centered - schur_float)
    require(tangent_error < 0.02 * max(1.0, abs(schur_float)),
            "Funding-dual policy tangent and nonlinear centered test disagree")

    report = {
        "status": "NUMERICAL_FROZEN_PYTHON_33_ROOT_NOT_34_BOUNDARY",
        "date_zero_instrument": "reserve-remuneration-rule log innovation",
        "branch": "binding B, stationary frozen predecessor",
        "dimension_first_rows": N,
        "dimension_augmented": N + 1,
        "baseline_log_coordinates": [0.] * N,
        "baseline_33_residual_max_abs": res33,
        "baseline_loan_rate": R,
        "beta_entrepreneur": s.be,
        "baseline_normalized_funding_dual_L": nu0,
        "baseline_augmented_34_residual_last_component": nu0,
        "baseline_34_root": False,
        "positive_domain_and_binding_dual": True,
        "dual_log_gradient_nonzero_positions": [8, 15, 24, 28],
        "dual_log_gradient_values_at_baseline": {
            str(k): c[k] for k in (8, 15, 24, 28)
        },
        "dual_log_gradient_max_abs_float_error": gradient_error,
        "python_float_min_gauss_jordan_pivot": min(pivots),
        "python_float_linear_tangent_residual": residual_linear,
        "python_float_reduced_dual_policy_derivative": schur_float,
        "python_centered_nonlinear_dual_policy_derivative": centered,
        "python_centered_tangent_difference": tangent_error,
        "plus_minus_policy_experiments": checked,
        "inherited_initial_state_unmodified": True,
        "certification": {
            "lean_source_34_root_proved": False,
            "source_and_python_operator_equivalence_proved": False,
            "interval_inverse_bound_proved": False,
            "source_schur_nonzero_certified": False,
            "full_equilibrium_or_growth_proved": False,
        },
        "source_sha256": digest(SOURCE),
        "python_engine_sha256": digest(ENGINE),
        "preconditioner_sha256": digest(P0),
        "limitations": [
            "The frozen stationary B reference is not the zero-dual boundary point.",
            "This diagnostic uses Python, not execution of the Lean SOURCE operator.",
            "Central differences and float64 solves are not directed interval bounds.",
            "The 16x6 tail is only the pinned finite linear continuation candidate.",
            "A positive funding dual does not refute the B binding branch itself.",
        ],
    }
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n",
                      encoding="utf-8")
    print(json.dumps({
        "status": report["status"],
        "baseline_33_residual_max_abs": res33,
        "baseline_normalized_funding_dual_L": nu0,
        "python_float_reduced_dual_policy_derivative": schur_float,
        "python_centered_nonlinear_dual_policy_derivative": centered,
        "output": str(OUTPUT),
    }, indent=2))


if __name__ == "__main__":
    main()

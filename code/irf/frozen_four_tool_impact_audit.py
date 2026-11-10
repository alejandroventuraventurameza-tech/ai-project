#!/usr/bin/env python3
"""Four-instrument DATE-ZERO impact diagnostics with frozen inherited assets.

For each small announced monetary innovation, solve the same original
33-equation binding-branch nonlinear finite prefix, starting from the true
stationary predecessor rather than from make_boundary()'s rate-dependent
inherited state. Carry the existing PINNED local-linear P0 tail mapping.

This is a NUMERICAL REDUCED-PREFIX diagnostic, not an existence proof,
a verified infinite-horizon equilibrium, a causal structural IRF, or
a calibrated magnitude. Do not reuse these impact results as long-run growth
effects. No instrument is redefined as a shock to a different instrument.
"""
from __future__ import annotations

import json
import math
from pathlib import Path

from finite_irf import (
    PREFIX_ROW_NAMES,
    max_abs,
    newton,
    numerical_jacobian,
    period_metrics,
    prefix_residual,
    solve_linear,
    steady_case,
)
from frozen_stationary_prefix_audit import frozen_stationary_seed

HERE = Path(__file__).resolve().parent
SHOCK_MAGNITUDE = -1e-5
SHOCKS = {
    "reserve_rate_rule_innovation": (SHOCK_MAGNITUDE, 0.0, 0.0, 0.0),
    "reserve_quantity_rule_innovation": (0.0, SHOCK_MAGNITUDE, 0.0, 0.0),
    "reserve_requirement_level": (0.0, 0.0, SHOCK_MAGNITUDE, 0.0),
    "corridor_width_level": (0.0, 0.0, 0.0, SHOCK_MAGNITUDE),
}
METRICS = (
    "output", "capital_next_H", "capital_next_L",
    "credit_H", "credit_L", "reserve_rate", "reserves_pre",
    "loan_rate", "deposit_rate", "capital_price", "wage",
    "consumption_H", "consumption_L", "worker_consumption",
    "investment", "labor", "bank_equity", "bank_loans",
)
STRICTLY_POSITIVE_METRICS = (
    "output", "capital_next_H", "capital_next_L", "credit_H",
    "credit_L", "reserve_rate", "reserves_pre", "loan_rate",
    "deposit_rate", "capital_price", "wage", "consumption_H",
    "consumption_L", "worker_consumption", "investment",
    "labor", "bank_equity", "bank_loans",
)


def unpack_solution(s, seed, z, intervention):
    next_state = [seed.X1[k] * math.exp(z[k]) for k in range(7)]
    u0 = [seed.U0[k] * math.exp(z[7 + k]) for k in range(10)]
    u1 = [seed.U1[k] * math.exp(z[23 + k]) for k in range(10)]
    v_r, v_m, v_rho, v_corridor = intervention
    metrics = period_metrics(
        s, seed.X0, u0, next_state, u1, [v_r, v_m],
        "binding", rho=s.rho + v_rho, corridor=s.Delta + v_corridor,
    )
    return next_state, u0, u1, metrics


def main():
    s = steady_case()
    seed = frozen_stationary_seed(s)
    source = HERE / "inputs/rational_preconditioners.json"
    matrix = json.loads(source.read_text(encoding="utf-8"))
    p0 = [[float(x) for x in row] for row in matrix["P0"]]
    zero = [0.0] * 33
    no_shock = (0.0, 0.0, 0.0, 0.0)
    baseline_fun = lambda z: prefix_residual(
        seed, p0, "binding", no_shock, z,
    )
    if max_abs(baseline_fun(zero)) >= 1e-9:
        raise AssertionError("Cannot begin at an inconsistent predecessor.")

    # Preserve the scalar historical API exactly in the v_R-only case.
    h = SHOCK_MAGNITUDE
    old_scalar = prefix_residual(seed, p0, "binding", h, zero)
    vector_scalar = prefix_residual(seed, p0, "binding", (h, 0, 0, 0), zero)
    if max_abs([a-b for a, b in zip(old_scalar, vector_scalar)]) > 1e-14:
        raise AssertionError("Legacy scalar v_R interface was changed.")

    jac = numerical_jacobian(baseline_fun, zero)
    _, baseline_pivots = solve_linear(jac, [0.0] * 33)
    baseline_metrics = unpack_solution(s, seed, zero, no_shock)[3]
    snapshot = tuple(seed.X0)
    table = {}

    for name, shock in SHOCKS.items():
        if not (s.rho + shock[2] > 0 and s.Delta + shock[3] > 0):
            raise AssertionError(f"Invalid parameter domain: {name}")
        perturb = lambda z: prefix_residual(seed, p0, "binding", shock, z)
        # Exact finite-prefix forcing under fixed initial inherited state.
        eps = 1e-6
        signed_dir = tuple(1.0 if x else 0.0 for x in shock)
        fp = prefix_residual(
            seed, p0, "binding", tuple(eps*x for x in signed_dir), zero
        )
        fm = prefix_residual(
            seed, p0, "binding", tuple(-eps*x for x in signed_dir), zero
        )
        forcing = [(a-b)/(2.0*eps) for a, b in zip(fp, fm)]
        tangent, _ = solve_linear(jac, [-x for x in forcing])
        initial = [shock[next(i for i,v in enumerate(shock) if v != 0.0)]*z
                   for z in tangent]
        solution, history, _ = newton(perturb, initial, tolerance=2e-12)
        row_residuals = perturb(solution)
        residual_max = max_abs(row_residuals)
        if not residual_max < 1e-10:
            raise AssertionError(f"{name}: large nonlinear residual {residual_max}")
        x1, u0, u1, metrics = unpack_solution(s, seed, solution, shock)
        if tuple(seed.X0) != snapshot:
            raise AssertionError("Frozen predecessor mutated during solution.")
        if any(not math.isfinite(z) for z in solution):
            raise AssertionError(f"{name}: nonfinite solution")
        if any(not (metrics[k] > 0.0) for k in STRICTLY_POSITIVE_METRICS):
            raise AssertionError(f"{name}: loss of strictly positive domain")
        if not (metrics["collateral_dual_H"] > 0
                and metrics["collateral_dual_L"] > 0):
            raise AssertionError(f"{name}: binding branch lost dual positivity")
        if not (abs(metrics["collateral_slack_H"]) < 1e-7
                and abs(metrics["collateral_slack_L"]) < 1e-7):
            raise AssertionError(f"{name}: binding face no longer tight")
        if not (metrics["deposit_cap_slack"] > 0
                and metrics["loan_cap_slack"] > 0):
            raise AssertionError(f"{name}: bank cap switched regime")

        table[name] = {
            "instruments_date_zero_vR_vM_vRho_vDelta": list(shock),
            "units": (
                "two log policy-rule innovations, followed by reserve "
                "requirement and corridor-width level changes"
            ),
            "max_original_33_row_residual": residual_max,
            "newton_residual_history": history,
            "max_log_coordinate_abs": max_abs(solution),
            "date_one_rule_innovations": list(seed.e1),
            "frozen_date_zero_initial_state_unchanged": True,
            "binding_collateral_duals": [
                metrics["collateral_dual_H"], metrics["collateral_dual_L"]
            ],
            "binding_collateral_slacks": [
                metrics["collateral_slack_H"], metrics["collateral_slack_L"]
            ],
            "impact_metrics": {k: metrics[k] for k in METRICS},
            "impact_changes_from_same_predecessor": {
                k: metrics[k] - baseline_metrics[k] for k in METRICS
            },
            "impact_log_deviations_pct": {
                k: 100 * math.log(metrics[k] / baseline_metrics[k])
                for k in METRICS if (
                    metrics[k] > 0 and baseline_metrics[k] > 0
                )
            },
            "date_one_state_H_L_capital_and_faces": x1[:4],
            "largest_prefix_row_errors": sorted(
                (
                    (k, abs(v)) for k, v in zip(PREFIX_ROW_NAMES, row_residuals)
                ),
                key=lambda z: z[1], reverse=True,
            )[:4],
        }

    print(json.dumps({
        "status": "NUMERICAL_FOUR_TOOL_FROZEN_STATE_BINDING_PREFIX_ONLY",
        "scope": (
            "Small one-at-a-time date-zero shocks; original 33 nonlinear "
            "binding-branch equations; same frozen stationary inheritance. "
            "P0 is an externally validated local-linear continuation, "
            "not a certified nonlinear infinite tail."
        ),
        "initial_state": list(snapshot),
        "baseline_max_33_row_residual": max_abs(baseline_fun(zero)),
        "baseline_numerical_min_pivot": min(baseline_pivots),
        "date_one_announcements": list(seed.e1),
        "shocks": table,
        "not_established": [
            "full competitive equilibrium or transversality",
            "full policy-specific nonlinear infinite-horizon continuation",
            "both-branch multiplicity / slack branch under same shock",
            "causal policy transmission identification",
            "long-run allocative growth, welfare or calibrated effects",
        ],
    }, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()

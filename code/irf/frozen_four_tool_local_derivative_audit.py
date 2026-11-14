#!/usr/bin/env python3
"""Audit the *direct* four-tool forcing and the frozen-state IFT tangent.

This verifies local numerics for the original 33-row binding finite prefix.
It does NOT certify an infinite-horizon equilibrium, identification, a
second branch, a policy multiplier, or a long-run growth effect.
"""
from __future__ import annotations

import json
import math

from finite_irf import (
    PREFIX_ROW_NAMES,
    auxiliary,
    max_abs,
    newton,
    numerical_jacobian,
    prefix_residual,
    solve_linear,
    steady_case,
)
from frozen_four_tool_impact_audit import unpack_solution
from frozen_stationary_prefix_audit import frozen_stationary_seed
from pathlib import Path

HERE = Path(__file__).resolve().parent
EPS = 1e-6
H = 2e-6
POLICIES = {
    "reserve_rate_rule_innovation": 0,
    "reserve_quantity_rule_innovation": 1,
    "reserve_requirement_level": 2,
    "corridor_width_level": 3,
}
EXPECTED_DIRECT_ROWS = {
    "reserve_rate_rule_innovation": {
        "reserve_rate_rule_0", "loan_pricing_0", "deposit_pricing_0", "bank_balance_0",
    },
    "reserve_quantity_rule_innovation": {
        "reserve_quantity_rule_0", "bank_balance_0",
    },
    "reserve_requirement_level": {
        "deposit_pricing_0", "bank_balance_0",
    },
    "corridor_width_level": {
        "loan_pricing_0", "deposit_pricing_0",
    },
}
LOG_METRICS = (
    "output", "capital_next_H", "capital_next_L", "credit_H", "credit_L",
    "loan_rate", "reserve_rate", "reserves_pre", "investment",
    "bank_loans", "labor", "worker_consumption",
)


def impulse(index, magnitude):
    return tuple(magnitude if j == index else 0.0 for j in range(4))


def analytic_forcing(s, seed):
    """Analytic partial_d F / partial_nu, *at fixed 33 endogenous coordinates*.

    This independent chain-rule check is compared with the finite-difference
    derivative of the literal prefix_residual implementation. It is not the
    derivative of the *solved* economy, which additionally requires -J^-1.
    """
    a = auxiliary(s, seed.X0, seed.U0, seed.X1[:2], [0.0, 0.0])
    rr, money, h, xi, cb, cd = (
        a["rr"], a["money"], a["h"], a["xi"], a["cb"], a["cd"]
    )
    tightness = seed.U0[9]
    slope_rho = 1.0 - s.zeta * (1.0 - tightness) / (1.0 + tightness)
    slope_rate = -xi * s.zeta * (1.0 - tightness) / (1.0 + tightness)
    coefficients = {
        "reserve_rate_rule_innovation": {
            "reserve_rate_rule_0": -1.0,
            "loan_pricing_0": -rr,
            "deposit_pricing_0": rr + xi * s.zeta * cd / 2.0,
            "bank_balance_0": money * slope_rate / (h*h),
        },
        "reserve_quantity_rule_innovation": {
            "reserve_quantity_rule_0": -1.0,
            "bank_balance_0": -(1.0 / h - 1.0) * money,
        },
        "reserve_requirement_level": {
            "deposit_pricing_0": -cb + s.zeta * cd / 2.0,
            "bank_balance_0": money * slope_rho / (h*h),
        },
        "corridor_width_level": {
            "loan_pricing_0": -cb / s.Delta,
            "deposit_pricing_0": (
                (1.0 - s.rho) * cb / s.Delta
                - (xi - s.rho) * s.zeta * cd / (2.0 * s.Delta)
            ),
        },
    }
    idx = {name: j for j, name in enumerate(PREFIX_ROW_NAMES)}
    result = {}
    for name, entries in coefficients.items():
        if set(entries) != EXPECTED_DIRECT_ROWS[name]:
            raise AssertionError(f"Direct policy support specification drift: {name}")
        col = [0.0] * len(PREFIX_ROW_NAMES)
        for row_name, val in entries.items():
            col[idx[row_name]] = val
        result[name] = col
    return result


def check_branch(metrics, name, sign):
    if any(not math.isfinite(v) for v in metrics.values()
           if isinstance(v, (int, float))):
        raise AssertionError(f"{name}/{sign}: nonfinite metric")
    if not (metrics["collateral_dual_H"] > 0.0
            and metrics["collateral_dual_L"] > 0.0):
        raise AssertionError(f"{name}/{sign}: collateral dual lost strict positivity")
    if not (abs(metrics["collateral_slack_H"]) < 1e-7
            and abs(metrics["collateral_slack_L"]) < 1e-7):
        raise AssertionError(f"{name}/{sign}: binding collateral face changed")
    if not (metrics["deposit_cap_slack"] > 0.0
            and metrics["loan_cap_slack"] > 0.0):
        raise AssertionError(f"{name}/{sign}: bank cap changed branch")


def main():
    s = steady_case()
    seed = frozen_stationary_seed(s)
    p0_data = json.loads(
        (HERE / "inputs" / "rational_preconditioners.json").read_text(encoding="utf-8")
    )
    p0 = [[float(x) for x in row] for row in p0_data["P0"]]
    if len(p0) != 16 or any(len(row) != 6 for row in p0):
        raise AssertionError("The pinned 16x6 P0 local tail has changed.")
    if len(PREFIX_ROW_NAMES) != 33:
        raise AssertionError("Expected original 33 row names.")

    zero = [0.0] * 33
    initial_state = tuple(seed.X0)
    zero_policy = (0.0,) * 4
    f0 = lambda z: prefix_residual(seed, p0, "binding", zero_policy, z)
    if max_abs(f0(zero)) >= 1e-9:
        raise AssertionError("The frozen steady-state seed is not a root.")
    jmat = numerical_jacobian(f0, zero)
    analytic = analytic_forcing(s, seed)
    result = {}

    for name, direction in POLICIES.items():
        expected = analytic[name]
        forward = prefix_residual(seed, p0, "binding", impulse(direction, EPS), zero)
        backward = prefix_residual(seed, p0, "binding", impulse(direction, -EPS), zero)
        numerical = [(a - b) / (2.0 * EPS) for a, b in zip(forward, backward)]
        forcing_error = max_abs([a-b for a, b in zip(numerical, expected)])
        if forcing_error > 2e-6 * max(1.0, max_abs(expected)):
            raise AssertionError(f"{name}: direct analytic forcing mismatch {forcing_error}")
        support = {
            row for row, val in zip(PREFIX_ROW_NAMES, numerical) if abs(val) > 1e-8
        }
        if support != EXPECTED_DIRECT_ROWS[name]:
            raise AssertionError(f"{name}: policy entered unexpected rows {support}")
        tangent, pivots = solve_linear(jmat, [-v for v in expected])
        identity_error = max_abs([
            sum(jmat[i][k] * tangent[k] for k in range(33)) + expected[i]
            for i in range(33)
        ])
        if identity_error > 1e-7 * max(1.0, max_abs(expected)):
            raise AssertionError(f"{name}: J*x'+B identity fails")

        roots, metrics, residuals = {}, {}, {}
        for sign in (+1, -1):
            v = impulse(direction, sign * H)
            objective = lambda z: prefix_residual(seed, p0, "binding", v, z)
            root, history, _ = newton(
                objective, [sign * H * t for t in tangent], tolerance=2e-12,
            )
            residual = max_abs(objective(root))
            if residual >= 1e-10 or any(not math.isfinite(x) for x in root):
                raise AssertionError(f"{name}/{sign}: 33-row nonlinear root fails")
            _, _, _, obs = unpack_solution(s, seed, root, v)
            check_branch(obs, name, sign)
            roots[sign] = root
            metrics[sign] = obs
            residuals[sign] = residual
            if tuple(seed.X0) != initial_state:
                raise AssertionError(f"{name}/{sign}: inherited state mutated")

        estimated_tangent = [
            (a-b)/(2.0 * H) for a,b in zip(roots[+1], roots[-1])
        ]
        tangent_error = max_abs([
            a-b for a,b in zip(estimated_tangent, tangent)
        ]) / max(1.0, max_abs(tangent))
        even_remainder = max_abs([
            a+b for a,b in zip(roots[+1], roots[-1])
        ])
        odd_magnitude = max_abs([
            a-b for a,b in zip(roots[+1], roots[-1])
        ])
        if tangent_error > 0.03 or even_remainder > 0.05*odd_magnitude + 1e-9:
            raise AssertionError(
                f"{name}: tangent mismatch={tangent_error:.6g}, "
                f"even/odd={even_remainder/max(odd_magnitude, 1e-20):.6g}"
            )
        semielasticity = {}
        for metric in LOG_METRICS:
            pos, neg = metrics[+1][metric], metrics[-1][metric]
            if not (pos > 0 and neg > 0):
                raise AssertionError(f"{name}: {metric} log domain failure")
            semielasticity[metric] = (math.log(pos) - math.log(neg)) / (2.0*H)

        result[name] = {
            "unit": "log rule innovation" if direction < 2 else "parameter level",
            "direct_33_row_support": sorted(support),
            "direct_forcing_coefficients": {
                row: expected[i] for i, row in enumerate(PREFIX_ROW_NAMES)
                if row in support
            },
            "max_direct_derivative_error": forcing_error,
            "max_linear_identity_error": identity_error,
            "numerical_min_pivot": min(pivots),
            "max_centered_tangent_relative_error": tangent_error,
            "even_to_odd_log_coordinate_ratio": even_remainder/max(odd_magnitude, 1e-20),
            "plus_minus_max_nonlinear_residual": [residuals[+1], residuals[-1]],
            "impact_log_metric_derivative_per_unit_instrument": semielasticity,
        }

    print(json.dumps({
        "status": "NUMERICAL_FOUR_TOOL_FROZEN_PREFIX_LOCAL_DERIVATIVE_ONLY",
        "date_zero_shock_size_plus_minus": H,
        "finite_difference_forcing_step": EPS,
        "inherited_prefix_state_unchanged": list(initial_state),
        "equation_count": 33,
        "branch": "both entrepreneurs collateral binding, bank caps slack",
        "local_linear_tail": "pinned 16-by-6 P0; not a nonlinear infinite continuation",
        "instrument_order": list(POLICIES),
        "columns": result,
        "not_established": [
            "IFT certification with interval inverse bounds",
            "full equilibrium optimality, TVC or nonlinear infinite continuation",
            "slack collateral alternative and both-branch equilibrium multiplicity",
            "causal identification, estimation or long-run growth",
        ],
    }, indent=2))


if __name__ == "__main__":
    main()

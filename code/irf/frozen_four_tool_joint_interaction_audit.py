#!/usr/bin/env python3
"""Pairwise monetary-policy interactions on a FROZEN-inheritance 33-row prefix.

The four coordinates are (log reserve-rate rule innovation, log reserve-
quantity rule innovation, reserve-requirement LEVEL, corridor-width LEVEL).
The baseline inherited state, date-one innovations and 16x6 local-linear tail
remain IDENTICAL across every experiment.

At an interior smooth root F(z,v)=0, first-order effects add:
  J dz/dv_j = - partial F/partial v_j.
The *nonlinear* pairwise difference z(h e_i+h e_j)-z(h e_i)-z(h e_j)+z(0)
need not vanish. Measure it rather than mislabel it an independent IRF or
a causal complementarity result.

NUMERICAL diagnostic only. No certified interval inverse, endogenous
branch switching, nonlinear infinite continuation or welfare/growth claim.
"""
from __future__ import annotations

import json
import math
from itertools import combinations
from pathlib import Path

from finite_irf import (
    PREFIX_ROW_NAMES, max_abs, newton, numerical_jacobian,
    prefix_residual, solve_linear, steady_case,
)
from frozen_stationary_prefix_audit import frozen_stationary_seed
from frozen_four_tool_impact_audit import unpack_solution
from frozen_four_tool_local_derivative_audit import (
    POLICIES, analytic_forcing, check_branch,
)

HERE = Path(__file__).resolve().parent
STEPS = (1.0e-5, 5.0e-6)
METRICS = (
    "output", "capital_next_H", "capital_next_L",
    "credit_H", "credit_L", "reserve_rate", "reserves_pre",
    "loan_rate", "investment", "worker_consumption",
)


def vector(*components):
    result = [0.0] * 4
    for i, size in components:
        result[i] = size
    return tuple(result)


def mean_abs_scale(x, y):
    """Scale for a joint-minus-singles comparison, avoiding cancellation."""
    return max(1.0e-10, max_abs(x) + max_abs(y))


def main():
    s = steady_case()
    seed = frozen_stationary_seed(s)
    p0_data = json.loads(
        (HERE / "inputs" / "rational_preconditioners.json").read_text(
            encoding="utf-8"
        )
    )
    p0 = [[float(x) for x in row] for row in p0_data["P0"]]
    if len(p0) != 16 or any(len(row) != 6 for row in p0):
        raise AssertionError("Pinned 16-by-6 local tail matrix has changed")
    if len(PREFIX_ROW_NAMES) != 33 or len(POLICIES) != 4:
        raise AssertionError("Original 33-row/four-policy model has changed")
    zero = [0.0] * 33
    baseline_policy = (0.0,) * 4
    frozen_inheritance = tuple(seed.X0)
    f0 = lambda z: prefix_residual(seed, p0, "binding", baseline_policy, z)
    f0zero = f0(zero)
    if max_abs(f0zero) >= 1.0e-9:
        raise AssertionError("Zero-shock 33-row reference is not a root")
    jmat = numerical_jacobian(f0, zero)
    forcing = analytic_forcing(s, seed)
    tangents = {}
    for name in POLICIES:
        dz, pivots = solve_linear(jmat, [-v for v in forcing[name]])
        error = max_abs([
            sum(jmat[i][k] * dz[k] for k in range(33)) + forcing[name][i]
            for i in range(33)
        ])
        if error >= 1.0e-7 * max(1.0, max_abs(forcing[name])):
            raise AssertionError(f"{name}: IFT tangent linear identity fails")
        tangents[name] = dz

    baseline_metrics = unpack_solution(s, seed, zero, baseline_policy)[3]
    if any(baseline_metrics[m] <= 0 for m in METRICS):
        raise AssertionError("Log metric requires a positive baseline")
    solved = {}
    report = []

    def solution(policy, trial, label):
        key = tuple(policy)
        if key in solved:
            return solved[key]
        fun = lambda z: prefix_residual(seed, p0, "binding", key, z)
        result, iterations, _ = newton(
            fun, trial, tolerance=2.0e-12
        )
        error = max_abs(fun(result))
        if not error < 1.0e-10:
            raise AssertionError(f"{label}: nonlinear residual {error}")
        if any(not math.isfinite(z) for z in result):
            raise AssertionError(f"{label}: non-finite root")
        obs = unpack_solution(s, seed, result, key)[3]
        check_branch(obs, label, "positive")
        if tuple(seed.X0) != frozen_inheritance:
            raise AssertionError(f"{label}: inherited state was mutated")
        solved[key] = (result, obs, error)
        return solved[key]

    labels = list(POLICIES)
    for h in STEPS:
        singles = {}
        for j, name in enumerate(labels):
            tangent = tangents[name]
            singles[name] = solution(
                vector((j, h)), [h * t for t in tangent],
                f"{name}@{h}",
            )

        for i, j in combinations(range(4), 2):
            name_i, name_j = labels[i], labels[j]
            zi, mi, _ = singles[name_i]
            zj, mj, _ = singles[name_j]
            pair = vector((i, h), (j, h))
            linear = [
                h * (tangents[name_i][k] + tangents[name_j][k])
                for k in range(33)
            ]
            zpair, mpair, residual = solution(
                pair, linear, f"{name_i}+{name_j}@{h}"
            )
            mixed = [
                zpair[k] - zi[k] - zj[k] for k in range(33)
            ]
            first_order_error = max_abs([
                zpair[k] - linear[k] for k in range(33)
            ]) / mean_abs_scale(zi, zj)
            interaction_fraction = max_abs(mixed) / mean_abs_scale(zi, zj)
            if first_order_error >= 0.08:
                raise AssertionError(
                    f"{name_i}+{name_j}@{h}: local linearization error "
                    f"{first_order_error:.6g}"
                )
            if interaction_fraction >= 0.08:
                raise AssertionError(
                    f"{name_i}+{name_j}@{h}: nonlinear pairwise interaction "
                    f"{interaction_fraction:.6g} exceeds local regime"
                )

            # The direct residual forcing itself can have an h^2 cross term.
            fi = prefix_residual(
                seed, p0, "binding", vector((i, h)), zero
            )
            fj = prefix_residual(
                seed, p0, "binding", vector((j, h)), zero
            )
            fij = prefix_residual(seed, p0, "binding", pair, zero)
            direct_cross = max_abs([
                fij[k] - fi[k] - fj[k] + f0zero[k]
                for k in range(33)
            ])
            direct_scale = max(
                1.0e-10,
                max_abs([x-f0zero[k] for k,x in enumerate(fi)]),
                max_abs([x-f0zero[k] for k,x in enumerate(fj)]),
            )
            if direct_cross/direct_scale >= 0.02:
                raise AssertionError(
                    f"{name_i}+{name_j}@{h}: direct forcing too nonlinear"
                )

            cross_log = {}
            for metric in METRICS:
                a, b, c, base = (
                    mi[metric], mj[metric], mpair[metric],
                    baseline_metrics[metric],
                )
                if min(a, b, c, base) <= 0:
                    raise AssertionError(
                        f"{name_i}+{name_j}: nonpositive {metric}"
                    )
                # Exact difference of log responses relative to one baseline:
                # log(m_ij/m0)-log(m_i/m0)-log(m_j/m0).
                cross_log[metric] = (
                    math.log(c/base)-math.log(a/base)-math.log(b/base)
                )

            report.append({
                "instrument_i": name_i,
                "instrument_j": name_j,
                "pair_shock_each_coordinate": h,
                "first_order_joint_tangent_error_fraction": first_order_error,
                "nonlinear_log_coordinate_interaction_fraction": (
                    interaction_fraction
                ),
                "nonlinear_log_coordinate_interaction_max_abs": max_abs(mixed),
                "direct_residual_cross_max_abs": direct_cross,
                "direct_residual_cross_fraction": direct_cross/direct_scale,
                "joint_original_33_row_residual_max_abs": residual,
                "joint_log_metric_interaction": cross_log,
                "binding_collateral_duals": [
                    mpair["collateral_dual_H"], mpair["collateral_dual_L"],
                ],
                "bank_caps_slack": [
                    mpair["deposit_cap_slack"], mpair["loan_cap_slack"],
                ],
            })

    if len(report) != 12:
        raise AssertionError("Expected all six instrument pairs at two sizes")
    ratios = {}
    for i, j in combinations(range(4), 2):
        pair_name = f"{labels[i]} + {labels[j]}"
        series = [
            item for item in report
            if item["instrument_i"] == labels[i]
            and item["instrument_j"] == labels[j]
        ]
        large, small = series
        den = large["nonlinear_log_coordinate_interaction_max_abs"]
        num = small["nonlinear_log_coordinate_interaction_max_abs"]
        ratio = None if den <= 1.0e-11 else num / den
        # D_ij(h) = h^2 z_ij(0) + o(h^2) on a regular active set.
        # For a detectable nonzero interaction, halving h should give ~1/4.
        # This is a numerical asymptotic diagnostic, not interval/IFT proof.
        if ratio is not None and abs(ratio - 0.25) > 0.03:
            raise AssertionError(
                f"{pair_name}: interaction fails second-order scaling "
                f"diagnostic (observed ratio {ratio:.6g})"
            )
        ratios[pair_name] = ratio

    payload = {
        "status": "NUMERICAL_PAIRWISE_FOUR_TOOL_FROZEN_PREFIX_ONLY",
        "reference": "original 33 nonlinear rows, frozen predecessor",
        "tail": "pinned 16-by-6 local-linear P0",
        "branch": "H and L binding collateral; bank caps slack",
        "instrument_units": [
            "log reserve-rate policy-rule innovation",
            "log reserve-quantity policy-rule innovation",
            "reserve-requirement parameter level",
            "corridor-width parameter level",
        ],
        "steps": list(STEPS),
        "six_pairs_at_two_sizes": report,
        "smaller_to_larger_interaction_size_ratios_diagnostic_only": ratios,
        "not_established": [
            "second-order derivative existence with certified bounds",
            "any global sign of interactions or policy complementarity",
            "nonlinear infinite-horizon continuation or complete equilibrium",
            "causal interpretation, welfare, long-run capital growth",
        ],
    }
    content = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    output = HERE / "output" / "four_tool_pairwise_audit.json"
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(content, encoding="utf-8")
    print(content, end="")


if __name__ == "__main__":
    main()

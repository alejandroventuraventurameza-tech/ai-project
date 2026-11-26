#!/usr/bin/env python3
"""Check the *true frozen-predecessor* reduced-prefix zero-shock seed.

This is a numerical audit of the original 33 residual functions, NOT
a proof of equilibrium, existence, KKT optimality, or an actual IRF.
The old make_boundary() constructor is used only as a negative
comparison; its rate-dependent inherited state and compensating
date-one innovations are never taken as the frozen seed.
"""
from __future__ import annotations

import json
from pathlib import Path
from types import SimpleNamespace

from finite_irf import (
    PREFIX_ROW_NAMES,
    make_boundary,
    max_abs,
    numerical_jacobian,
    prefix_residual,
    solve_linear,
    steady_case,
)

HERE = Path(__file__).resolve().parent


def frozen_stationary_seed(s):
    """All original inherited positions at date zero, unchanged by policy."""
    predecessor = [*s.k, *s.F, s.E, s.rr, s.M]
    controls = list(s.base[6:])
    return SimpleNamespace(
        s=s,
        X0=list(predecessor),
        U0=list(controls),
        X1=list(predecessor),
        U1=list(controls),
        X2=list(s.base[:6]),
        e0=[0.0, 0.0],
        e1=[0.0, 0.0],
    )


def main():
    s = steady_case()
    matrices = json.loads(
        (HERE / "inputs/rational_preconditioners.json").read_text(encoding="utf-8")
    )
    p0 = [[float(q) for q in row] for row in matrices["P0"]]
    if len(p0) != 16 or any(len(row) != 6 for row in p0):
        raise AssertionError("Expected the existing 16-by-6 stable graph P0.")

    seed = frozen_stationary_seed(s)
    zero = [0.0] * 33
    binding_residuals = prefix_residual(seed, p0, "binding", 0.0, zero)
    if len(binding_residuals) != 33 or len(PREFIX_ROW_NAMES) != 33:
        raise AssertionError("The original literal 33 residual rows changed.")
    binding_error = max_abs(binding_residuals)
    if not binding_error < 1e-9:
        details = sorted(
            zip(PREFIX_ROW_NAMES, binding_residuals),
            key=lambda pair: abs(pair[1]), reverse=True
        )[:8]
        raise AssertionError(
            f"Frozen stationary binding seed fails residuals: "
            f"max={binding_error:.6g}; largest={details}"
        )

    # The same stationary point must not be mislabeled as the L-slack
    # branch: the predecessor has strictly active entrepreneur constraints.
    slack_error = max_abs(prefix_residual(seed, p0, "slack", 0.0, zero))
    if not slack_error > 1e-6:
        raise AssertionError(
            "Stationary L-slack branch unexpectedly indistinguishable "
            "from the binding predecessor."
        )

    # Numerical rank check for the *frozen-state* reduced local system.
    # It is not an interval-based inverse bound or an IFT theorem.
    fun = lambda z: prefix_residual(seed, p0, "binding", 0.0, z)
    jac = numerical_jacobian(fun, zero)
    _, pivots = solve_linear(jac, [0.0] * 33)
    if not min(pivots) > 1e-15:
        raise AssertionError("Numerical pivot too small at frozen-state seed.")

    # Old SOURCE differs in installed capital, inherited bank face and
    # imposed return-to-stationarity announcement at date one.
    old = make_boundary(s)
    if not (old.X0[0] < seed.X0[0] and old.X0[1] < seed.X0[1]
            and old.X0[4] < seed.X0[4]):
        raise AssertionError("Old SOURCE state unexpectedly equals predecessor.")
    if not max_abs(old.e1) > 1e-8:
        raise AssertionError("Old SOURCE imposed date-one correction missing.")

    print(json.dumps({
        "status": "NUMERICAL_FROZEN_STATIONARY_PREFIX_AUDIT_ONLY",
        "row_count": 33,
        "binding_residual_max_abs": binding_error,
        "stationary_L_slack_residual_max_abs": slack_error,
        "numerical_gauss_jordan_min_pivot": min(pivots),
        "initial_capital_frozen_H_L": list(seed.X0[:2]),
        "old_SOURCE_initial_capital_H_L": list(old.X0[:2]),
        "stationary_bank_face_frozen": seed.X0[4],
        "old_SOURCE_bank_face": old.X0[4],
        "old_SOURCE_date_one_innovations": old.e1,
        "new_frozen_seed_date_one_innovations": seed.e1,
        "hypothesis": "zero exogenous intervention, binding branch, stationary inherited state",
        "not_proved": [
            "nonzero-shock 33-row solution",
            "full infinite-horizon competitive equilibrium",
            "optimality / terminality",
            "four-instrument structural IRFs",
            "growth or welfare effects",
        ]
    }, indent=2))


if __name__ == "__main__":
    main()

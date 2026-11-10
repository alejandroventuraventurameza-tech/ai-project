#!/usr/bin/env python3
"""Finite NONLINEAR-tail S/B robustness from ONE inherited stationary state.

Uses the existing sparse stacked equations, but overrides the historical
make_boundary() initial state with frozen_stationary_seed(). Periods 2,...,T-1
are solved nonlinearly, and only the terminal boundary at T is imposed.

Both branches are compared under identical inherited X0 and same v_R shock.
A finite-horizon root with valid KKT-necessary margins is still NOT a proof
of infinite-horizon equilibrium, dynamic bank optimality, or causality.

Failures are recorded as failures, not silently relabeled as nonexistence.
"""
from __future__ import annotations

import json
import math
import sys
from pathlib import Path
import numpy as np

from finite_irf import max_abs, steady_case, validate_margins
from frozen_stationary_prefix_audit import frozen_stationary_seed
from compare_nonlinear_tail import StackedPath

HERE = Path(__file__).resolve().parent
OUT = HERE / "output" / "same_predecessor_nonlinear_tail_probe.json"
BRANCHES = ("binding", "slack")
HORIZONS = (8, 20, 40)
TERMINALS = ("linear_graph", "zero_controls")
SHOCKS = (0.0, -1e-5)


def log_percentage(x, base):
    if x <= 0 or base <= 0:
        raise AssertionError("Impact log percentage invalid")
    return 100 * math.log(x / base)


def run_one(T, terminal, branch, shock, p0, f0):
    p = StackedPath(T, branch, shock, terminal, p0, f0)
    p.base = frozen_stationary_seed(p.s)
    predecessor = tuple(p.base.X0)
    try:
        root, iterations = p.solve(tolerance=2e-11, max_iterations=14)
        residual = p.residual(root)
        norm = max_abs(residual)
        if not (norm < 1e-8 and np.all(np.isfinite(root))):
            return {
                "status": "NONLINEAR_RESIDUAL_FAILED",
                "max_residual": norm,
                "initial_inheritance_unchanged": tuple(p.base.X0) == predecessor,
            }
        rows = p.metrics(root)
        minima, failed_margins = validate_margins(rows, branch)
        if tuple(p.base.X0) != predecessor:
            raise AssertionError("Inherited date-zero state was mutated")
        return {
            "status": (
                "FINITE_REDUCED_NECESSARY_MARGIN_CANDIDATE"
                if not failed_margins else "FINITE_ROOT_BUT_INVALID_MARGINS"
            ),
            "horizon": T,
            "terminal": terminal,
            "branch": branch,
            "vR_log_innovation": shock,
            "fixed_initial_X0": list(predecessor),
            "date_one_announced_innovations": list(p.base.e1),
            "max_residual_all_nonlinear_rows": norm,
            "newton_residual_history": iterations,
            "prefix_log_state_max": max_abs(root[:33]),
            "date_two_state_log_max": max_abs(root[p.indices(2)][:6]),
            "max_state_log_across_tail": max(
                max_abs(root[p.indices(t)][:6]) for t in range(2, T+1)
            ),
            "tail_terminal_control_log_max": max_abs(root[p.indices(T)][6:]),
            "date_zero_output": rows[0]["output"],
            "date_zero_kH_next": rows[0]["capital_next_H"],
            "date_zero_kL_next": rows[0]["capital_next_L"],
            "date_zero_credit_H": rows[0]["credit_H"],
            "date_zero_credit_L": rows[0]["credit_L"],
            "date_zero_dual_L": rows[0]["collateral_dual_L"],
            "date_zero_gap_L": rows[0]["collateral_slack_L"],
            "minima": {str(k): float(v) for k,v in minima.items()},
            "failed_margins": failed_margins,
            "initial_inheritance_unchanged": True,
            "warning": (
                "Finite deterministic reduced path; no source equilibrium, "
                "bank Bellman sufficiency or exact infinite continuation"
            ),
        }
    except (ArithmeticError, ValueError, OverflowError,
            ZeroDivisionError, AssertionError, RuntimeError) as e:
        return {
            "status": "NUMERICAL_SOLVER_OR_DOMAIN_FAILURE_NOT_NONEXISTENCE",
            "horizon": T,
            "terminal": terminal,
            "branch": branch,
            "vR_log_innovation": shock,
            "type": type(e).__name__,
            "message": str(e)[:600],
            "initial_inheritance_unchanged": tuple(p.base.X0) == predecessor,
        }


def main():
    raw = json.loads(
        (HERE / "inputs" / "rational_preconditioners.json").read_text(
            encoding="utf-8"
        )
    )
    p0 = np.asarray(raw["P0"], float)
    f0 = np.asarray(raw["F0"], float)
    if p0.shape != (16, 6) or f0.shape != (6, 6):
        raise AssertionError("Pinned continuation graph dimension drift")
    table = []
    for T in HORIZONS:
        for terminal in (TERMINALS if T in (8, 20) else ("linear_graph",)):
            for branch in BRANCHES:
                outcomes = {}
                for shock in SHOCKS:
                    result = run_one(T, terminal, branch, shock, p0, f0)
                    outcomes["zero" if shock == 0 else "rate_shock"] = result
                    print(json.dumps({
                        "T": T, "terminal": terminal, "branch": branch,
                        "shock": shock, "status": result["status"],
                        "max_residual": result.get(
                            "max_residual_all_nonlinear_rows"
                        ),
                        "failed_margins": result.get("failed_margins", []),
                    }), flush=True)
                baseline, impacted = (
                    outcomes["zero"], outcomes["rate_shock"]
                )
                if (
                    baseline["status"] == "FINITE_REDUCED_NECESSARY_MARGIN_CANDIDATE"
                    and impacted["status"]
                    == "FINITE_REDUCED_NECESSARY_MARGIN_CANDIDATE"
                ):
                    impact = {
                        "output_log_pct": log_percentage(
                            impacted["date_zero_output"],
                            baseline["date_zero_output"],
                        ),
                        "kH_next_log_pct": log_percentage(
                            impacted["date_zero_kH_next"],
                            baseline["date_zero_kH_next"],
                        ),
                        "kL_next_log_pct": log_percentage(
                            impacted["date_zero_kL_next"],
                            baseline["date_zero_kL_next"],
                        ),
                        "credit_H_log_pct": log_percentage(
                            impacted["date_zero_credit_H"],
                            baseline["date_zero_credit_H"],
                        ),
                        "credit_L_log_pct": log_percentage(
                            impacted["date_zero_credit_L"],
                            baseline["date_zero_credit_L"],
                        ),
                    }
                else:
                    impact = None
                table.append({
                    "T": T, "terminal": terminal, "branch": branch,
                    "experiments": outcomes, "branch_specific_impact": impact,
                })
    # The stationary B zero-shock must always solve the nonlinear stacked
    # system when the continuation is pinned to the stationary reference.
    b_zero = [
        row["experiments"]["zero"] for row in table
        if row["branch"] == "binding"
    ]
    if any(r["status"] != "FINITE_REDUCED_NECESSARY_MARGIN_CANDIDATE"
           or r["max_residual_all_nonlinear_rows"] >= 1e-8
           for r in b_zero):
        raise AssertionError(
            "Baseline stationary B path failed at some finite horizon"
        )
    report = {
        "status": "FINITE_NONLINEAR_TAIL_SAME_PREDECESSOR_PROBE_ONLY",
        "scenarios": table,
        "necessary_benchmark": "B stationary zero-shock all horizons",
        "not_established": [
            "infinite-horizon convergence or transversality",
            "global bank, entrepreneur or household optimality",
            "a second structural equilibrium if S also has a finite root",
            "nonexistence of S if its finite Newton solve fails",
            "policy rate distinct from reserve-remuneration, and growth",
        ],
    }
    OUT.parent.mkdir(exist_ok=True, parents=True)
    OUT.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({
        "report_path": str(OUT),
        "rows": len(table),
        "successes": sum(
            outcome["status"] == "FINITE_REDUCED_NECESSARY_MARGIN_CANDIDATE"
            for row in table for outcome in row["experiments"].values()
        ),
        "failures": [
            {
                "T": row["T"], "terminal": row["terminal"],
                "branch": row["branch"],
                "statuses": [v["status"] for v in row["experiments"].values()],
            } for row in table
            if any(v["status"] != "FINITE_REDUCED_NECESSARY_MARGIN_CANDIDATE"
                   for v in row["experiments"].values())
        ],
    }, indent=2))


if __name__ == "__main__":
    main()

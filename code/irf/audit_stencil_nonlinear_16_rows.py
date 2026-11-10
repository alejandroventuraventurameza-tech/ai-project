#!/usr/bin/env python3
"""Independent NUMERICAL Jacobian audit of the 16 recurrent Python rows.

Compare the hand C0/C1 interval stencil from the directed 80-digit builder
with centered finite differences of the actual binding_period_residual()
in the same 16 log-level coordinates. The hand stencil row convention is
[B_H,B_L,FOC_H,FOC_L,...], while the nonlinear source convention is
[B_H,FOC_H,B_L,FOC_L,...]; rows 1 and 2 MUST be transposed.

This is a diagnostic for the reduced Python evaluator. Finite differences
are NOT a certified interval enclosure, nor an equivalence theorem for
the 34-row EconomicModel.lean original, nor a nonlinear infinite T limit.
"""
from __future__ import annotations

import hashlib
import importlib.util
import json
import math
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
IRF = ROOT / "code" / "irf"
V0M = ROOT / "code" / "v0m" / "cotas_2026_10_15"
OUT = IRF / "output" / "stencil_nonlinear_16_rows_audit.json"

sys.path.insert(0, str(IRF))
from finite_irf import (
    binding_period_residual, expand_compact_state, steady_case,
)

SPEC = importlib.util.spec_from_file_location(
    "_verified_linear_builder_for_independent_jacobian",
    str(V0M / "verified_linear_operator.py"),
)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError("80-digit builder module cannot be imported")
builder = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(builder)

N = 16
ROW_PERMUTATION = (0, 2, 1, 3, *range(4, N))
ROW_NAMES = (
    "H_firm_budget",
    "L_firm_budget",
    "H_capital_KKT",
    "L_capital_KKT",
    "new_collateral_face_identity",
    "bank_renewal_face",
    "capital_price_and_investment",
    "aggregate_resources",
    "worker_labor",
    "worker_deposit_Euler",
    "Rotemberg_pricing",
    "reserve_remuneration_rule",
    "reserve_quantity_rule",
    "loan_rate_OTC",
    "deposit_rate_OTC",
    "bank_funding",
)
STEPS = (1e-6, 5e-7)
ABS_TOL = 2e-5
CONVERGENCE_TOL = 1e-5


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    sn = steady_case()
    sh = builder.steady()
    c0, c1 = builder.coefficients(sh)
    if c0.shape != (16, 16) or c1.shape != (16, 16):
        raise AssertionError("16-by-16 hand stencil changed")
    if len(sn.base) != 16 or len(sh.base) != 16:
        raise AssertionError("Recurrent compact state and controls changed")
    original_levels = [float(x.midpoint()) for x in sh.base]
    max_stationary_mismatch = max(
        abs(sn.base[j] - original_levels[j])
        for j in range(N)
    )
    if max_stationary_mismatch > 1e-9:
        raise AssertionError(
            "The nonlinear and hand-stencil stationary levels differ"
        )

    def source_residual(y0, y1):
        v0 = [sn.base[j]*math.exp(y0[j]) for j in range(N)]
        v1 = [sn.base[j]*math.exp(y1[j]) for j in range(N)]
        current_state = expand_compact_state(sn, v0[:6])
        raw = binding_period_residual(
            sn, current_state, v0[6:], v1[:6], v1[6:],
            [0.0, 0.0],
        )
        if len(raw) != N:
            raise AssertionError("Nonlinear original recurrent row count changed")
        return [raw[k] for k in ROW_PERMUTATION]

    stationary = source_residual([0.0]*N, [0.0]*N)
    stationary_error = max(abs(z) for z in stationary)
    targets = [
        [[float(c0[i, j].midpoint()) for j in range(N)]
         for i in range(N)],
        [[float(c1[i, j].midpoint()) for j in range(N)]
         for i in range(N)],
    ]
    analyses = []
    for step in STEPS:
        fd = [[[0.0]*N for _ in range(N)] for _ in range(2)]
        for axis in range(2):
            for j in range(N):
                y0p, y1p = [0.0]*N, [0.0]*N
                y0m, y1m = [0.0]*N, [0.0]*N
                plus = (y0p, y1p)
                minus = (y0m, y1m)
                plus[axis][j] = step
                minus[axis][j] = -step
                fp = source_residual(y0p, y1p)
                fm = source_residual(y0m, y1m)
                for i in range(N):
                    fd[axis][i][j] = (fp[i]-fm[i])/(2*step)
        rows = []
        worst = []
        for i in range(N):
            worst_i = max(
                (abs(fd[axis][i][j]-targets[axis][i][j]), axis, j)
                for axis in range(2) for j in range(N)
            )
            rows.append({
                "name": ROW_NAMES[i],
                "max_error_abs": worst_i[0],
                "axis": ("current" if worst_i[1] == 0 else "next"),
                "column": worst_i[2],
                "reference": targets[worst_i[1]][i][worst_i[2]],
                "finite_difference": fd[worst_i[1]][i][worst_i[2]],
            })
            worst.append(worst_i[0])
        analyses.append({
            "step": step, "max_abs_row_jacobian_error": max(worst),
            "row_breakdown": rows,
            "raw_jacobians_for_step_comparison": fd,
        })
    max_fd_disagreement = max(
        abs(analyses[0]["raw_jacobians_for_step_comparison"][axis][i][j]
            - analyses[1]["raw_jacobians_for_step_comparison"][axis][i][j])
        for axis in range(2) for i in range(N) for j in range(N)
    )
    for item in analyses:
        del item["raw_jacobians_for_step_comparison"]
    good = (
        stationary_error < 1e-9
        and all(r["max_abs_row_jacobian_error"] < ABS_TOL for r in analyses)
        and max_fd_disagreement < CONVERGENCE_TOL
    )
    report = {
        "status": ("NUMERICAL_HAND_STENCIL_VS_NONLINEAR_ROWS_MATCH"
                   if good else "NUMERICAL_HAND_STENCIL_MISMATCH"),
        "scope": (
            "Nonlinear Python recurrent binding-period rows, at the same "
            "stationary 16-log-coordinate state, against hand-interval "
            "analytic coefficients; not original 34-row Lean SOURCE"
        ),
        "row_permutation_nonlinear_to_hand": list(ROW_PERMUTATION),
        "row_names_hand_order": ROW_NAMES,
        "input_sha256": {
            str(p.relative_to(ROOT)): sha256(p)
            for p in (
                IRF / "finite_irf.py",
                V0M / "verified_linear_operator.py",
                V0M / "inputs" / "hand_linearization.py",
            )
        },
        "max_steady_level_difference": max_stationary_mismatch,
        "stationary_16_row_residual_max_abs": stationary_error,
        "finite_difference_analyses": analyses,
        "two_step_jacobian_max_abs_disagreement": max_fd_disagreement,
        "acceptance_threshold_abs": ABS_TOL,
        "step_consistency_threshold": CONVERGENCE_TOL,
        "not_established": [
            "full 34-row SOURCE semantic equality",
            "certified interval Jacobian for nonlinear Python evaluator",
            "state derivative equality over a positive-radius neighborhood",
            "infinite-horizon economic equilibrium and TVC",
        ],
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({
        "status": report["status"],
        "stationary_row_error": stationary_error,
        "max_first_step_error": analyses[0]["max_abs_row_jacobian_error"],
        "max_second_step_error": analyses[1]["max_abs_row_jacobian_error"],
        "steps_disagreement": max_fd_disagreement,
        "worst_rows": sorted(analyses[0]["row_breakdown"],
                             key=lambda r:r["max_error_abs"],
                             reverse=True)[:4],
        "report": str(OUT),
    }, indent=2), flush=True)
    if not good:
        raise AssertionError(
            "Nonlinear 16-row and hand-interval stencil derivative mismatch; "
            "inspect the archived JSON, do not relax the gate automatically"
        )


if __name__ == "__main__":
    main()

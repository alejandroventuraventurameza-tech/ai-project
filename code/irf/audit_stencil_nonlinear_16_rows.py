#!/usr/bin/env python3
"""Audit 16 recurrent Python rows modulo an INVERTIBLE pledge-row operation.

The hand interval stencil reduces the firm capital Euler expression by the
pledge identity J_{t+1}=ad*Pi_{t+1}*q_{t+1}. The nonlinear evaluator retains
the unsimplified Euler plus the pledge log residual g.

Exactly, off the pledge manifold:
  f_source_i - f_hand_i
     = sdf_i*theta_i*ad*q_next * (exp(g)-1).
At the stationary binding point g=0:
  Df_source_i = Df_hand_i + (be*theta_i*J) Dg.
Hence the two 16x16 coefficient systems are RELATED BY AN INVERTIBLE
ELEMENTARY ROW OPERATION; raw equality of their rows is NOT required.

The code checks numerical differentiation and the exact algebraic identity
evaluated at test states. This is NOT a Lean/kernel SOURCE 34-row bridge or
a nonlinear invariant-graph/TVC theorem. The separate 80-digit certificate
still applies to the HAND linear operator, conditional on its source input.
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
    binding_period_residual, expand_compact_state, production, steady_case,
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
    "H_firm_budget", "L_firm_budget", "H_capital_KKT", "L_capital_KKT",
    "new_collateral_face_log_identity", "bank_renewal_face",
    "capital_price_and_investment", "aggregate_resources",
    "worker_labor", "worker_deposit_Euler", "Rotemberg_pricing",
    "reserve_remuneration_rule", "reserve_quantity_rule",
    "loan_rate_OTC", "deposit_rate_OTC", "bank_funding",
)
STEPS = (1e-6, 5e-7)
ABS_TOL = 2e-5
CONVERGENCE_TOL = 1e-5
OFF_MANIFOLD_TOL = 2e-13


def sha256(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    sn = steady_case()
    sh = builder.steady()
    c0, c1 = builder.coefficients(sh)
    if c0.shape != (N, N) or c1.shape != (N, N):
        raise AssertionError("Expected 16-by-16 analytic stencil")
    if len(sn.base) != N or len(sh.base) != N:
        raise AssertionError("Compact state/control axis changed")
    steady_levels = [float(v.midpoint()) for v in sh.base]
    levels_error = max(abs(sn.base[j]-steady_levels[j]) for j in range(N))
    if levels_error >= 1e-9:
        raise AssertionError("Stationary levels differ across builders")

    # 16 variables = six compact inherited state coordinates plus ten controls.
    def values(z):
        return [sn.base[j]*math.exp(z[j]) for j in range(N)]

    def full_source(y0, y1):
        v0, v1 = values(y0), values(y1)
        state = expand_compact_state(sn, v0[:6])
        raw = binding_period_residual(
            sn, state, v0[6:], v1[:6], v1[6:], [0., 0.]
        )
        if len(raw) != N:
            raise AssertionError("Original 16-row recurrent function changed")
        return raw, v0, v1

    def reordered(y0, y1):
        raw, _, _ = full_source(y0, y1)
        return [raw[i] for i in ROW_PERMUTATION]

    z = [0.] * N
    baseline_error = max(abs(v) for v in reordered(z, z))
    if baseline_error >= 1e-9:
        raise AssertionError("Nonlinear recurrent stationary point is not a root")

    # The explicit pledge row has g=log(J_next/(ad Pi_next q_next)).
    # Therefore its Dg row is e_(J_next)-e_(Pi_next)-e_(q_next).
    targets_hand = [
        [[float(c0[i,j].midpoint()) for j in range(N)] for i in range(N)],
        [[float(c1[i,j].midpoint()) for j in range(N)] for i in range(N)],
    ]
    correct_g = [
        (axis, col, target)
        for axis in range(2) for col in range(N)
        for target in (
            ([1 if col==2 else -1 if col in (11,12) else 0]
             if axis==1 else [0]),
        )
    ]
    # Compare directly to the 16-vector of coefficients of the pledge row.
    for axis in range(2):
        for col in range(N):
            expected = (
                1. if col == 2 else
                -1. if col in (11,12) else 0.
            ) if axis == 1 else 0.
            if abs(targets_hand[axis][4][col]-expected) > 1e-12:
                raise AssertionError("Pledge-identity Jacobian row changed")

    coeffs = {
        "H": sn.be * sn.pledge[0] * sn.J,
        "L": sn.be * sn.pledge[1] * sn.J,
    }
    # Row 4 is independent of rows 2 and 3. Let N have entries
    # N[2,4]=lambda_H and N[3,4]=lambda_L. Then N^2=0,
    # so T=I+N is invertible with T^{-1}=I-N, independently of lambdas.
    # The SAME T acts on current and next coefficient matrices.
    targets_source = [
        [list(row) for row in block] for block in targets_hand
    ]
    for name, row in (("H", 2), ("L", 3)):
        for axis in range(2):
            for col in range(N):
                targets_source[axis][row][col] += (
                    coeffs[name]*targets_hand[axis][4][col]
                )

    # Check the OFF-constraint identity, not just its linearization:
    # source FOC minus reduced FOC = sdf*theta*ad*qnext*expm1(g).
    probes = []
    for kind in ("steady", "pledge_only", "inflation_only",
                 "capital_price_only", "mixed"):
        y0, y1 = [0.]*N, [0.]*N
        if kind == "pledge_only":
            y1[2] = 0.002
        elif kind == "inflation_only":
            y1[11] = -0.0015
        elif kind == "capital_price_only":
            y1[12] = 0.0008
        elif kind == "mixed":
            y0[6], y0[7], y0[12], y0[14] = (
                0.0003, -0.0004, 0.0002, -0.0001
            )
            y1[2], y1[6], y1[7], y1[11], y1[12] = (
                -0.0009, 0.0007, -0.0002, 0.0014, -0.0005
            )
        raw, current, nxt = full_source(y0, y1)
        g = raw[4]
        marginal = production(sn, nxt[:2], nxt[6:])[3]
        for i, name in enumerate(("H","L")):
            sdf = sn.be * current[6+i]/nxt[6+i]
            pledge = sn.pledge[i]
            collateral = pledge*nxt[2]
            reduced = (
                current[12] - collateral/current[14]
                - sdf*(marginal[i]+(1-pledge)*sn.ad*nxt[12])
            )
            difference = raw[2*i+1] - reduced
            analytic = sdf*pledge*sn.ad*nxt[12]*math.expm1(g)
            probes.append({
                "probe": kind, "firm": name,
                "g_pledge_row": g,
                "actual_source_minus_reduced": difference,
                "identity_predicted": analytic,
                "error": abs(difference-analytic),
            })
    off_manifold_error = max(q["error"] for q in probes)

    analyses = []
    raw_derivatives = []
    for step in STEPS:
        fd = [[[0.]*N for _ in range(N)] for _ in range(2)]
        for axis in range(2):
            for col in range(N):
                plus0, plus1 = [0.]*N, [0.]*N
                minus0, minus1 = [0.]*N, [0.]*N
                plus = (plus0, plus1)
                minus = (minus0, minus1)
                plus[axis][col] = step
                minus[axis][col] = -step
                fplus, fminus = reordered(*plus), reordered(*minus)
                for row in range(N):
                    fd[axis][row][col] = (
                        fplus[row]-fminus[row]
                    )/(2*step)
        raw_derivatives.append(fd)
        legacy_rows, source_rows = [], []
        for row in range(N):
            raw_max = max(
                (abs(fd[axis][row][col]
                     - targets_hand[axis][row][col]), axis, col)
                for axis in range(2) for col in range(N)
            )
            restored_max = max(
                (abs(fd[axis][row][col]
                     - targets_source[axis][row][col]), axis, col)
                for axis in range(2) for col in range(N)
            )
            legacy_rows.append({
                "name": ROW_NAMES[row],
                "max_error_abs": raw_max[0],
                "axis": raw_max[1], "column": raw_max[2],
            })
            source_rows.append({
                "name": ROW_NAMES[row],
                "max_error_abs": restored_max[0],
                "axis": restored_max[1], "column": restored_max[2],
            })
        analyses.append({
            "finite_difference_step": step,
            "raw_row_equality_error_max_abs": max(
                x["max_error_abs"] for x in legacy_rows
            ),
            "row_equivalence_adjusted_error_max_abs": max(
                x["max_error_abs"] for x in source_rows
            ),
            "raw_row_violations": sorted(
                legacy_rows, key=lambda r:r["max_error_abs"],reverse=True
            )[:4],
            "row_equivalence_adjusted_worst_rows": sorted(
                source_rows, key=lambda r:r["max_error_abs"],reverse=True
            )[:4],
        })
    derivative_disagreement = max(
        abs(raw_derivatives[0][axis][row][col]
            -raw_derivatives[1][axis][row][col])
        for axis in range(2) for row in range(N) for col in range(N)
    )
    good = (
        off_manifold_error < OFF_MANIFOLD_TOL
        and baseline_error < 1e-9
        and all(
            z["row_equivalence_adjusted_error_max_abs"] < ABS_TOL
            and z["raw_row_equality_error_max_abs"] > 0.1
            for z in analyses
        )
        and derivative_disagreement < CONVERGENCE_TOL
    )
    report = {
        "status": (
            "NUMERICAL_RECURRENT_16_ROW_INVERTIBLE_PLEDGE_ROW_EQUIVALENCE"
            if good else "PLEDGE_ROW_EQUIVALENCE_FAILED"
        ),
        "scope": "Python 16-row binding recurrence, not Lean SOURCE 34-row",
        "status_evidence": {
            "algebraic_identity_for_all_positive_states": (
                "f_source_i-f_reduced_i = sdf_i*theta_i*ad*q_next*(exp(g)-1), "
                "g=log(J_next/(ad*Pi_next*q_next))"
            ),
            "stationary_derivative_row_operation": (
                "D f_source_i = D f_hand_i + "
                "(be*theta_i*J)*Dg; same transform for C0 and C1"
            ),
            "invertibility": (
                "T=I+lambda_H E_(2,4)+lambda_L E_(3,4); "
                "(T-I)^2=0, T_inverse=I-(T-I)"
            ),
            "lambda_H": coeffs["H"],
            "lambda_L": coeffs["L"],
        },
        "row_permutation_to_hand_convention": list(ROW_PERMUTATION),
        "input_sha256": {
            str(p.relative_to(ROOT)): sha256(p)
            for p in (
                IRF / "finite_irf.py",
                V0M / "verified_linear_operator.py",
                V0M / "inputs" / "hand_linearization.py",
            )
        },
        "max_stationary_level_difference": levels_error,
        "stationary_16_row_residual_max_abs": baseline_error,
        "off_pledge_manifold_identity_probes": probes,
        "off_pledge_manifold_identity_max_error": off_manifold_error,
        "finite_difference_analyses": analyses,
        "two_step_jacobian_max_abs_disagreement": derivative_disagreement,
        "acceptance_max_abs_derivative_error": ABS_TOL,
        "not_established": [
            "Lean SOURCE 34-row semantic equality with Python 16-row",
            "an interval Jacobian enclosure for Python nonlinear evaluator",
            "uniform C1 nonlinear invariant graph or economic TVC",
            "state-specific bank optimality and stochastic settlement",
            "infinite-horizon equilibrium, structural IRF, or growth theorem",
        ],
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(report,indent=2)+"\n",encoding="utf-8")
    print(json.dumps({
        "status": report["status"],
        "raw_row_max_error": analyses[0]["raw_row_equality_error_max_abs"],
        "after_elementary_row_transform_max_error": (
            analyses[0]["row_equivalence_adjusted_error_max_abs"]
        ),
        "off_manifold_identity_max_error": off_manifold_error,
        "lambda_H": coeffs["H"], "lambda_L": coeffs["L"],
        "output": str(OUT),
    },indent=2),flush=True)
    if not good:
        raise AssertionError(
            "Recurrent and hand-stencil Jacobians fail pledge-row "
            "equivalence: inspect JSON instead of relaxing tolerance"
        )


if __name__ == "__main__":
    main()

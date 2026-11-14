#!/usr/bin/env python3
"""Explore a SAME-INHERITED-STATE 34-equation boundary root in Python.

The extra unknown h is the date-zero reserve-remuneration-rule innovation.
At each h, solve all 33 B-binding prefix rows then evaluate the SOURCE-shaped
L funding dual. Bracket its zero by continuation, never by modifying X0.

Exploratory float64 calculation only. An economic SOURCE reference root,
directed-interval existence proof, and infinite-horizon equilibrium remain OPEN.
A failed bracket is a reported diagnostic, not an economic nonexistence proof.
"""
from __future__ import annotations
import hashlib
import json
import math
from pathlib import Path

from finite_irf import max_abs, newton, numerical_jacobian, prefix_residual, solve_linear, steady_case
from frozen_stationary_prefix_audit import frozen_stationary_seed
from frozen_four_tool_impact_audit import unpack_solution
from audit_frozen_python_augmented34_basepoint import exact_shape_dual

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
SOURCE = ROOT / "lean/checkpoint/modules/Ventura26LiquidityAllocation/EconomicModel.lean"
ENGINE = HERE / "finite_irf.py"
PRE = HERE / "inputs/rational_preconditioners.json"
REPORT = HERE / "output/frozen_python_augmented34_boundary_search.json"
N = 33
STEP = 0.0005
MAX_H = 0.020


def require(ok, message):
    if not ok:
        raise AssertionError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    s = steady_case()
    seed = frozen_stationary_seed(s)
    inherited = tuple(seed.X0)
    pdata = json.loads(PRE.read_text(encoding="utf-8"))
    p0 = [[float(x) for x in row] for row in pdata["P0"]]
    require(len(p0) == 16 and all(len(row) == 6 for row in p0),
            "Frozen 16x6 tail candidate changed")
    initial = [0.0] * N
    initial_residual = max_abs(prefix_residual(
        seed, p0, "binding", (0., 0., 0., 0.), initial
    ))
    require(initial_residual < 1e-9, "Invalid frozen B 33-row reference")
    start_dual = exact_shape_dual(s, seed, initial)[0]
    require(start_dual > 0, "Frozen B reference no longer has positive dual")

    def solve(h, guess):
        policy = (h, 0., 0., 0.)
        fun = lambda z: prefix_residual(seed, p0, "binding", policy, z)
        z, history, _ = newton(fun, guess, tolerance=2e-12)
        residual = max_abs(fun(z))
        require(residual < 1e-9, "33-row nonlinear root was not solved")
        nu = exact_shape_dual(s, seed, z)[0]
        require(math.isfinite(nu), "Nonfinite SOURCE-shaped funding dual")
        require(tuple(seed.X0) == inherited, "Inherited state was modified")
        return z, nu, residual, len(history)

    scanned = [{"h": 0., "dual_L": start_dual,
                "max_33_row_residual": initial_residual}]
    previous = (0.0, initial, start_dual)
    bracket = None
    failure = None
    steps = int(round(MAX_H / STEP))

    for k in range(1, steps + 1):
        h = k * STEP
        try:
            z, nu, residual, it = solve(h, previous[1])
        except (ArithmeticError, AssertionError, OverflowError,
                ZeroDivisionError, ValueError) as exc:
            failure = {"h": h, "exception": type(exc).__name__,
                       "details": str(exc)}
            break
        scanned.append({"h": h, "dual_L": nu,
                        "max_33_row_residual": residual,
                        "newton_iterations": it})
        if previous[2] > 0 and nu <= 0:
            bracket = (previous, (h, z, nu))
            break
        previous = (h, z, nu)

    result = None
    if bracket is not None:
        (lo, zlo, nulo), (hi, zhi, nuhi) = bracket
        require(nulo > 0 and nuhi <= 0,
                "Invalid sign-crossing bracket for the dual")
        for _ in range(55):
            mid = (lo + hi) / 2
            weight = (mid - lo) / (hi - lo)
            guess = [a + weight * (b-a) for a,b in zip(zlo,zhi)]
            try:
                zmid, numid, residual, _it = solve(mid, guess)
            except (ArithmeticError, AssertionError, OverflowError,
                    ZeroDivisionError, ValueError) as exc:
                failure = {"h": mid, "stage": "bisection",
                           "exception": type(exc).__name__, "details": str(exc)}
                break
            if numid > 0:
                lo, zlo, nulo = mid, zmid, numid
            else:
                hi, zhi, nuhi = mid, zmid, numid
            if abs(numid) < 1e-10 and hi - lo < 1e-8:
                break
        best_h, best_z, best_nu = (
            (lo, zlo, nulo) if abs(nulo) <= abs(nuhi)
            else (hi, zhi, nuhi)
        )
        pol = (best_h, 0., 0., 0.)
        full_res33 = max_abs(prefix_residual(seed, p0, "binding", pol, best_z))
        _, _, _, metrics = unpack_solution(s, seed, best_z, pol)
        regime = {
            "H_dual_positive": metrics["collateral_dual_H"] > 0,
            "L_dual_near_zero": abs(metrics["collateral_dual_L"]) < 1e-9,
            "H_face_binding": abs(metrics["collateral_slack_H"]) < 1e-8,
            "L_face_binding": abs(metrics["collateral_slack_L"]) < 1e-8,
            "bank_deposit_cap_slack": metrics["deposit_cap_slack"] > 0,
            "bank_loan_cap_slack": metrics["loan_cap_slack"] > 0,
        }
        result = {
            "innovation_h": best_h,
            "funding_dual_L": best_nu,
            "max_first_33_residual": full_res33,
            "max_34_residual": max(full_res33, abs(best_nu)),
            "max_abs_33_log_coordinate": max_abs(best_z),
            "regime_checks": regime,
            "all_local_regime_checks_pass": all(regime.values()),
            "baseline_33_unknowns": best_z,
        }

    # At the NEW boundary candidate (never the stationary B point),
    # evaluate the 33-by-33 float Jacobian, its inverse defect and the
    # SOURCE-shaped sparse row-34 Schur scalar. No interval claim follows.
    if result is not None:
        try:
            hstar = result["innovation_h"]
            zstar = result["baseline_33_unknowns"]
            fstar = lambda z: prefix_residual(
                seed, p0, "binding", (hstar, 0., 0., 0.), z
            )
            A = numerical_jacobian(fstar, zstar, step=2e-6)
            dh = 1e-6
            fplus = prefix_residual(
                seed, p0, "binding", (hstar+dh, 0., 0., 0.), zstar
            )
            fminus = prefix_residual(
                seed, p0, "binding", (hstar-dh, 0., 0., 0.), zstar
            )
            b = [(u-v)/(2*dh) for u,v in zip(fplus,fminus)]
            _nu, G, rate = exact_shape_dual(s, seed, zstar)
            c = [0.]*N
            c[8], c[15], c[24], c[28] = (
                -s.sigmaE*G, -1.0/rate, s.sigmaE*G, G
            )
            dz, pivots = solve_linear(A, [-v for v in b])
            schur = sum(c[j]*dz[j] for j in range(N))
            tangent_residual = max_abs([
                sum(A[i][j]*dz[j] for j in range(N)) + b[i]
                for i in range(N)
            ])
            inverse_cols = []
            for k in range(N):
                e = [0.]*N
                e[k] = 1.
                col, _ = solve_linear(A, e)
                inverse_cols.append(col)
            inverse = [
                [inverse_cols[k][i] for k in range(N)]
                for i in range(N)
            ]
            left_error = max(
                abs(sum(inverse[i][k]*A[k][j] for k in range(N))
                    - (1. if i == j else 0.))
                for i in range(N) for j in range(N)
            )
            right_error = max(
                abs(sum(A[i][k]*inverse[k][j] for k in range(N))
                    - (1. if i == j else 0.))
                for i in range(N) for j in range(N)
            )
            _zm, num, _rm, _ = solve(hstar-dh, zstar)
            _zp, nup, _rp, _ = solve(hstar+dh, zstar)
            centered_schur = (nup-num)/(2*dh)
            result["float_jacobian_probe"] = {
                "first33_jacobian": A,
                "first33_inverse_approximation": inverse,
                "policy_forcing_column_b": b,
                "sparse_funding_dual_gradient_c": {
                    str(k): c[k] for k in (8,15,24,28)
                },
                "approximate_schur_minus_c_Ainv_b": schur,
                "centered_nonlinear_dual_policy_derivative": centered_schur,
                "schur_centered_abs_difference": abs(schur-centered_schur),
                "min_abs_float_pivot": min(pivots),
                "max_left_inverse_defect": left_error,
                "max_right_inverse_defect": right_error,
                "float_inverse_infinity_norm":
                    max(sum(abs(t) for t in row) for row in inverse),
                "max_33_tangent_residual": tangent_residual,
                "true_SOURCE_Jacobian_evaluated": False,
                "directed_interval_inverse_proved": False,
            }
        except (ArithmeticError, AssertionError, OverflowError,
                ZeroDivisionError, ValueError) as exc:
            result["float_jacobian_probe_failure"] = {
                "exception": type(exc).__name__, "details": str(exc)
            }

    status = (
        "NUMERICAL_PYTHON_34_BOUNDARY_CANDIDATE_FOUND_NOT_SOURCE_PROOF"
        if result is not None and result["max_34_residual"] < 1e-9
        and result["all_local_regime_checks_pass"]
        else "NO_VALID_NUMERICAL_PYTHON_34_BOUNDARY_CANDIDATE_IN_SEARCH"
    )
    report = {
        "status": status,
        "branch": "B binding, frozen identical inherited X0",
        "unknowns": "33 Python prefix log coordinates plus reserve-rule h",
        "policy_other_three_innovations": [0., 0., 0.],
        "search_max_positive_h": MAX_H,
        "continuation_step": STEP,
        "initial_33_residual_max": initial_residual,
        "initial_source_shape_dual": start_dual,
        "scanned": scanned,
        "sign_crossing_bracket_found": bracket is not None,
        "numerical_candidate": result,
        "diagnostic_failure": failure,
        "fixed_inherited_state": list(inherited),
        "source_sha256": digest(SOURCE),
        "python_engine_sha256": digest(ENGINE),
        "preconditioner_sha256": digest(PRE),
        "source_functional_identity_proved": False,
        "source_economic_root_proved": False,
        "source_jacobian_interval_enclosed": False,
        "full_dynamic_competitive_equilibrium_proved": False,
    }
    REPORT.parent.mkdir(parents=True, exist_ok=True)
    REPORT.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n",
                      encoding="utf-8")
    print(json.dumps({
        "status": status, "first_dual": start_dual,
        "bracket_found": report["sign_crossing_bracket_found"],
        "candidate_h": result["innovation_h"] if result else None,
        "candidate_max_34_residual": result["max_34_residual"] if result else None,
        "float_schur": result.get("float_jacobian_probe", {}).get(
            "approximate_schur_minus_c_Ainv_b") if result else None,
        "centered_float_schur": result.get("float_jacobian_probe", {}).get(
            "centered_nonlinear_dual_policy_derivative") if result else None,
        "all_local_regime_checks_pass":
            result["all_local_regime_checks_pass"] if result else None,
        "failure": failure, "report": str(REPORT)
    }, indent=2))


if __name__ == "__main__":
    main()

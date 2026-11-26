#!/usr/bin/env python3
"""Numerically test the *original Python* local banking Jacobian shear.

At the frozen stationary binding root, compare the 33x33 numerical
Jacobian of finite_irf.prefix_residual to the Jacobian of a SOURCE-
shaped REALIZED-rate/reserve banking proxy built from the SAME Python
OTC slopes and primitives, plus predicted rate/quantity row shears.

An exact SOURCE/Python off-root or derivative identification is NOT
established by this test. The proxy is deliberately not evaluated
Lean SOURCE, nor is floating-point differencing an interval proof.
"""

from __future__ import annotations

import hashlib
import json
import math
from pathlib import Path

import finite_irf as model
from frozen_stationary_prefix_audit import frozen_stationary_seed
from audit_source_python_33_row_permutation import audit as row_audit

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
P0 = HERE / "inputs/rational_preconditioners.json"
ORIGINAL = HERE / "finite_irf.py"
OUT = HERE / "output/original_python_33_bank_jacobian_shear_audit.json"
N = 33
H = 2e-6
MONETARY = ((12, 13, 14, 15, 16), (28, 29, 30, 31, 32))


def check(condition, message):
    if not condition:
        raise AssertionError(message)


def jacobian(fun, z):
    rows = [[0.0] * N for _ in range(N)]
    for j in range(N):
        plus = list(z)
        minus = list(z)
        plus[j] += H
        minus[j] -= H
        fp, fm = fun(plus), fun(minus)
        check(len(fp) == len(fm) == N, "33-row evaluator drift")
        for i in range(N):
            rows[i][j] = (fp[i] - fm[i]) / (2.0 * H)
    return rows


def python_and_realized_proxy(base, p0, z):
    s = base.s
    x1, u0, compact2, u1, u2 = model.decode_prefix(base, p0, z)
    x2 = model.expand_compact_state(s, compact2)
    aux0 = model.auxiliary(s, base.X0, u0, x1[:2], base.e0)
    aux1 = model.auxiliary(s, x1, u1, x2[:2], base.e1)
    aux2 = model.auxiliary(s, x2, u2, x2[:2], [0.0, 0.0])
    original = model.prefix_residual(base, p0, "binding", (0., 0., 0., 0.), z)
    proxy = list(original)
    coefficients = []
    for date, (state, controls, next_state, next_controls, aux, aux_next) in enumerate(
        ((base.X0, u0, x1, u1, aux0, aux1),
         (x1, u1, x2, u2, aux1, aux2))
    ):
        rate_idx, quantity_idx, loan_idx, deposit_idx, bank_idx = MONETARY[date]
        rr_real = next_state[5]
        money_real = next_state[6]
        target_rr, target_money = aux["rr"], aux["money"]
        rd, rl = controls[7], controls[8]
        inflation, tightness = controls[5], controls[9]
        rho, cb, cd = aux["rho"], aux["cb"], aux["cd"]
        theta = s.zeta * (1.0 - tightness) / (1.0 + tightness)
        h_real = rho + (rd / rr_real - rho) * theta
        h_target = aux["h"]
        check(min(rr_real, money_real, target_rr, target_money,
                  h_real, h_target, inflation) > 0.0,
              "Invalid bank denominator/domain")
        bank_loans = model.dot(s.mass,
            [next_state[2 + i] / rl for i in range(2)])
        proxy[loan_idx] = rl - rr_real - cb
        proxy[deposit_idx] = (
            rr_real + (1.0 - rho) * cb
            - (rd / rr_real - rho) * s.zeta * cd / 2.0 - rd
        )
        proxy[bank_idx] = bank_loans - state[4] / inflation - (
            1.0 / h_real - 1.0
        ) * money_real
        coefficients.append({
            "rate_idx": rate_idx,
            "quantity_idx": quantity_idx,
            "loan_idx": loan_idx,
            "deposit_idx": deposit_idx,
            "bank_idx": bank_idx,
            "loan_rate": target_rr,
            "deposit_rate": -target_rr * (
                1.0 + rd * s.zeta * cd / (2.0 * rr_real * target_rr)
            ),
            "balance_rate": (
                target_money * rd * theta /
                (rr_real * h_real * h_target)
            ),
            "balance_quantity": (
                (1.0 / h_real - 1.0) * target_money
            ),
        })
    return original, proxy, coefficients


def main():
    p0 = [[float(v) for v in row]
          for row in json.loads(P0.read_text(encoding="utf-8"))["P0"]]
    check(len(p0) == 16 and all(len(x) == 6 for x in p0),
          "Frozen P0 matrix unexpectedly changed")
    s = model.steady_case()
    base = frozen_stationary_seed(s)
    z0 = [0.0] * N

    original, proxy, coefs = python_and_realized_proxy(base, p0, z0)
    check(all(abs(original[j]) < 1e-9
              for block in MONETARY for j in block[:2]),
          "Stationary seed is not a common reserve-rule root")
    check(max(abs(original[i] - proxy[i]) for i in range(N)) < 1e-9,
          "Monetary root does not collapse original and proxy banking rows")

    Jpy = jacobian(lambda z:
        python_and_realized_proxy(base, p0, z)[0], z0)
    Jproxy = jacobian(lambda z:
        python_and_realized_proxy(base, p0, z)[1], z0)
    expected = [row.copy() for row in Jproxy]
    for c in coefs:
        r, q = c["rate_idx"], c["quantity_idx"]
        for idx, k in (
            (c["loan_idx"], "loan_rate"),
            (c["deposit_idx"], "deposit_rate"),
            (c["bank_idx"], "balance_rate"),
        ):
            expected[idx] = [
                expected[idx][j] + c[k] * Jproxy[r][j]
                for j in range(N)
            ]
        idx = c["bank_idx"]
        expected[idx] = [
            expected[idx][j] + c["balance_quantity"] * Jproxy[q][j]
            for j in range(N)
        ]
    differences = [
        (abs(expected[i][j] - Jpy[i][j]), i, j)
        for i in range(N) for j in range(N)
    ]
    maximum, worst_i, worst_j = max(differences)
    check(maximum < 3e-6, (
        "Original Python banking Jacobian shear numerical discrepancy "
        f"{maximum} at row {worst_i}, coordinate {worst_j}"
    ))
    row_map = row_audit()
    check(row_map["bank_rows_identity"], "Bank-row permutation changed")
    report = {
        "status": "NUMERICAL_PYTHON_REALIZED_PROXY_BANK_JACOBIAN_SHEAR_ONLY",
        "original_python_residuals": 33,
        "compared_jacobian_entries": N * N,
        "bank_rows_compared": 6,
        "monetary_roots_checked": 4,
        "central_difference_step": H,
        "max_abs_jacobian_shear_error": maximum,
        "worst_python_row": worst_i,
        "worst_log_coordinate": worst_j,
        "root_original_vs_proxy_max_abs_gap":
            max(abs(a - b) for a, b in zip(original, proxy)),
        "source_to_python_row_permutation": row_map["source_to_python"],
        "two_date_coefficients": coefs,
        "source_runtime_evaluated": False,
        "source_python_exact_derivative_parity_proved": False,
        "interval_certified_jacobian_inverse": False,
        "infinite_horizon_equilibrium_proved": False,
        "original_python_sha256":
            hashlib.sha256(ORIGINAL.read_bytes()).hexdigest(),
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({k: report[k] for k in (
        "status", "compared_jacobian_entries",
        "max_abs_jacobian_shear_error", "worst_python_row",
        "worst_log_coordinate", "source_python_exact_derivative_parity_proved"
    )}, indent=2))


if __name__ == "__main__":
    main()

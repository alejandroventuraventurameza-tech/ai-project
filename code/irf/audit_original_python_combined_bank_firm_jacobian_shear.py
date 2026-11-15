#!/usr/bin/env python3
"""Joint 33x33 bank and firm row-shear audit on the frozen Python system.

Construct a unified SOURCE-SHAPED PYTHON PROXY: the actual original
Python finite_irf residual vector, with six realized-reserve banking
rows substituted for target-reserve banking rows (three at each date)
AND with both date-one constrained Euler rows based on the actual
next inflation and capital price rather than Python's free common
pledge chart coordinate.

At the stationary binding seed verify:
  D F_Python = T_bank+firm D F_proxy,
where T is the exact triangular output row shear:
  six bank monetary rows add rate/quantity rule differentials,
  two firm Euler rows add the common-pledge rule differential.

The ORIGINAL Python system still supplies all other rows. Therefore
this is a NUMERICAL internal row-shear audit, NOT a direct evaluation
of the Lean SOURCE 33x33 Jacobian or a proof of economic equilibrium.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

import finite_irf as model
from audit_original_python_33_bank_jacobian_shear import (
    N, H, MONETARY, jacobian, python_and_realized_proxy,
)
from audit_original_python_source_shaped_firm_rows import firm_rows
from frozen_stationary_prefix_audit import frozen_stationary_seed

HERE = Path(__file__).resolve().parent
P0 = HERE / "inputs/rational_preconditioners.json"
OUT = HERE / "output/original_python_combined_bank_firm_jacobian_shear.json"


def ensure(ok, msg):
    if not ok:
        raise AssertionError(msg)


def main():
    s = model.steady_case()
    base = frozen_stationary_seed(s)
    matrices = json.loads(P0.read_text(encoding="utf-8"))
    p0 = [[float(v) for v in row] for row in matrices["P0"]]
    ensure(len(p0) == 16 and all(len(row) == 6 for row in p0),
           "Frozen continuation P0 changed")
    z0 = [0.0] * N
    f0, _, bank_coefs = python_and_realized_proxy(base, p0, z0)
    ensure(len(f0) == 33 and max(abs(v) for v in f0) < 1e-9,
           "Stationary base is not original Python 33-row root")
    x1, u0, compact, u1, u2 = model.decode_prefix(base, p0, z0)
    common_pledge = compact[2]
    ensure(abs(f0[21]) < 1e-12, "Common terminal pledge equation not zero")

    def both_proxies(z):
        original, proxy, _ = python_and_realized_proxy(base, p0, z)
        x1, u0, compact, u1, u2 = model.decode_prefix(base, p0, z)
        x2 = model.expand_compact_state(s, compact)
        aux1 = model.auxiliary(s, x1, u1, x2[:2], base.e1)
        aux2 = model.auxiliary(s, x2, u2, x2[:2], [0.0, 0.0])
        actual_source_valued_eulers, _ = firm_rows(
            s, x1, u1, x2, u2, aux2, aux1, "binding")
        proxy[18] = actual_source_valued_eulers[1]
        proxy[20] = actual_source_valued_eulers[4]
        return original, proxy

    root_original, root_proxy = both_proxies(z0)
    root_gap = max(abs(a - b) for a, b in zip(root_original, root_proxy))
    ensure(root_gap < 1e-9,
           f"Joint SOURCE-shaped Python proxy does not share root: {root_gap}")

    J_original = jacobian(lambda z: both_proxies(z)[0], z0)
    J_proxy = jacobian(lambda z: both_proxies(z)[1], z0)
    expected = [row[:] for row in J_proxy]
    shear_rows = set()
    # Original bank rate, quantity, balance transformations are exact
    # derivatives at a monetary-rule root, computed from the frozen
    # Python algebra and verified by the independent prior audit.
    for c in bank_coefs:
        r, q = c["rate_idx"], c["quantity_idx"]
        for row, key in ((c["loan_idx"], "loan_rate"),
                         (c["deposit_idx"], "deposit_rate"),
                         (c["bank_idx"], "balance_rate")):
            shear_rows.add(row)
            expected[row] = [
                expected[row][j] + c[key] * J_proxy[r][j]
                for j in range(N)
            ]
        row = c["bank_idx"]
        expected[row] = [
            expected[row][j] + c["balance_quantity"] * J_proxy[q][j]
            for j in range(N)
        ]

    # SOURCE-valued Euler_i --> Python chart-valued Euler_i is a
    # shear by the single common terminal pledge row (index 21).
    firm_coefs = []
    for i in range(2):
        row = 18 + 2*i
        sdf = s.be * u1[i] / u2[i]
        coefficient = (
            s.pledge[i] * (-1.0/u1[8] + sdf/u2[5]) * common_pledge
        )
        firm_coefs.append({"firm": i, "row": row,
                           "pledge_row": 21, "coefficient": coefficient})
        ensure(row not in shear_rows,
               "Firm/bank output transforms unexpectedly overlap")
        shear_rows.add(row)
        expected[row] = [
            expected[row][j] + coefficient * J_proxy[21][j]
            for j in range(N)
        ]

    diffs = [
        (abs(expected[i][j] - J_original[i][j]), i, j)
        for i in range(N) for j in range(N)
    ]
    worst, wi, wj = max(diffs)
    ensure(worst < 3e-6,
           f"Joint bank/firm 33x33 row shear failed: {worst} at ({wi},{wj})")
    ensure(shear_rows == {14, 15, 16, 18, 20, 30, 31, 32},
           "Unexpected eight modified economic equations")

    # The output transformation has the form I + N, with
    # each source row targeting only UNMODIFIED policy/pledge rows.
    # Hence N squared is EXACTLY zero, and T inverse = I-N.
    targets = {12, 13, 21, 28, 29}
    ensure(not (shear_rows & targets), "Output shear is not unit triangular")
    inv_max = 0.0
    for i in range(N):
        for j in range(N):
            reconstructed = expected[i][j]
            if i in {18, 20}:
                c = firm_coefs[(i-18)//2]["coefficient"]
                reconstructed -= c * expected[21][j]
            for c in bank_coefs:
                if i == c["loan_idx"]:
                    reconstructed -= c["loan_rate"] * expected[c["rate_idx"]][j]
                if i == c["deposit_idx"]:
                    reconstructed -= c["deposit_rate"] * expected[c["rate_idx"]][j]
                if i == c["bank_idx"]:
                    reconstructed -= (
                        c["balance_rate"] * expected[c["rate_idx"]][j] +
                        c["balance_quantity"] * expected[c["quantity_idx"]][j]
                    )
            inv_max = max(inv_max, abs(reconstructed - J_proxy[i][j]))
    ensure(inv_max < 3e-12, "Unit-triangular shear inverse verification failed")

    report = {
        "status": "NUMERICAL_INTERNAL_COMBINED_BANK_FIRM_33_JACOBIAN_SHEAR",
        "jacobian_rows": N,
        "jacobian_cols": N,
        "entries_compared": N * N,
        "eight_sheared_rows": sorted(shear_rows),
        "five_unchanged_driver_rows": sorted(targets),
        "bank_rows_sheared": 6,
        "firm_euler_rows_sheared": 2,
        "monetary_rule_rows_used": [12, 13, 28, 29],
        "common_pledge_row_used": 21,
        "unit_triangular_shear_inverse_tested": True,
        "max_abs_joint_jacobian_error": worst,
        "max_abs_shear_inverse_error": inv_max,
        "worst_row": wi,
        "worst_coordinate": wj,
        "root_original_proxy_max_abs_gap": root_gap,
        "firm_coefficients": firm_coefs,
        "bank_coefficients": bank_coefs,
        "source_lean_residual_directly_evaluated": False,
        "actual_SOURCE_python_cross_language_jacobian_parity_proved": False,
        "root_invertibility_interval_certified": False,
        "full_equilibrium_proved": False,
        "python_sha256": hashlib.sha256((HERE/"finite_irf.py").read_bytes()).hexdigest(),
        "p0_sha256": hashlib.sha256(P0.read_bytes()).hexdigest(),
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({k: report[k] for k in (
        "status", "entries_compared", "max_abs_joint_jacobian_error",
        "max_abs_shear_inverse_error", "eight_sheared_rows",
        "actual_SOURCE_python_cross_language_jacobian_parity_proved"
    )}, indent=2))


if __name__ == "__main__":
    main()

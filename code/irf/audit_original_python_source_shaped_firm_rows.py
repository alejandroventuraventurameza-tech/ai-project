#!/usr/bin/env python3
"""Independent SOURCE-shaped firm-block audit of frozen Python's actual 33 rows.

For date zero, check six separate H/L budget, constrained Euler, and
binding collateral rows. For date one, check the four H/L budget/Euler
rows, while both binding collateral gaps factor through the ONE common
pledge value gap of the six-coordinate date-two chart. They vanish
only when the common-pledge row vanishes, not off-root. A separate
common-pledge equation identifies next nominal liquidation value.

Uses the original Python production and auxiliary primitives for
marginal products and cash flows. Therefore this is a same-Python
formula/row-layout check against manually transcribed SOURCE economic
equations, NOT evaluation of the Lean SOURCE functions or certified
cross-language equality. It does not establish any economic root.
"""
from __future__ import annotations

import hashlib
import json
import math
from pathlib import Path

import finite_irf as model
from frozen_stationary_prefix_audit import frozen_stationary_seed

HERE = Path(__file__).resolve().parent
SOURCE = HERE.parents[1] / "lean/checkpoint/modules/Ventura26LiquidityAllocation/EconomicModel.lean"
PYTHON = HERE / "finite_irf.py"
P0 = HERE / "inputs/rational_preconditioners.json"
OUT = HERE / "output/original_python_source_shaped_firm_rows.json"

# Literal bank-neutral SOURCE firm equations. Payment-rate and collateral
# variables have the original SOURCE date timing: current controls and
# NEXT-period inflation/capital-price form nominal pledge face.
def firm_rows(s, current, controls, following, following_controls, next_aux,
              current_aux, branch, common_pledge=None):
    residuals = []
    implied_faces = []
    for i in range(2):
        pledge = (s.pledge[i] * (1.0 - s.delta)
                  * following_controls[5] * following_controls[6])
        sdf = s.be * controls[i] / following_controls[i]
        euler_pledge = (s.pledge[i] * common_pledge
                        if common_pledge is not None else pledge)
        wealth = current_aux["N"][i]
        budget = (controls[i] + controls[6] * following[i]
                  - following[2 + i] / controls[8] - wealth)
        if branch == "slack" and i == 1:
            euler = (controls[6] - sdf *
                     (next_aux["uk"][i] + (1.0 - s.delta) * following_controls[6]))
            regime = controls[8] * sdf / following_controls[5] - 1.0
        else:
            euler = (controls[6] - euler_pledge / controls[8] -
                     sdf * (next_aux["uk"][i] +
                            (1.0 - s.delta) * following_controls[6] -
                            euler_pledge / following_controls[5]))
            regime = following[2 + i] - pledge * following[i]
        residuals.extend([budget, euler, regime])
        implied_faces.append(pledge * following[i])
    return residuals, implied_faces


def require(condition, msg):
    if not condition:
        raise AssertionError(msg)


def compare(actual, predicted, name, tolerance=1e-10):
    error = abs(actual - predicted)
    require(math.isfinite(error) and error < tolerance,
            f"{name}: actual={actual!r} source-shaped={predicted!r} err={error!r}")
    return error


def main():
    source = SOURCE.read_text(encoding="utf-8")
    for anchor in (
        "noncomputable def localReducedFirmBudgetResidual",
        "noncomputable def localReducedFirmCapitalEulerResidual",
        "noncomputable def localReducedFirmRegimeResidual",
        "localPrefixPledgeUnit",
        "d.nextFace i - localPrefixPledgeUnit P d i * d.nextCapital i",
        "d.controls.capitalPrice * d.nextCapital i",
    ):
        require(anchor in source, "SOURCE firm equation definition drift: " + anchor)

    matrices = json.loads(P0.read_text(encoding="utf-8"))
    p0 = [[float(x) for x in row] for row in matrices["P0"]]
    require(len(p0) == 16 and all(len(x) == 6 for x in p0),
            "Expected frozen 16x6 continuation")
    s = model.steady_case()
    base = frozen_stationary_seed(s)
    charts = ([0.0] * 33,
              [3e-4 * math.sin(i * .41 + .2) for i in range(33)],
              [-4e-4 * math.cos(i * .36 + .3) for i in range(33)])
    shocks = [(0.0, 0.0, 0.0, 0.0),
              (1e-4, 0.0, 0.0, 0.0),
              (0.0, 1e-4, 0.0, 0.0),
              (0.0, 0.0, 1e-4, 0.0),
              (0.0, 0.0, 0.0, 1e-4)]
    checked = 0
    worst = 0.0
    date_one_regime_max = 0.0
    for z in charts:
        x1, u0, x2compact, u1, u2 = model.decode_prefix(base, p0, z)
        x2 = model.expand_compact_state(s, x2compact)
        aux1 = model.auxiliary(s, x1, u1, x2[:2], base.e1)
        aux2 = model.auxiliary(s, x2, u2, x2[:2], [0., 0.])
        # SOURCE reduced date-one firm's two nominal face constraints
        # are encoded into the common date-two pledge chart, not 2 rows.
        date1, implied = firm_rows(s, x1, u1, x2, u2, aux2, aux1, "binding")
        date1_python_coordinate, _ = firm_rows(
            s, x1, u1, x2, u2, aux2, aux1, "binding",
            common_pledge=x2compact[2])
        # Both original SOURCE date-one raw collateral equations
        # are proportional to the SINGLE common-pledge mismatch.
        # They only vanish IF the Python row 21 vanishes.
        expected_pledge = (1.0 - s.delta) * u2[5] * u2[6]
        common_pledge_gap = x2compact[2] - expected_pledge
        for i in range(2):
            expected_gap = s.pledge[i] * x2[i] * common_pledge_gap
            date_one_regime_max = max(date_one_regime_max, abs(date1[3*i+2]))
            worst = max(worst, compare(date1[3*i+2], expected_gap,
                        "date1 raw collateral gap proportional to common pledge row"))
            checked += 1
        for shock in shocks:
            e0 = [base.e0[0] + shock[0], base.e0[1] + shock[1]]
            aux0 = model.auxiliary(s, base.X0, u0, x1[:2], e0,
                                   rho=s.rho + shock[2],
                                   corridor=s.Delta + shock[3])
            date0, _ = firm_rows(s, base.X0, u0, x1, u1, aux1, aux0,
                                 "binding")
            residuals = model.prefix_residual(base, p0, "binding", shock, z)
            require(len(residuals) == 33, "Frozen Python row count drift")
            for idx, predicted in enumerate(date0):
                if idx % 3 == 2:
                    # Python implements positive-domain equivalent log of
                    # (face / pledge / capital), not SOURCE raw-face gap.
                    i = idx // 3
                    ratio = x1[2+i] / (
                        s.pledge[i] * (1.0-s.delta) * u1[5] * u1[6] * x1[i])
                    require(ratio > 0, "Invalid log-face collateral domain")
                    predicted = math.log(ratio)
                worst = max(worst, compare(residuals[idx], predicted,
                                            f"date0 firm row {idx}"))
                checked += 1
            for i in range(2):
                for offset in (0, 1):
                    idx = 17 + 2*i + offset
                    # Original SOURCE Euler is expressed with the
                    # inflation/capital-price pledge, while Python's
                    # off-root chart uses the independent common pledge.
                    # Their difference is exactly linear in row-21's
                    # UNLOGGED common pledge gap.
                    if offset == 1:
                        sdf = s.be * u1[i] / u2[i]
                        correction = (s.pledge[i] * common_pledge_gap *
                            (-1.0 / u1[8] + sdf / u2[5]))
                        worst = max(worst, compare(
                            date1_python_coordinate[3*i+1] -
                            date1[3*i+1], correction,
                            f"date1 Euler common-pledge shear firm {i}"))
                        checked += 1
                    worst = max(worst, compare(residuals[idx],
                         date1_python_coordinate[3*i+offset],
                         f"date1 Python-coordinate firm row {idx}"))
                    checked += 1
            worst = max(worst, compare(residuals[21],
                    math.log(x2compact[2] / expected_pledge),
                    "date1 common pledge row 21"))
            checked += 1
    report = {
        "status": "NUMERICAL_ORIGINAL_PYTHON_SOURCE_SHAPED_FIRM_BLOCK_ONLY",
        "charted_points": len(charts),
        "four_instrument_scenarios_plus_baseline": len(shocks),
        "firm_rows_and_collateral_identities_checked": checked,
        "max_abs_firm_row_error": worst,
        "date_one_raw_collateral_gap_max_abs_off_root": date_one_regime_max,
        "date_one_raw_collateral_gaps_proportional_to_common_pledge_gap": True,
        "date_one_euler_correction_proportional_to_common_pledge_gap": True,
        "date_zero_regime_normalization": "log face-to-pledge ratio vs SOURCE raw gap",
        "date_one_common_pledge_normalization": "log common pledge value ratio",
        "source_firm_primitive_functions_actually_evaluated": False,
        "exact_full_source_python_equivalence_proved": False,
        "root_or_equilibrium_certified": False,
        "python_sha256": hashlib.sha256(PYTHON.read_bytes()).hexdigest(),
        "source_sha256": hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()

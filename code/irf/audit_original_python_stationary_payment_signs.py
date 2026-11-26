#!/usr/bin/env python3
"""Audit the ORIGINAL frozen Python stationary payment-sign regime.

This is a numerical sign and residual test, not a rigorous interval proof
of a SOURCE equilibrium or a validated nonlinear root. At the frozen
predecessor, both economic dates must have a negative-minus-shock
settlement surplus and a positive-plus-shock surplus. The reserve-buffer
inequality is tested separately, including its exact symmetric-payment
algebra and the policy-rule residuals at the stationary 33-equation seed.
"""

from __future__ import annotations

import hashlib
import json
import math
from fractions import Fraction
from pathlib import Path

import finite_irf as model
from frozen_stationary_prefix_audit import frozen_stationary_seed

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
OUT = HERE / "output/original_python_stationary_bank_payment_signs.json"
P0 = HERE / "inputs/rational_preconditioners.json"


def require(ok, msg):
    if not ok:
        raise AssertionError(msg)


def report_date(s, state, controls, next_state, next_controls, innovations, date):
    aux = model.auxiliary(s, state, controls, next_state[:2], innovations)
    realized_rate, realized_reserves = next_state[5:7]
    target_rate, target_reserves = aux["rr"], aux["money"]
    rho = aux["rho"]
    deposits = target_reserves / aux["h"]
    require(deposits > 0 and realized_rate > 0 and realized_reserves > 0,
            "Nonpositive banking domain")
    xi_real = controls[7] / realized_rate
    spread = xi_real - rho
    require(spread > 0, "Deposit-to-reserve rate ratio does not exceed requirement")
    stationary_ratio_reserves = (rho + spread / 15.0) * deposits
    ratio_gap = abs(realized_reserves - stationary_ratio_reserves)
    require(ratio_gap < 1e-10,
            "Stationary 1/15 reserve/deposit ratio fails numerical audit")
    buffer = realized_reserves - rho * deposits
    exposure = (xi_real - rho) * deposits
    margin_minus = exposure * s.zeta - buffer
    margin_plus = exposure * s.zeta + buffer
    surplus_minus = buffer - s.zeta * exposure
    # Exact rational verification of the finite binary64 INPUT VALUES,
    # not an enclosure for the unknown exact SOURCE equilibrium.
    q = Fraction.from_float
    qreserve = q(realized_reserves)
    qrho = q(rho)
    qdeposits = q(deposits)
    qxi = q(controls[7]) / q(realized_rate)
    qzeta = Fraction(1, 5)
    exact_buffer = qreserve - qrho * qdeposits
    exact_exposure = (qxi - qrho) * qdeposits
    exact_minus = exact_buffer - qzeta * exact_exposure
    exact_plus = exact_buffer + qzeta * exact_exposure
    require(exact_minus < -Fraction(41, 100),
            "Exact binary64-input negative-shock surplus lost 0.41 bound")
    require(exact_plus > Fraction(83, 100),
            "Exact binary64-input positive-shock surplus lost 0.83 bound")
    surplus_plus = buffer + s.zeta * exposure

    require(abs(realized_rate - target_rate) < 1e-11,
            "Frozen seed failed realized-rate equals target")
    require(abs(realized_reserves - target_reserves) < 1e-11,
            "Frozen seed failed realized-reserves equals target")
    require(exposure > 0, "Shock exposure must be positive")
    require(margin_minus > 1e-10 and margin_plus > 1e-10,
            "Strict buffer inequalities fail at the frozen seed")
    require(surplus_minus < 0 < surplus_plus,
            "Strict settlement sign regime fails at the frozen seed")
    require(math.isclose(buffer / exposure,
        s.zeta * (1 - controls[9]) / (1 + controls[9]),
        abs_tol=5e-12, rel_tol=5e-12),
        "Stationary reserve buffer/OTC matching ratio identity failed")

    remain = model.remaining_residuals(
        s, state, controls, next_state, next_controls,
        aux, model.auxiliary(s, next_state, next_controls,
            next_state[:2], [0., 0.]))
    require(max(abs(remain[i]) for i in (6, 7)) < 1e-11,
            "Stationary reserve policy residuals not zero")
    return {
        "date": date,
        "buffer": buffer,
        "rate_requirement_spread": spread,
        "bank_deposits": deposits,
        "stationary_reserve_ratio_abs_gap": ratio_gap,
        "shock_exposure": exposure,
        "buffer_to_exposure": buffer / exposure,
        "negative_shock_surplus": surplus_minus,
        "positive_shock_surplus": surplus_plus,
        "strict_minus_margin": margin_minus,
        "exact_binary64_input_minus_lt_negative_0_41": bool(
            exact_minus < -Fraction(41, 100)),
        "exact_binary64_input_plus_gt_0_83": bool(
            exact_plus > Fraction(83, 100)),
        "exact_binary64_input_minus_numerator": str(exact_minus.numerator),
        "exact_binary64_input_minus_denominator": str(exact_minus.denominator),
        "exact_binary64_input_plus_numerator": str(exact_plus.numerator),
        "exact_binary64_input_plus_denominator": str(exact_plus.denominator),
        "strict_plus_margin": margin_plus,
        "loan_reserve_rate_realized_target_abs_gap": abs(
            realized_rate - target_rate),
        "reserve_quantity_realized_target_abs_gap": abs(
            realized_reserves - target_reserves),
        "rate_policy_residual": remain[6],
        "quantity_policy_residual": remain[7],
    }


def main():
    s = model.steady_case()
    require(math.isclose(s.zeta, .2, abs_tol=0, rel_tol=1e-15),
            "Original Python binary payment magnitude drift")
    require(math.isclose(s.aa, .5, abs_tol=0, rel_tol=1e-15),
            "Original Python matching share drift")
    require(s.tight <= 1 and s.tight > 0,
            "Original stationary tightness outside low branch")
    base = frozen_stationary_seed(s)
    p0 = [[float(v) for v in row]
          for row in json.loads(P0.read_text(encoding="utf-8"))["P0"]]
    require(len(p0) == 16 and all(len(row) == 6 for row in p0),
            "Frozen 16x6 continuation changed")
    z = [0.0] * 33
    x1, u0, x2c, u1, u2 = model.decode_prefix(base, p0, z)
    x2 = model.expand_compact_state(s, x2c)
    rows = model.prefix_residual(base, p0, "binding",
                                 (0., 0., 0., 0.), z)
    require(len(rows) == 33 and max(abs(v) for v in rows) < 1e-9,
            "Original 33-equation stationary seed not a numerical root")
    dates = [
        report_date(s, base.X0, u0, x1, u1, base.e0, 0),
        report_date(s, x1, u1, x2, u2, base.e1, 1),
    ]
    require(all(math.isclose(dates[0][key], dates[1][key],
                abs_tol=1e-10, rel_tol=1e-10)
                for key in ("buffer", "shock_exposure",
                            "strict_minus_margin", "strict_plus_margin")),
            "Stationary dates disagree")
    report = {
        "status": "NUMERICAL_STATIONARY_ORIGINAL_PYTHON_STRICT_PAYMENT_SIGNS",
        "root_33_residual_max_abs": max(abs(v) for v in rows),
        "branches": "binding",
        "shock_magnitude": s.zeta,
        "dates": dates,
        "min_strict_sign_margin": min(
            min(d["strict_minus_margin"], d["strict_plus_margin"])
            for d in dates),
        "finite_precision_not_interval_certified": True,
        "binary64_inputs_verified_exactly_by_fraction_arithmetic": True,
        "exact_economic_real_inputs_enclosed": False,
        "actual_Lean_SOURCE_economy_instantiated": False,
        "full_equilibrium_proved": False,
        "source_code_sha256": hashlib.sha256(
            (HERE / "finite_irf.py").read_bytes()).hexdigest(),
        "p0_sha256": hashlib.sha256(P0.read_bytes()).hexdigest(),
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()

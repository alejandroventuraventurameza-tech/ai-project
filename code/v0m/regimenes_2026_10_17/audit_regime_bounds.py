"""Arithmetic audit of analytical regime barriers; no paths or IRFs."""
from pathlib import Path
import hashlib
import importlib.util
import json

HERE = Path(__file__).resolve().parent
INPUT = HERE.parent / "cotas_2026_10_15" / "verified_linear_operator.py"
spec = importlib.util.spec_from_file_location("previous_interval_bounds", INPUT)
bounds = importlib.util.module_from_spec(spec)
spec.loader.exec_module(bounds)


def enclosure(value):
    return [str(value.lo), str(value.hi)]


def main():
    s = bounds.steady()
    I = bounds.I
    denominator = 2 * s.sigmaE + 2
    r_mu = (1 / (s.be * s.rate)).ln() / denominator
    r_deposit = (1 / (s.be * s.rd)).ln() / denominator
    radius = I(".007")
    mu_floor = (-radius).exp() / s.rate - s.be * (
        (2 * s.sigmaE + 1) * radius
    ).exp()
    deposit_floor = 1 - s.rd * s.be * (denominator * radius).exp()
    u = s.J / (s.rate * s.q)
    elasticities = [theta * u / (1 - theta * u) for theta in s.pledge]

    # Check directed enclosures before reporting rounded prose values.
    assert r_mu.lo > radius.hi
    assert mu_floor.lo > bounds.D(".00082951")
    assert deposit_floor.lo > bounds.D(".00276782")
    assert elasticities[1].lo > elasticities[0].hi
    out = {
        "scope": (
            "Directed interval arithmetic for analytical inequalities in "
            "sections 58-60; does not establish existence on these tubes, "
            "regime-switching trajectories, empirical calibration or IRFs."
        ),
        "input_sha256": hashlib.sha256(INPUT.read_bytes()).hexdigest(),
        "sigma_E": enclosure(s.sigmaE),
        "R_L": enclosure(s.rate),
        "R_D": enclosure(s.rd),
        "r_mu": enclosure(r_mu),
        "r_deposit": enclosure(r_deposit),
        "illustrative_log_tube": enclosure(radius),
        "mu_lower_bound_formula_at_tube": enclosure(mu_floor),
        "deposit_corner_lower_bound_formula_at_tube": enclosure(deposit_floor),
        "conditional_capacity_elasticities": [enclosure(x) for x in elasticities],
        "conditional_relative_cash_threshold": enclosure(
            elasticities[1] - elasticities[0]
        ),
        "release_Eexp_required_at_steady_rate": enclosure(1 / (s.be * s.rate)),
        "annual_implications_if_test_parameters_were_quarterly": {
            "depreciation": enclosure(1 - s.ad ** 4),
            "beta_W": enclosure(s.bw ** 4),
            "beta_E": enclosure(s.be ** 4),
            "bank_exit": enclosure(1 - (1 - s.eta) ** 4),
        },
    }
    (HERE / 'regime_bounds.json').write_text(json.dumps(out, indent=2) + '\n', encoding='utf-8', newline='\n')
    print(
        "Analytical regime thresholds and rounded bounds verified; "
        "no macroeconomic simulation performed."
    )


if __name__ == "__main__":
    main()

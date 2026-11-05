"""Stress-check new handwritten derivations; this is not a Lean proof."""
from collections import Counter
from datetime import datetime, timezone
from fractions import Fraction as Q
from pathlib import Path
import cmath
import hashlib
import json
import math
import random

HERE = Path(__file__).resolve().parent
PAPER = HERE.parents[1] / 'paper' / 'paper.tex'
SEED = 20261017
DRAWS = 5000


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def funding_checks(rng):
    regimes = Counter()
    support_comparisons = 0
    rejected_bad_slopes = 0
    for n in range(DRAWS):
        rd = Q(rng.randint(50, 150), 100)
        rl = rd + Q(rng.randint(1, 50), 100)
        cap = Q(rng.randint(1, 1000), 100)

        # Independent minimum-of-affine representation versus raw portfolios.
        z = lambda f: min(f / rl, f / rd)
        b_raw = cap / rl * Q(rng.randint(0, 100), 100)
        a_raw = Q(rng.randint(0, 1000), 100)
        f_raw = rl * b_raw - rd * a_raw
        b = max(f_raw, 0) / rl
        a = max(-f_raw, 0) / rd
        assert rl * b - rd * a == f_raw
        assert b - a == z(f_raw)
        assert b_raw - a_raw <= b - a
        assert rl * b <= rl * b_raw <= cap
        assert (b_raw - a_raw < b - a) == (b_raw > 0 and a_raw > 0)
        # A common future face gives the same real payment in every child.
        for inflation in (Q(4, 5), Q(1), Q(6, 5)):
            assert (rl * b_raw - rd * a_raw) / inflation == (rl * b - rd * a) / inflation

        lower, upper = 1 / rl, 1 / rd
        case = n % 5
        if case == 0:
            name = "deposit"
            face, dual, discount = -cap, Q(0), upper
        elif case == 1:
            name = "zero_face"
            face, dual = Q(0), Q(0)
            discount = lower + Q(rng.randint(0, 100), 100) * (upper - lower)
        elif case == 2:
            name = "slack_positive_loan"
            face, dual, discount = cap * Q(rng.randint(1, 99), 100), Q(0), lower
        elif case == 3:
            name = "active_zero_dual"
            face, dual, discount = cap, Q(0), lower
        else:
            name = "active_positive_dual"
            face = cap
            dual = lower * Q(rng.randint(1, 99), 100)
            discount = lower - dual
        regimes[name] += 1
        assert discount > 0
        assert cap - face >= 0 and dual >= 0 and dual * (cap - face) == 0
        b, a = max(face, 0) / rl, max(-face, 0) / rd
        z_b = rl * (discount + dual) - 1
        z_a = 1 - rd * discount
        assert z_b >= 0 and z_a >= 0 and z_b * b == z_a * a == 0
        assert cap - rl * b >= 0 and dual * (cap - rl * b) == 0
        slope = discount + dual
        probes = [Q(0), face, -2 * cap, 2 * cap]
        probes += [Q(rng.randint(-2000, 2000), 100) for _ in range(4)]
        for g in probes:
            assert z(g) <= z(face) + slope * (g - face)
            support_comparisons += 1
        # Negative controls: slopes outside the zero-face interval must fail.
        assert not z(Q(1)) <= z(Q(0)) + (lower - 1)
        assert not z(Q(-1)) <= z(Q(0)) - (upper + 1)
        rejected_bad_slopes += 2
    assert set(regimes.values()) == {DRAWS // 5}
    return {
        "raw_portfolio_draws": DRAWS,
        "financial_regime_draws": dict(regimes),
        "exact_rational_support_comparisons": support_comparisons,
        "invalid_slopes_rejected": rejected_bad_slopes,
        "scope": "Exact rational checks on sampled inputs; not universal theorem verification.",
    }


def output_at_optimal_labor(k, masses, productivity, labor, alpha, beta):
    # Obtain employment through a common wage and original production FOCs.
    b = [productivity[i] * k[i] ** alpha for i in range(2)]
    g = sum(masses[i] * b[i] ** (1 / (1 - beta)) for i in range(2))
    wage = beta * (g / labor) ** (1 - beta)
    employment = [(beta * b[i] / wage) ** (1 / (1 - beta)) for i in range(2)]
    output = [b[i] * employment[i] ** beta for i in range(2)]
    return sum(masses[i] * output[i] for i in range(2)), output, employment


def allocation_checks(rng):
    maximum_identity_error = 0.0
    maximum_derivative_error = 0.0
    maximum_competitor_ratio = 0.0
    for _ in range(DRAWS):
        alpha = rng.uniform(0.1, 0.55)
        beta = rng.uniform(0.1, 0.9 - alpha)
        d = 1 - alpha - beta
        masses = [rng.uniform(0.2, 2) for _ in range(2)]
        productivity = [rng.uniform(0.5, 2) for _ in range(2)]
        capital = [rng.uniform(0.2, 20) for _ in range(2)]
        labor = rng.uniform(0.5, 20)
        total_capital = sum(masses[i] * capital[i] for i in range(2))
        output, firm_output, employment = output_at_optimal_labor(
            capital, masses, productivity, labor, alpha, beta
        )
        assert math.isclose(sum(masses[i] * employment[i] for i in range(2)), labor, rel_tol=2e-13)
        z_a = sum(masses[i] * productivity[i] ** (1 / d) for i in range(2))
        efficient_k = [total_capital * productivity[i] ** (1 / d) / z_a for i in range(2)]
        efficient_l = [labor * productivity[i] ** (1 / d) / z_a for i in range(2)]
        efficient_output_direct = sum(
            masses[i] * productivity[i] * efficient_k[i] ** alpha * efficient_l[i] ** beta
            for i in range(2)
        )
        efficient_output = total_capital ** alpha * labor ** beta * z_a ** d
        assert math.isclose(efficient_output, efficient_output_direct, rel_tol=2e-13)
        g = sum(
            masses[i] * productivity[i] ** (1 / (1 - beta)) * capital[i] ** (alpha / (1 - beta))
            for i in range(2)
        )
        loss_direct = math.log(efficient_output_direct / output)
        loss_formula = alpha * math.log(total_capital) + d * math.log(z_a) - (1 - beta) * math.log(g)
        identity_error = abs(loss_direct - loss_formula)
        maximum_identity_error = max(maximum_identity_error, identity_error)
        assert loss_direct >= -2e-13 and identity_error < 2e-12

        # Independently choose feasible capital and employment reallocations.
        share_k, share_l = rng.uniform(0, 1), rng.uniform(0, 1)
        alternative_k = [total_capital * share_k / masses[0], total_capital * (1 - share_k) / masses[1]]
        alternative_l = [labor * share_l / masses[0], labor * (1 - share_l) / masses[1]]
        competitor = sum(
            masses[i] * productivity[i] * alternative_k[i] ** alpha * alternative_l[i] ** beta
            for i in range(2)
        )
        ratio = competitor / efficient_output
        maximum_competitor_ratio = max(maximum_competitor_ratio, ratio)
        assert ratio <= 1 + 2e-13

        direction = [rng.uniform(-2, 2), rng.uniform(-2, 2)]
        step = 1e-22
        perturbed_k = [capital[i] * cmath.exp(1j * step * direction[i]) for i in range(2)]
        perturbed_total = sum(masses[i] * perturbed_k[i] for i in range(2))
        perturbed_output, _, _ = output_at_optimal_labor(
            perturbed_k, masses, productivity, labor, alpha, beta
        )
        perturbed_efficient = perturbed_total ** alpha * labor ** beta * z_a ** d
        derivative_direct = cmath.log(perturbed_efficient / perturbed_output).imag / step
        capital_share = masses[0] * capital[0] / total_capital
        output_share = masses[0] * firm_output[0] / output
        derivative_formula = alpha * (capital_share - output_share) * (direction[0] - direction[1])
        error = abs(derivative_direct - derivative_formula)
        maximum_derivative_error = max(maximum_derivative_error, error)
        assert error < 2e-11
        mpk_h = alpha * firm_output[0] / capital[0]
        mpk_l = alpha * firm_output[1] / capital[1]
        if abs(output_share - capital_share) > 1e-10:
            assert (output_share > capital_share) == (mpk_h > mpk_l)
    return {
        "draws": DRAWS,
        "maximum_loss_identity_absolute_error": maximum_identity_error,
        "maximum_complex_step_derivative_error": maximum_derivative_error,
        "maximum_feasible_competitor_output_ratio": maximum_competitor_ratio,
        "scope": "Floating-point stress checks; no stochastic equilibrium, welfare or data validation.",
    }


def main():
    rng = random.Random(SEED)
    report = {
        "seed": SEED,
        "checked_at_utc": datetime.now(timezone.utc).isoformat(),
        "script_sha256": sha(Path(__file__)),
        "source_sha256": sha(PAPER),
        "funding": funding_checks(rng),
        "allocation": allocation_checks(rng),
        "status": "passed",
        "lean_verification": False,
        "macro_simulation": False,
        "external_data": False,
    }
    (HERE / 'sampled_checks.json').write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8', newline='\n')
    print("Passed: 5,000 raw portfolios; 5,000 financial regimes; 5,000 allocation cases.")
    print("All five financial regimes covered; 40,000 exact support checks; 10,000 invalid slopes rejected.")
    print("Maximum allocation derivative error:", report["allocation"]["maximum_complex_step_derivative_error"])
    print("Sampled verification only; Lean not run; no macro simulations or external data.")


if __name__ == "__main__":
    main()

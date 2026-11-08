#!/usr/bin/env python3
"""Directed-interval comparison of the *scalar stationary formulas* only.

The numerical producer in
    code/v0m/cotas_2026_10_15/verified_linear_operator.py:steady
uses the Python source constants. An independent interval calculation
reconstructs the real closed-form formulas represented in the stationary
Lean candidate:
    InterbankCancellationCandidate.lean / ProposedStationaryBank
    StationaryReducedSystemCandidate.lean / seedShare

This test checks overlapping, tight enclosures of rates and renewal
factors. The exact mathematical identities themselves are proved in
LocalScalarStationaryPythonCalibrationCandidate.lean, subject to the
corresponding Lean CI run.

It DOES NOT validate external Python AD derivatives, all 34 residuals,
numeric-to-Lean input mapping, policy IRFs, or a competitive equilibrium.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import sys
from decimal import Decimal as D
from pathlib import Path

HERE = Path(__file__).resolve().parent
V0M = HERE.parent
PRODUCER = V0M / "cotas_2026_10_15" / "verified_linear_operator.py"

sys.path.insert(0, str(PRODUCER.parent))
from verified_linear_operator import I, steady  # noqa: E402

# The 80-digit directed interval backend yields considerably tighter
# enclosures on this problem. This is a NUMERICAL comparison threshold,
# not an assumption or a proof of real-number equality.
MAX_ENCLOSURE_GAP = D("1e-60")


def compare(name: str, observed: I, reconstructed: I) -> dict[str, str]:
    """Require overlap and bound the enclosure of their difference."""
    if max(observed.lo, reconstructed.lo) > min(observed.hi, reconstructed.hi):
        raise AssertionError(
            f"{name}: source-style and producer interval enclosures are disjoint"
        )
    diff = observed - reconstructed
    gap = max(diff.lo.copy_abs(), diff.hi.copy_abs())
    if gap > MAX_ENCLOSURE_GAP:
        raise AssertionError(f"{name}: discrepancy upper bound {gap} too wide")
    return {
        "observed_interval": [str(observed.lo), str(observed.hi)],
        "source_formula_interval": [str(reconstructed.lo), str(reconstructed.hi)],
        "difference_enclosure": [str(diff.lo), str(diff.hi)],
        "max_abs_difference_upper": str(gap),
    }


def audit() -> dict:
    s = steady()
    one = I(1)
    two = I(2)

    # Source: weight = 1/(1+sqrt(3/2)), matchingIntensity = log 2.
    weight = one / (one + (I(3) / two).root(2))

    # Source: meanSlope=(2+3*weight)/400;
    #         slopeGap=(2+weight)/200.
    # These are derived independently from illustrative OTC parameters.
    deficit = (one / I(50)) * (one - one / two + weight / two)
    surplus = (one / I(50)) * (one / two) * (one / two) * weight
    mean = (deficit + surplus) / two
    gap = deficit - surplus

    # Source rootCoefficient, reserveRate and loanRate.
    source_rd = I(100) / I(99)
    root_coeff = (
        source_rd - (one - one / I(10)) * mean
        - (one / I(10)) * (one / I(5)) * gap / two
    )
    source_rr = (
        root_coeff
        + (root_coeff ** 2 + (two / I(5)) * source_rd * gap).root(2)
    ) / two
    source_rl = source_rr + mean

    # StationaryPrimitivesCandidate sets bankExit = 1/10 and seedShare
    # from the stationary R. This is not a seeded Python parameter.
    source_seed = I(10) / source_rl - I(9)
    source_renewal = (
        one - one / I(10) + (one / I(10)) * source_seed
    )

    compared = {
        "matching_weight": compare("matching_weight", s.vv, weight),
        "OTC_mean_slope": compare("OTC_mean_slope", s.cbar, mean),
        "OTC_slope_gap": compare("OTC_slope_gap", s.cdiff, gap),
        "root_coefficient": compare(
            "root_coefficient",
            s.rd - (one - s.rho) * s.cbar
            - s.rho * s.zeta * s.cdiff / two,
            root_coeff,
        ),
        "reserve_remuneration_rate": compare(
            "reserve_remuneration_rate", s.rr, source_rr
        ),
        "gross_loan_rate": compare("gross_loan_rate", s.rate, source_rl),
        "bank_renewal": compare("bank_renewal", s.aB, source_renewal),
    }
    if source_seed.lo <= 0 or source_seed.hi >= 1:
        raise AssertionError("Inferred stationary seed share outside (0,1)")
    if source_rl.lo <= 1:
        raise AssertionError("Loan rate must exceed one gross")

    return {
        "schema": "ie-stationary-scalar-bridge-v1",
        "status": "PASS_SCOPED_INTERVAL_COMPARISON",
        "producer_path": str(PRODUCER.relative_to(V0M.parent.parent)),
        "producer_sha256": hashlib.sha256(PRODUCER.read_bytes()).hexdigest(),
        "exact_lean_object": (
            "ProposedLocalScalarStationaryPythonCalibration"
        ),
        "source_formula_reference": [
            "InterbankCancellationCandidate.lean",
            "StationaryReducedSystemCandidate.lean",
            "StationaryPrimitivesCandidate.lean",
        ],
        "arithmetic": "80-digit directed decimal intervals, no binary float inputs",
        "max_difference_tolerance": str(MAX_ENCLOSURE_GAP),
        "comparison": compared,
        "inferred_stationary_seed_share": [
            str(source_seed.lo), str(source_seed.hi)
        ],
        "actual_producer_seed_share_input": None,
        "limits": {
            "does_not_check_all_34_rows": True,
            "does_not_check_lean_actual_jacobian_boxes": True,
            "does_not_check_infinite_equilibrium": True,
            "does_not_check_policy_irfs": True,
            "does_not_identify_external_python_inputs_with_lean_primitives": True,
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    try:
        report = audit()
    except (AssertionError, ArithmeticError, ValueError, OSError) as exc:
        print(f"SCOPED STATIONARY SCALAR BRIDGE: FAIL ({exc})", file=sys.stderr)
        return 1
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(
            json.dumps(report, indent=2) + "\n", encoding="utf-8"
        )
    print("SCOPED STATIONARY SCALAR BRIDGE: PASS")
    print("Source numeric producer hash:", report["producer_sha256"])
    for name, result in report["comparison"].items():
        print(name, "upper discrepancy:", result["max_abs_difference_upper"])
    print("34-row Python/Lean semantic bridge: NOT established")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

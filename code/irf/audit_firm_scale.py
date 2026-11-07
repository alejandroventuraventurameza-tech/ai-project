#!/usr/bin/env python3
"""Audit relative firm scale only in the illustrative stationary anchor.

This does not establish size at the shocked date-0 boundary or a causal
pledgeability effect. It reuses the existing steady_case primitives unchanged.
"""
import json
import math
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from finite_irf import steady_case


def main():
    s = steady_case()
    firms = {}
    for j, name in enumerate(("H", "L")):
        firms[name] = {
            "productivity": s.technology[j],
            "pledgeability": s.pledge[j],
            "capital": s.k[j],
            "output": s.yy[j],
            "employment": s.ell[j],
            "gross_loans": s.b[j],
            "consumption": s.cc[j],
            "marginal_revenue_product_of_capital": (
                s.alpha * s.mc * s.yy[j] / s.k[j]
            ),
        }
    h, ell = firms["H"], firms["L"]
    checks = {
        "H_has_higher_productivity": h["productivity"] > ell["productivity"],
        "H_has_lower_pledgeability": h["pledgeability"] < ell["pledgeability"],
        "H_has_smaller_capital": h["capital"] < ell["capital"],
        "H_has_smaller_output": h["output"] < ell["output"],
        "H_has_less_credit": h["gross_loans"] < ell["gross_loans"],
        "all_finite": all(math.isfinite(v) for f in firms.values() for v in f.values()),
        "capital_output_positive": all(f["capital"] > 0 and f["output"] > 0
                                       for f in firms.values()),
    }
    report = {
        "scope": "illustrative_stationary_anchor_only",
        "source": "code/irf/finite_irf.py :: steady_case()",
        "firms": firms,
        "capital_ratio_H_over_L": h["capital"] / ell["capital"],
        "checks": checks,
        "not_proved": [
            "firm-size ordering at shocked date-0 boundary",
            "firm-size ordering along the complete IRF",
            "causal dependence of firm size on pledgeability",
            "complete stochastic dynamic equilibrium",
        ],
    }
    print(json.dumps(report, indent=2, sort_keys=True, ensure_ascii=False))
    if not all(checks.values()):
        raise SystemExit("Firm scale audit failed; economic interpretation must be revised")


if __name__ == "__main__":
    main()

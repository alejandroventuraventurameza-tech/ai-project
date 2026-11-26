#!/usr/bin/env python3
"""Reproducible FINITE-path identity for the heterogeneous collateral price wedge.

The observed accounting object is the difference of two "effective prices"
printed by finite_irf.py:
    W_t = pH_eff,t - pL_eff,t
        = (theta_L-theta_H)*(1-delta)*Pi_{t+1}*q_{t+1}/RL_t.

With unchanged theta/delta, the relative shock-vs-baseline identity is
    log(W_t^shock/W_t^base)
      = log(J_{t+1}^shock/J_{t+1}^base)
        - log(RL_t^shock/RL_t^base).

Both sides are calculated independently from CSV fields, not trusted as
a verbal claim. This is a bookkeeping identity, NOT an identification
of a causal monetary-policy channel. In S at date zero firm L is SLACK:
the L "effective price" is a hypothetical pledge-price accounting object,
not L's KKT marginal investment price. From date one the local model
uses the binding form, still WITHOUT proving global dynamic equilibrium.
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import json
import math
from pathlib import Path


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
DEFAULT_EXPERIMENT = HERE / "output" / "main"
OUT = HERE / "output" / "effective_price_wedge_irf_audit.json"


def digest(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def get(row, key):
    value = float(row[key])
    if not math.isfinite(value):
        raise AssertionError(f"Non-finite path metric {key}")
    return value


def require(ok, message):
    if not ok:
        raise AssertionError(message)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--experiment", type=Path, default=DEFAULT_EXPERIMENT)
    parser.add_argument("--output", type=Path, default=OUT)
    args = parser.parse_args()
    path = args.experiment / "finite_irf_paths.csv"
    meta_path = args.experiment / "finite_irf_validation.json"
    require(path.is_file() and meta_path.is_file(),
            "Finite IRFs must be reproduced before the wedge audit")
    with path.open(newline="", encoding="utf-8") as f:
        data = list(csv.DictReader(f))
    meta = json.loads(meta_path.read_text(encoding="utf-8"))
    require(meta["shock"]["instrument"] ==
            "date-0 log reserve-remuneration-rule innovation v_R",
            "Do not misidentify this shock as an encaje or corridor change")
    require(meta["shock"]["value"] != 0.0, "Expected a nonzero rule innovation")
    delta = float(meta["parameters"]["depreciation"])
    pledge_h, pledge_l = map(float, meta["parameters"]["pledgeabilities"])
    require(0.0 <= delta < 1.0 and 0 <= pledge_h < pledge_l < 1,
            "Pledgeability order or depreciation assumption changed")
    require(meta["parameters"]["productivities"][0] >
            meta["parameters"]["productivities"][1],
            "Productivity ordering changed")
    gap_theta = pledge_l - pledge_h
    grouped = {}
    for row in data:
        branch = row["branch"]
        t = int(row["period"])
        require(t >= 0, "Negative time index")
        key = (branch, t)
        require(key not in grouped, "Duplicate branch/period row")
        grouped[key] = row
    branches = ("slack", "binding")
    require({x[0] for x in grouped} == set(branches),
            "Expected exactly S/B branch paths")
    horizons = {
        branch: sorted(t for (b, t) in grouped if b == branch)
        for branch in branches
    }
    require(len(set(map(len, horizons.values()))) == 1,
            "Branch horizons must match")
    count = len(horizons["slack"])
    require(count >= 2 and all(
        horizons[branch] == list(range(count)) for branch in branches
    ), "Branch periods must be contiguous from date zero")
    tol_levels = 2e-10
    tol_logs = 2e-11
    records = {}
    max_level = 0.0
    max_log = 0.0
    for branch in branches:
        by_date = []
        for t in range(count-1):
            now = grouped[(branch, t)]
            next_date = grouped[(branch, t+1)]
            r = get(now, "loan_rate")
            r0 = get(now, "loan_rate_baseline")
            pi = get(next_date, "inflation")
            pi0 = get(next_date, "inflation_baseline")
            q = get(next_date, "capital_price")
            q0 = get(next_date, "capital_price_baseline")
            require(min(r, r0, pi, pi0, q, q0) > 0,
                    "Gross rates and next collateral prices must be positive")
            collateral = (1-delta)*pi*q
            collateral0 = (1-delta)*pi0*q0
            wedge = get(now, "effective_price_H") - get(now, "effective_price_L")
            wedge0 = (get(now, "effective_price_H_baseline") -
                      get(now, "effective_price_L_baseline"))
            wpred = gap_theta * collateral / r
            wpred0 = gap_theta * collateral0 / r0
            require(min(wedge, wedge0) > 0,
                    "Cross-firm pledge wedge must be strictly positive")
            err = max(abs(wedge-wpred), abs(wedge0-wpred0))
            dlog_wedge = math.log(wedge/wedge0)
            dlog_J = math.log(collateral/collateral0)
            dlog_R = math.log(r/r0)
            decomp_err = abs(dlog_wedge-dlog_J+dlog_R)
            max_level = max(max_level, err)
            max_log = max(max_log, decomp_err)
            by_date.append({
                "period": t,
                "original_branch_L_collateral_binding_at_date0": branch == "binding",
                "date0_L_price_is_hypothetical_if_slack": (
                    branch == "slack" and t == 0
                ),
                "observed_wedge_level": wedge,
                "baseline_wedge_level": wedge0,
                "wedge_level_identity_max_abs_error": err,
                "wedge_log_shock_minus_baseline_pct": 100*dlog_wedge,
                "collateral_J_log_shock_minus_baseline_pct": 100*dlog_J,
                "loan_rate_negative_log_shock_minus_baseline_pct": -100*dlog_R,
                "log_decomposition_max_abs_error": decomp_err,
            })
        records[branch] = {
            "audited_periods": len(by_date),
            "date_zero_to_two_illustrative_components": by_date[:3],
            "max_observed_abs_wedge_log_response_pct": max(
                abs(z["wedge_log_shock_minus_baseline_pct"])
                for z in by_date
            ),
            "max_level_identity_error": max(
                z["wedge_level_identity_max_abs_error"] for z in by_date
            ),
            "max_log_decomposition_error": max(
                z["log_decomposition_max_abs_error"] for z in by_date
            ),
        }
    require(max_level < tol_levels,
            f"Finite IRF effective price wedge identity failed: {max_level}")
    require(max_log < tol_logs,
            f"Finite IRF log wedge decomposition failed: {max_log}")
    report = {
        "status": "NUMERICAL_FINITE_IRF_COLLATERAL_WEDGE_IDENTITY_ONLY",
        "experiment": str(args.experiment.relative_to(ROOT)),
        "source_hashes": {
            str(p.relative_to(ROOT)): digest(p)
            for p in (path, meta_path, HERE/"finite_irf.py")
        },
        "shock": meta["shock"],
        "technology_H_greater_than_L": True,
        "pledgeability_H": pledge_h,
        "pledgeability_L": pledge_l,
        "depreciation": delta,
        "wedge_definition": (
            "pH_eff-pL_eff=(thetaL-thetaH)"
            "*(1-delta)*Pi_next*q_next/Rloan"
        ),
        "log_decomposition_exact_identity": (
            "log(wedge_shock/wedge_base) = "
            "log(J_next_shock/J_next_base) - "
            "log(Rloan_shock/Rloan_base)"
        ),
        "scope": (
            "Finite internal IRFs with two-date nonlinear prefix, "
            "local-linear recurrent continuation, and illustrative parameters."
        ),
        "important_branch_warning": (
            "At date 0 in S, L is collateral-slack, so the printed L "
            "effective price is NOT its true KKT marginal investment price. "
            "Report the formula as a hypothetical pledged-price accounting "
            "wedge only at this date."
        ),
        "not_proved": [
            "Equilibrium causal impact from a rate move",
            "Global firm investment optimum under S or B",
            "Full stochastic bank optimality and terminal constraints",
            "Infinite-horizon SOURCE equivalence and trend growth",
        ],
        "maximum_level_identity_error": max_level,
        "maximum_log_decomposition_error": max_log,
        "level_error_tolerance": tol_levels,
        "log_error_tolerance": tol_logs,
        "branches": records,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True)+"\n",
                           encoding="utf-8")
    print(json.dumps({
        "status": report["status"],
        "instrument": meta["shock"]["instrument"],
        "periods_per_branch": count-1,
        "max_identity_error": max_level,
        "max_log_error": max_log,
        "date0_slack_L_effective_price": "hypothetical—not KKT",
        "file": str(args.output),
    }, indent=2))


if __name__ == "__main__":
    main()

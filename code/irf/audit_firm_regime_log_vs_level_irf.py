#!/usr/bin/env python3
"""Audit positive-domain SOURCE/Python firm-regime row transformations on IRFs.

The SOURCE uses level gaps or ratio-minus-one. Python uses log ratios.
On positive states:
  cap * expm1(log(face/cap)) = face - cap,
  expm1(log(R*sdf/Pi)) = R*sdf/Pi - 1.
These are exact *functional* transformations (not raw residual equality).
The script reads the generated shocked/base CSV independently and checks
the realizations for B/S, both firms and both dates, including the shared
pledge row from date one. The two Lean log-zero-set theorems are separate.

It does not prove all remaining 33 rows, the source Jacobian, policy
causality, any non-linear invariant graph or infinite-horizon equilibrium.
"""
from __future__ import annotations

import csv
import hashlib
import json
import math
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
LEAN = ROOT / "lean/checkpoint/modules/Ventura26LiquidityAllocation/EconomicModel.lean"
PYTHON = HERE / "finite_irf.py"
CSV = HERE / "output/main/finite_irf_paths.csv"
META = HERE / "output/main/finite_irf_validation.json"
OUT = HERE / "output/source_python_firm_regime_log_level_audit.json"
THRESHOLD = 2e-11


def check(cond, msg):
    if not cond:
        raise AssertionError(msg)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def number(row, field):
    x = float(row[field])
    check(math.isfinite(x), "Nonfinite "+field)
    return x


def main():
    lean = LEAN.read_text(encoding="utf-8").replace("\r\n", "\n")
    py = PYTHON.read_text(encoding="utf-8")
    for fragment in (
        "d.controls.loanRate * localPrefixEntrepreneurSDF P d i /",
        "| _, _ => d.nextFace i - localPrefixPledgeUnit P d i * d.nextCapital i",
        "| .commonPledgeOne => Z.stateTwo.commonPledgeValue -",
    ):
        check(fragment in lean, "Literal SOURCE regime definition changed: "+fragment)
    for fragment in (
        "math.log(u0[8] * sdf0[i] / u1[5])",
        "math.log(x1[2 + i] / (collateral * x1[i]))",
        "math.log(next_compact[2] / (s.ad * next_controls[5] * next_controls[6]))",
    ):
        check(fragment in py, "Python log-regime expression changed: "+fragment)
    check(CSV.is_file() and META.is_file(), "Regenerate IRFs before auditing")
    meta = json.loads(META.read_text(encoding="utf-8"))
    assert meta["shock"]["instrument"] == (
        "date-0 log reserve-remuneration-rule innovation v_R"
    )
    pp = meta["parameters"]
    theta_h, theta_l = map(float, pp["pledgeabilities"])
    beta, sigma = float(pp["beta_entrepreneur"]), float(
        pp["risk_aversion_entrepreneur"]
    )
    depreciation = float(pp["depreciation"])
    check(0 < theta_h < theta_l < 1 and 0 <= depreciation < 1
          and beta > 0 and sigma == 1.0,
          "Model's positive source-domain illustrative assumptions changed")
    with CSV.open(newline="", encoding="utf-8") as f:
        rows = list(csv.DictReader(f))
    bykey = {(row["branch"], int(row["period"])): row for row in rows}
    check(len(bykey) == len(rows) and
          {b for b,t in bykey} == {"slack", "binding"},
          "Missing, duplicate or unexpected branch/period")
    stats = {}
    global_max = 0.0
    for branch in ("slack", "binding"):
        times = sorted(t for b,t in bykey if b == branch)
        check(times == list(range(len(times))) and len(times) >= 2,
              "Expected all contiguous periods")
        max_binding = 0.0
        max_slack = 0.0
        max_pledge = 0.0
        first = {}
        rowcount = 0
        for t in times[:-1]:
            cur, nxt = bykey[(branch,t)], bykey[(branch,t+1)]
            for suffix, scenario in (("", "shock"), ("_baseline", "base")):
                rate = number(cur, "loan_rate"+suffix)
                inflation = number(nxt, "inflation"+suffix)
                price = number(nxt, "capital_price"+suffix)
                J = (1-depreciation)*inflation*price
                check(min(rate,inflation,price,J) > 0,
                      "Positive-domain rate, future inflation, q or J violated")
                firm_faces = {}
                for i,(firm,theta) in enumerate((("H",theta_h),("L",theta_l))):
                    cap = number(cur,"capital_next_"+firm+suffix)
                    face = rate*number(cur,"credit_"+firm+suffix)
                    collateral = theta*J*cap
                    check(min(cap,face,collateral) > 0,
                          "Positive nominal face or capacity violated")
                    firm_faces[firm] = face
                    log_ratio = math.log(face/collateral)
                    source_gap = face-collateral
                    exact_transform = collateral*math.expm1(log_ratio)
                    error = abs(exact_transform-source_gap)
                    check(error < THRESHOLD,
                          "Face log/level row mismatch for "+branch+" "+firm)
                    check(abs(source_gap/collateral +
                              number(cur,"collateral_slack_"+firm+suffix)) <
                              THRESHOLD,
                          "Normalized collateral slack is inconsistent")
                    max_binding = max(max_binding,error)
                    rowcount += 1
                    if t == 0 and scenario == "shock":
                        first[firm+"_binding_level_gap"] = source_gap
                        first[firm+"_binding_log_ratio"] = log_ratio
                if t >= 1:
                    # From the six-state recurrence, H's originated face
                    # recovers the common unscaled pledge unit exactly.
                    common_j = firm_faces["H"] / (
                        theta_h*number(cur,"capital_next_H"+suffix)
                    )
                    log_common = math.log(common_j/J)
                    source_common = common_j-J
                    error = abs(J*math.expm1(log_common)-source_common)
                    check(error < THRESHOLD,
                          "SOURCE common-pledge row differs from Python log")
                    max_pledge = max(max_pledge,error)
                if branch == "slack" and t == 0:
                    c_t = number(cur,"consumption_L"+suffix)
                    c_next = number(nxt,"consumption_L"+suffix)
                    check(c_t > 0 and c_next > 0,
                          "Firm L CRRA consumption must be positive")
                    sdf = beta*(c_t/c_next)**sigma
                    positive_ratio = rate*sdf/inflation
                    check(positive_ratio > 0,"S-branch ratio nonpositive")
                    source_ratio_minus_one = positive_ratio-1
                    python_log = math.log(positive_ratio)
                    error = abs(math.expm1(python_log)-source_ratio_minus_one)
                    check(error < THRESHOLD,
                          "S-branch L Euler log/level equivalence failed")
                    max_slack = max(max_slack,error)
                    if scenario=="shock":
                        first["L_slack_source_ratio_minus_one"] = (
                            source_ratio_minus_one
                        )
                        first["L_slack_python_log_ratio"] = python_log
        global_max = max(global_max,max_binding,max_slack,max_pledge)
        stats[branch] = {
            "audited_periods": len(times)-1,
            "binding_face_rows_tested_including_off_branch_L": rowcount,
            "max_abs_binding_gap_transform_error": max_binding,
            "max_abs_slack_ratio_transform_error": max_slack,
            "max_abs_common_pledge_transform_error": max_pledge,
            "impact_diagnostics": first,
            "important_note": (
                "In S at t=0 the L binding face comparison is off-branch "
                "and the L slack log condition is the active equation."
            ),
        }
    report = {
        "status": "FINITE_SOURCE_LOG_LEVEL_REGIME_TRANSFORM_VERIFIED",
        "source_sha256": {
            str(p.relative_to(ROOT)):sha(p)
            for p in (LEAN,PYTHON,CSV,META)
        },
        "transformation": (
            "face-cap=cap*expm1(log(face/cap)); "
            "R*SDF/Pi-1=expm1(log(R*SDF/Pi))"
        ),
        "strictly_positive_domain_verified_for_tested_entries": True,
        "maximum_absolute_transformation_error":global_max,
        "threshold":THRESHOLD,
        "branches":stats,
        "not_established":[
            "Source-Python operator equality for all 33 rows",
            "Source exact Fréchet derivative equivalence as 33x33 matrices",
            "Nonlinear infinite-horizon invariant-graph existence",
            "Global KKT sufficiency or trends in productivity growth",
        ],
    }
    OUT.parent.mkdir(parents=True,exist_ok=True)
    OUT.write_text(json.dumps(report,indent=2,sort_keys=True)+"\n",
                   encoding="utf-8")
    print(json.dumps({
        "status":report["status"],
        "max_error":global_max,
        "rows_by_branch":{b:stats[b]["binding_face_rows_tested_including_off_branch_L"]
                          for b in stats},
        "artifact":str(OUT)
    },indent=2))


if __name__=="__main__":
    main()

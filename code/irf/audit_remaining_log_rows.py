#!/usr/bin/env python3
"""Independent log-versus-level accounting audit for three SOURCE 11-rows.

SOURCE zero-set transformations, on strictly positive charts:
 - bank face row 0:  B_next - a_B R^L B_current / Pi_current
   vs Python log(next face / predicted face);
 - worker labor row 3: W - chi_W C_W^sigmaW L^varphi
   vs Python log(W / (chi_W C_W L)) when sigmaW=varphi=1;
 - household deposit Euler row 4:
   1 - R^D * betaW*(C_W/C_W,next)^sigmaW / Pi_next
   vs Python log of that Euler ratio.

For each historical *finite* path observation, verify the exact nonlinear
transformations, and separately test off-zero positive perturbations.
We do not execute Lean in Python or claim that all source equations,
Jacobian columns, or infinite-horizon equilibrium have been certified.
"""
from __future__ import annotations

import csv
import hashlib
import json
import math
from pathlib import Path

from finite_irf import steady_case

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
LEAN = ROOT / "lean/checkpoint/modules/Ventura26LiquidityAllocation/EconomicModel.lean"
ENGINE = HERE / "finite_irf.py"
CSV = HERE / "output/main/finite_irf_paths.csv"
META = HERE / "output/main/finite_irf_validation.json"
OUT = HERE / "output/remaining_log_rows_audit.json"
TOL = 2e-10
OFF_ROOT_SHIFTS = (0.001, -0.0007, 0.003)


def require(ok, why):
    if not ok:
        raise AssertionError(why)


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def raw(row, key):
    value = float(row[key])
    require(math.isfinite(value), f"Non-finite {key}")
    return value


def check_positive(*values):
    require(all(math.isfinite(x) and x > 0 for x in values),
            "Log transform outside positive economic domain")


def log_face_check(face, prediction):
    check_positive(face, prediction)
    original = face - prediction
    log_res = math.log(face / prediction)
    reconstruction = prediction * math.expm1(log_res)
    return abs(original - reconstruction), original, log_res


def household_euler_check(ratio):
    check_positive(ratio)
    original = 1.0 - ratio
    log_res = math.log(ratio)
    return abs(original + math.expm1(log_res)), original, log_res


def main():
    require(LEAN.is_file() and CSV.is_file() and META.is_file(),
            "Run finite reproducibility first, then this SOURCE audit")
    source = LEAN.read_text(encoding="utf-8").replace("\r\n", "\n")
    source_remaining = source.split(
        "noncomputable def localReducedRemainingResidual\n", 1
    )[1].split("noncomputable def localPrefixReducedBankLoans", 1)[0]
    engine = ENGINE.read_text(encoding="utf-8")
    for tag in (
        "| 0 => d.nextBankFace -",
        "bankRenewalFactor P * d.controls.loanRate * d.currentBankFace /",
        "| 3 => d.controls.wage - P.laborScale *",
        "d.controls.workerConsumption ^ P.workerRiskAversion *",
        "localPrefixAggregateLabor P d ^ P.laborCurvature",
        "| 4 => 1 - householdSDF * d.controls.depositRate /",
    ):
        require(tag in source_remaining, "SOURCE 11-row definition changed: "+tag)
    for tag in (
        "math.log(next_state[4] / (s.aB * rl * state[4] / inflation))",
        "math.log(wage / (s.chiW * aux[\"L\"] * cw))",
        "math.log(rd * household_sdf / next_controls[5])",
    ):
        require(tag in engine, "Python normalization code changed: "+tag)
    meta = json.loads(META.read_text(encoding="utf-8"))
    require(meta["shock"]["instrument"] ==
            "date-0 log reserve-remuneration-rule innovation v_R",
            "Do not silently change monetary instrument")
    s = steady_case()
    pp = meta["parameters"]
    require(pp["risk_aversion_worker"] == s.sigmaW == 1.0
            and s.varphi == 1.0 and s.chiW > 0 and s.aB > 0,
            "Worker-power parameter identity is NOT source-compatible")
    require(pp["beta_worker"] == s.bw, "Worker discount mismatch")
    with CSV.open(encoding="utf-8", newline="") as f:
        data = list(csv.DictReader(f))
    bykey = {(r["branch"], int(r["period"])): r for r in data}
    require(len(bykey) == len(data) and
            {branch for branch,_ in bykey} == {"slack", "binding"},
            "Missing or duplicated branch dates")
    max_errors = {"bank_face": 0., "worker_labor": 0., "household_euler": 0.}
    observations = {}
    for branch in ("slack", "binding"):
        ts = sorted(t for b,t in bykey if b == branch)
        require(ts == list(range(len(ts))) and len(ts) >= 2,
                "Periods must be consecutive from zero")
        count = 0
        impact = {}
        for t in ts[:-1]:
            current, future = bykey[(branch,t)],bykey[(branch,t+1)]
            for suffix, label in (("", "shock"), ("_baseline", "baseline")):
                infl = raw(current, "inflation"+suffix)
                infl_future = raw(future, "inflation"+suffix)
                loan_rate = raw(current, "loan_rate"+suffix)
                deposit_rate = raw(current, "deposit_rate"+suffix)
                bank_face = raw(current, "bank_equity"+suffix)*infl
                bank_face_next = raw(future,"bank_equity"+suffix)*infl_future
                predicted = s.aB*loan_rate*bank_face/infl
                wage=raw(current,"wage"+suffix)
                labor=raw(current,"labor"+suffix)
                worker_c=raw(current,"worker_consumption"+suffix)
                worker_c_future=raw(future,"worker_consumption"+suffix)
                labor_cost=s.chiW*worker_c**s.sigmaW*labor**s.varphi
                household_sdf=s.bw*(worker_c/worker_c_future)**s.sigmaW
                euler_ratio=deposit_rate*household_sdf/infl_future
                e_bank,level_bank,log_bank=log_face_check(bank_face_next,predicted)
                e_labor,level_labor,log_labor=log_face_check(wage,labor_cost)
                e_euler,level_euler,log_euler=household_euler_check(euler_ratio)
                for name,err in (("bank_face",e_bank),
                                 ("worker_labor",e_labor),
                                 ("household_euler",e_euler)):
                    max_errors[name]=max(max_errors[name],err)
                if t==0:
                    impact[label]={
                        "source_bank_face_level":level_bank,
                        "python_bank_face_log":log_bank,
                        "source_worker_labor_level":level_labor,
                        "python_worker_labor_log":log_labor,
                        "source_household_euler_level":level_euler,
                        "python_household_euler_log":log_euler,
                    }
                count+=1
        observations[branch]={"scenarios_and_transitions":count,
                              "date_zero":impact}
    # Off-zero-domain perturbation test; avoids passing simply because
    # all root residuals are numerically zero. Not source differentiation.
    off_root_max=0.
    for branch in ("slack", "binding"):
        row=bykey[(branch,0)]
        for delta in OFF_ROOT_SHIFTS:
            f=raw(row,"wage")*math.exp(delta)
            c=s.chiW*raw(row,"worker_consumption")*raw(row,"labor")
            e,lev,lg=log_face_check(f,c)
            require(abs(lev)>1e-6, "Off-root test collapsed to root")
            off_root_max=max(off_root_max,e)
            ratio=math.exp(delta)
            ee,_,_=household_euler_check(ratio)
            off_root_max=max(off_root_max,ee)
    require(max(max_errors.values()) < TOL and off_root_max<TOL,
            f"Log/level transformation failed: {max_errors}, {off_root_max}")
    report={
        "status":"FINITE_THREE_SOURCE_REMAINING_ROWS_LOG_LEVEL_VERIFIED",
        "source_file_hashes": {
            str(p.relative_to(ROOT)):sha256(p)
            for p in (LEAN,ENGINE,CSV,META)
        },
        "source_rows":[0,3,4],
        "source_row_names":["bankEquity","workerLabor","householdEuler"],
        "worker_risk_aversion_source_equals_python":s.sigmaW,
        "worker_labor_curvature_source_equals_python":s.varphi,
        "max_absolute_reconstruction_errors":max_errors,
        "max_off_root_positive_perturbation_error":off_root_max,
        "output_precision_absolute_tolerance":TOL,
        "branches":observations,
        "not_proved":[
            "Lean-Python executable equality of these 33-dimensional operators",
            "Derivative of original SOURCE economic Jacobian",
            "Sufficiency of household or bank optimality",
            "All other SOURCE conditions, dynamic TVC and invariant graph",
        ],
    }
    OUT.parent.mkdir(parents=True,exist_ok=True)
    OUT.write_text(json.dumps(report,indent=2,sort_keys=True)+"\n",
                   encoding="utf-8")
    print(json.dumps({
        "status":report["status"],
        "errors":max_errors,
        "off_root_max":off_root_max,
        "count_per_branch":observations["binding"]["scenarios_and_transitions"],
        "artifact":str(OUT)
    },indent=2))


if __name__=="__main__":
    main()

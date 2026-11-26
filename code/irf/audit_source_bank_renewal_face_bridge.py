#!/usr/bin/env python3
"""Conditional SOURCE/Python bank-renewal primitive and bank-face row audit.

This constructs the *candidate* SOURCE bankSeedShare required to match the
Python benchmark aB=1/R_star from the original SOURCE formula
aB=1-bankExit+bankExit*bankSeedShare. It tests positivity/admissibility
and the exact level/log residual relationship on 33-dimensional positive
off-root charts. It does NOT construct a full SOURCE Primitives witness,
prove bank optimality or certify the full operator/Jacobian.
"""
from __future__ import annotations

import hashlib
import json
import math
from pathlib import Path

import finite_irf as model

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
SOURCE = ROOT / "lean/checkpoint/modules/Ventura26LiquidityAllocation/EconomicModel.lean"
PYTHON = HERE / "finite_irf.py"
P0 = HERE / "inputs/rational_preconditioners.json"
OUT = HERE / "output/source_bank_renewal_witness_and_face_rows.json"


def need(ok, why):
    if not ok:
        raise AssertionError(why)


def fingerprint(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def source_guards():
    src = SOURCE.read_text(encoding="utf-8").replace("\r\n", "\n")
    py = PYTHON.read_text(encoding="utf-8")
    anchors = (
        "def bankRenewalFactor (P : Primitives S) : ℝ :=\n  1 - P.bankExit + P.bankExit * P.bankSeedShare",
        "bank_exit_mem : 0 ≤ bankExit ∧ bankExit ≤ 1",
        "bank_seed_mem : 0 ≤ bankSeedShare ∧ bankSeedShare ≤ 1",
        "| 0 => d.nextBankFace -",
        "bankRenewalFactor P * d.controls.loanRate * d.currentBankFace /",
        "d.controls.inflation",
    )
    for anchor in anchors:
        need(anchor in src, "SOURCE bank row or primitive changed: " + anchor)
    for anchor in (
        "s.aB = 1.0 / s.rate",
        "math.log(next_state[4] / (s.aB * rl * state[4] / inflation))",
        '"bank_exit_probability": s.eta',
    ):
        need(anchor in py, "Python bank benchmark changed: "+anchor)
    return True


def rows(base, p0, branch, shock, z, renewal):
    x1,u0,x2,u1,_ = model.decode_prefix(base,p0,z)
    py = model.prefix_residual(base,p0,branch,shock,z)
    need(len(py)==33, "Python 33-row vector changed")
    data=(
        # (SOURCE and Python bank face row index, previous face, next face, loan rate, inflation)
        (6,base.X0[4],x1[4],u0[8],u0[5]),
        (22,x1[4],x2[3],u1[8],u1[5]),
    )
    out={}
    for j,prev,nxt,R,pi in data:
        need(min(prev,nxt,R,pi,renewal)>0,
             "Outside positive bank-face log coordinate chart")
        target=renewal*R*prev/pi
        source_level=nxt-target
        python_log=py[j]
        # Exact identity on positive domain, not only around stationary root.
        corrected=target*math.expm1(python_log)
        out[j] = {"level":source_level,"target":target,
                  "python_log":python_log,
                  "level_log_discrepancy":abs(source_level-corrected)}
    return out


def main():
    source_guards()
    s=model.steady_case()
    eta=s.eta
    Rstar=s.rate
    aB=s.aB
    need(0<eta<1 and Rstar>1, "Bank benchmark outside targeted interior")
    need(abs(aB-1/Rstar)<1e-15, "Python renewal benchmark changed")
    seed=(aB-(1-eta))/eta
    need(0<seed<1, "Bank SOURCE seed-share witness not admissible")
    renewal=1-eta+eta*seed
    need(abs(renewal-aB)<1e-14, "SOURCE renewal identity failed")
    feasible_rate_bounds=(1,1/(1-eta))
    need(feasible_rate_bounds[0]<Rstar<feasible_rate_bounds[1],
         "Positive SOURCE seed needs 1<Rstar<1/(1-eta)")
    # Counterexamples: a loan rate below one or beyond the feasibility
    # cap forces the matched seed share outside SOURCE's [0,1] domain.
    negative_seed_R=feasible_rate_bounds[1]+0.01
    excessive_seed_R=0.99
    negative_seed=(1/negative_seed_R-(1-eta))/eta
    excessive_seed=(1/excessive_seed_R-(1-eta))/eta
    need(negative_seed<0 and excessive_seed>1,
         "Seed-share feasibility boundary was not enforced")

    b=model.make_boundary(s)
    p=json.loads(P0.read_text(encoding="utf-8"))
    p0=[[float(x) for x in row] for row in p["P0"]]
    need(len(p0)==16 and all(len(row)==6 for row in p0),"Pinned P0 changed")
    zs=(
        [0.]*33,
        [3e-4*math.sin((i+1)*.73) for i in range(33)],
        [-4e-4*math.cos((i+1)*.91) for i in range(33)],
    )
    shocks=(
        (0.,0.,0.,0.),(-1e-5,0.,0.,0.),(0.,-1e-5,0.,0.),
        (0.,0.,-1e-5,0.),(0.,0.,0.,-1e-5),
    )
    max_level_log=0.
    max_root_derivative=0.
    max_offroot_derivative=0.
    max_invalid_root_only_offroot_derivative=0.
    offroot_direction_checks=0
    root_direction_checks=0
    comparisons=0
    for branch in ("slack","binding"):
        for v in shocks:
            for z in zs:
                r=rows(b,p0,branch,v,z,renewal)
                for j in (6,22):
                    max_level_log=max(max_level_log,
                                      r[j]["level_log_discrepancy"])
                    comparisons+=1
        root=rows(b,p0,branch,shocks[0],zs[0],renewal)
        need(max(abs(root[j]["level"]) for j in (6,22))<1e-10,
             "Common reference is not bank-face stationary")
        for z in (zs[0],zs[1]):
            base=rows(b,p0,branch,shocks[0],z,renewal)
            h=1e-6
            for k in range(33):
                zp=z.copy();zm=z.copy();zp[k]+=h;zm[k]-=h
                rp=rows(b,p0,branch,shocks[0],zp,renewal)
                rm=rows(b,p0,branch,shocks[0],zm,renewal)
                for j in (6,22):
                    dF=(rp[j]["level"]-rm[j]["level"])/(2*h)
                    dG=(rp[j]["python_log"]-rm[j]["python_log"])/(2*h)
                    dD=(rp[j]["target"]-rm[j]["target"])/(2*h)
                    G=base[j]["python_log"];D=base[j]["target"]
                    predicted=dD*math.expm1(G)+D*math.exp(G)*dG
                    if z is zs[0]:
                        root_direction_checks+=1
                        max_root_derivative=max(max_root_derivative,
                                                abs(dF-D*dG))
                    else:
                        offroot_direction_checks+=1
                        max_offroot_derivative=max(max_offroot_derivative,
                                                   abs(dF-predicted))
                        max_invalid_root_only_offroot_derivative=max(
                            max_invalid_root_only_offroot_derivative,
                            abs(dF-D*dG))
    need(root_direction_checks==2*2*33 and
         offroot_direction_checks==2*2*33,
         "Expected derivative coverage for both bank rows, branches and points")
    need(max_invalid_root_only_offroot_derivative>1e-10,
         "Off-root witness did not distinguish the invalid root-only derivative")
    need(max_level_log<3e-11,
         "SOURCE bank face level/log candidate mismatch")
    need(max_root_derivative<3e-6 and max_offroot_derivative<3e-6,
         "SOURCE/Python bank face derivative candidate mismatch")
    report={
      "status":"CONDITIONAL_SOURCE_BANK_RENEWAL_WITNESS_AND_2_LEVEL_LOG_ROWS_PASS",
      "source_bank_exit_candidate_eta":eta,
      "source_bank_seed_share_candidate":seed,
      "source_bank_renewal_matched_to_python_aB":renewal,
      "python_Rstar_loan_rate":Rstar,
      "feasible_Rstar_interval_for_seed_in_[0,1]":list(feasible_rate_bounds),
      "counterexample_below_one_Rstar_seed_gt_one":{
        "Rstar":excessive_seed_R,"seed":excessive_seed},
      "counterexample_above_cap_Rstar_seed_lt_zero":{
        "Rstar":negative_seed_R,"seed":negative_seed},
      "bank_face_source_row_indices":[6,22],
      "exact_chart_identity":"SOURCE_level=D*expm1(Python_log), D=aB*RL*previous_nominal_bank_face/Pi",
      "root_row_derivative_identity":"D(SOURCE_level)=D_stationary*d(Python_log)",
      "offroot_row_derivative_identity":"dF=dD*expm1(G)+D*exp(G)*dG",
      "positive_offroot_points":len(zs),
      "policy_vectors":len(shocks),
      "branches":2,
      "individual_bank_face_row_comparisons":comparisons,
      "max_level_log_discrepancy":max_level_log,
      "max_root_derivative_discrepancy":max_root_derivative,
      "max_offroot_derivative_discrepancy":max_offroot_derivative,
      "root_derivative_direction_checks":root_direction_checks,
      "offroot_derivative_direction_checks":offroot_direction_checks,
      "max_offroot_error_if_root_only_formula_misused":max_invalid_root_only_offroot_derivative,
      "offroot_correction_is_required":True,
      "source_to_python_full_primitive_instance_constructed":False,
      "source_to_python_complete_bank_optimization_proved":False,
      "source_equilibrium_jacobian_invertible_proved":False,
      "actual_source_lean_rows_executed_in_python":False,
      "input_sha256":{str(p.relative_to(ROOT)):fingerprint(p)
                      for p in (SOURCE,PYTHON,P0)},
    }
    OUT.parent.mkdir(parents=True,exist_ok=True)
    OUT.write_text(json.dumps(report,indent=2,sort_keys=True)+"\n",
                   encoding="utf-8")
    print(json.dumps({
      "status":report["status"],"eta":eta,"Rstar":Rstar,
      "source_seed_share":seed,"checks":comparisons,
      "max_level_err":max_level_log,
      "max_root_derivative_err":max_root_derivative,
      "max_offroot_derivative_err":max_offroot_derivative,
      "max_invalid_root_only_offroot_error":max_invalid_root_only_offroot_derivative,
      "report":str(OUT)},indent=2))


if __name__=="__main__":
    main()

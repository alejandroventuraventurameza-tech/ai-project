#!/usr/bin/env python3
"""A NON-CERTIFYING 9-of-33 SOURCE Jacobian row-scale ledger.

Read actual regenerated finite IRF baseline and the independently audited
SOURCE->Python row-name permutation. Construct the analytically implied
root factors for nine indices: two firm regimes (branch dependent), bank
nominal-face transition at dates 0/1, worker-labor at dates 0/1, worker
Euler at dates 0/1, and date-one common nominal pledge.

The identity DG=P*T*DF*Dpsi for all 33 rows is NOT asserted: 24 SOURCE
indices, the firm Euler pledge shears and the state/control chart psi
remain open. A scalar finite-difference sanity check is NOT a source
Fréchet derivative proof.
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
CSV = HERE / "output/main/finite_irf_paths.csv"
META = HERE / "output/main/finite_irf_validation.json"
INDEX_MAP = HERE / "output/lean_python_33_row_permutation.json"
LEAN = ROOT / "lean/checkpoint/modules/Ventura26LiquidityAllocation/EconomicModel.lean"
OUT = HERE / "output/partial_source_jacobian_row_scale_ledger.json"
KNOWN = {4: 2, 5: 5, 6: 6, 9: 9, 10: 10,
         21: 21, 22: 22, 25: 25, 26: 26}


def require(x, why):
    if not x:
        raise AssertionError(why)


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def number(row, name):
    v = float(row[name+"_baseline"])
    require(math.isfinite(v) and v > 0, "Nonpositive baseline " + name)
    return v


def derivative(f, h=1e-5):
    return (f(h)-f(-h))/(2*h)


def scalar_ratio_chart_error(capacity, factor, signed=False):
    if signed:
        dsource = derivative(lambda z: 1.0-math.exp(.07*z))
        dpython = derivative(lambda z: math.log(math.exp(.07*z)))
    else:
        dsource = derivative(
            lambda z: capacity*(math.exp(.07*z)-math.exp(-.025*z))
        )
        dpython = derivative(
            lambda z: math.log(math.exp(.07*z)/math.exp(-.025*z))
        )
    return abs(dpython-factor*dsource)


def main():
    for path in (CSV,META,INDEX_MAP,LEAN):
        require(path.exists(), "Run verify and reproduction first: "+str(path))
    meta=json.loads(META.read_text(encoding="utf-8"))
    mapping=json.loads(INDEX_MAP.read_text(encoding="utf-8"))
    source_to_python=mapping["source_to_python_permutation"]
    require(len(source_to_python)==33 and
            sorted(source_to_python)==list(range(33)),
            "Need the verified SOURCE/Python 33-row bijection")
    for i,j in KNOWN.items():
        require(source_to_python[i]==j,
                f"Known normalized row {i} moved to Python {source_to_python[i]}")
    s=steady_case()
    require(meta["parameters"]["risk_aversion_worker"] == s.sigmaW == 1
            and s.varphi==1 and s.chiW>0 and s.aB>0,
            "Illustrative worker elasticity/curvature mismatch")
    require(meta["parameters"]["depreciation"]==s.delta and
            meta["parameters"]["pledgeabilities"]==s.pledge,
            "SOURCE physical/financial positive parameters changed")
    with CSV.open(newline="",encoding="utf-8") as f:
        raw=list(csv.DictReader(f))
    bykey={(r["branch"],int(r["period"])):r for r in raw}
    require(len(bykey)==len(raw) and len(raw)>=6,
            "Missing branch times or duplicate records")
    result={}
    maximum_scalar_derivative_error=0.
    maximum_baseline_zero_residual=0.
    for branch in ("slack","binding"):
        require(all((branch,t) in bykey for t in (0,1,2)),
                "Three consecutive baseline rows required")
        factors=[]
        def add(i,fac,formula,denom=1.):
            nonlocal maximum_scalar_derivative_error
            require(math.isfinite(fac) and fac!=0,"Known scalar factor vanishes")
            error=scalar_ratio_chart_error(denom,fac,signed=(i in (10,26)))
            if i==5 and branch=="slack":
                error=abs(derivative(lambda z: math.log(math.exp(.07*z))) -
                          derivative(lambda z: math.exp(.07*z)-1.0))
            require(error<1e-7,"Scalar derivative chart failed for row "+str(i))
            maximum_scalar_derivative_error=max(maximum_scalar_derivative_error,error)
            factors.append({
                "source_index":i,"python_index":KNOWN[i],
                "factor_candidate":fac,"factor_formula":formula,
                "scalar_chart_difference_error":error,
                "formal_full_jacobian_mapping_proved":False,
            })
        for t in (0,1):
            cur,nxt=bykey[(branch,t)],bykey[(branch,t+1)]
            pi_now=number(cur,"inflation")
            pi_next=number(nxt,"inflation")
            q_next=number(nxt,"capital_price")
            rl=number(cur,"loan_rate")
            J=(1-s.delta)*pi_next*q_next
            bankface_current=number(cur,"bank_equity")*pi_now
            bankface_next=number(nxt,"bank_equity")*pi_next
            bank_pred=s.aB*rl*bankface_current/pi_now
            wage=number(cur,"wage")
            labor=number(cur,"labor")
            cw=number(cur,"worker_consumption")
            labor_pred=s.chiW*cw**s.sigmaW*labor**s.varphi
            eulerratio=(
                number(cur,"deposit_rate")*s.bw*
                (cw/number(nxt,"worker_consumption"))**s.sigmaW/pi_next
            )
            require(min(J,bank_pred,labor_pred)>0,"Nonpositive scale")
            maximum_baseline_zero_residual=max(
                maximum_baseline_zero_residual,
                abs(bankface_next-bank_pred),abs(wage-labor_pred),
                abs(1-eulerratio)
            )
            if t==0:
                capH=s.pledge[0]*J*number(cur,"capital_next_H")
                capL=s.pledge[1]*J*number(cur,"capital_next_L")
                faceH=rl*number(cur,"credit_H")
                maximum_baseline_zero_residual=max(
                    maximum_baseline_zero_residual,abs(faceH-capH)
                )
                add(4,1/capH,"1/(theta_H*J_1*K_H,1)",capH)
                if branch=="binding":
                    faceL=rl*number(cur,"credit_L")
                    maximum_baseline_zero_residual=max(
                        maximum_baseline_zero_residual,abs(faceL-capL)
                    )
                    add(5,1/capL,"1/(theta_L*J_1*K_L,1)",capL)
                else:
                    add(5,1.0,"+1 (L slack: SOURCE r-1; Python log r)")
                add(6,1/bank_pred,"1/(predicted bank face at t=1)",bank_pred)
                add(9,1/labor_pred,"1/(chi_W*Cw_0^sigmaW*L_0^varphi)",labor_pred)
                add(10,-1.0,"-1 (SOURCE 1-r vs Python log r)")
            else:
                add(21,1/J,"1/J_2 (date-one nominal pledge)",J)
                add(22,1/bank_pred,"1/(predicted bank face at t=2)",bank_pred)
                add(25,1/labor_pred,"1/(chi_W*Cw_1^sigmaW*L_1^varphi)",labor_pred)
                add(26,-1.0,"-1 (SOURCE 1-r vs Python log r)")
        require(len(factors)==9,"Expected 9 known scalar source rows")
        result[branch]={
            "coefficient_rows":factors,
            "known_factor_product_nonzero":math.prod(
                entry["factor_candidate"] for entry in factors
            ),
            "IMPORTANT":"Only a proper subblock is tested. The full 33x33 T is unknown."
        }
    require(maximum_baseline_zero_residual < 5e-9,
            "Base paths are not valid nearby zeros for partial scaling")
    unknown=sorted(set(range(33))-set(KNOWN))
    require(len(unknown)==24,"Unknown source rows must remain unfilled")
    report={
        "status":"NUMERICAL_PARTIAL_9_OF_33_ROW_SCALES_NOT_FULL_MATRIX_CERTIFICATE",
        "source_sha256":{
            str(path.relative_to(ROOT)):sha256(path)
            for path in (CSV,META,INDEX_MAP,LEAN,HERE/"finite_irf.py")
        },
        "source_to_python_permutation":source_to_python,
        "known_source_indices":sorted(KNOWN),
        "unknown_source_indices":unknown,
        "source_row_count":33,
        "known_source_row_count":9,
        "unproved_source_row_count":24,
        "max_scalar_chart_derivative_error":maximum_scalar_derivative_error,
        "max_baseline_known_row_source_zero_residual":maximum_baseline_zero_residual,
        "full_source_jacobian_inverse_certified":False,
        "full_source_operator_equality_certified":False,
        "coord_chart_source_to_python_certified":False,
        "firm_euler_row_shear_proof_for_full_33":False,
        "branches":result,
        "warnings":[
            "Only exact scalar normalization shapes are recorded on root candidate",
            "The 33 source functions and all cross-Jacobian coefficients still need matching",
            "No conclusion about source nonlinear invariant graph, infinite equilibrium or permanent growth",
        ],
    }
    OUT.parent.mkdir(parents=True,exist_ok=True)
    OUT.write_text(json.dumps(report,indent=2,sort_keys=True)+"\n",encoding="utf-8")
    print(json.dumps({
        "status":report["status"],
        "known_rows":len(KNOWN),"unknown_rows":len(unknown),
        "max_scalar_chart_derivative_error":maximum_scalar_derivative_error,
        "max_baseline_zero_residual":maximum_baseline_zero_residual,
        "output":str(OUT)
    },indent=2))


if __name__=="__main__":
    main()

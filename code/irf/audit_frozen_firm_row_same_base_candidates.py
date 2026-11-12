#!/usr/bin/env python3
"""Same-base frozen-binding firm-row transcription checks.

Checks the independently SOURCE-shaped eight firm rows on the very SAME
frozen predecessor and P0 as the floating Python Jacobian diagnostic.
This is a conditional Python transcription test, never an execution of
the original SOURCE Lean economic residuals or a validated derivative.
"""
from __future__ import annotations
import hashlib
import json
import math
from pathlib import Path
import finite_irf as py
from frozen_stationary_prefix_audit import frozen_stationary_seed
from audit_source_firm_budget_euler_shear import (
    source_transcription, INDEX, DIRECT, SHEAR
)

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
SOURCE=ROOT/"lean/checkpoint/modules/Ventura26LiquidityAllocation/EconomicModel.lean"
ENGINE=HERE/"finite_irf.py"
PRE=HERE/"inputs/rational_preconditioners.json"
TRANS=HERE/"audit_source_firm_budget_euler_shear.py"
OUT=HERE/"output/frozen_source_firm_same_base_candidate.json"

def require(v,msg):
    if not v:raise AssertionError(msg)

def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    s=py.steady_case()
    seed=frozen_stationary_seed(s)
    pdata=json.loads(PRE.read_text(encoding="utf-8"))
    p0=[[float(x) for x in row] for row in pdata["P0"]]
    require(len(p0)==16 and all(len(row)==6 for row in p0),"P0 shape mismatch")
    require(set(DIRECT)=={0,1,2,3,17,18} and set(SHEAR)=={19,20},
            "SOURCE firm row partition changed")
    require(all(seed.X0[i]==seed.X1[i] for i in range(7))
            and seed.e0==seed.e1==[0.0,0.0],
            "Not the fixed inherited stationary predecessor")
    require(all(seed.U0[i]==seed.U1[i] for i in range(10)),
            "Stationary controls not frozen")
    z_points=[
        [0.0]*33,
        [3e-4*math.sin(1.37*(i+1)) for i in range(33)],
        [-6e-4*math.cos(.83*(i+1)) for i in range(33)],
    ]
    result={}
    for branch in ("binding","slack"):
        max_direct=max_shear=max_derivative=0.0
        count=0
        for z in z_points:
            src,shear,g,coef=source_transcription(seed,p0,z,branch)
            residual=py.prefix_residual(seed,p0,branch,(0.,0.,0.,0.),z)
            require(len(residual)==33 and set(src)==set(INDEX),
                    "Invalid reduced firm rows")
            for ix in DIRECT:
                max_direct=max(max_direct,abs(src[ix]-residual[INDEX[ix][0]]))
            for ix in SHEAR:
                max_shear=max(max_shear,abs(
                    src[ix]-residual[INDEX[ix][0]]-shear[ix]))
            require(abs(g-residual[21])<2e-11,
                    "Common pledge row mismatch at frozen predecessor")
            count+=1
        # Derivative of the full conditional SOURCE/Python residual identity,
        # including state dependence of the Euler shear coefficient.
        z=z_points[1]
        for k in range(33):
            h=1e-6
            xp=list(z);xm=list(z);xp[k]+=h;xm[k]-=h
            sp,shp,_,_=source_transcription(seed,p0,xp,branch)
            sm,shm,_,_=source_transcription(seed,p0,xm,branch)
            pp=py.prefix_residual(seed,p0,branch,(0.,0.,0.,0.),xp)
            pm=py.prefix_residual(seed,p0,branch,(0.,0.,0.,0.),xm)
            for ix in INDEX:
                j=INDEX[ix][0]
                left=(sp[ix]-sm[ix])/(2*h)
                right=(pp[j]-pm[j])/(2*h)
                if ix in SHEAR:
                    right+=(shp[ix]-shm[ix])/(2*h)
                max_derivative=max(max_derivative,abs(left-right))
        require(max_direct<2e-10 and max_shear<2e-10
                and max_derivative<5e-7,
                "Frozen SOURCE-shaped firm candidate failed numeric equality")
        result[branch]={
            "evaluation_points":count,
            "max_direct_row_error":max_direct,
            "max_firm_euler_shear_identity_error":max_shear,
            "max_conditional_directional_difference":max_derivative,
            "tested_directions":33,
            "source_rows":sorted(INDEX),
        }
    data={
      "status":"FROZEN_FIRM_SOURCE_SHAPED_PYTHON_CANDIDATES_ONLY",
      "baseline":"frozen_stationary_seed(steady_case())",
      "branch_regimes":result,
      "candidate_rows_tested":8,
      "remaining_rows_not_tested_on_this_same_base":25,
      "four_policy_intervention_shocks_applied":False,
      "source_lean_operator_executed":False,
      "source_python_full_33_functional_identity_proved":False,
      "source_jacobian_inverse_certified":False,
      "source_same_base_row_transform_proved":False,
      "numerical_tests_only":True,
      "files_sha256":{str(x.relative_to(ROOT)):digest(x)
                      for x in (SOURCE,ENGINE,PRE,TRANS)}
    }
    OUT.parent.mkdir(parents=True,exist_ok=True)
    OUT.write_text(json.dumps(data,indent=2,sort_keys=True)+"\n",
                   encoding="utf-8")
    print(json.dumps({"status":data["status"],"branches":result},indent=2))

if __name__=="__main__":
    main()

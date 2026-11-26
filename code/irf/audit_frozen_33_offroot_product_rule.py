#!/usr/bin/env python3
"""Explicit off-root product/quotient rule for all 33 SOURCE-shaped rows.

A conditional NUMERICAL audit over independently transcribed Python forms,
not a mathematical certificate of original Lean SOURCE economic derivative.
"""
from __future__ import annotations
import math,json,hashlib
from pathlib import Path
import finite_irf as engine
from frozen_stationary_prefix_audit import frozen_stationary_seed
from audit_frozen_33_offroot_nonlinear_transform import (
    build_source_shaped,SOURCE_TO_PY,SOURCE_INDICES,SHEAR,N
)

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
P0=HERE/"inputs/rational_preconditioners.json"
SOURCE=ROOT/"lean/checkpoint/modules/Ventura26LiquidityAllocation/EconomicModel.lean"
ENGINE=HERE/"finite_irf.py"
TRANS=HERE/"audit_frozen_33_offroot_nonlinear_transform.py"
OUT=HERE/"output/frozen_33_offroot_explicit_product_rule.json"

def check(v,msg):
    if not v:raise AssertionError(msg)

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    s=engine.steady_case()
    base=frozen_stationary_seed(s)
    m=json.loads(P0.read_text(encoding="utf-8"))
    p0=[[float(x) for x in row] for row in m["P0"]]
    check(len(p0)==16 and all(len(row)==6 for row in p0),"Wrong P0")
    shock_cases=((0.,0.,0.,0.),(-1e-5,0.,0.,0.),(0.,0.,-1e-5,0.))
    zs=(
       [4e-4*math.sin(1.39*(k+1)) for k in range(N)],
       [-7e-4*math.cos(.79*(k+1)) for k in range(N)]
    )
    result={}
    for branch in ("binding","slack"):
        max_error=0.
        max_scalar_denom_term=0.
        max_euler_coefficient_term=0.
        comparisons=0
        for v in shock_cases:
            for z in zs:
                current,scale,coef,_,_=build_source_shaped(base,p0,z,branch,v)
                for k in range(N):
                    h=1e-6
                    xp=list(z);xm=list(z);xp[k]+=h;xm[k]-=h
                    plus,sp,cp,_,_=build_source_shaped(base,p0,xp,branch,v)
                    minus,sm,cm,_,_=build_source_shaped(base,p0,xm,branch,v)
                    fp=engine.prefix_residual(base,p0,branch,v,xp)
                    fm=engine.prefix_residual(base,p0,branch,v,xm)
                    for ix,j in SOURCE_TO_PY.items():
                        ds=(plus[ix]-minus[ix])/(2*h)
                        if ix in SOURCE_INDICES:
                            level,_,denom,sgn=scale[ix]
                            dd=(sp[ix][2]-sm[ix][2])/(2*h)
                            check(denom>0 and 1+sgn*level/denom>0,
                                  "Scalar row outside positive log chart")
                            direct=sgn*ds/denom
                            denom_term=-sgn*level*dd/(denom*denom)
                            derivative=(direct+denom_term)/(1+sgn*level/denom)
                            max_scalar_denom_term=max(max_scalar_denom_term,
                                                      abs(denom_term))
                        elif ix in SHEAR:
                            pledge=scale[21][0]
                            denom=scale[21][2]
                            dp=(sp[21][0]-sm[21][0])/(2*h)
                            dd=(sp[21][2]-sm[21][2])/(2*h)
                            dc=(cp[ix]-cm[ix])/(2*h)
                            coefficient_term=-dc*pledge/denom
                            derivative=(ds+coefficient_term-
                                coef[ix]*(dp/denom-pledge*dd/(denom*denom)))
                            max_euler_coefficient_term=max(
                                max_euler_coefficient_term,abs(coefficient_term))
                        else:
                            derivative=ds
                        actual=(fp[j]-fm[j])/(2*h)
                        error=abs(derivative-actual)
                        check(math.isfinite(error),"Nonfinite derivative")
                        max_error=max(max_error,error)
                        comparisons+=1
        check(max_error<5e-7,
              "Offroot full derivative chain/product rule mismatch")
        result[branch]={
            "max_abs_explicit_product_rule_vs_python_derivative":max_error,
            "max_abs_scalar_denominator_derivative_term":max_scalar_denom_term,
            "max_abs_euler_coefficient_derivative_term":max_euler_coefficient_term,
            "scalar_nonzero_residual_term_retained":True,
            "euler_state_dependent_shear_derivative_retained":True,
            "individual_entry_comparisons":comparisons,
            "coordinate_directions":N
        }
    report={
        "status":"NUMERICAL_EXPLICIT_OFFROOT_33_PRODUCT_RULE_ONLY",
        "base":"frozen_stationary_seed(steady_case())",
        "branches":result,
        "source_operator_evaluated_in_lean":False,
        "source_to_python_33_functional_identity_proved":False,
        "source_economic_jacobian_inverse_certified":False,
        "conditional_source_shaped_transcriptions_only":True,
        "original_source_tail_identified":False,
        "inputs_sha256":{str(p.relative_to(ROOT)):digest(p)
                         for p in (SOURCE,ENGINE,P0,TRANS)}
    }
    OUT.parent.mkdir(parents=True,exist_ok=True)
    OUT.write_text(json.dumps(report,indent=2,sort_keys=True)+"\n",
                   encoding="utf-8")
    print(json.dumps({"status":report["status"],"branches":result},indent=2))
if __name__=="__main__":
    main()

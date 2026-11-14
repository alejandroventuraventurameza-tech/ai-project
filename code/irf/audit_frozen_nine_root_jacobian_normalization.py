#!/usr/bin/env python3
"""At-root derivative normalization of nine SOURCE-shaped scalar rows.

The nine source-level residuals are *transcribed* expressions. This tests
the derivative of log residuals and level residuals at the SAME frozen
binding root. At a root, D log_r = sign/scale * D level_r.
It does not compute or certify the original Lean SOURCE fderiv.
"""
from __future__ import annotations
from pathlib import Path
import hashlib
import json
import math
import finite_irf as model
from frozen_stationary_prefix_audit import frozen_stationary_seed
from audit_frozen_nine_scalar_source_shapes import (
    source_shape_pairs, SOURCE_INDICES, SOURCE_TO_PY
)
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
SOURCE=ROOT/"lean/checkpoint/modules/Ventura26LiquidityAllocation/EconomicModel.lean"
ENGINE=HERE/"finite_irf.py"
P0_FILE=HERE/"inputs/rational_preconditioners.json"
TRANS=HERE/"audit_frozen_nine_scalar_source_shapes.py"
OUTPUT=HERE/"output/frozen_nine_scalar_root_jacobian_normalization.json"

def ensure(ok,msg):
    if not ok:raise AssertionError(msg)

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    seed=frozen_stationary_seed(model.steady_case())
    pdata=json.loads(P0_FILE.read_text(encoding="utf-8"))
    p0=[[float(v) for v in row] for row in pdata["P0"]]
    ensure(len(p0)==16 and all(len(row)==6 for row in p0),"Invalid common P0")
    z=[0.]*33
    v=(0.,0.,0.,0.)
    branch="binding"
    base_rows=source_shape_pairs(seed,p0,branch,z)
    base_python=model.prefix_residual(seed,p0,branch,v,z)
    ensure(len(base_rows)==9 and len(base_python)==33,"Missing rows")
    ensure(max(abs(x) for x in base_python)<1e-9,
           "Frozen binding base is not a common Python root")
    labels={}
    for i in sorted(SOURCE_INDICES):
        level,log_value,denom,sign=base_rows[i]
        ensure(abs(level)<1e-9 and abs(log_value)<1e-9,
               "A source-shaped scalar level row is not at root")
        ensure(denom>0,"Nonpositive root normalizer")
        ensure(sign in (-1,1),"Unexpected source sign")
        labels[str(i)]={"python_index":SOURCE_TO_PY[i],
                        "root_source_level":level,
                        "root_denominator":denom,
                        "root_multiplier_python_log_from_source_level":sign/denom}
    summaries={}
    for h in (2e-5,2e-6,2e-7):
        max_derivative_error=0.
        max_source_product_remainder=0.
        max_level_direction=0.
        for col in range(33):
            zp=list(z);zm=list(z)
            zp[col]+=h;zm[col]-=h
            sp=source_shape_pairs(seed,p0,branch,zp)
            sm=source_shape_pairs(seed,p0,branch,zm)
            pp=model.prefix_residual(seed,p0,branch,v,zp)
            pm=model.prefix_residual(seed,p0,branch,v,zm)
            for ix in SOURCE_INDICES:
                py_idx=SOURCE_TO_PY[ix]
                multiplier=labels[str(ix)]["root_multiplier_python_log_from_source_level"]
                d_source=(sp[ix][0]-sm[ix][0])/(2*h)
                d_python=(pp[py_idx]-pm[py_idx])/(2*h)
                max_derivative_error=max(max_derivative_error,
                                         abs(multiplier*d_source-d_python))
                max_level_direction=max(max_level_direction,abs(d_source))
                # Differentiate the EXACT nonlinear relation:
                # d(level)=sign*(d(denom)*expm1(log) +
                #                 denom*exp(log)*d(log)).
                d_denom=(sp[ix][2]-sm[ix][2])/(2*h)
                denominator_at_root=base_rows[ix][2]
                product_derivative=base_rows[ix][3]*(
                    d_denom*math.expm1(base_rows[ix][1])+
                    denominator_at_root*math.exp(base_rows[ix][1])*d_python)
                max_source_product_remainder=max(
                    max_source_product_remainder,abs(d_source-product_derivative))
        ensure(max_derivative_error<5e-7 and max_source_product_remainder<5e-7,
               "Conditional nine SOURCE-shaped root derivative normalization mismatch")
        summaries[str(h)]={
            "max_root_multiplier_times_source_level_derivative_minus_python_log_derivative":max_derivative_error,
            "max_product_rule_derivative_remainder":max_source_product_remainder,
            "max_abs_source_shaped_level_derivative":max_level_direction,
            "directions":33
        }
    report={
        "status":"NUMERICAL_FROZEN_BINDING_NINE_SCALAR_ROOT_DERIVATIVE_NORMALIZATION_ONLY",
        "base":"frozen_stationary_seed(steady_case())",
        "branch":"binding",
        "common_zero_interventions":[0.]*4,
        "source_row_count":9,
        "source_row_root_factors":labels,
        "base_max_abs_python_residual":max(abs(x) for x in base_python),
        "step_sensitivity":summaries,
        "source_operator_executed":False,
        "source_frechet_derivative_executed":False,
        "source_jacobian_inverse_proved":False,
        "source_to_python_full_functional_identity_proved":False,
        "slack_branch_root_proved":False,
        "input_sha256":{str(p.relative_to(ROOT)):sha(p)
                        for p in (SOURCE,ENGINE,P0_FILE,TRANS)}
    }
    OUTPUT.parent.mkdir(parents=True,exist_ok=True)
    OUTPUT.write_text(json.dumps(report,indent=2,sort_keys=True)+"\n",
                      encoding="utf-8")
    print(json.dumps({"status":report["status"],
                      "base_max_abs_python_residual":report["base_max_abs_python_residual"],
                      "step_sensitivity":summaries},indent=2))
if __name__=="__main__":main()

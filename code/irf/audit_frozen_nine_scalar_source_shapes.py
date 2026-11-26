#!/usr/bin/env python3
"""Nine SOURCE-shaped level-versus-log rows at the FROZEN Python predecessor.

These conditional transcriptions are not executions of original Lean SOURCE.
A nonzero SOURCE level residual is related to its Python logarithmic row
by expm1; the linear root multiplier only applies AT a common zero.
"""
from __future__ import annotations
import hashlib
import json
import math
from pathlib import Path
import finite_irf as py
from frozen_stationary_prefix_audit import frozen_stationary_seed

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
SOURCE=ROOT/"lean/checkpoint/modules/Ventura26LiquidityAllocation/EconomicModel.lean"
ENGINE=HERE/"finite_irf.py"
P0=HERE/"inputs/rational_preconditioners.json"
OUT=HERE/"output/frozen_nine_scalar_source_shape_candidates.json"
SOURCE_INDICES={4,5,6,9,10,21,22,25,26}
SOURCE_TO_PY={4:2,5:5,6:6,9:9,10:10,21:21,22:22,25:25,26:26}

def require(c,msg):
    if not c:raise AssertionError(msg)

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def source_shape_pairs(base,p0,branch,z):
    s=base.s
    x1,u0,x2c,u1,u2=py.decode_prefix(base,p0,z)
    x2=py.expand_compact_state(s,x2c)
    # Independent level-form transcription of SOURCE rows, not Python residual.
    records={}
    for date,(state,ctrl,next_state,next_ctrl,regime) in enumerate((
       (base.X0,u0,x1,u1,branch),
       (x1,u1,x2,u2,"binding")
    )):
        aux=py.auxiliary(s,state,ctrl,next_state[:2],base.e0 if date==0 else base.e1)
        wage=ctrl[3]
        labor=aux["L"]
        cw=ctrl[2]
        denom_labor=s.chiW*cw*labor
        bank_pred=s.aB*ctrl[8]*state[4]/ctrl[5]
        bank_actual=next_state[4]
        euler_ratio=s.bw*cw/next_ctrl[2]*ctrl[7]/next_ctrl[5]
        require(min(wage,denom_labor,bank_pred,bank_actual,euler_ratio)>0,
                "Source scalar log chart left positive domain")
        ix=(6,9,10) if date==0 else (22,25,26)
        records[ix[0]]=(bank_actual-bank_pred, math.log(bank_actual/bank_pred),
                        bank_pred,1)
        records[ix[1]]=(wage-denom_labor,math.log(wage/denom_labor),
                        denom_labor,1)
        records[ix[2]]=(1-euler_ratio,math.log(euler_ratio),1.,-1)
    for i,ix in enumerate((4,5)):
        face=x1[2+i]
        collateral=s.pledge[i]*s.ad*u1[5]*u1[6]*x1[i]
        require(min(face,collateral)>0,"Nonpositive collateral face")
        if branch=="slack" and i==1:
            ratio=u0[8]*(s.be*u0[i]/u1[i])/u1[5]
            require(ratio>0,"L slack ratio is not positive")
            records[ix]=(ratio-1,math.log(ratio),1.,1)
        else:
            records[ix]=(face-collateral,math.log(face/collateral),
                         collateral,1)
    pledge=x2c[2]
    pledge_pred=s.ad*u2[5]*u2[6]
    require(min(pledge,pledge_pred)>0,"Nonpositive second-date pledge")
    records[21]=(pledge-pledge_pred,math.log(pledge/pledge_pred),
                 pledge_pred,1)
    require(set(records)==SOURCE_INDICES,"Incomplete scalar SOURCE partition")
    return records

def main():
    s=py.steady_case()
    base=frozen_stationary_seed(s)
    payload=json.loads(P0.read_text(encoding="utf-8"))
    p0=[[float(v) for v in row] for row in payload["P0"]]
    require(len(p0)==16 and all(len(row)==6 for row in p0),"Wrong terminal P0")
    z_points=(
       [0.]*33,
       [4e-4*math.sin(1.19*(i+1)) for i in range(33)],
       [-6e-4*math.cos(.91*(i+1)) for i in range(33)],
    )
    summary={}
    for branch in ("binding","slack"):
        max_transcription=max_nonlinear=max_direction=0.
        max_source_zero=0.
        for z in z_points:
            entries=source_shape_pairs(base,p0,branch,z)
            pred=py.prefix_residual(base,p0,branch,(0.,0.,0.,0.),z)
            for source_idx,(level,logrow,denom,sign) in entries.items():
                py_idx=SOURCE_TO_PY[source_idx]
                max_transcription=max(max_transcription,abs(pred[py_idx]-logrow))
                require(math.isfinite(level) and denom>0,"Invalid level/scale")
                # Exact nonlinear relation on the positive domain, OFF roots.
                # level=scale*expm1(sign*logrow), except signed Euler has
                # level=-expm1(logrow) and carries sign=-1.
                predicted_level=sign*denom*math.expm1(logrow)
                max_nonlinear=max(max_nonlinear,abs(level-predicted_level))
            max_source_zero=max(max_source_zero,max(abs(v[0]) for v in entries.values()))
        z=z_points[1];step=1e-6
        for k in range(33):
            zp=list(z);zm=list(z);zp[k]+=step;zm[k]-=step
            ep=source_shape_pairs(base,p0,branch,zp)
            em=source_shape_pairs(base,p0,branch,zm)
            pp=py.prefix_residual(base,p0,branch,(0.,0.,0.,0.),zp)
            pm=py.prefix_residual(base,p0,branch,(0.,0.,0.,0.),zm)
            for source_idx in SOURCE_INDICES:
                j=SOURCE_TO_PY[source_idx]
                derivative_log_source=(ep[source_idx][1]-em[source_idx][1])/(2*step)
                derivative_log_python=(pp[j]-pm[j])/(2*step)
                max_direction=max(max_direction,abs(derivative_log_source-derivative_log_python))
        require(max_transcription<2e-10 and max_nonlinear<2e-10
                and max_direction<5e-7,"Frozen nine-row scalar candidate mismatch")
        summary[branch]={
            "max_log_shape_error":max_transcription,
            "max_exact_nonlinear_level_transform_error":max_nonlinear,
            "max_log_directional_error":max_direction,
            "source_level_max_abs_on_probes":max_source_zero,
            "source_row_indices":sorted(SOURCE_INDICES),
            "source_to_python_mapping":{str(i):SOURCE_TO_PY[i] for i in sorted(SOURCE_INDICES)},
            "tested_33_coordinate_directions":33,
            "positive_log_domain_at_test_points":True
        }
    report={
      "status":"FROZEN_NINE_SCALAR_SOURCE_SHAPED_ROW_CANDIDATES_ONLY",
      "base":"frozen_stationary_seed(steady_case())",
      "branches":summary,
      "scalar_row_count":9,
      "same_base_frozen_predecessor":True,
      "same_base_P0_used":True,
      "source_operator_executed":False,
      "full_source_python_33_functional_identity_proved":False,
      "source_jacobian_inverse_certified":False,
      "nonlinear_ratio_transform_off_root_required":True,
      "at_nonzero_residual_cannot_replace_by_constant_root_factor":True,
      "source_inputs_sha256":{str(p.relative_to(ROOT)):sha(p) for p in (SOURCE,ENGINE,P0)}
    }
    OUT.parent.mkdir(parents=True,exist_ok=True)
    OUT.write_text(json.dumps(report,indent=2,sort_keys=True)+"\n",encoding="utf-8")
    print(json.dumps({"status":report["status"],"branches":summary},indent=2))
if __name__=="__main__":main()

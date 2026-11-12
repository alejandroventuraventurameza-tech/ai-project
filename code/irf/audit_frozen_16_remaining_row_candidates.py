#!/usr/bin/env python3
"""Conditional sixteen SOURCE-shaped remaining-row checks, same frozen base.

This transcribes Python equations under SOURCE-guided forms; it does NOT
execute Lean's original economic 33-row operator or certify a derivative.
"""
from pathlib import Path
import hashlib
import json
import math
import finite_irf as model
from frozen_stationary_prefix_audit import frozen_stationary_seed
from audit_source_identity_row_candidates import ROWS, transcribed_prefix_rows
from audit_source_firm_budget_euler_shear import INDEX as FIRM

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
SOURCE=ROOT/"lean/checkpoint/modules/Ventura26LiquidityAllocation/EconomicModel.lean"
ENGINE=HERE/"finite_irf.py"
P0=HERE/"inputs/rational_preconditioners.json"
TRANS=HERE/"audit_source_identity_row_candidates.py"
OUT=HERE/"output/frozen_source_16_remaining_row_candidates.json"

def require(test,msg):
    if not test:raise AssertionError(msg)

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    seed=frozen_stationary_seed(model.steady_case())
    raw=json.loads(P0.read_text(encoding="utf-8"))
    p0=[[float(v) for v in row] for row in raw["P0"]]
    require(len(p0)==16 and all(len(row)==6 for row in p0),"Wrong P0 shape")
    indices={src for src,*_ in ROWS}
    require(len(indices)==16 and indices.isdisjoint(set(FIRM)),
            "Row audit overlaps firm rows")
    probes=(
      (0.,0.,0.,0.),
      (-1e-5,0.,0.,0.),
      (0.,-1e-5,0.,0.),
      (0.,0.,-1e-5,0.),
      (0.,0.,0.,-1e-5)
    )
    zs=(
      [0.]*33,
      [4e-4*math.sin(1.39*(i+1)) for i in range(33)],
      [-7e-4*math.cos(.79*(i+1)) for i in range(33)]
    )
    report={}
    for branch in ("binding","slack"):
        max_level=0.;max_direction=0.;count=0
        for shock in probes:
            for z in zs:
                src=transcribed_prefix_rows(seed,p0,z,shock)
                got=model.prefix_residual(seed,p0,branch,shock,z)
                require(len(src)==16 and len(got)==33,"Row shape mismatch")
                for n,(_,j,_,_) in enumerate(ROWS):
                    err=abs(src[n]-got[j])
                    require(math.isfinite(err),"Nonfinite residual")
                    max_level=max(max_level,err)
                count+=1
        h=1e-6
        z=zs[1]
        shock=probes[1]
        for col in range(33):
            plus=list(z);minus=list(z)
            plus[col]+=h;minus[col]-=h
            sp=transcribed_prefix_rows(seed,p0,plus,shock)
            sm=transcribed_prefix_rows(seed,p0,minus,shock)
            pp=model.prefix_residual(seed,p0,branch,shock,plus)
            pm=model.prefix_residual(seed,p0,branch,shock,minus)
            for n,(_,j,_,_) in enumerate(ROWS):
                err=abs((sp[n]-sm[n])/(2*h)-(pp[j]-pm[j])/(2*h))
                require(math.isfinite(err),"Nonfinite derivative estimate")
                max_direction=max(max_direction,err)
        require(max_level<2e-10 and max_direction<5e-7,
                "Frozen same-base sixteen-row candidate failed")
        report[branch]={
            "policy_probes":len(probes),"coordinate_probes":len(zs),
            "row_count":len(ROWS),"direction_count":33,
            "max_conditional_level_error":max_level,
            "max_conditional_directional_error":max_direction,
            "evaluations":count
        }
    data={
       "status":"FROZEN_SAME_BASE_16_SOURCE_SHAPED_ROW_CANDIDATES_ONLY",
       "base":"frozen_stationary_seed(steady_case())",
       "branch_results":report,
       "source_row_indices":sorted(indices),
       "previous_firm_source_rows_excluded":sorted(FIRM),
       "source_economic_operator_executed":False,
       "source_python_33_functional_equality_proved":False,
       "source_jacobian_invertibility_certified":False,
       "source_lean_derivative_executed":False,
       "candidate_only":True,
       "input_sha256":{str(p.relative_to(ROOT)):sha(p)
                       for p in (SOURCE,ENGINE,P0,TRANS)}
    }
    OUT.parent.mkdir(parents=True,exist_ok=True)
    OUT.write_text(json.dumps(data,indent=2,sort_keys=True)+"\n",encoding="utf-8")
    print(json.dumps({"status":data["status"],"branches":report},indent=2))

if __name__=="__main__":
    main()

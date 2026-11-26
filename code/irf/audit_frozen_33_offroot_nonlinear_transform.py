#!/usr/bin/env python3
"""Nonlinear off-root 33-row SOURCE-shaped -> Python transform candidate.

T(z) is NOT constant away from the common root. Scalar rows use exact
log1p level transforms; two firm Euler rows require state-dependent
common-pledge shears. Executes ONLY Python SOURCE-shaped transcriptions,
never the original Lean SOURCE operator.
"""
from __future__ import annotations
import hashlib
import json
import math
from pathlib import Path
import finite_irf as model
from frozen_stationary_prefix_audit import frozen_stationary_seed
from audit_source_firm_budget_euler_shear import source_transcription, INDEX as FIRMS, SHEAR
from audit_source_identity_row_candidates import transcribed_prefix_rows, ROWS
from audit_frozen_nine_scalar_source_shapes import source_shape_pairs, SOURCE_TO_PY as SCALAR_TO_PY, SOURCE_INDICES

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
SOURCE=ROOT/"lean/checkpoint/modules/Ventura26LiquidityAllocation/EconomicModel.lean"
ENGINE=HERE/"finite_irf.py"
P0_FILE=HERE/"inputs/rational_preconditioners.json"
OUT=HERE/"output/frozen_33_offroot_nonlinear_transform_candidate.json"
N=33

def require(ok,msg):
    if not ok:raise AssertionError(msg)

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

SOURCE_TO_PY={}
SOURCE_TO_PY.update({i:j for i,(j,_) in FIRMS.items()})
SOURCE_TO_PY.update({i:j for i,j,*_ in ROWS})
SOURCE_TO_PY.update(SCALAR_TO_PY)
require(len(SOURCE_TO_PY)==N and
        sorted(SOURCE_TO_PY.values())==list(range(N)),
        "SOURCE/Python 33-row mapping not bijective")

def build_source_shaped(base,p0,z,branch,shock):
    firm,actual_shear,g,coeff=source_transcription(base,p0,z,branch)
    rest=transcribed_prefix_rows(base,p0,z,shock)
    scalar=source_shape_pairs(base,p0,branch,z)
    bysource=dict(firm)
    bysource.update({i:rest[k] for k,(i,*_) in enumerate(ROWS)})
    bysource.update({i:scalar[i][0] for i in SOURCE_INDICES})
    require(len(bysource)==N and set(bysource)==set(range(N)),
            "Malformed 8+16+9 source-shaped partition")
    return bysource,scalar,coeff,actual_shear,g

def nonlinear_pullback(candidate,scalar,coeff):
    """Construct all 33 Python-style rows WITHOUT using prefix_residual."""
    rows=[None]*N
    for i,j in SOURCE_TO_PY.items():
        if i in SOURCE_INDICES:
            level,unused_log,denom,sign=scalar[i]
            require(denom>0 and sign in (-1,1),
                    "Positive chart violated for a scalar SOURCE row")
            ratio_shift=sign*level/denom
            require(1.0+ratio_shift>0,"Logarithm outside its positive domain")
            rows[j]=math.log1p(ratio_shift)
        elif i in SHEAR:
            pledge_source=scalar[21][0]
            pledge_denom=scalar[21][2]
            require(pledge_denom>0,"Nonpositive pledge denominator")
            rows[j]=candidate[i]-coeff[i]*(pledge_source/pledge_denom)
        else:
            rows[j]=candidate[i]
    require(all(v is not None and math.isfinite(v) for v in rows),
            "Invalid nonlinear SOURCE-shaped reconstructed residual")
    return rows

def main():
    s=model.steady_case()
    base=frozen_stationary_seed(s)
    data=json.loads(P0_FILE.read_text(encoding="utf-8"))
    p0=[[float(v) for v in row] for row in data["P0"]]
    require(len(p0)==16 and all(len(row)==6 for row in p0),
            "Pinned tail P0 changed")
    probe_states=(
       [0.]*N,
       [4e-4*math.sin(1.39*(j+1)) for j in range(N)],
       [-7e-4*math.cos(.79*(j+1)) for j in range(N)],
    )
    shocks=(
       (0.,0.,0.,0.),
       (-1e-5,0.,0.,0.),
       (0.,-1e-5,0.,0.),
       (0.,0.,-1e-5,0.),
       (0.,0.,0.,-1e-5),
    )
    result={}
    for branch in ("binding","slack"):
        max_functional=max_shear=max_direction=0.
        location=None
        evaluated=0
        for shock in shocks:
            for z in probe_states:
                src,sc,coeff,shear,g=build_source_shaped(base,p0,z,branch,shock)
                recon=nonlinear_pullback(src,sc,coeff)
                original=model.prefix_residual(base,p0,branch,shock,z)
                for k in range(N):
                    discrepancy=abs(recon[k]-original[k])
                    if discrepancy>max_functional:
                        max_functional=discrepancy
                        location={"python_row":k,"intervention":list(shock),
                                  "probe_index":probe_states.index(z)}
                for i in SHEAR:
                    exact_shear=coeff[i]*math.expm1(g)
                    max_shear=max(max_shear,abs(shear[i]-exact_shear))
                evaluated+=1
        for shock in (shocks[0],shocks[1],shocks[3]):
            z=probe_states[1]
            h=1e-6
            for col in range(N):
                zp=list(z);zm=list(z);zp[col]+=h;zm[col]-=h
                sp,scale_p,coef_p,_,_=build_source_shaped(base,p0,zp,branch,shock)
                sm,scale_m,coef_m,_,_=build_source_shaped(base,p0,zm,branch,shock)
                rp=nonlinear_pullback(sp,scale_p,coef_p)
                rm=nonlinear_pullback(sm,scale_m,coef_m)
                pp=model.prefix_residual(base,p0,branch,shock,zp)
                pm=model.prefix_residual(base,p0,branch,shock,zm)
                for k in range(N):
                    error=abs((rp[k]-rm[k])/(2*h)-(pp[k]-pm[k])/(2*h))
                    max_direction=max(max_direction,error)
        require(max_functional<2e-10 and max_shear<2e-10 and
                max_direction<5e-7,
                "Nonlinear off-root candidate transform mismatch")
        result[branch]={
          "candidate_state_and_shock_evaluations":evaluated,
          "shock_vectors":len(shocks),
          "positive_chart_probes":len(probe_states),
          "max_abs_full_33_candidate_functional_error":max_functional,
          "max_abs_euler_state_dependent_shear_error":max_shear,
          "max_abs_full_33_directional_derivative_error":max_direction,
          "derivative_shocks":3,
          "derivative_coordinates":N,
          "largest_discrepancy_location":location
        }
    report={
       "status":"NUMERICAL_NONLINEAR_33_SOURCE_SHAPED_OFFROOT_TRANSFORM_ONLY",
       "base":"frozen_stationary_seed(steady_case())",
       "branches":result,
       "policy_shocks":["none","reserve_rate","reserve_quantity","reserve_requirement","corridor_width"],
       "source_row_count":N,
       "original_lean_source_operator_executed":False,
       "original_source_to_python_functional_equivalence_proved":False,
       "original_lean_source_jacobian_certified":False,
       "branch_slack_equilibrium_root_proved":False,
       "state_dependent_euler_shear_included":True,
       "scalar_level_log_nonlin_transform_included":True,
       "root_only_constant_transform_used_offroot":False,
       "source_inputs_sha256":{
           str(p.relative_to(ROOT)):digest(p)
           for p in (SOURCE,ENGINE,P0_FILE,
                     HERE/"audit_source_firm_budget_euler_shear.py",
                     HERE/"audit_source_identity_row_candidates.py",
                     HERE/"audit_frozen_nine_scalar_source_shapes.py")}
    }
    OUT.parent.mkdir(parents=True,exist_ok=True)
    OUT.write_text(json.dumps(report,indent=2,sort_keys=True)+"\n",
                   encoding="utf-8")
    print(json.dumps({"status":report["status"],"branches":result},indent=2))
if __name__=="__main__":
    main()

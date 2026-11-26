#!/usr/bin/env python3
"""Off-root inverse and row-map Jacobians for 33 SOURCE-shaped candidates.

Proves no Lean SOURCE equality. Computes an explicit inverse of the
nonlinear row transformation at fixed positive chart coordinates, for
two branches and four date-zero policy shocks. The 33x33 matrices here
are derivatives with respect to RESIDUALS at fixed z, not total D_z.
"""
from __future__ import annotations
import hashlib,json,math
from pathlib import Path
import finite_irf as engine
from frozen_stationary_prefix_audit import frozen_stationary_seed
from audit_frozen_33_offroot_nonlinear_transform import (
    build_source_shaped,nonlinear_pullback,SOURCE_TO_PY,SOURCE_INDICES,SHEAR,N
)
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
SOURCE=ROOT/"lean/checkpoint/modules/Ventura26LiquidityAllocation/EconomicModel.lean"
PY=HERE/"finite_irf.py"
P0=HERE/"inputs/rational_preconditioners.json"
TRANS=HERE/"audit_frozen_33_offroot_nonlinear_transform.py"
OUT=HERE/"output/frozen_33_offroot_inverse_rowmap_candidate.json"

def check(v,msg):
    if not v:raise AssertionError(msg)

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def inverse_row_map(p,scale,coeff):
    """Recover SOURCE-shaped candidate residual vector from PY residuals."""
    rows=[0.]*N
    jp=SOURCE_TO_PY[21]
    for i,j in SOURCE_TO_PY.items():
        if i in SOURCE_INDICES:
            _,_,denom,sign=scale[i]
            check(denom>0 and sign in (-1,1),
                  "Nonpositive scalar scale or sign")
            rows[i]=sign*denom*math.expm1(p[j])
        elif i in SHEAR:
            rows[i]=p[j]+coeff[i]*math.expm1(p[jp])
        else:
            rows[i]=p[j]
    return rows

def row_jacobians(p,scale,coeff):
    """Construct exact residual-coordinate Jacobian and its inverse."""
    D=[[0.]*N for _ in range(N)]
    DI=[[0.]*N for _ in range(N)]
    for i,j in SOURCE_TO_PY.items():
        diagonal=(scale[i][3]*scale[i][2]*math.exp(p[j])
                  if i in SOURCE_INDICES else 1.)
        check(math.isfinite(diagonal) and diagonal!=0,
              "Noninvertible scalar residual row-map derivative")
        D[i][j]=diagonal
        DI[j][i]=1/diagonal
    pledge_py=SOURCE_TO_PY[21]
    pledge_diag=D[21][pledge_py]
    for i in SHEAR:
        j=SOURCE_TO_PY[i]
        cross=coeff[i]*math.exp(p[pledge_py])
        D[i][pledge_py]=cross
        DI[j][21]=-cross/pledge_diag
    return D,DI

def identity_error(A):
    return max(abs(A[i][j]-(1. if i==j else 0.))
               for i in range(N) for j in range(N))

def norm_inf(A):
    return max(sum(abs(x) for x in row) for row in A)

def main():
    seed=frozen_stationary_seed(engine.steady_case())
    inp=json.loads(P0.read_text(encoding="utf-8"))
    p0=[[float(x) for x in row] for row in inp["P0"]]
    check(len(p0)==16 and all(len(row)==6 for row in p0),"Wrong P0")
    probes=(
      [0.]*N,
      [4e-4*math.sin(1.39*(i+1)) for i in range(N)],
      [-7e-4*math.cos(.79*(i+1)) for i in range(N)]
    )
    shocks=(
      (0.,0.,0.,0.),(-1e-5,0.,0.,0.),
      (0.,-1e-5,0.,0.),(0.,0.,-1e-5,0.),(0.,0.,0.,-1e-5)
    )
    result={}
    for branch in ("binding","slack"):
        max_source_recovery=max_python_recovery=0.
        max_inverse_left=max_inverse_right=0.
        max_forward_norm=max_reverse_norm=0.
        evaluated=0
        for shock in shocks:
            for z in probes:
                src,scale,coeff,_,_=build_source_shaped(seed,p0,z,branch,shock)
                p=engine.prefix_residual(seed,p0,branch,shock,z)
                inverse_src=inverse_row_map(p,scale,coeff)
                original_src=[src[i] for i in range(N)]
                p_roundtrip=nonlinear_pullback(src,scale,coeff)
                max_source_recovery=max(max_source_recovery,
                    max(abs(inverse_src[i]-original_src[i]) for i in range(N)))
                max_python_recovery=max(max_python_recovery,
                    max(abs(p_roundtrip[i]-p[i]) for i in range(N)))
                D,DI=row_jacobians(p,scale,coeff)
                left=identity_error(engine.matmul(D,DI))
                right=identity_error(engine.matmul(DI,D))
                max_inverse_left=max(max_inverse_left,left)
                max_inverse_right=max(max_inverse_right,right)
                max_forward_norm=max(max_forward_norm,norm_inf(D))
                max_reverse_norm=max(max_reverse_norm,norm_inf(DI))
                evaluated+=1
        check(max(max_source_recovery,max_python_recovery)<2e-10,
              "Nonlinear residual inverse round-trip failed")
        check(max(max_inverse_left,max_inverse_right)<1e-12,
              "Residual-space derivative/inverse identity failed")
        result[branch]={
          "state_and_shock_points":evaluated,
          "max_abs_SOURCE_shaped_reconstruction_error":max_source_recovery,
          "max_abs_Python_reconstruction_error":max_python_recovery,
          "max_abs_rowmap_derivative_left_inverse_error":max_inverse_left,
          "max_abs_rowmap_derivative_right_inverse_error":max_inverse_right,
          "max_rowmap_derivative_infinity_norm":max_forward_norm,
          "max_inverse_rowmap_derivative_infinity_norm":max_reverse_norm
        }
    report={
      "status":"NUMERICAL_INVERTIBLE_SOURCE_SHAPED_RESIDUAL_ROW_MAP_ONLY",
      "same_frozen_base":True,
      "branches":result,
      "residual_dimension":N,
      "residual_row_map_only_not_total_Dz":True,
      "row_map_invertible_for_positive_scalar_denominators":True,
      "actual_Lean_SOURCE_residuals_executed":False,
      "SOURCE_Python_functional_identity_proved":False,
      "SOURCE_economic_Jacobian_inverse_certified":False,
      "SLACK_equilibrium_or_root_proved":False,
      "inputs_sha256":{str(p.relative_to(ROOT)):sha(p)
         for p in (SOURCE,PY,P0,TRANS)}
    }
    OUT.parent.mkdir(parents=True,exist_ok=True)
    OUT.write_text(json.dumps(report,indent=2,sort_keys=True)+"\n",
                   encoding="utf-8")
    print(json.dumps({"status":report["status"],"branches":result},indent=2))

if __name__=="__main__":
    main()

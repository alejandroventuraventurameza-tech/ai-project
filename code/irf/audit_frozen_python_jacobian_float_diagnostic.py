#!/usr/bin/env python3
"""Floating-point diagnostics for the FROZEN stationary Python 33x33 log Jacobian.

NOT a SOURCE derivative, interval proof, verified inverse, IFT certificate,
branch-S solution, or a proof of structural impulse responses.
"""
from __future__ import annotations
import hashlib
import json
import math
from pathlib import Path
from finite_irf import (
    PREFIX_ROW_NAMES, steady_case, prefix_residual, numerical_jacobian,
    solve_linear, max_abs, matmul,
)
from frozen_stationary_prefix_audit import frozen_stationary_seed

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
ENGINE=HERE/"finite_irf.py"
SOURCE=ROOT/"lean/checkpoint/modules/Ventura26LiquidityAllocation/EconomicModel.lean"
P0_FILE=HERE/"inputs/rational_preconditioners.json"
OUT=HERE/"output/frozen_python_33_jacobian_float_diagnostic.json"
N=33

def require(condition,message):
    if not condition: raise AssertionError(message)

def hsh(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def matrix_inverse(A):
    columns=[]
    pivot_min=float("inf")
    for i in range(N):
        e=[0.0]*N
        e[i]=1.0
        column,pivots=solve_linear(A,e)
        columns.append(column)
        pivot_min=min(pivot_min,*pivots)
    return [[columns[j][i] for j in range(N)] for i in range(N)],pivot_min

def matrix_error(A):
    return max(abs(A[i][j]-(1.0 if i==j else 0.0))
               for i in range(N) for j in range(N))

def norm_infty(A):
    return max(sum(abs(v) for v in row) for row in A)

def maximum_difference(A,B):
    return max(abs(A[i][j]-B[i][j]) for i in range(N) for j in range(N))

def main():
    seed=frozen_stationary_seed(steady_case())
    payload=json.loads(P0_FILE.read_text(encoding="utf-8"))
    P0=[[float(v) for v in row] for row in payload["P0"]]
    require(len(P0)==16 and all(len(row)==6 for row in P0),
            "Pinned P0 has wrong shape")
    require(len(PREFIX_ROW_NAMES)==N and len(set(PREFIX_ROW_NAMES))==N,
            "Prefix row labels changed")
    z=[0.0]*N
    f=lambda x: prefix_residual(seed,P0,"binding",(0.0,0.0,0.0,0.0),x)
    root=f(z)
    require(len(root)==N and all(math.isfinite(x) for x in root),
            "Nonfinite stationary 33-row residual")
    require(max_abs(root)<1e-9,"Frozen binding prefix base is no longer a numerical root")
    steps=(2e-5,2e-6,2e-7)
    matrices=[numerical_jacobian(f,z,step=h) for h in steps]
    for A in matrices:
        require(len(A)==N and all(len(row)==N for row in A),
                "Expected a square 33x33 Jacobian")
        require(all(math.isfinite(v) for row in A for v in row),
                "Nonfinite Python finite-difference Jacobian")
    A=matrices[1]
    inv, min_pivot=matrix_inverse(A)
    left=matrix_error(matmul(inv,A))
    right=matrix_error(matmul(A,inv))
    require(min_pivot>1e-15,"Numerical Jacobian has extremely small pivot")
    require(max(left,right)<1e-5,
            "Floating-point inverse products fail stated numerical tolerance")
    drift_up=maximum_difference(matrices[0],A)
    drift_down=maximum_difference(matrices[2],A)
    require(all(math.isfinite(v) for v in (drift_up,drift_down)),
            "Nonfinite finite-difference step sensitivity")
    result={
       "status":"FLOAT64_FROZEN_PYTHON_33X33_DIAGNOSTIC_NOT_SOURCE_CERTIFICATE",
       "operator":"finite_irf.prefix_residual",
       "branch":"binding",
       "base":"frozen_stationary_seed(steady_case())",
       "policy_intervention":[0.0]*4,
       "date_zero_innovations":seed.e0,
       "date_one_innovations":seed.e1,
       "log_coordinates":N,
       "finite_difference_step_sizes":list(steps),
       "root_max_abs_residual":max_abs(root),
       "gauss_jordan_min_abs_pivot":min_pivot,
       "max_abs_left_inverse_product_error":left,
       "max_abs_right_inverse_product_error":right,
       "float_inverse_infinity_norm":norm_infty(inv),
       "jacobian_infinity_norm":norm_infty(A),
       "max_abs_jacobian_step_drift_2e5_vs_2e6":drift_up,
       "max_abs_jacobian_step_drift_2e7_vs_2e6":drift_down,
       "source_jacobian_equality_proved":False,
       "source_functional_identity_proved":False,
       "source_frechet_derivative_computed_by_lean":False,
       "interval_inverse_enclosure_proved":False,
       "positive_log_chart_and_smoothness_proved_for_source":False,
       "infinite_horizon_equilibrium_or_growth_proved":False,
       "limitations":[
         "Finite differences have truncation and floating-point rounding error",
         "Two approximate inverse products do not constitute exact left/right inverses",
         "The 16x6 P0 terminal graph remains a Python local continuation candidate",
         "The SOURCE and Python systems have not been proved functionally equal",
         "A well-conditioned frozen binding root does not imply branch S existence"
       ],
       "input_sha256":{str(p.relative_to(ROOT)):hsh(p) for p in (SOURCE,ENGINE,P0_FILE)}
    }
    OUT.parent.mkdir(parents=True,exist_ok=True)
    OUT.write_text(json.dumps(result,indent=2,sort_keys=True)+"\n",encoding="utf-8")
    print(json.dumps({k:result[k] for k in (
      "status","root_max_abs_residual","gauss_jordan_min_abs_pivot",
      "max_abs_left_inverse_product_error","max_abs_right_inverse_product_error",
      "float_inverse_infinity_norm",
      "max_abs_jacobian_step_drift_2e5_vs_2e6",
      "max_abs_jacobian_step_drift_2e7_vs_2e6")},indent=2))

if __name__=="__main__":main()

#!/usr/bin/env python3
"""Full 33x33 SAME-ROOT candidate row-transform derivative audit.

Recombines independent SOURCE-SHAPED Python transcriptions of 8 firm, 16
remaining, and 9 level/log rows; it NEVER evaluates the real Lean SOURCE
operator. The root transform maps candidate SOURCE row derivatives to
Python row derivatives. It is a purely numerical, conditional bridge.
"""
from __future__ import annotations
import hashlib
import json
import math
from pathlib import Path
import finite_irf as engine
from frozen_stationary_prefix_audit import frozen_stationary_seed
from audit_source_firm_budget_euler_shear import (
    source_transcription, INDEX as FIRM_INDICES, SHEAR
)
from audit_source_identity_row_candidates import (
    transcribed_prefix_rows, ROWS as IDENTITY_ROWS
)
from audit_frozen_nine_scalar_source_shapes import (
    source_shape_pairs, SOURCE_INDICES as SCALAR_INDICES,
    SOURCE_TO_PY as SCALAR_TO_PY,
)

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
SOURCE=ROOT/"lean/checkpoint/modules/Ventura26LiquidityAllocation/EconomicModel.lean"
PYTHON=HERE/"finite_irf.py"
PRE=HERE/"inputs/rational_preconditioners.json"
REPORT=HERE/"output/frozen_33_root_candidate_matrix_bridge.json"
N=33

def require(condition,msg):
    if not condition:raise AssertionError(msg)

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def max_entry_error(A,B):
    return max(abs(A[i][j]-B[i][j]) for i in range(N) for j in range(N))

def max_identity_error(A):
    return max(abs(A[i][j]-(1.0 if i==j else 0.0))
               for i in range(N) for j in range(N))

def candidate_source_vector(base,p0,z):
    """Assemble actual independently TRANSCRIBED rows in SOURCE order."""
    branch="binding"
    firm,_,_,_=source_transcription(base,p0,z,branch)
    remaining=transcribed_prefix_rows(base,p0,z,(0.,0.,0.,0.))
    scalar=source_shape_pairs(base,p0,branch,z)
    rows={}
    rows.update(firm)
    rows.update({idx:remaining[n] for n,(idx,*_) in enumerate(IDENTITY_ROWS)})
    rows.update({idx:scalar[idx][0] for idx in SCALAR_INDICES})
    require(len(rows)==N and set(rows)==set(range(N)),
            "Transcribed SOURCE 33-row partition missing or overlapping")
    return [rows[i] for i in range(N)]

def main():
    s=engine.steady_case()
    base=frozen_stationary_seed(s)
    payload=json.loads(PRE.read_text(encoding="utf-8"))
    p0=[[float(v) for v in row] for row in payload["P0"]]
    require(len(p0)==16 and all(len(row)==6 for row in p0),
            "Wrong P0 terminal graph")
    z=[0.]*N
    pyfun=lambda x: engine.prefix_residual(
        base,p0,"binding",(0.,0.,0.,0.),x)
    srcfun=lambda x: candidate_source_vector(base,p0,x)
    pyroot=pyfun(z)
    srcroot=srcfun(z)
    require(max(abs(t) for t in pyroot)<1e-9
            and max(abs(t) for t in srcroot)<1e-9,
            "Different or nonzero root: root-only matrix transform invalid")
    scales=source_shape_pairs(base,p0,"binding",z)
    _,_,g,coeff=source_transcription(base,p0,z,"binding")
    require(abs(g)<1e-9,"Common pledge root not zero")
    source_to_python={}
    for i,(j,_) in FIRM_INDICES.items():source_to_python[i]=j
    for i,j,*_ in IDENTITY_ROWS:source_to_python[i]=j
    source_to_python.update(SCALAR_TO_PY)
    require(len(source_to_python)==N and
            sorted(source_to_python.values())==list(range(N)),
            "Not a SOURCE/Python row permutation")
    # T maps a SOURCE-shaped candidate differential in SOURCE index order
    # to a Python differential in Python row index order.
    T=[[0.]*N for _ in range(N)]
    inverse=[[0.]*N for _ in range(N)]
    for i,j in source_to_python.items():
        multiplier=(scales[i][3]/scales[i][2]) if i in SCALAR_INDICES else 1.
        require(math.isfinite(multiplier) and multiplier!=0,
                "Bad root diagonal scale")
        T[j][i]=multiplier
        inverse[i][j]=1/multiplier
    # At the COMMON pledge root, SOURCE Euler_i = Python Euler_i +
    # a_i * Python pledge, where a_i is the root shear coefficient.
    # Python pledge = (1/J) * SOURCE pledge, from the scalar row 21.
    pledge_source_row=21
    pledge_python_row=source_to_python[pledge_source_row]
    for i in SHEAR:
        j=source_to_python[i]
        a=coeff[i]
        require(math.isfinite(a),"Nonfinite root Euler coefficient")
        T[j][pledge_source_row]=-a*T[pledge_python_row][pledge_source_row]
        inverse[i][pledge_python_row]=a
    eye=engine.identity(N)
    left_error=max_identity_error(engine.matmul(T,inverse))
    right_error=max_identity_error(engine.matmul(inverse,T))
    require(max(left_error,right_error)<1e-12,
            "At-root candidate transform algebraic inverse failed")
    sensitivity={}
    for h in (2e-5,2e-6,2e-7):
        Jpy=engine.numerical_jacobian(pyfun,z,step=h)
        Jsrc=engine.numerical_jacobian(srcfun,z,step=h)
        mapped=engine.matmul(T,Jsrc)
        error=max_entry_error(mapped,Jpy)
        require(math.isfinite(error) and error<5e-6,
                "At-root 33-row SOURCE-shaped matrix derivative mismatch")
        sensitivity[str(h)]={
            "max_abs_33x33_candidate_root_Jacobian_transport_error":error,
            "entries_compared":N*N}
    report={
       "status":"NUMERICAL_33_SOURCE_SHAPED_ROOT_JACOBIAN_BRIDGE_CANDIDATE_ONLY",
       "base":"frozen_stationary_seed(steady_case())",
       "branch":"binding",
       "terminal_graph":"P0 rational_preconditioners.json",
       "root_source_candidate_max_abs_residual":max(abs(t) for t in srcroot),
       "root_python_max_abs_residual":max(abs(t) for t in pyroot),
       "source_to_python_row_permutation":[source_to_python[i] for i in range(N)],
       "root_scalar_multipliers":{
         str(i):scales[i][3]/scales[i][2] for i in sorted(SCALAR_INDICES)},
       "root_pledge_shear_coefficients":{
         str(i):coeff[i] for i in sorted(SHEAR)},
       "candidate_transform_numerical_left_inverse_error":left_error,
       "candidate_transform_numerical_right_inverse_error":right_error,
       "step_sensitivity":sensitivity,
       "original_SOURCE_Lean_operator_executed":False,
       "original_SOURCE_fderiv_equal_to_transcription_proved":False,
       "full_SOURCE_Python_functional_identity_proved":False,
       "original_SOURCE_Jacobian_invertibility_certified":False,
       "root_transform_not_valid_off_root_without_product_rule":True,
       "branch_S_root_or_equilibrium_proved":False,
       "inputs_sha256":{
         str(p.relative_to(ROOT)):digest(p)
         for p in (SOURCE,PYTHON,PRE,
                   HERE/"audit_source_firm_budget_euler_shear.py",
                   HERE/"audit_source_identity_row_candidates.py",
                   HERE/"audit_frozen_nine_scalar_source_shapes.py")}
    }
    REPORT.parent.mkdir(parents=True,exist_ok=True)
    REPORT.write_text(json.dumps(report,indent=2,sort_keys=True)+"\n",
                      encoding="utf-8")
    print(json.dumps({
      "status":report["status"],
      "candidate_transform_left_error":left_error,
      "candidate_transform_right_error":right_error,
      "step_sensitivity":sensitivity},indent=2))

if __name__=="__main__":
    main()

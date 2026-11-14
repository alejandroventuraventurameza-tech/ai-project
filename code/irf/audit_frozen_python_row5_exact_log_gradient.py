#!/usr/bin/env python3
"""Audit the original Python 34-map L collateral row's exact log gradient.

Inside the binding branch, the original finite_irf.prefix_residual
row 5 is log(x1[3]/(pledge_L * (1-delta)*u1[5]*u1[6]*x1[1])).
On the positive baseline log chart its real-arithmetic gradient is
exactly e3 - e1 - e28 - e29, with all other 29 coordinate derivatives
and the DIRECT policy derivative zero.

The corresponding SOURCE identity is proved separately in
SourceCanonicalPythonCollateralFourCoordinatesCandidate.lean.
This script validates the original Python AD and the literal Python
function at the frozen boundary and nearby points. It does not prove
cross-language semantics or directed-rounding float64 bounds.
"""
from __future__ import annotations

import hashlib
import json
import math
from pathlib import Path

import finite_irf as engine
from frozen_stationary_prefix_audit import frozen_stationary_seed
from audit_frozen_python_34_forward_ad import auto_jacobian

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
FRONTIER=HERE/"output/frozen_python_augmented34_boundary_search.json"
AD=HERE/"output/frozen_python_augmented34_forward_ad.json"
P0=HERE/"inputs/rational_preconditioners.json"
SOURCE=ROOT/"lean/checkpoint/modules/Ventura26LiquidityAllocation/EconomicModel.lean"
LEAN=ROOT/"lean/candidates/Ventura26LiquidityAllocation/SourceCanonicalPythonCollateralFourCoordinatesCandidate.lean"
OUT=HERE/"output/frozen_python_row5_exact_log_gradient.json"
N=33


def require(ok,msg):
    if not ok: raise AssertionError(msg)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def expected_gradient():
    out=[0.0]*34
    for j,value in {1:-1.0,3:1.0,28:-1.0,29:-1.0}.items():
        out[j]=value
    return out


def main():
    frontier=json.loads(FRONTIER.read_text(encoding="utf-8"))
    ad=json.loads(AD.read_text(encoding="utf-8"))
    require(frontier["status"] ==
            "NUMERICAL_PYTHON_34_BOUNDARY_CANDIDATE_FOUND_NOT_SOURCE_PROOF"
            and ad["status"] ==
            "FLOAT64_FORWARD_AD_PYTHON_34_JACOBIAN_NOT_SOURCE",
            "Wrong frontier or AD object")
    require(ad["parent_boundary_report_sha256"]==sha(FRONTIER)
            and frontier["source_sha256"]==sha(SOURCE),
            "Boundary/AD/SOURCE hashes mismatch")
    candidate=frontier["numerical_candidate"]
    z=list(candidate["baseline_33_unknowns"])
    h=float(candidate["innovation_h"])
    require(len(z)==N,"Incorrect 33-dimensional log chart")
    raw=json.loads(P0.read_text(encoding="utf-8"))
    matrix=[[float(v) for v in row] for row in raw["P0"]]
    require(len(matrix)==16 and all(len(row)==6 for row in matrix),
            "Original finite P0 not 16x6")
    seed=frozen_stationary_seed(engine.steady_case())
    s=seed.s
    require(min(seed.X1[1],seed.X1[3],seed.U1[5],seed.U1[6],
                s.pledge[1],s.ad)>0, "Nonpositive collateral chart")
    frozen=tuple(seed.X0)

    reference=math.log(
        seed.X1[3]/(
            (s.pledge[1]*s.ad*seed.U1[5]*seed.U1[6])*seed.X1[1]
        )
    )
    def analytical_value(x):
        return reference+x[3]-x[1]-x[28]-x[29]
    def original_row5(x,innovation):
        return engine.prefix_residual(
            seed,matrix,"binding",(innovation,0.0,0.0,0.0),x
        )[5]

    probes=[(list(z),h)]
    radius=8.0e-5
    for index in (1,3,28,29,N):
        for sign in (-1.0,1.0):
            zz=list(z)
            hh=h
            if index==N: hh+=sign*radius
            else: zz[index]+=sign*radius
            probes.append((zz,hh))
    probes.extend([
        ([x+radius*math.sin((i+1)*0.37) for i,x in enumerate(z)],
         h+0.75*radius),
        ([x-radius*math.cos((i+1)*0.53) for i,x in enumerate(z)],
         h-0.75*radius),
    ])

    gradient=expected_gradient()
    max_value_error=0.0
    max_gradient_error=0.0
    max_independence_h_error=0.0
    for zz,hh in probes:
        original=original_row5(zz,hh)
        predicted=analytical_value(zz)
        max_value_error=max(max_value_error,abs(original-predicted))
        actual_row=auto_jacobian(seed,matrix,zz,hh)[5]
        max_gradient_error=max(max_gradient_error,
                               max(abs(a-b) for a,b in zip(actual_row.grad,gradient)))
        max_independence_h_error=max(
            max_independence_h_error,
            abs(original-original_row5(zz,hh+radius))
        )
    require(tuple(seed.X0)==frozen,"Inherited nominal state mutated")
    require(len(ad["forward_ad_jacobian_34"])==34,
            "Original forward AD report has wrong number of rows")
    root_AD=ad["forward_ad_jacobian_34"][5]
    require(max(abs(x-y) for x,y in zip(root_AD,gradient))<1e-12,
            "Original Python row5 forward AD gradient differs from symbolic support")
    require(max_value_error<1e-12
            and max_gradient_error<1e-12
            and max_independence_h_error<1e-12,
            "Original Python row5 disagrees with exact four-coordinate formula")

    result={
        "status":"NUMERICAL_ORIGINAL_PYTHON_ROW5_EXACT_LOG_GRADIENT_NOT_SOURCE",
        "source_model_sha256":sha(SOURCE),
        "source_lean_row5_candidate_sha256":sha(LEAN),
        "original_python_engine_sha256":sha(HERE/"finite_irf.py"),
        "p0_source_sha256":sha(P0),
        "parent_boundary_sha256":sha(FRONTIER),
        "parent_forward_ad_sha256":sha(AD),
        "number_of_positive_chart_probes":len(probes),
        "root_h":h,
        "tested_local_radius":radius,
        "row5_nonzero_log_coordinate_indices":[1,3,28,29],
        "row5_exact_real_log_coordinate_gradient":{
            "1":-1,"3":1,"28":-1,"29":-1},
        "all_other_29_log_derivatives_zero_in_analytical_formula":True,
        "direct_policy_h_derivative_zero_in_analytical_formula":True,
        "original_python_max_value_error":max_value_error,
        "original_python_max_forward_AD_gradient_error":max_gradient_error,
        "original_python_max_direct_h_independence_error":max_independence_h_error,
        "genuine_SOURCE_row5_exact_formula_lean_kernel_verified_here":False,
        "python_float64_directed_roundoff_enclosed":False,
        "actual_source_34_equilibrium_root_proved":False,
    }
    OUT.parent.mkdir(parents=True,exist_ok=True)
    OUT.write_text(json.dumps(result,indent=2,sort_keys=True)+"\n",encoding="utf-8")
    print(json.dumps({k:result[k] for k in (
        "status","number_of_positive_chart_probes",
        "original_python_max_value_error",
        "original_python_max_forward_AD_gradient_error",
        "original_python_max_direct_h_independence_error",
    )},indent=2))


if __name__=="__main__":
    main()

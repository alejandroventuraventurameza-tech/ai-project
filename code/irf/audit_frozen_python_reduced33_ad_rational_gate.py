#!/usr/bin/env python3
"""Conditional exact-rational Jacobian gate for the reduced Python 33-map.

The 34th source-shaped funding dual has been eliminated analytically
from the Python 34 boundary at sigmaE=1. At its reduced float64 root,
forward AD of the ORIGINAL Python 34-vector is evaluated, and the chain
rule constructs the derivative of the reduced 33-vector.

The resulting float AD matrix is rounded to exact rational entries
and an approximate inverse is independently rounded to rationals.
All subsequent Neumann and Banach thresholds use exact Fraction math.

These results certify a rationalized PYTHON MATRIX ONLY. The actual
SOURCE reduced 33-map and its box derivatives are not enclosed here.
"""
from __future__ import annotations
import hashlib
import json
import math
from fractions import Fraction
from pathlib import Path

from audit_frozen_python_34_forward_ad import auto_jacobian
from audit_frozen_python_34_rational_preconditioner import (
    approximate_inverse, norm_inf, q, require, witness,
)
from audit_frozen_python_34_ad_rational_gate import conditional_root_contraction_gate
from frozen_stationary_prefix_audit import frozen_stationary_seed
from finite_irf import numerical_jacobian, prefix_residual, steady_case

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
INPUT=HERE/"output/frozen_python_reduced33_dual_eliminated_search.json"
PRE=HERE/"inputs/rational_preconditioners.json"
SOURCE=ROOT/"lean/checkpoint/modules/Ventura26LiquidityAllocation/EconomicModel.lean"
PYTHON=HERE/"finite_irf.py"
OUT=HERE/"output/frozen_python_reduced33_ad_rational_gate.json"
N=33
ELIM=15
FREE=tuple(i for i in range(33) if i!=ELIM)
CHAIN={8:-1,24:1,28:1}

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def lift_from_reduced(x, rate, beta):
    z=[0.0]*33
    for i,v in zip(FREE,x[:32]):
        z[i]=v
    z[ELIM]=-math.log(rate)-math.log(beta)-z[8]+z[24]+z[28]
    return z,x[32]

def main():
    require(INPUT.is_file() and PRE.is_file(),
            "Reduced Python 33-root and preconditioner data missing")
    data=json.loads(INPUT.read_text(encoding="utf-8"))
    require(data["status"]=="NUMERICAL_PYTHON_REDUCED33_DUAL_ELIMINATION_CANDIDATE"
            and data["all_regime_checks_pass"]
            and data["final_34_equation_max_float_residual"]<1e-10,
            "Reduced Python root/regime diagnostic not accepted")
    require(data["source_34_equations_formally_validated"] is False,
            "Incorrect assertion that SOURCE economics already certified")
    s=steady_case()
    require(s.sigmaE==1.0 and s.be>0 and s.rate>0,
            "Eliminated scalar assumptions not satisfied")
    seed=frozen_stationary_seed(s)
    inherited=tuple(seed.X0)
    prep=json.loads(PRE.read_text(encoding="utf-8"))
    p0=[[float(t) for t in row] for row in prep["P0"]]
    x=data["final_33_free_coordinates_plus_h"]
    require(len(x)==N and all(math.isfinite(v) for v in x),
            "Expected finite 32 log coordinates plus policy h")
    z,h=lift_from_reduced(x,s.rate,s.be)
    require(all(abs(z[i]-data["final_log_coordinates"][i])<3e-14
                for i in range(33))
            and h==data["final_innovation_h"],
            "Canonical log-rate elimination differs from root candidate")
    objects=auto_jacobian(seed,p0,z,h)
    require(len(objects)==34,"Original augmented AD must have 34 outputs")
    jfull=[list(o.grad) for o in objects]
    require(all(len(row)==34 for row in jfull),
            "Full original AD Jacobian shape drift")
    Jred=[
        [jfull[i][k]+CHAIN.get(k,0)*jfull[i][ELIM]
            for k in FREE] + [jfull[i][33]]
        for i in range(N)
    ]
    require(len(Jred)==N and all(len(row)==N for row in Jred),
            "Reduced Jacobian not 33x33")
    # The 34th row must vanish identically along the eliminated
    # 33-variable surface. The float64 AD check is only a diagnostic.
    eliminated_gradient=[
        jfull[33][k]+CHAIN.get(k,0)*jfull[33][ELIM] for k in FREE
    ] + [jfull[33][33]]
    eliminated_row_ad_error=max(abs(v) for v in eliminated_gradient)
    require(eliminated_row_ad_error<1e-11,
            "Dual does not differentiate to zero along eliminated surface")
    def reduced_residual(y):
        zz,hh=lift_from_reduced(y,s.rate,s.be)
        return prefix_residual(seed,p0,"binding",(hh,0.,0.,0.),zz)
    fd=numerical_jacobian(reduced_residual,x,step=2e-6)
    difference=max(abs(Jred[i][k]-fd[i][k])
                   for i in range(N) for k in range(N))
    require(difference<2e-5,
            "Original forward AD chain-rule derivative differs from FD")
    Cfloat,min_pivot=approximate_inverse(Jred)
    M,C,defect,cnorm,K=witness(Jred,Cfloat)
    entry_eps=(1-defect)/(4*N*cnorm)
    require(entry_eps>0 and defect+N*cnorm*entry_eps<1,
            "Rational reduced Jacobian uniform tolerance failed")
    radii=(Fraction(1,10**6),Fraction(1,10**5),Fraction(1,10**4))
    gates=[
        conditional_root_contraction_gate(defect,cnorm,N,entry_eps,r)
        for r in radii
    ]
    # The exact-rational centre is built from rounded AD entries only.
    # No true SOURCE Jacobian or residual enclosure has been supplied.
    require(tuple(seed.X0)==inherited,
            "Inherited state mutated during reduced AD")
    report={
        "status":"EXACT_RATIONAL_ROUNDED_PYTHON_REDUCED33_JACOBIAN_GATE_ONLY",
        "parent_python_reduced_root_sha256":sha(INPUT),
        "parent_python_engine_sha256":sha(PYTHON),
        "parent_lean_source_sha256":sha(SOURCE),
        "preconditioner_sha256":sha(PRE),
        "free_log_indices":list(FREE),
        "eliminated_log_index":ELIM,
        "analytic_elimination_derivative":{str(i):v for i,v in CHAIN.items()},
        "eliminated_row_forward_ad_chain_error_float":eliminated_row_ad_error,
        "reduced_forward_ad_vs_finite_difference_max_error":difference,
        "rational_reference_neumann_defect":str(defect),
        "rational_reference_neumann_defect_float":float(defect),
        "rational_preconditioner_norm":str(cnorm),
        "rational_inverse_norm_upper":str(K),
        "rounded_33_matrix_invertible_exact":True,
        "conditional_per_entry_33_jacobian_tolerance":str(entry_eps),
        "conditional_per_entry_33_jacobian_tolerance_float":float(entry_eps),
        "conditional_root_boxes":[{
            "radius_exact":str(g["box_radius"]),
            "radius_float":float(g["box_radius"]),
            "uniform_contraction_upper_exact":
                str(g["uniform_contraction_upper"]),
            "uniform_contraction_upper_float":
                float(g["uniform_contraction_upper"]),
            "true_reduced_SOURCE_center_residual_limit_strict":
                str(g["maximum_source_residual_sup_norm_strict"]),
            "residual_limit_float":
                float(g["maximum_source_residual_sup_norm_strict"]),
            "true_SOURCE_uniform_box_jacobian_verified":False,
            "true_SOURCE_center_residual_verified":False,
        } for g in gates],
        "python_float64_reduced_root_max_residual":
            data["final_reduced33_max_residual"],
        "finite_difference_vs_ad_is_not_an_interval_proof":True,
        "SOURCE_to_Python_33_semantic_identity_verified":False,
        "true_reduced_SOURCE_jacobian_box_enclosed":False,
        "true_reduced_SOURCE_root_certified":False,
        "full_dynamic_equilibrium_certified":False,
    }
    OUT.parent.mkdir(parents=True,exist_ok=True)
    OUT.write_text(json.dumps(report,indent=2,sort_keys=True)+"\n",
                   encoding="utf-8")
    print(json.dumps({k:report[k] for k in (
        "status","rational_reference_neumann_defect_float",
        "conditional_per_entry_33_jacobian_tolerance_float",
        "reduced_forward_ad_vs_finite_difference_max_error",
        "eliminated_row_forward_ad_chain_error_float",
        "python_float64_reduced_root_max_residual",
        "true_reduced_SOURCE_root_certified")},indent=2))
    print(json.dumps({"conditional_reduced33_root_boxes":[
        {"radius":r["radius_float"],
         "residual_budget":r["residual_limit_float"],
         "contraction":r["uniform_contraction_upper_float"]}
        for r in report["conditional_root_boxes"]]},indent=2))

if __name__=="__main__":
    main()

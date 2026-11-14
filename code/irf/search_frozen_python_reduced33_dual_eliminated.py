#!/usr/bin/env python3
"""Explore a 33-unknown reduction of the Python 34-boundary example.

At sigmaE=1 and the frozen stationary source-shaped L dual, coordinate
z15 (log loan-rate) is eliminated analytically as a function of
z8,z24,z28. The remaining 32 log coordinates and policy innovation h
are found by a 33-equation float64 Newton solve. This is only a Python
NUMERICAL cross-check, not a validated SOURCE root or equilibrium.
"""
from __future__ import annotations
import hashlib
import json
import math
from pathlib import Path

from finite_irf import max_abs, newton, prefix_residual, steady_case
from frozen_stationary_prefix_audit import frozen_stationary_seed
from audit_frozen_python_augmented34_basepoint import exact_shape_dual
from frozen_four_tool_impact_audit import unpack_solution
from audit_frozen_frontier_source_dual_interval import require

HERE=Path(__file__).resolve().parent
FRONTIER=HERE/"output/frozen_python_augmented34_boundary_search.json"
PRE=HERE/"inputs/rational_preconditioners.json"
OUT=HERE/"output/frozen_python_reduced33_dual_eliminated_search.json"

def main():
    data=json.loads(FRONTIER.read_text(encoding="utf-8"))
    require(data["status"]==
            "NUMERICAL_PYTHON_34_BOUNDARY_CANDIDATE_FOUND_NOT_SOURCE_PROOF",
            "Frozen numerical boundary not found")
    s=steady_case()
    require(s.sigmaE==1.0 and s.be>0 and s.rate>0,
            "Stationary scalar elimination no longer applicable")
    seed=frozen_stationary_seed(s)
    original_inherited=tuple(seed.X0)
    pre=json.loads(PRE.read_text(encoding="utf-8"))
    p0=[[float(t) for t in row] for row in pre["P0"]]
    oldz=data["numerical_candidate"]["baseline_33_unknowns"]
    oldh=data["numerical_candidate"]["innovation_h"]
    freeidx=[i for i in range(33) if i!=15]
    assert len(freeidx)==32
    log_const=-(math.log(s.rate)+math.log(s.be))
    def lift(y):
        require(len(y)==33,"Expected 32 free logs and one policy innovation")
        z=[0.0]*33
        for i,v in zip(freeidx,y[:32]):
            z[i]=v
        z[15]=log_const-z[8]+z[24]+z[28]
        return z,y[32]
    def resid(y):
        z,h=lift(y)
        return prefix_residual(seed,p0,"binding",(h,0.0,0.0,0.0),z)
    start=[oldz[i] for i in freeidx]+[oldh]
    before=max_abs(resid(start))
    require(math.isfinite(before) and before<1e-6,
            "Initial reduced 33 equation seed too far from solution")
    solve_error=None
    final=start
    history=[before]
    try:
        final,history,_=newton(resid,start,tolerance=2e-12)
    except (ArithmeticError,AssertionError,OverflowError,ValueError,
            ZeroDivisionError) as exc:
        solve_error={"exception":type(exc).__name__,"message":str(exc)}
    z,h=lift(final)
    residual33=max_abs(resid(final))
    dual=exact_shape_dual(s,seed,z)[0]
    require(tuple(seed.X0)==original_inherited,
            "Frozen date-zero inherited capital/bank state mutated")
    require(math.isfinite(residual33) and math.isfinite(dual),
            "Reduced 33 solve produced a non-finite value")
    regime={}
    if solve_error is None:
        _,_,_,metrics=unpack_solution(s,seed,z,(h,0.0,0.0,0.0))
        regime={
            "H_dual_positive":metrics["collateral_dual_H"]>0,
            "L_dual_near_zero":abs(metrics["collateral_dual_L"])<1e-9,
            "H_face_binding":abs(metrics["collateral_slack_H"])<1e-8,
            "L_face_binding":abs(metrics["collateral_slack_L"])<1e-8,
            "bank_deposit_cap_slack":metrics["deposit_cap_slack"]>0,
            "bank_loan_cap_slack":metrics["loan_cap_slack"]>0,
        }
    good=(solve_error is None and residual33<1e-10
          and abs(dual)<1e-12 and all(regime.values()))
    report={
        "status":("NUMERICAL_PYTHON_REDUCED33_DUAL_ELIMINATION_CANDIDATE"
                  if good else
                  "NO_COMPLETE_NUMERICAL_PYTHON_REDUCED33_CANDIDATE"),
        "source_34_equations_formally_validated":False,
        "remaining_unknowns":"32 log economic coordinates + h",
        "last_SOURCE_analytic_dual_equation_eliminated_exactly":True,
        "floating_elimination_coordinates":list(freeidx),
        "initial_reduced33_max_residual":before,
        "residual_history":history,
        "final_reduced33_max_residual":residual33,
        "final_dual_L_float":dual,
        "final_34_equation_max_float_residual":max(residual33,abs(dual)),
        "final_innovation_h":h,
        "initial_innovation_h":oldh,
        "final_log_loan_rate_z15":z[15],
        "original_log_loan_rate_z15":oldz[15],
        "final_log_coordinates":z,
        "final_33_free_coordinates_plus_h":final,
        "regime_checks":regime,
        "all_regime_checks_pass":all(regime.values()) if regime else False,
        "solve_error":solve_error,
        "frozen_original_inherited_state":list(original_inherited),
        "python_only_float64":True,
        "true_SOURCE_33_equation_root_certified":False,
        "validated_SOURCE_derivative_box":False,
        "true_SOURCE_34_equation_root_certified":False,
        "full_dynamic_competitive_equilibrium_certified":False,
    }
    OUT.parent.mkdir(parents=True,exist_ok=True)
    OUT.write_text(json.dumps(report,indent=2,sort_keys=True)+"\n",
                   encoding="utf-8")
    print(json.dumps({k:report[k] for k in (
        "status","initial_reduced33_max_residual",
        "final_reduced33_max_residual","final_dual_L_float",
        "final_34_equation_max_float_residual",
        "initial_innovation_h","final_innovation_h",
        "all_regime_checks_pass","solve_error",
        "true_SOURCE_34_equation_root_certified")},indent=2))

if __name__=="__main__":
    main()

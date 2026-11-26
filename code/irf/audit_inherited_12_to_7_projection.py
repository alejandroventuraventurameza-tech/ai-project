#!/usr/bin/env python3
"""Conditional 12-to-7 SOURCE inherited-state chart, with explicit fibers.

Numerical reconstruction only: the source inheritedState(G) uses symbolic
G and functions in Lean, not a computed Lean value exposed to Python.
Never interpret this as a kernel proof of SOURCE/Python equality.
"""
from __future__ import annotations
import hashlib
import json
import math
import re
from pathlib import Path
from finite_irf import steady_case
from frozen_stationary_prefix_audit import frozen_stationary_seed

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
LEAN=ROOT/"lean/candidates/Ventura26LiquidityAllocation/StationaryInheritedStateCandidate.lean"
PY=HERE/"finite_irf.py"
OUT=HERE/"output/source_predecessor_12_to_7_conditional_chart.json"
NAMES=("capital_H","capital_L","firmFace_H","firmFace_L","bankFace",
       "reserveRateLag","reservesPreLag")
OTHER=("householdDeposits","householdBonds","depositRateLag",
       "governmentBondRateLag","reservesLag","facilityRateLag","facilityBorrowingLag")

def require(ok,msg):
    if not ok:raise AssertionError(msg)
def close(x,y,tol=3e-12):
    return math.isclose(x,y,rel_tol=tol,abs_tol=tol)
def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def conditional_source_state(s,G):
    # The formulas correspond to literal Lean inheritedState fields,
    # CONDITIONAL on identifying SOURCE primitives with s.
    reserve_pre=s.M
    W=(s.rd/s.rr-s.rho)*s.D/30.0
    require(W>0,"SOURCE facility candidate is not positive")
    return {
      "capital_H":s.k[0], "capital_L":s.k[1],
      "firmFace_H":s.F[0],"firmFace_L":s.F[1],
      "bankFace":s.E,
      "householdDeposits":s.D,
      "householdBonds":G-reserve_pre,
      "depositRateLag":s.rd,
      "governmentBondRateLag":s.rd,
      "reserveRateLag":s.rr,
      "reservesPreLag":reserve_pre,
      "reservesLag":reserve_pre+W,
      "facilityRateLag":s.rr+1/50,
      "facilityBorrowingLag":W,
    }

def projection(state):
    return [state[k] for k in NAMES]

def main():
    lean=LEAN.read_text(encoding="utf-8")
    py=PY.read_text(encoding="utf-8")
    required=(
      "householdBonds := G - reservesPre",
      "reservesPreLag := reservesPre",
      "reservesLag := reservesPost",
      "facilityBorrowingLag := facilityBorrowing",
      "facilityRateLag := facilityRate",
      "(ProposedStationaryBank.depositRate / ProposedStationaryBank.reserveRate -",
    )
    for anchor in required:
        require(anchor in lean,"SOURCE inherited semantics changed: "+anchor)
    require("s.base = [*s.k, s.J, s.E, s.rr, s.M" in py,
            "Python stationary benchmark coordinate names drifted")
    s=steady_case()
    frozen=frozen_stationary_seed(s)
    require(len(frozen.X0)==7,"Python predecessor dimension changed")
    # G remains a free financial/fiscal parameter; changing it must not
    # alter the seven entries read by Python.
    Gs=(s.M,s.M+1,s.M+2)
    states=[conditional_source_state(s,G) for G in Gs]
    maximum=0.
    for state,G in zip(states,Gs):
        require(set(state)==set(NAMES)|set(OTHER),
                "SOURCE 12-field reconstruction mismatch")
        maximum=max(maximum,max(abs(x-y) for x,y in zip(projection(state),frozen.X0)))
        require(all(close(x,y) for x,y in zip(projection(state),frozen.X0)),
                "Seven-coordinate conditional SOURCE/Python projection mismatch")
        require(close(state["householdBonds"]+state["reservesPreLag"],G),
                "Fiscal identity G=bonds+reservesPre fails")
        require(close(state["reservesLag"],
                      state["reservesPreLag"]+state["facilityBorrowingLag"]),
                "SOURCE pre/post reserves distinction lost")
        require(state["householdBonds"]>=0 and state["facilityBorrowingLag"]>0,
                "Outside financial-domain candidate")
    require(all(close(x,y) for x,y in
                zip(projection(states[0]),projection(states[-1]))),
            "G changed the seven inherited prefix coordinates")
    require(not close(states[0]["householdBonds"],
                      states[-1]["householdBonds"]),
            "The seven coordinates failed to discard the G fiber")
    missing=list(OTHER)
    report={
      "status":"CONDITIONAL_SOURCE_INHERITED_PROJECTION_7_OF_12_MATCHES_FROZEN_PYTHON",
      "projection_names":list(NAMES),
      "non_projected_source_fields":missing,
      "source_state_struct_field_count":12,
      "source_field_values_reconstructed":14,
      "source_inherited_seven_dim_projection_max_abs_error":maximum,
      "tested_G_values":Gs,
      "symbolic_G_fiber_exists":True,
      "bank_reserves_post_minus_pre":states[0]["facilityBorrowingLag"],
      "source_inherited_state_executed_in_lean":False,
      "source_python_primitives_equality_proved":False,
      "economic_33_residual_operator_equality_proved":False,
      "full_state_bijection_proved":False,
      "limitations":[
       "The source record includes functions FirmType->R counted as one structural field each",
       "The seven-vector loses deposits, bonds, price lags and pre/post reserves information",
       "The result assumes primitive-to-Python matching of s and thus is conditional",
       "Terminal tail and fiscal closure remain outside the seven-dimensional projection"
      ],
      "sha256":{str(p.relative_to(ROOT)):sha(p) for p in (LEAN,PY)},
    }
    OUT.parent.mkdir(parents=True,exist_ok=True)
    OUT.write_text(json.dumps(report,indent=2,sort_keys=True)+"\n",encoding="utf-8")
    print(json.dumps({"status":report["status"],"max_error":maximum,
                      "projection_dimension":7,"lost_fields":len(missing),
                      "report":str(OUT)},indent=2))

if __name__=="__main__":main()

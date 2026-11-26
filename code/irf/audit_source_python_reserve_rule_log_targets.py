#!/usr/bin/env python3
"""Compare original Python reserve-rule rows to SOURCE-shaped log targets.

In SOURCE localReducedRemainingResidual rows 6,7:
  log R_current - [rhoR log R_lag + (1-rhoR)(log R_bar
      +phiPi log pi +phiY log(Y/Y_bar)) + vR]
  log M_current - [rhoM log M_lag
      +(1-rhoM) log M_bar + vM]
Original Python remaining_residuals uses log(next_state[5]/aux['rr'])
and log(next_state[6]/aux['money']).

This audits the ORIGINAL Python auxiliary and prefix code via AST and
compares both forms for fixed original Python data off root. It never
executes Lean's SOURCE real model and does not prove SOURCE/Python
equality of the economic inputs or an actual SOURCE root.
"""
from __future__ import annotations

import ast
import hashlib
import json
import math
from pathlib import Path

import finite_irf as engine
from frozen_stationary_prefix_audit import frozen_stationary_seed

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
SOURCE = ROOT / "lean/checkpoint/modules/Ventura26LiquidityAllocation/EconomicModel.lean"
PROOF = ROOT / "lean/candidates/Ventura26LiquidityAllocation/SourceReserveRulesLogRatioBridgeCandidate.lean"
PYTHON = HERE / "finite_irf.py"
P0FILE = HERE / "inputs/rational_preconditioners.json"
OUT = HERE / "output/source_python_reserve_rule_log_targets.json"

def require(check: bool, message: str):
    if not check:
        raise AssertionError(message)

def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def ast_guard():
    tree = ast.parse(PYTHON.read_text(encoding="utf-8"))
    def get(name):
        matches = [x for x in tree.body if isinstance(x, ast.FunctionDef)
                   and x.name == name]
        require(len(matches) == 1, f"Original Python function {name} not unique")
        return matches[0]
    fn = get("auxiliary")
    target_rr = next((x.value for x in fn.body if isinstance(x, ast.Assign)
                      and any(isinstance(t, ast.Name) and t.id == "rr"
                              for t in x.targets)), None)
    target_m = next((x.value for x in fn.body if isinstance(x, ast.Assign)
                     and any(isinstance(t, ast.Name) and t.id == "money"
                             for t in x.targets)), None)
    require(target_rr is not None and target_m is not None,
            "Original Python policy target assignments missing")
    rr = ast.unparse(target_rr)
    money = ast.unparse(target_m)
    for anchor in ("s.rr * math.exp", "math.log(state[5] / s.rr)",
                   "math.log(inflation)", "math.log(output / s.Y)",
                   "innovations[0]"):
        require(anchor in rr, f"Original rate target changed: {anchor}")
    for anchor in ("s.M * math.exp", "math.log(state[6] / s.M)",
                   "innovations[1]"):
        require(anchor in money, f"Original quantity target changed: {anchor}")
    remaining = get("remaining_residuals")
    returns = [x for x in ast.walk(remaining) if isinstance(x, ast.Return)]
    require(len(returns) == 1 and isinstance(returns[0].value, ast.List),
            "Original Python 11 other rows changed")
    rows = returns[0].value.elts
    require(len(rows) == 11, "Original Python remaining row count changed")
    require(ast.unparse(rows[6]) == "math.log(next_state[5] / aux['rr'])" and
            ast.unparse(rows[7]) == "math.log(next_state[6] / aux['money'])",
            "Python reserve-rule residual formulas changed")
    prefix = get("prefix_residual")
    code = ast.unparse(prefix)
    require("e0 = [base.e0[0] + v_rate, base.e0[1] + v_quantity]" in code,
            "Original Python date-zero policy innovation channel changed")
    return {"rr":rr, "money":money, "remaining_rows":[ast.unparse(rows[i]) for i in (6,7)]}

def compare(s, state, controls, next_state, next_controls, innov):
    aux = engine.auxiliary(s, state, controls, next_state[:2], innov)
    aux_next = engine.auxiliary(s,next_state,next_controls,next_state[:2],[0.,0.])
    r = engine.remaining_residuals(s,state,controls,next_state,next_controls,aux,aux_next)
    pi=controls[5]
    require(all(math.isfinite(q) and q>0 for q in (
        next_state[5],next_state[6],state[5],state[6],
        s.rr,s.M,pi,aux["Y"],s.Y,aux["rr"],aux["money"])),
        "Reserve-policy logarithmic positivity domain changed")
    logrr = (.5*math.log(state[5])+
             .5*(math.log(s.rr)+1.5*math.log(pi)+.125*math.log(aux["Y"]/s.Y))+
             innov[0])
    logm = (.5*math.log(state[6])+.5*math.log(s.M)+innov[1])
    source_shaped=(math.log(next_state[5])-logrr,
                   math.log(next_state[6])-logm)
    differences=[abs(r[6+i]-source_shaped[i]) for i in range(2)]
    require(max(differences)<5e-13,
            f"Original Python reserve-rule normalizations drift: {max(differences)}")
    return differences

def main():
    files=(SOURCE,PROOF,PYTHON,P0FILE)
    require(all(p.is_file() for p in files),"SOURCE or Python inputs missing")
    s=SOURCE.read_text(encoding="utf-8")
    t=PROOF.read_text(encoding="utf-8")
    for anchor in ("| 6 => Real.log d.currentReserveRate -",
                   "| 7 => Real.log d.currentReservesPre -"):
        require(anchor in s, "Actual SOURCE policy row changed: "+anchor)
    for name in ("sourceReserveRateRule_actual_logRatio",
                 "sourceReserveQuantityRule_actual_logRatio"):
        require("theorem "+name in t, "Companion Lean candidate missing: "+name)
    expressions=ast_guard()
    p0=json.loads(P0FILE.read_text(encoding="utf-8"))["P0"]
    p0=[[float(x) for x in row] for row in p0]
    require(len(p0)==16 and all(len(row)==6 for row in p0),
            "Frozen P0 shape changed")
    steady=engine.steady_case()
    require(steady.rr>0 and steady.M>0, "Stationary policy reference changed")
    base=frozen_stationary_seed(steady)
    require(base.e0==[0.,0.] and base.e1==[0.,0.],
            "Frozen baseline innovations changed")
    maxerror=0.
    records=0
    for branch in ("slack","binding"):
        for shocks in ((0.,0.),(-1e-5,0.),(0.,2e-5),(-1e-5,2e-5)):
            for amplitude in (0.,1e-4,-1e-4):
                z=[amplitude*math.sin(.29*(i+1)) for i in range(33)]
                x1=[base.X1[i]*math.exp(z[i]) for i in range(7)]
                u0=[base.U0[i]*math.exp(z[7+i]) for i in range(10)]
                x2c=[base.X2[i]*math.exp(z[17+i]) for i in range(6)]
                x2=engine.expand_compact_state(steady,x2c)
                u1=[base.U1[i]*math.exp(z[23+i]) for i in range(10)]
                pt=engine.matvec(p0,z[17:23])
                u2=[steady.base[6+i]*math.exp(pt[6+i]) for i in range(10)]
                for dt,data in enumerate((
                    (base.X0,u0,x1,u1,list(shocks)),
                    (x1,u1,x2,u2,base.e1))):
                    diffs=compare(steady,*data)
                    maxerror=max(maxerror,*diffs)
                    records+=1
                full=engine.prefix_residual(base,p0,branch,
                    (shocks[0],shocks[1],0.,0.),z)
                require(len(full)==33 and all(math.isfinite(f) for f in full),
                        "Original Python economic system shape or domain drifted")
    report={
        "status":"ORIGINAL_PYTHON_RESERVE_RULE_LOG_TARGETS_MATCH_SOURCE_SHAPED_FORM_ONLY",
        "tested_date_records":records,
        "original_remaining_row_indices":[6,7],
        "original_prefix_positions_date_zero":[12,13],
        "original_prefix_positions_date_one":[28,29],
        "two_policy_instruments_tested":["reserve_remuneration_vR","reserve_quantity_vM"],
        "maximum_float_log_normalization_discrepancy":maxerror,
        "original_python_aux_ast":expressions,
        "actual_Lean_SOURCE_real_economic_functions_executed":False,
        "Lean_candidate_compilation_certified_by_this_script":False,
        "actual_SOURCE_Python_full_33_row_equivalence_proved":False,
        "true_SOURCE_jacobian_interval_enclosure_certified":False,
        "fixed_policy_SOURCE_root_certified":False,
        "full_competitive_equilibrium_certified":False,
        "input_sha256":{str(f.relative_to(ROOT)):digest(f) for f in files},
        "note":"This is original-Python internal consistency on the SOURCE-shaped log policy formulas. Its inputs are not a verified SOURCE real calibration.",
    }
    OUT.parent.mkdir(parents=True,exist_ok=True)
    OUT.write_text(json.dumps(report,indent=2,sort_keys=True)+"\n",encoding="utf-8")
    print(json.dumps({key:report[key] for key in
      ("status","tested_date_records","maximum_float_log_normalization_discrepancy",
       "fixed_policy_SOURCE_root_certified")},indent=2))

if __name__=="__main__":
    main()

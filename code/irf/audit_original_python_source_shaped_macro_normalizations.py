#!/usr/bin/env python3
"""Audit SOURCE-shaped macro row NORMALIZATIONS against original Python.

Independently reconstruct 16 unchanged-position economic macro/policy
rows across both dates. IMPORTANT: SOURCE uses LEVEL residuals for
bank-face renewal, worker labor and household Euler; original Python
uses their logarithmic normalizations. We test the exact nonlinear
normalizations, not a false literal residual equality.

This evaluates original Python primitives with manually transcribed
EconomicModel forms; it does NOT evaluate Lean SOURCE functions, prove
parameter identification, or certify any SOURCE equilibrium.
"""
from __future__ import annotations
import hashlib
import json
import math
from pathlib import Path
import finite_irf as m
from frozen_stationary_prefix_audit import frozen_stationary_seed

HERE = Path(__file__).resolve().parent
SOURCE = HERE.parents[1] / "lean/checkpoint/modules/Ventura26LiquidityAllocation/EconomicModel.lean"
OUT = HERE / "output/original_python_source_shaped_macro_row_normalizations.json"
P0 = HERE / "inputs/rational_preconditioners.json"

def require(condition, message):
    if not condition:
        raise AssertionError(message)

def close(a, b, label):
    require(math.isfinite(a) and math.isfinite(b) and abs(a-b) < 8e-10,
            f"{label}: {a!r} vs {b!r} err={abs(a-b)!r}")
    return abs(a-b)

def check_date(s, state, controls, next_state, next_controls, aux, aux_next,
               innovations, original, start, date):
    cw, wage, mc, pi, q, rd, rl, tight = controls[2:]
    next_pi = next_controls[5]
    household_sdf = s.bw*cw/next_controls[2]
    capital = m.dot(s.mass, state[:2])
    next_capital = m.dot(s.mass, next_state[:2])
    investment = next_capital - s.ad*capital
    # These are the same original Python technology primitives,
    # independently assembled into SOURCE-shaped equation residuals.
    economic = {
        0: next_state[4] - s.aB*rl*state[4]/pi,
        1: q-1-s.phiI*investment/capital,
        2: cw+m.dot(s.mass,controls[:2])+aux["Gamma"]+aux["Rot"]-aux["Y"],
        3: wage-s.chiW*cw**s.sigmaW*aux["L"]**s.varphi,
        4: 1-household_sdf*rd/next_pi,
        5: 1-s.eps+s.eps*mc-150*pi*(pi-1)
           +household_sdf*150*aux_next["Y"]/aux["Y"]*next_pi*(next_pi-1),
        6: math.log(next_state[5])-math.log(aux["rr"]),
        7: math.log(next_state[6])-math.log(aux["money"]),
    }
    # Compare SOURCE levels with original Python's positive-domain
    # logarithmic normalized equations at 0,3,4.
    predicted = {
        0: math.log(next_state[4]/(s.aB*rl*state[4]/pi)),
        1: economic[1],
        2: economic[2],
        3: math.log(wage/(s.chiW*cw**s.sigmaW*aux["L"]**s.varphi)),
        4: math.log(1-economic[4]),
        5: economic[5],
        6: economic[6],
        7: economic[7],
    }
    # Check explicitly that the log rows preserve zero sets on
    # strictly positive domains, without claiming equal derivatives.
    require(min(next_state[4],state[4],pi,rl,cw,wage,aux["L"],
                household_sdf,rd,next_pi,aux["rr"],aux["money"])>0,
            "Source/Python normalized log row outside positive domain")
    errors=[]
    for j in range(8):
        errors.append(close(original[start+j],predicted[j],
                            f"date{date} macro/source shape row {start+j}"))
    return errors, economic

def main():
    source=SOURCE.read_text(encoding="utf-8")
    for anchor in (
        "noncomputable def localReducedRemainingResidual",
        "d.nextBankFace -",
        "d.controls.wage - P.laborScale",
        "1 - householdSDF * d.controls.depositRate",
        "Real.log d.currentReserveRate",
        "Real.log d.currentReservesPre",
    ):
        require(anchor in source,"SOURCE macro structural anchor drift: "+anchor)
    s=m.steady_case()
    p0=[[float(x) for x in row] for row in
        json.loads(P0.read_text(encoding="utf-8"))["P0"]]
    require(len(p0)==16 and all(len(row)==6 for row in p0),
            "Original P0 continuation changed")
    base=frozen_stationary_seed(s)
    charts=([0.]*33,
            [3e-4*math.sin(.41*(j+1)) for j in range(33)],
            [-3e-4*math.cos(.34*(j+1)) for j in range(33)])
    shocks=((0.,0.,0.,0.),(1e-4,0.,0.,0.),(0.,1e-4,0.,0.),
            (0.,0.,1e-4,0.),(0.,0.,0.,1e-4))
    max_error=0.
    checked=0
    for z in charts:
        x1,u0,compact,u1,u2=m.decode_prefix(base,p0,z)
        x2=m.expand_compact_state(s,compact)
        aux1=m.auxiliary(s,x1,u1,x2[:2],base.e1)
        aux2=m.auxiliary(s,x2,u2,x2[:2],[0.,0.])
        for shock in shocks:
            e0=[base.e0[0]+shock[0],base.e0[1]+shock[1]]
            aux0=m.auxiliary(s,base.X0,u0,x1[:2],e0,
                             rho=s.rho+shock[2],corridor=s.Delta+shock[3])
            original=m.prefix_residual(base,p0,"binding",shock,z)
            for args in ((base.X0,u0,x1,u1,aux0,aux1,e0,6,0),
                         (x1,u1,x2,u2,aux1,aux2,base.e1,22,1)):
                errs,_=check_date(s,*args[:7],original,*args[7:])
                checked+=len(errs)
                max_error=max(max_error,*errs)
    report={
        "status":"NUMERICAL_PYTHON_INTERNAL_SOURCE_SHAPED_MACRO_NORMALIZATIONS_ONLY",
        "charts_tested":len(charts),
        "policy_cases_tested":len(shocks),
        "macro_rows_per_date":8,
        "two_date_row_comparisons":checked,
        "maximum_absolute_normalized_row_error":max_error,
        "level_to_log_rows_per_date":{
            "bank_face":0,"worker_labor":3,"household_euler":4
        },
        "log_household_euler_relation":"python_log=log(1-source_level)",
        "log_bank_face_relation":"python_log=log(nextBankFace/renewalTarget)",
        "log_worker_labor_relation":"python_log=log(wage/laborTarget)",
        "derivative_normalizations_still_to_compose":True,
        "original_Lean_SOURCE_functions_evaluated":False,
        "full_SOURCE_Python_jacobian_parity_proved":False,
        "source_sha256":hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
        "python_sha256":hashlib.sha256((HERE/"finite_irf.py").read_bytes()).hexdigest(),
    }
    OUT.parent.mkdir(parents=True,exist_ok=True)
    OUT.write_text(json.dumps(report,indent=2)+"\n",encoding="utf-8")
    print(json.dumps(report,indent=2))

if __name__=="__main__":
    main()

#!/usr/bin/env python3
"""Semantic calendar/field contract: literal SOURCE against Python implementation.

Static correspondence of constructor fields and policy timing, not execution
of Lean economics or a full residual/Jacobian equivalence certificate.
"""
from pathlib import Path
import hashlib
import json
import re

ROOT=Path(__file__).resolve().parents[2]
SOURCE=ROOT/"lean/checkpoint/modules/Ventura26LiquidityAllocation/EconomicModel.lean"
PYTHON=ROOT/"code/irf/finite_irf.py"
OUT=ROOT/"code/irf/output/source_python_calendar_contract.json"

FIELDS={
 "currentCapital":"I.capital",
 "inheritedFace":"I.firmFace",
 "currentBankFace":"I.bankFace",
 "lagReserveRate":"I.reserveRateLag",
 "lagReservesPre":"I.reservesPreLag",
 "controls":"Z.controlsZero",
 "nextCapital":"localPrefixStateSevenCapital Z.stateOne",
 "nextFace":"localPrefixStateSevenFace Z.stateOne",
 "nextBankFace":"Z.stateOne.bankFace",
 "currentReserveRate":"Z.stateOne.reserveRateLag",
 "currentReservesPre":"Z.stateOne.reservesPreLag",
 "nextControls":"Z.controlsOne",
 "currentAggregateProductivity":"P.aggregateProductivity P.tree.initial",
 "nextAggregateProductivity":"P.aggregateProductivity dateOne",
 "reserveRateInnovation":"P.reserveRateInnovation P.tree.initial",
 "reserveQuantityInnovation":"P.reserveQuantityInnovation P.tree.initial",
 "reserveRequirement":"P.reserveRequirementPath 0 (bridgeDateZeroHistory P)",
 "corridorWidth":"P.corridorWidthPath 0 (bridgeDateZeroHistory P)"
}
DATE_ONE_FIELDS={
 "currentCapital":"localPrefixStateSevenCapital Z.stateOne",
 "inheritedFace":"localPrefixStateSevenFace Z.stateOne",
 "currentBankFace":"Z.stateOne.bankFace",
 "lagReserveRate":"Z.stateOne.reserveRateLag",
 "lagReservesPre":"Z.stateOne.reservesPreLag",
 "controls":"Z.controlsOne",
 "nextCapital":"localPrefixStateSixCapital Z.stateTwo",
 "nextFace":"localPrefixStateSixFace P Z.stateTwo",
 "nextBankFace":"Z.stateTwo.bankFace",
 "currentReserveRate":"Z.stateTwo.reserveRateLag",
 "currentReservesPre":"Z.stateTwo.reservesPreLag",
 "nextControls":"tail Z.stateTwo",
 "currentAggregateProductivity":"P.aggregateProductivity dateOne",
 "nextAggregateProductivity":"P.aggregateProductivity recurrent",
 "reserveRateInnovation":"P.reserveRateInnovation dateOne",
 "reserveQuantityInnovation":"P.reserveQuantityInnovation dateOne",
 "reserveRequirement":"P.reserveRequirementPath 1 (bridgeDateOneHistory P dateOne)",
 "corridorWidth":"P.corridorWidthPath 1 (bridgeDateOneHistory P dateOne)"
}

def require(ok,msg):
    if not ok: raise AssertionError(msg)

def section(src,start,end):
    a=src.index(start);b=src.index(end,a+len(start))
    return src[a:b]

def normalized(s):
    return " ".join(s.split())

def assignments(text):
    # The final policy paths in date one span two physical lines.
    body=text.split("LocalPrefixDateData where",1)[1]
    chunks=re.split(r"(?m)^  (?=[A-Za-z][A-Za-z0-9_]*\s*:=)",body)
    out={}
    for chunk in chunks:
        match=re.match(r"([A-Za-z][A-Za-z0-9_]*)\s*:=\s*(.*)",chunk,re.S)
        if match:
            out[match.group(1)]=normalized(match.group(2))
    return out

def main():
    src=SOURCE.read_text(encoding="utf-8")
    py=PYTHON.read_text(encoding="utf-8")
    s0=section(src,"noncomputable def localPrefixDateZeroData","noncomputable def localPrefixDateOneData")
    s1=section(src,"noncomputable def localPrefixDateOneData","noncomputable def localPrefixLabor")
    for label,actual,expected in (("zero",assignments(s0),FIELDS),("one",assignments(s1),DATE_ONE_FIELDS)):
        require(set(actual)==set(expected),f"{label}: SOURCE field set changed")
        for key,value in expected.items():
            require(actual[key]==normalized(value),f"{label}.{key}: SOURCE value changed")

    intervened=section(src,"def initialIntervenedPrimitives","/-- The three supported calendar phases")
    requires_source=(
      "if s = P.tree.initial then v.reserveRateInnovation else 0",
      "if s = P.tree.initial then v.reserveQuantityInnovation else 0",
      "if t = 0 then v.reserveRequirement else 0",
      "if t = 0 then v.corridorWidth else 0",
    )
    for snippet in requires_source:
        require(normalized(snippet) in normalized(intervened),
                "SOURCE policy timing has changed: "+snippet)
    pref=section(py,"def prefix_residual(","def decode_prefix(")
    requires_python=(
        "v_rate, v_quantity, v_requirement, v_corridor = intervention",
        "e0 = [base.e0[0] + v_rate, base.e0[1] + v_quantity]",
        "rho=s.rho + v_requirement, corridor=s.Delta + v_corridor",
        "aux1 = auxiliary(s, x1, u1, state2[:2], base.e1)",
        "aux2 = auxiliary(s, state2, u2, state2[:2], [0.0, 0.0])",
    )
    for snippet in requires_python:
        require(normalized(snippet) in normalized(pref),
                "Python policy timing has changed: "+snippet)
    require("if branch == \"slack\" and i == 1:" in pref,
            "Python branch-dependent L condition changed")
    require("if len(result) != 33:" in pref,
            "Python residual dimension changed")
    report={
       "status":"LITERAL_DATE_FIELD_AND_POLICY_TIMING_CONTRACT_PASS_NOT_OPERATOR_CERTIFICATE",
       "date_zero_fields_checked":len(FIELDS),
       "date_one_fields_checked":len(DATE_ONE_FIELDS),
       "source_policy_timing_anchors":len(requires_source),
       "python_policy_timing_anchors":len(requires_python),
       "source_sha256":hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
       "python_sha256":hashlib.sha256(PYTHON.read_bytes()).hexdigest(),
       "same_numeric_source_inherited_state_proved":False,
       "same_loan_reserve_and_bank_optimization_proved":False,
       "source_residuals_executed":False,
       "economic_33_row_functional_identity_proved":False,
       "source_jacobian_inverse_proved":False,
       "notes":[
          "Field and timing syntax guards, not structural execution of original Lean source",
          "Future source/Python parity must identify date-one tail and distinct branch roots",
          "Do not infer zero endogenous date-one response from zero direct innovation"
       ],
    }
    OUT.parent.mkdir(parents=True,exist_ok=True)
    OUT.write_text(json.dumps(report,indent=2,sort_keys=True)+"\n",encoding="utf-8")
    print(json.dumps({"status":report["status"],"date_fields":36,
                      "source_sha256":report["source_sha256"],
                      "report":str(OUT)},indent=2))

if __name__=="__main__":main()

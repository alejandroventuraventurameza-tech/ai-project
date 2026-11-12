#!/usr/bin/env python3
"""Partition ledger: 8+16+9 SOURCE-shaped candidates, ONE frozen Python base.

This records COMPLETE CANDIDATE ROW COVERAGE, but NEVER a proof of
SOURCE-to-Python functional identity or of a SOURCE Jacobian inverse.
"""
from __future__ import annotations
import hashlib
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
OUT=HERE/"output"
FIRM=OUT/"frozen_source_firm_same_base_candidate.json"
SIXTEEN=OUT/"frozen_source_16_remaining_row_candidates.json"
NINE=OUT/"frozen_nine_scalar_source_shape_candidates.json"
REPORT=OUT/"frozen_33_source_shaped_candidate_partition.json"
SOURCE=ROOT/"lean/checkpoint/modules/Ventura26LiquidityAllocation/EconomicModel.lean"
PY=HERE/"finite_irf.py"
P0=HERE/"inputs/rational_preconditioners.json"

def require(ok,message):
    if not ok:raise AssertionError(message)

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def load(path):
    require(path.is_file(),"Missing prerequisite: "+str(path))
    return json.loads(path.read_text(encoding="utf-8"))

def main():
    f=load(FIRM);r=load(SIXTEEN);n=load(NINE)
    require(f["status"]=="FROZEN_FIRM_SOURCE_SHAPED_PYTHON_CANDIDATES_ONLY",
            "Firm candidate status invalid")
    require(r["status"]=="FROZEN_SAME_BASE_16_SOURCE_SHAPED_ROW_CANDIDATES_ONLY",
            "Sixteen row candidate status invalid")
    require(n["status"]=="FROZEN_NINE_SCALAR_SOURCE_SHAPED_ROW_CANDIDATES_ONLY",
            "Nine scalar candidate status invalid")
    a=set(f["branch_regimes"]["binding"]["source_rows"])
    b=set(r["source_row_indices"])
    c=set(n["branches"]["binding"]["source_row_indices"])
    require(len(a)==8 and len(b)==16 and len(c)==9,
            "One of the three candidate row groups changed")
    require(not a&b and not a&c and not b&c,
            "Candidate row partition overlaps")
    require(a|b|c==set(range(33)),
            "Candidate audit does not cover all 33 SOURCE indices")
    require(set(f["branch_regimes"])==set(r["branch_results"])==
            set(n["branches"])=={"binding","slack"},
            "Unmatched branch sets")
    require(f["baseline"]==r["base"]==n["base"]==
            "frozen_stationary_seed(steady_case())",
            "Reports do not share the fixed inherited stationary base")
    require(n["same_base_P0_used"] is True,
            "Nine scalar audit lacks common terminal continuation P0")
    require(f["source_lean_operator_executed"] is False
            and r["source_economic_operator_executed"] is False
            and n["source_operator_executed"] is False,
            "A candidate report falsely claims actual SOURCE execution")
    require(f["source_python_full_33_functional_identity_proved"] is False
            and r["source_python_33_functional_equality_proved"] is False
            and n["full_source_python_33_functional_identity_proved"] is False,
            "Candidate row coverage falsely asserts functional proof")
    actual_hashes={str(p.relative_to(ROOT)):digest(p) for p in (SOURCE,PY,P0)}
    for report,key in ((f,"files_sha256"),(r,"input_sha256"),
                       (n,"source_inputs_sha256")):
        hashes=report[key]
        for path,checksum in actual_hashes.items():
            require(hashes.get(path)==checksum,
                    "Mismatched SOURCE/Python/P0 evidence: "+path)
    for branch in ("binding","slack"):
        require(f["branch_regimes"][branch]["tested_directions"]==33,
                "Firm audit incomplete in a branch")
        require(r["branch_results"][branch]["direction_count"]==33,
                "Sixteen row audit incomplete in a branch")
        require(n["branches"][branch]["tested_33_coordinate_directions"]==33,
                "Nine scalar audit incomplete in a branch")
    result={
        "status":"FROZEN_33_SOURCE_SHAPED_PYTHON_CANDIDATE_ROWS_ONLY",
        "candidate_row_count":33,
        "candidate_row_partition":{
            "firm_eight":sorted(a),"other_sixteen":sorted(b),
            "scalar_nine":sorted(c)},
        "common_base":"frozen_stationary_seed(steady_case())",
        "common_P0":True,
        "branches_checked":["binding","slack"],
        "source_economic_operator_executed":False,
        "full_SOURCE_Python_functional_equivalence_proved":False,
        "source_Jacobian_inverse_certified":False,
        "same_base_frozen_root_slack_equilibrium_proved":False,
        "missing_gates":[
          "SOURCE Primitives, inherited states and positive log chart equality",
          "Original Lean SOURCE 33-row functional identity with Python",
          "SOURCE and Python tail function equivalence on a neighborhood",
          "Rigorous SOURCE Jacobian inverse enclosure and local IFT",
          "Complete equilibrium optimality, fiscal closure and growth claims"],
        "input_sha256":actual_hashes,
        "reports_sha256":{str(p.relative_to(ROOT)):digest(p)
                          for p in (FIRM,SIXTEEN,NINE)}
    }
    REPORT.write_text(json.dumps(result,indent=2,sort_keys=True)+"\n",
                      encoding="utf-8")
    print(json.dumps({"status":result["status"],
                      "candidate_rows":33,
                      "source_functional_identity_proved":False,
                      "report":str(REPORT)},indent=2))

if __name__=="__main__":
    main()

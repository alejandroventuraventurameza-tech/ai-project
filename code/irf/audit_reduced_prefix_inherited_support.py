#!/usr/bin/env python3
"""SOURCE reduced-prefix inherited-field support and Python invariance audit.

The check is deliberately limited to the 33-equation REDUCED prefix.
It does not certify that dropped fiscal/bank fields are irrelevant to the
underlying original equilibrium, bank optimization or fiscal closure.
"""
from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path

import finite_irf as model
from frozen_stationary_prefix_audit import frozen_stationary_seed

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
SOURCE=ROOT/"lean/checkpoint/modules/Ventura26LiquidityAllocation/EconomicModel.lean"
ENGINE=HERE/"finite_irf.py"
OUT=HERE/"output/source_reduced_prefix_inherited_support.json"

DIRECT={
  "currentCapital":"capital",
  "inheritedFace":"firmFace",
  "currentBankFace":"bankFace",
  "lagReserveRate":"reserveRateLag",
  "lagReservesPre":"reservesPreLag",
}
DROPPED={
 "householdDeposits","householdBonds","depositRateLag",
 "governmentBondRateLag","reservesLag","facilityRateLag",
 "facilityBorrowingLag"
}

def check(ok,why):
    if not ok:
        raise AssertionError(why)

def normalize(value):
    return " ".join(value.split())

def extract(source,begin,end):
    a=source.index(begin)
    b=source.index(end,a+len(begin))
    return source[a:b]

def assignments(section):
    body=section.split("LocalPrefixDateData where",1)[1]
    chunks=re.split(r"(?m)^  (?=[A-Za-z][A-Za-z0-9_]*\s*:=)",body)
    result={}
    for c in chunks:
        match=re.match(r"([A-Za-z][A-Za-z0-9_]*)\s*:=\s*(.*)",c,re.S)
        if match:
            result[match.group(1)]=normalize(match.group(2))
    return result

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    src=SOURCE.read_text(encoding="utf-8")
    py=ENGINE.read_text(encoding="utf-8")
    record=extract(src,"structure InheritedState where",
                   "/-- Give one bank type its own inherited nominal face")
    fields=set(re.findall(r"(?m)^  ([A-Za-z][A-Za-z0-9_]*)\s*:",record))
    check(fields==set(DIRECT.values())|DROPPED,
          "InheritedState record membership changed")
    date0=extract(src,"noncomputable def localPrefixDateZeroData",
                  "noncomputable def localPrefixDateOneData")
    date1=extract(src,"noncomputable def localPrefixDateOneData",
                  "noncomputable def localPrefixLabor")
    residual=extract(src,"noncomputable def localReducedPrefixResidual",
                     "def LocalReducedPrefixEquationsHold")
    extracted=assignments(date0)
    references={k:v for k,v in extracted.items() if re.search(r"\bI\.",v)}
    check(references=={k:"I."+v for k,v in DIRECT.items()},
          "Date-zero SOURCE inherited fields no longer match the seven-coordinate projection")
    check(len(assignments(date0))==len(assignments(date1))==18,
          "SOURCE date-data constructor dimensions changed")
    check("let d0 := localPrefixDateZeroData P I Z dateOne" in normalize(residual),
          "Original SOURCE prefix no longer enters through date-zero data")
    check("let d1 := localPrefixDateOneData P Z dateOne recurrent tail" in normalize(residual),
          "Date-one SOURCE prefix data construction changed")
    # The restricted 33-row dispatcher may use I only through d0.
    matches=re.findall(r"\bI\.[A-Za-z][A-Za-z0-9_]*",residual)
    check(not matches,"SOURCE residual dispatcher now reads inherited record directly")
    check("I." not in date1,
          "SOURCE date-one residual now consumes inherited record directly")
    check("return result" in py and "def prefix_residual(" in py,
          "Python reduced-prefix engine changed")
    s=model.steady_case()
    seed=frozen_stationary_seed(s)
    from pathlib import Path
    p=json.loads((HERE/"inputs/rational_preconditioners.json").read_text(encoding="utf-8"))
    p0=[[float(x) for x in row] for row in p["P0"]]
    check(len(p0)==16 and all(len(row)==6 for row in p0),
          "Pinned continuation projection dimensions changed")
    z=[0.]*33
    initial=model.prefix_residual(seed,p0,"binding",(0.,0.,0.,0.),z)
    # Python does not pass G, bonds or the excluded source fields into
    # the reduced-prefix API. A copy with extra metadata must be inert.
    class ExtendedSeed:
        pass
    alt=ExtendedSeed()
    for name in ("s","X0","U0","X1","U1","X2","e0","e1"):
        setattr(alt,name,getattr(seed,name))
    alt.householdBonds=1e9
    alt.householdDeposits=1e9
    alt.reservesPost=1e9
    alt.governmentBondRateLag=1e9
    alternate=model.prefix_residual(alt,p0,"binding",(0.,0.,0.,0.),z)
    check(initial==alternate,"Python reduced-prefix API depends on appended excluded metadata")
    report={
       "status":"SOURCE_REDUCED_PREFIX_USES_ONLY_SEVEN_INHERITED_COORDINATES_CONDITIONALLY",
       "direct_inherited_source_struct_fields":sorted(DIRECT.values()),
       "direct_inherited_source_field_count":len(DIRECT),
       "expanded_inherited_coordinates":7,
       "excluded_inherited_struct_fields":sorted(DROPPED),
       "excluded_inherited_struct_field_count":len(DROPPED),
       "date0_and_date1_fields_each":18,
       "source_dispatcher_reads_I_only_through_date_zero_data":True,
       "python_appended_metadata_invariance":True,
       "source_lean_semantic_extensionality_proved_in_kernel":False,
       "source_python_primitives_alignment_proved":False,
       "underlying_original_equilibrium_independence_of_excluded_fields_proved":False,
       "fiscal_closure_unchanged_proved":False,
       "bank_and_household_KKT_unchanged_proved":False,
       "full_33_operator_transport_proved":False,
       "input_sha256":{str(f.relative_to(ROOT)):sha(f) for f in (SOURCE,ENGINE)}
    }
    OUT.parent.mkdir(parents=True,exist_ok=True)
    OUT.write_text(json.dumps(report,indent=2,sort_keys=True)+"\n",encoding="utf-8")
    print(json.dumps({"status":report["status"],
                       "retained":sorted(DIRECT.values()),
                       "excluded":sorted(DROPPED),
                       "output":str(OUT)},indent=2))

if __name__=="__main__":
    main()

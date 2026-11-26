#!/usr/bin/env python3
"""Provenance guard: SOURCE inherited record vs two distinct Python seeds.

Reports exact literal field structure and numerical distinction of the
common-boundary experiment from the frozen predecessor. Not SOURCE
economic equivalence, KKT optimality, or a second equilibrium proof.
"""
from __future__ import annotations
import hashlib
import json
import math
import re
from pathlib import Path
from finite_irf import steady_case, make_boundary
from frozen_stationary_prefix_audit import frozen_stationary_seed

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
LEAN=ROOT/"lean/candidates/Ventura26LiquidityAllocation/StationaryInheritedStateCandidate.lean"
SOURCE=ROOT/"lean/checkpoint/modules/Ventura26LiquidityAllocation/EconomicModel.lean"
ENGINE=HERE/"finite_irf.py"
SEED_FILE=HERE/"frozen_stationary_prefix_audit.py"
OUT=HERE/"output/source_python_predecessor_provenance.json"
EXPECTED={
"capital":"capital","firmFace":"firmFace","bankFace":"bankEquity",
"householdDeposits":"bankDeposits","householdBonds":"G - reservesPre",
"depositRateLag":"ProposedStationaryBank.depositRate",
"governmentBondRateLag":"ProposedStationaryBank.depositRate",
"reserveRateLag":"ProposedStationaryBank.reserveRate",
"reservesPreLag":"reservesPre","reservesLag":"reservesPost",
"facilityRateLag":"facilityRate",
"facilityBorrowingLag":"facilityBorrowing"
}
def require(x,msg):
    if not x: raise AssertionError(msg)
def norm(x):
    return " ".join(x.split())
def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    lean=LEAN.read_text(encoding="utf-8")
    source=SOURCE.read_text(encoding="utf-8")
    engine=ENGINE.read_text(encoding="utf-8")
    seed_code=SEED_FILE.read_text(encoding="utf-8")
    body=lean.split("noncomputable def inheritedState (G : ℝ) : InheritedState where",1)[1].split("theorem inherited_financial_positions",1)[0]
    observed=dict(re.findall(r"(?m)^  (\w+)\s*:=\s*(.+?)\s*$",body))
    require(set(observed)==set(EXPECTED) and all(norm(observed[k])==v for k,v in EXPECTED.items()),
            "SOURCE inheritedState twelve fields changed")
    require("structure InheritedState where" in source,
            "Original InheritedState record changed")
    for anchor in ("predecessor = [*s.k, *s.F, s.E, s.rr, s.M]",
                   "e0=[0.0, 0.0]","e1=[0.0, 0.0]"):
        require(anchor in seed_code,"Frozen predecessor convention changed: "+anchor)
    for anchor in ("def make_boundary(s):","return SimpleNamespace(s=s, z=z, X0=x0",
                   "e1 = [-.5 * math.log(z[\"rr\"] / s.rr), -.5 * math.log(money / s.M)]"):
        require(anchor in engine,"Common-boundary convention changed: "+anchor)
    s=steady_case()
    frozen=frozen_stationary_seed(s)
    frontier=make_boundary(s)
    require(len(frozen.X0)==len(frontier.X0)==7 and len(frozen.e1)==2,
            "Unexpected predecessor vector dimensions")
    differences={str(i):frontier.X0[i]-frozen.X0[i] for i in range(7)}
    require(all(math.isfinite(x) for x in differences.values()),"Nonfinite predecessor difference")
    maximum=max(abs(x) for x in differences.values())
    require(maximum>1e-9 and max(abs(x) for x in frontier.e1)>1e-8,
            "Common frontier was wrongly identified with frozen predecessor")
    require(frozen.e0==[0.0,0.0] and frozen.e1==[0.0,0.0],
            "Frozen predecessor innovations are no longer zero")
    report={
      "status":"SOURCE_INHERITED_FIELDS_LITERALLY_GUARDED_FRONTIER_NOT_FROZEN",
      "source_inherited_fields":len(EXPECTED),
      "source_household_bonds_G_remains_symbolic":True,
      "frozen_python_X0":frozen.X0,
      "frontier_python_X0":frontier.X0,
      "frontier_minus_frozen_X0":differences,
      "max_abs_frontier_minus_frozen_X0":maximum,
      "frozen_date_one_innovations":frozen.e1,
      "frontier_date_one_innovations":frontier.e1,
      "different_numeric_predecessors":True,
      "source_exact_numeric_predecessor_identification_proved":False,
      "source_economic_operator_equivalence_proved":False,
      "branch_distinct_global_equilibria_proved":False,
      "input_sha256":{str(p.relative_to(ROOT)):sha(p) for p in (LEAN,SOURCE,ENGINE,SEED_FILE)}
    }
    OUT.parent.mkdir(parents=True,exist_ok=True)
    OUT.write_text(json.dumps(report,indent=2,sort_keys=True)+"\n",encoding="utf-8")
    print(json.dumps({"status":report["status"],"max_predecessor_difference":maximum,
                      "source_numeric_identification_proved":False,"report":str(OUT)},indent=2))
if __name__=="__main__":main()

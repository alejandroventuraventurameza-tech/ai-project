#!/usr/bin/env python3
"""Check the 60 exact real decimal literals of the SOURCE P0 Lean candidate.

Companion to code/irf/inputs/rational_preconditioners.json. Converts both
representations directly to Fraction(Decimal(...)); NEVER converts to float.
Parsing matched source notation is strictly guarded by the named definition.
This is a semantic DATA contract, not a Lean kernel proof or an economic
equilibrium continuation.
"""
from __future__ import annotations

import hashlib
import json
import re
from decimal import Decimal
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PIN = HERE / "inputs/rational_preconditioners.json"
LEAN = ROOT / "lean/candidates/Ventura26LiquidityAllocation/SourceFrozenP0ExactDecimalTailCandidate.lean"
SOURCE = ROOT / "lean/checkpoint/modules/Ventura26LiquidityAllocation/EconomicModel.lean"
OUT = HERE / "output/source_frozen_p0_lean_exact_decimal_contract.json"

def require(condition, message):
    if not condition:
        raise AssertionError(message)

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    p0=json.loads(PIN.read_text(encoding="utf-8"))["P0"]
    require(len(p0)==16 and all(len(row)==6 for row in p0),
            "Expected pinned 16x6 P0")
    require(all(Fraction(Decimal(p0[i][j]))==int(i==j)
                for i in range(6) for j in range(6)),
            "First six P0 rows are not the exact identity")
    src=LEAN.read_text(encoding="utf-8")
    begin="noncomputable def sourceFrozenP0TenControls : SourceFiniteTailMatrix :="
    end="/-- The SOURCE-typed FINITE P0 continuation"
    require(src.count(begin)==1 and src.count(end)==1,
            "Pinned source declaration changed")
    literal_section=src.split(begin,1)[1].split(end,1)[0]
    values=re.findall(r"\((-?[0-9]+(?:\.[0-9]+)?)\s*:\s*ℝ\)",literal_section)
    require(len(values)==60,"Expected exactly 60 typed decimal Lean literals")
    require(literal_section.count("![")==11,
            "Expected one vector of ten control-row vectors")
    expected=[p0[i][j] for i in range(6,16) for j in range(6)]
    # Compare BOTH surface strings and exact rational values. This rejects
    # a numeric reformatted source even if its real value is unchanged:
    # every input string must be traceable to the pinned P0 artifact.
    mismatches=[
        {"position":i,"expected":expected[i],"lean":values[i]}
        for i in range(60) if expected[i]!=values[i]
    ]
    require(not mismatches,"Lean exact decimal P0 drifted: "+str(mismatches[:3]))
    assert all(Fraction(Decimal(a))==Fraction(Decimal(b))
               for a,b in zip(values,expected))
    report={
        "status":"EXACT_DECIMAL_60_COEFFICIENT_SOURCE_P0_LEAN_DATA_MATCH",
        "source_economic_model_sha256":sha(SOURCE),
        "pinned_p0_json_sha256":sha(PIN),
        "source_lean_candidate_sha256":sha(LEAN),
        "source_control_rows":10,
        "source_state_columns":6,
        "exact_decimal_matches":60,
        "first_six_p0_rows_are_identity":True,
        "source_real_literals_not_binary64":True,
        "all_values_compared_as_exact_Fraction_Decimal":True,
        "lean_theorem_kernel_verified_by_this_script":False,
        "source_python_economic_equivalence_proved":False,
        "source_infinite_horizon_tail_proved":False,
        "scope":"Exactly 60 coefficient strings and rational values, no economic model semantics.",
    }
    OUT.parent.mkdir(parents=True,exist_ok=True)
    OUT.write_text(json.dumps(report,sort_keys=True,indent=2)+"\n",encoding="utf-8")
    print(json.dumps({k:report[k] for k in (
        "status","exact_decimal_matches","first_six_p0_rows_are_identity",
        "lean_theorem_kernel_verified_by_this_script",
    )},indent=2))

if __name__=="__main__":
    main()

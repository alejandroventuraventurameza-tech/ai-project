#!/usr/bin/env python3
"""Fail-closed audit of original Python log-vs-SOURCE level normalization.

The original SOURCE `localReducedRemainingResidual` uses differences
in levels in rows 0/3 and 1-minus-ratio in row 4. The original Python
`remaining_residuals` uses log ratios in those three slots at both dates.
These are NOT equal functions. Their zeros coincide under positivity,
as formalized in the companion Lean module.

This checks the literal ORIGINAL source declarations and Python AST,
then evaluates the ORIGINAL Python prefix at 12 off-root inputs.
It does not execute Lean real arithmetic or establish all-row parity,
a SOURCE root, derivatives, or a competitive equilibrium.
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
PY = HERE / "finite_irf.py"
SOURCE = ROOT / "lean/checkpoint/modules/Ventura26LiquidityAllocation/EconomicModel.lean"
LEAN = ROOT / "lean/candidates/Ventura26LiquidityAllocation/SourcePythonLogResidualZeroSetBridgeCandidate.lean"
P0 = HERE / "inputs/rational_preconditioners.json"
OUT = HERE / "output/source_python_three_log_normalizations.json"

def require(condition, explanation):
    if not condition:
        raise AssertionError(explanation)

def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def original_row_ast(code):
    module = ast.parse(code, filename=str(PY))
    candidates = [node for node in module.body
                  if isinstance(node, ast.FunctionDef)
                  and node.name == "remaining_residuals"]
    require(len(candidates) == 1, "Original Python remaining_residuals changed")
    returns = [node for node in ast.walk(candidates[0]) if isinstance(node, ast.Return)]
    require(len(returns) == 1 and isinstance(returns[0].value, ast.List),
            "Expected one original Python 11-row return list")
    rows = returns[0].value.elts
    require(len(rows) == 11, "Expected exactly 11 original Python other rows")
    expected = {
        0: "math.log(next_state[4] / (s.aB * rl * state[4] / inflation))",
        3: "math.log(wage / (s.chiW * aux['L'] * cw))",
        4: "math.log(rd * household_sdf / next_controls[5])",
    }
    for index, expression in expected.items():
        expected_ast = ast.parse(expression, mode="eval").body
        require(ast.dump(rows[index], include_attributes=False) ==
                ast.dump(expected_ast, include_attributes=False),
                f"Original Python row {index} log normalization changed")
    require(any(
        ast.unparse(node) == "household_sdf = s.bw * cw / next_controls[2]"
        for node in candidates[0].body if isinstance(node, ast.Assign)),
        "Python household SDF expression changed")
    return expected

def check_rows(observed, state, controls, next_state, next_controls, aux, s):
    require(len(observed) == 11, "Original remaining row count changed")
    cw, wage, _mc, inflation, _q, rd, rl, _tightness = controls[2:]
    bank_A = next_state[4]
    bank_B = s.aB * rl * state[4] / inflation
    labor_A = wage
    labor_B = s.chiW * aux["L"] * cw
    household_A = rd * (s.bw * cw / next_controls[2])
    household_B = next_controls[5]
    data = [(0,bank_A,bank_B),(3,labor_A,labor_B),(4,household_A,household_B)]
    worst = 0.0
    for index, A, B in data:
        require(math.isfinite(A) and math.isfinite(B) and A > 0 and B > 0,
                f"Nonpositive SOURCE/Python log-comparison domain for row {index}")
        expected = math.log(A/B)
        err = abs(observed[index] - expected)
        require(math.isfinite(err) and err <= 2e-13,
                f"Original Python row {index} log AST/runtime inconsistency: {err}")
        # These are the exact transformations of the SOURCE-shaped
        # LEVEL residuals; they are not claims of literal equality.
        normalized_level = (A - B) / B if index in (0,3) else 1 - A / B
        predicted_level = math.expm1(observed[index])
        if index == 4:
            predicted_level = -predicted_level
        delta = abs(normalized_level - predicted_level)
        require(math.isfinite(delta) and delta < 2e-12,
                f"Original Python row {index} level-vs-log conversion drift: {delta}")
        worst = max(worst, err, delta)
    return worst

def main():
    require(all(x.is_file() for x in (PY,SOURCE,LEAN,P0)),
            "Pinned SOURCE/Python inputs missing")
    pycode = PY.read_text(encoding="utf-8")
    srccode = SOURCE.read_text(encoding="utf-8")
    leancode = LEAN.read_text(encoding="utf-8")
    formula = original_row_ast(pycode)
    anchors = ("| 0 => d.nextBankFace -", "| 3 => d.controls.wage -",
               "| 4 => 1 - householdSDF * d.controls.depositRate /")
    require(all(x in srccode for x in anchors),
            "Original SOURCE level row declarations changed")
    proofs = (
        "sourceBankFaceLevelRow_zero_iff_pythonShapedLog",
        "sourceLaborSupplyLevelRow_zero_iff_pythonShapedLog",
        "sourceHouseholdDepositLevelRow_zero_iff_pythonShapedLog",
    )
    require(all("theorem " + x in leancode for x in proofs),
            "Companion Lean exact real theorems not found")

    j = json.loads(P0.read_text(encoding="utf-8"))
    matrix = [[float(x) for x in row] for row in j["P0"]]
    require(len(matrix) == 16 and all(len(r) == 6 for r in matrix),
            "Expected frozen 16x6 P0")
    s = engine.steady_case()
    require(s.bw == .99 and s.chiW == 1.0 and s.sigmaW == 1.0,
            "Stationary worker Euler/labor coefficients changed")
    base = frozen_stationary_seed(s)
    charts = [
        [0.0]*33,
        [1e-4*math.sin(0.29*(i+1)) for i in range(33)],
        [-1e-4*math.cos(0.37*(i+1)) for i in range(33)],
    ]
    max_error = 0.0
    total = 0
    for branch in ("slack", "binding"):
        for vR in (0.0,-1e-5):
            for z in charts:
                x1 = [base.X1[i]*math.exp(z[i]) for i in range(7)]
                u0 = [base.U0[i]*math.exp(z[7+i]) for i in range(10)]
                x2compact = [base.X2[i]*math.exp(z[17+i]) for i in range(6)]
                x2 = engine.expand_compact_state(s,x2compact)
                u1 = [base.U1[i]*math.exp(z[23+i]) for i in range(10)]
                tail = engine.matvec(matrix,z[17:23])
                u2 = [s.base[6+i]*math.exp(tail[6+i]) for i in range(10)]
                aux0 = engine.auxiliary(s,base.X0,u0,x1[:2],
                                        [base.e0[0]+vR,base.e0[1]])
                aux1 = engine.auxiliary(s,x1,u1,x2[:2],base.e1)
                aux2 = engine.auxiliary(s,x2,u2,x2[:2],[0.0,0.0])
                rows0 = engine.remaining_residuals(
                    s,base.X0,u0,x1,u1,aux0,aux1)
                rows1 = engine.remaining_residuals(
                    s,x1,u1,x2,u2,aux1,aux2)
                full = engine.prefix_residual(base,matrix,branch,vR,z)
                require(len(full)==33, "Original Python prefix not 33 equations")
                # Original first date has 6 firm rows; second has
                # 4 firm equations plus the independent pledge row.
                for raw,root_pos,args in (
                    (rows0,6,(base.X0,u0,x1,u1,aux0)),
                    (rows1,22,(x1,u1,x2,u2,aux1)),
                ):
                    state,controls,next_state,next_controls,aux=args
                    for k in (0,3,4):
                        require(abs(full[root_pos+k]-raw[k]) <= 2e-13,
                                f"Original Python prefix slot for normalized row {k} drifted")
                    max_error=max(max_error,check_rows(
                        raw,state,controls,next_state,next_controls,aux,s))
                    total+=1
    result = {
        "status":"SOURCE_LEVEL_AND_ORIGINAL_PYTHON_LOG_ZEROS_DISTINCT_FUNCTIONS",
        "source_and_python_residual_functions_literally_equal":False,
        "source_to_python_zero_sets_proved_for_positive_rows_in_Lean_by_this_script":False,
        "companion_Lean_theorems_source_present":True,
        "original_python_remaining_row_indices":[0,3,4],
        "original_python_prefix_first_date_positions":[6,9,10],
        "original_python_prefix_second_date_positions":[22,25,26],
        "tested_date_records":total,
        "positive_domain_verified_in_python_tests":True,
        "maximum_same_engine_normalization_abs_discrepancy":max_error,
        "requirement":"Prove actual-source-to-python primitive, inherited-data and transformed Jacobian correspondence; Lean real formulas are not executed here.",
        "actual_source_full_33_row_functional_equivalence":False,
        "actual_source_interval_jacobian_enclosure":False,
        "actual_source_root_certified":False,
        "inputs_sha256":{str(p.relative_to(ROOT)):digest(p) for p in
                         (PY,SOURCE,LEAN,P0)},
        "python_ast_rows":formula,
    }
    OUT.parent.mkdir(parents=True,exist_ok=True)
    OUT.write_text(json.dumps(result,indent=2,sort_keys=True)+"\n",
                   encoding="utf-8")
    print(json.dumps({key:result[key] for key in
        ("status","tested_date_records",
         "maximum_same_engine_normalization_abs_discrepancy",
         "actual_source_full_33_row_functional_equivalence")},indent=2))

if __name__=="__main__":
    main()

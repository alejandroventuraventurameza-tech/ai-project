#!/usr/bin/env python3
"""Check the ORIGINAL Python date-one P0-to-16-row call chain.

The SOURCE Lean constructor says date-one nextControls := tail Z.stateTwo.
A separate Lean candidate constructs the tail using the pinned exact
decimal P0 10x6 matrix. This audit checks that finite_irf.py's genuine
33-row residual computes its date-two controls from those same six
compact-state deviations and passes them to the 16 date-one equations,
including their eleven "remaining" source-shaped rows.

The checks are Python AST and binary64 execution tests, not proof of
cross-language economic function identity or infinite-horizon equilibrium.
"""
from __future__ import annotations

import ast
import hashlib
import json
import math
from pathlib import Path

import finite_irf as engine

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PYTHON = HERE / "finite_irf.py"
SOURCE = ROOT / "lean/checkpoint/modules/Ventura26LiquidityAllocation/EconomicModel.lean"
LEAN_P0 = ROOT / "lean/candidates/Ventura26LiquidityAllocation/SourceFrozenP0ExactDecimalTailCandidate.lean"
LEAN_CALENDAR = ROOT / "lean/candidates/Ventura26LiquidityAllocation/SourceFrozenP0LiteralDateCalendarCandidate.lean"
P0 = HERE / "inputs/rational_preconditioners.json"
OUT = HERE / "output/source_dateone_p0_operational_wiring.json"

def require(ok, message):
    if not ok:
        raise AssertionError(message)

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def find_fn(tree, name):
    found = [x for x in tree.body if isinstance(x, ast.FunctionDef) and x.name == name]
    require(len(found) == 1, "Expected unique original Python function: " + name)
    return found[0]

def simple_assign(fn, name):
    hits = [x for x in ast.walk(fn)
            if isinstance(x, ast.Assign) and len(x.targets) == 1
            and isinstance(x.targets[0], ast.Name)
            and x.targets[0].id == name]
    require(len(hits) == 1, "Expected unique original assignment: " + name)
    return hits[0].value

def calls(fn, name):
    return [x for x in ast.walk(fn)
            if isinstance(x, ast.Call) and isinstance(x.func, ast.Name)
            and x.func.id == name]

def main():
    code = PYTHON.read_text(encoding="utf-8")
    tree = ast.parse(code, filename=str(PYTHON))
    p = find_fn(tree, "prefix_residual")
    b = find_fn(tree, "binding_period_residual")
    d = find_fn(tree, "decode_prefix")
    for fn in (p, d):
        require(ast.unparse(simple_assign(fn, "tail_log")) ==
                "matvec(p0, z[17:23])",
                f"{fn.name}: P0 must consume the SIX date-two state logs")
        require(ast.unparse(simple_assign(fn, "u2")) ==
                "[s.base[6 + i] * math.exp(tail_log[6 + i]) for i in range(10)]",
                f"{fn.name}: ten date-two controls must use P0 rows 6-15")
    date1 = calls(p, "binding_period_residual")
    require(len(date1) == 1 and
            [ast.unparse(arg) for arg in date1[0].args] ==
            ["s", "x1", "u1", "x2", "u2", "base.e1"],
            "Date-one residual no longer receives the decoded P0 controls")
    other = calls(b, "remaining_residuals")
    require(len(other) == 1 and
            [ast.unparse(arg) for arg in other[0].args] ==
            ["s", "state", "controls", "next_state",
             "next_controls", "aux", "aux_next"],
            "The date-one eleven economic rows no longer use the same P0 continuation")
    require(len(calls(b, "auxiliary")) == 2,
            "Date-one current/next intermediate object construction changed")

    source = SOURCE.read_text(encoding="utf-8")
    s1 = source.split("noncomputable def localPrefixDateOneData", 1)[1].split(
        "noncomputable def localPrefixLabor", 1)[0]
    require("nextControls := tail Z.stateTwo" in s1,
            "Genuine SOURCE date-one future-control builder changed")
    pinned = LEAN_P0.read_text(encoding="utf-8")
    calendar = LEAN_CALENDAR.read_text(encoding="utf-8")
    require("noncomputable def sourceFrozenP0TenControls" in pinned,
            "Lean exact P0 source matrix missing")
    for theorem in (
        "sourceFrozenP0_dateZero_nextControls",
        "sourceFrozenP0_dateOne_nextControl_level",
        "sourceFrozenP0_dateOne_nextControl_log",
        "sourceFrozenP0_dateOne_nextControl_positive",
    ):
        require("theorem " + theorem in calendar,
                "Lean calendar proof statement missing: " + theorem)

    raw = json.loads(P0.read_text(encoding="utf-8"))["P0"]
    require(len(raw) == 16 and all(len(row) == 6 for row in raw),
            "Expected frozen P0 shape 16x6")
    p0 = [[float(x) for x in row] for row in raw]
    s = engine.steady_case()
    base = engine.make_boundary(s)
    deviations = [
        [0.0] * 33,
        [1e-4 * math.sin(.37 * (i+1)) for i in range(33)],
        [-1e-4 * math.cos(.53 * (i+1)) for i in range(33)],
    ]
    innovations = [(0.0,0.0,0.0,0.0),(-1e-5,0.0,0.0,0.0)]
    max_date1_error = 0.0
    for branch in ("slack", "binding"):
        for v in innovations:
            for z in deviations:
                x1 = [base.X1[i] * math.exp(z[i]) for i in range(7)]
                u1 = [base.U1[i] * math.exp(z[23+i]) for i in range(10)]
                x2 = [base.X2[i] * math.exp(z[17+i]) for i in range(6)]
                log_u2 = engine.matvec(p0,z[17:23])
                u2 = [s.base[6+i]*math.exp(log_u2[6+i]) for i in range(10)]
                observed = engine.prefix_residual(base,p0,branch,v,z)
                direct = engine.binding_period_residual(s,x1,u1,x2,u2,base.e1)
                require(len(observed) == 33 and len(direct) == 16,
                        "SOURCE/Python date-one partition drifted")
                err = max(abs(a-b) for a,b in zip(observed[17:33],direct))
                require(math.isfinite(err) and err < 1e-12,
                        "Date-one original Python call chain is inconsistent")
                max_date1_error = max(max_date1_error,err)

    report = {
        "status": "ORIGINAL_PYTHON_DATEONE_16_ROW_P0_WIRING_AUDITED_NOT_SOURCE_EQUIVALENCE",
        "ast_verified": True,
        "verified_prefix_p0_state_log_indices": [17,18,19,20,21,22],
        "verified_date_two_control_rows": list(range(6,16)),
        "date_one_prefix_row_positions": list(range(17,33)),
        "test_points": len(deviations)*len(innovations)*2,
        "date_one_max_abs_python_call_chain_error": max_date1_error,
        "original_SOURCE_next_control_constructor_guarded": True,
        "original_SOURCE_economic_16_rows_executed_in_Lean": False,
        "Lean_calendar_kernel_compilation_certified_by_this_script": False,
        "SOURCE_Python_inherited_state_identified": False,
        "SOURCE_Python_16_row_functional_equality_proved": False,
        "complete_SOURCE_Python_33_row_identity_proved": False,
        "infinite_horizon_equilibrium_proved": False,
        "sha256": {str(x.relative_to(ROOT)):digest(x)
                   for x in (PYTHON,SOURCE,LEAN_P0,LEAN_CALENDAR,P0)},
        "notes": "Static AST and same-engine off-root equality do not execute original Lean SOURCE residuals.",
    }
    OUT.parent.mkdir(parents=True,exist_ok=True)
    OUT.write_text(json.dumps(report,indent=2,sort_keys=True)+"\n",
                   encoding="utf-8")
    print(json.dumps({key:report[key] for key in (
        "status","test_points","date_one_max_abs_python_call_chain_error",
        "SOURCE_Python_16_row_functional_equality_proved"
    )},indent=2))

if __name__ == "__main__":
    main()

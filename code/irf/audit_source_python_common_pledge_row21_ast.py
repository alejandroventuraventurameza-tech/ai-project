#!/usr/bin/env python3
"""Audit the second collateral equation: SOURCE commonPledgeOne vs Python.

Original Python has at OUTPUT row 21:
  log(next_compact[2]/(s.ad*next_controls[5]*next_controls[6])).
Original SOURCE has a LEVEL equation J2 - (1-delta)*Pi2*q2.
The corresponding proposed Lean file changes that SOURCE level row
to an exact log ratio and proves zero-set equivalence under positivity.

This program fingerprints both ORIGINAL source expressions and
the candidate's selected row index; it does not prove cross-language
runtime equivalence or existence of an economic root.
"""
from __future__ import annotations

import ast
import hashlib
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
PY=HERE/"finite_irf.py"
SOURCE=ROOT/"lean/checkpoint/modules/Ventura26LiquidityAllocation/EconomicModel.lean"
LEAN=ROOT/"lean/candidates/Ventura26LiquidityAllocation/SourceCanonicalTwoPledgeLogBoundaryCandidate.lean"
OUT=HERE/"output/source_python_common_pledge_row21_ast.json"


def require(ok,msg):
    if not ok: raise AssertionError(msg)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def original_function(tree,name):
    funcs=[v for v in tree.body if isinstance(v,ast.FunctionDef) and v.name==name]
    require(len(funcs)==1,"Function changed or duplicated: "+name)
    return funcs[0]


def main():
    fn_tree=ast.parse(PY.read_text(encoding="utf-8"))
    binding=original_function(fn_tree,"binding_period_residual")
    prefix=original_function(fn_tree,"prefix_residual")
    calls=[
        ast.unparse(n.args[0])
        for n in ast.walk(binding)
        if isinstance(n,ast.Call) and ast.unparse(n.func)=="result.append"
        and len(n.args)==1
    ]
    expected="math.log(next_compact[2] / (s.ad * next_controls[5] * next_controls[6]))"
    require(calls.count(expected)==1,
            "Original period-one common pledge Python log residual changed: "+str(calls))
    require(any(ast.unparse(n) ==
        "result.extend(binding_period_residual(s, x1, u1, x2, u2, base.e1))"
        for n in ast.walk(prefix) if isinstance(n,ast.Call)),
        "Original 33-prefix does not use binding-period function")
    # First date-0 block is 6 firm rows + 11 common rows = 17.
    # Date-one firm block adds 4; therefore common pledge is row 21.
    # The AST has two append statements INSIDE the two-firm loop,
    # plus one common-pledge append AFTER that loop; runtime unrolls
    # two budget/Euler pairs (4 rows) before the log row.
    common=[n for n in binding.body
            if isinstance(n,ast.Expr) and isinstance(n.value,ast.Call)
            and ast.unparse(n.value.func)=="result.append"]
    require(len(calls)==3 and len(common)==1
            and ast.unparse(common[0].value.args[0])==expected,
            "Original Python row 21 ordering changed")
    loops=[n for n in binding.body if isinstance(n,ast.For)
           and ast.unparse(n.target)=="i" and ast.unparse(n.iter)=="range(2)"]
    require(len(loops)==1 and sum(
        isinstance(n,ast.Expr) and isinstance(n.value,ast.Call)
        and ast.unparse(n.value.func)=="result.append"
        for n in loops[0].body)==2,
        "Two-firm date-one loop no longer emits exactly four residual rows")

    src=SOURCE.read_text(encoding="utf-8")
    marker="| .commonPledgeOne => Z.stateTwo.commonPledgeValue -"
    p=src.index(marker)
    source_def=src[p:p+250]
    require("(1 - P.depreciation)" in source_def
            and "d1.nextControls.inflation" in source_def
            and "d1.nextControls.capitalPrice" in source_def,
            "SOURCE commonPledgeOne raw level equation changed")
    lemma=LEAN.read_text(encoding="utf-8")
    begin=lemma.index("noncomputable def sourceCanonicalTwoPledgeLog34")
    end=lemma.index("/-- Strictly positive level",begin)
    code=lemma[begin:end]
    for text in [
        "row = (21 : Fin 33)",
        "Real.log",
        ".stateTwo.commonPledgeValue",
        "sourceDateOneCommonPledgeValuation",
        "sourceReserveSlicePrimitives P h",
    ]:
        require(text in code,"SOURCE second collateral log formula changed: "+text)
    for name in [
        "sourceCanonicalPythonOrder34_row21_eq_source_pledge_level",
        "sourceCanonicalTwoPledgeLog34_row_zero_iff",
        "sourceCanonicalTwoPledgeLog34_eq_zero_iff_original_source_boundary",
    ]:
        require("theorem "+name in lemma,"Expected exact SOURCE lemma missing: "+name)

    report={
        "status":"SOURCE_PYTHON_DATE_ONE_COMMON_PLEDGE_ROW21_FORMULA_AST_MATCH",
        "python_original_engine_sha256":sha(PY),
        "source_economic_model_sha256":sha(SOURCE),
        "source_normalization_candidate_sha256":sha(LEAN),
        "python_function":"binding_period_residual",
        "python_common_pledge_log":expected,
        "python_common_pledge_output_index":21,
        "source_common_pledge_original_row_index":21,
        "source_original_row_kind":"level value J2 - (1-delta)*Pi2*q2",
        "source_candidate_row_kind":"log(J2/((1-delta)*Pi2*q2))",
        "source_pos_domain_required":True,
        "source_lean_theorems_kernel_verified_here":False,
        "cross_language_economic_semantics_proved":False,
        "source_34_root_certified":False,
    }
    OUT.parent.mkdir(parents=True,exist_ok=True)
    OUT.write_text(json.dumps(report,sort_keys=True,indent=2)+"\n",encoding="utf-8")
    print(json.dumps({k:report[k] for k in (
        "status","python_common_pledge_output_index",
        "python_common_pledge_log","source_pos_domain_required"
    )},indent=2))


if __name__=="__main__":
    main()

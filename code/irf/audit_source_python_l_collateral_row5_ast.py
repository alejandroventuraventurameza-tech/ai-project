#!/usr/bin/env python3
"""Strict SOURCE/Python row-5 expression/coordinate correspondence.

Checks the ACTUAL AST of finite_irf.prefix_residual's firm-L
binding branch (not a retyped duplicate), the SOURCE economic
coordinate indexing in EconomicModel.lean, and the four-coordinate
formula written in the corresponding proposed Lean theorem.

This is a reproducible exact SOURCE formula + Python source-code
STRUCTURAL contract. AST equivalence is not a formal cross-language
semantic theorem, and Python uses binary64 math.exp/log.
"""
from __future__ import annotations

import ast
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PY = HERE/"finite_irf.py"
SOURCE = ROOT/"lean/checkpoint/modules/Ventura26LiquidityAllocation/EconomicModel.lean"
LEMMA = ROOT/"lean/candidates/Ventura26LiquidityAllocation/SourceCanonicalPythonCollateralFourCoordinatesCandidate.lean"
OUT = HERE/"output/source_python_l_collateral_row5_ast_contract.json"


def require(ok, message):
    if not ok:
        raise AssertionError(message)


def sha(file):
    return hashlib.sha256(file.read_bytes()).hexdigest()


def find_function(tree, name):
    funcs=[n for n in tree.body if isinstance(n, (ast.FunctionDef,ast.AsyncFunctionDef))
           and n.name==name]
    require(len(funcs)==1,"Expected unique original Python function "+name)
    return funcs[0]


def attr_repr(expr):
    return ast.unparse(expr)


def main():
    tree=ast.parse(PY.read_text(encoding="utf-8"))
    fn=find_function(tree,"prefix_residual")
    require(any(isinstance(n, ast.For)
                and attr_repr(n.target)=="i"
                and attr_repr(n.iter)=="range(2)"
                for n in ast.walk(fn)),
            "Original Python firm H/L iteration changed")
    collateral=[
        n for n in ast.walk(fn)
        if isinstance(n,ast.Assign)
        and any(attr_repr(t)=="collateral" for t in n.targets)
    ]
    require(len(collateral)==1, "Expected one original collateral numerator")
    pledge=attr_repr(collateral[0].value)
    require(pledge=="s.pledge[i] * s.ad * u1[5] * u1[6]",
            "Python face normalization unexpectedly changed: "+pledge)

    branch_candidates=[
        n for n in ast.walk(fn)
        if isinstance(n,ast.If)
        and attr_repr(n.test)=="branch == 'slack' and i == 1"
    ]
    require(len(branch_candidates)==1, "Binding/slack branch guard changed")
    guarded=branch_candidates[0]
    append_expr=[
        n for n in guarded.orelse
        if isinstance(n,ast.Expr) and isinstance(n.value,ast.Call)
        and attr_repr(n.value.func)=="result.append"
    ]
    require(len(append_expr)==2,
            "Expected Euler and collateral binding residual in else branch")
    expression=attr_repr(append_expr[-1].value.args[0])
    require(expression=="math.log(x1[2 + i] / (collateral * x1[i]))",
            "Python binding L logarithmic row changed: "+expression)

    # Under i=1 this is precisely math.log(x1[3] /
    # (s.pledge[1] * s.ad * u1[5] * u1[6] * x1[1])).
    # Compare exactly the SOURCE original coordinate order with
    # the proposed Lean four-coordinate formula.
    source=SOURCE.read_text(encoding="utf-8")
    start=source.index("def localPrefixCoordinatesVector")
    end=source.index("def localPrefixCoordinatesOfVector",start)
    vector=source[start:end]
    expected={1:"stateOne.capitalL",3:"stateOne.firmFaceL",
              28:"controlsOne.inflation",29:"controlsOne.capitalPrice"}
    for idx,label in expected.items():
        pat=r"\|\s*"+str(idx)+r"\s*=>\s*Z\."+re.escape(label)+r"\b"
        require(bool(re.search(pat,vector)),
                "SOURCE log coordinate/index mapping drift "+str(idx))

    lex=LEMMA.read_text(encoding="utf-8")
    a=lex.index("noncomputable def sourcePythonLBindingFourCoordinates")
    b=lex.index("/-- The genuine SOURCE log-collateral row",a)
    definition=lex[a:b]
    terms=[
        "Z0.stateOne.firmFaceL * Real.exp (z 3)",
        "P.pledgeability FirmType.L",
        "(1 - P.depreciation)",
        "Z0.controlsOne.inflation * Real.exp (z 28)",
        "Z0.controlsOne.capitalPrice * Real.exp (z 29)",
        "Z0.stateOne.capitalL * Real.exp (z 1)",
    ]
    require(all(t in definition for t in terms),
            "SOURCE real-arithmetic four-coordinate log formula drifted")
    require("sourceCanonicalPythonOrder34_row5_eq_fourCoordinates" in lex,
            "Expected SOURCE row-5 mathematical identity was deleted")
    require("sourceCanonicalPythonOrder34_row5_only_four_coordinates" in lex,
            "Expected SOURCE row-5 functional sparsity theorem was deleted")

    report={
        "status":"SOURCE_PYTHON_FIRM_L_BINDING_ROW5_AST_FORMULA_AND_INDEX_CONTRACT",
        "lean_economic_model_sha256":sha(SOURCE),
        "python_engine_sha256":sha(PY),
        "source_lean_formula_sha256":sha(LEMMA),
        "actual_python_prefix_function":"prefix_residual",
        "binding_condition":attr_repr(guarded.test),
        "unmodified_binding_branch_collateral_log":expression,
        "unmodified_collateral_denominator":pledge,
        "python_firm_type_i":1,
        "source_four_log_indices":expected,
        "source_formula_string_components_checked":len(terms),
        "all_source_python_formula_index_guards_passed":True,
        "lean_kernel_claim_audited_by_this_python_script":False,
        "strict_cross_language_real_semantics_proved":False,
        "python_float64_exp_log_error_enclosed":False,
        "original_lean_source_34_root_existence_proved":False,
        "scope":"Exact source code shape and coordinates for L binding regime row ONLY.",
    }
    OUT.parent.mkdir(parents=True,exist_ok=True)
    OUT.write_text(json.dumps(report,sort_keys=True,indent=2)+"\n",encoding="utf-8")
    print(json.dumps({k:report[k] for k in (
        "status","actual_python_prefix_function",
        "unmodified_binding_branch_collateral_log",
        "source_four_log_indices","all_source_python_formula_index_guards_passed",
    )},indent=2))


if __name__=="__main__":
    main()

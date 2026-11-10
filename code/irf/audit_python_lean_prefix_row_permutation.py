#!/usr/bin/env python3
"""Audit NAME/ORDER correspondence between Lean SOURCE and reduced Python prefix.

This checks only the indexing of the 33-row prefixes. It does NOT claim
the economic residual functions have been proven symbolically equal.
"""
from __future__ import annotations
import ast
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
LEAN = ROOT / "lean/checkpoint/modules/Ventura26LiquidityAllocation/EconomicModel.lean"
PYTHON = ROOT / "code/irf/finite_irf.py"
OUT = ROOT / "code/irf/output/lean_python_33_row_permutation.json"
STANDARD = {
    "bankEquity": "bank_equity",
    "capitalSupply": "capital_supply",
    "resources": "resources",
    "workerLabor": "worker_labor",
    "householdEuler": "household_euler",
    "nkpc": "nkpc",
    "reserveRateRule": "reserve_rate_rule",
    "reserveQuantityRule": "reserve_quantity_rule",
    "loanPricing": "loan_pricing",
    "depositPricing": "deposit_pricing",
    "bankBalance": "bank_balance",
    "commonPledge": "common_pledge",
}
FIRM = {
    "firmBudget": "firm_budget",
    "firmCapitalEuler": "firm_capital_euler",
    "firmRegime": "firm_regime",
}


def name_from_lean(name):
    firm = re.fullmatch(r"(firmBudget|firmCapitalEuler|firmRegime)(Zero|One)(H|L)", name)
    if firm:
        kind, date, typ = firm.groups()
        return f"{FIRM[kind]}_{0 if date == 'Zero' else 1}_{typ}"
    other = re.fullmatch(
        r"(bankEquity|capitalSupply|resources|workerLabor|householdEuler|"
        r"nkpc|reserveRateRule|reserveQuantityRule|loanPricing|depositPricing|"
        r"bankBalance|commonPledge)(Zero|One)", name
    )
    if other:
        kind, date = other.groups()
        return f"{STANDARD[kind]}_{0 if date == 'Zero' else 1}"
    raise AssertionError(f"Unrecognized literal SOURCE prefix equation: {name}")


def main():
    src = LEAN.read_text(encoding="utf-8")
    start = src.index("def localPrefixEquationOfIndex : Fin 33")
    end = src.index("noncomputable def localReducedPrefixResidualVector", start)
    block = src[start:end]
    assignments = re.findall(r"^\s*\|\s*(\d+)\s*=>\s*\.(\w+)\s*$", block, re.M)
    if len(assignments) != 33:
        raise AssertionError(f"Expected 33 explicit Lean rows, got {len(assignments)}")
    if [int(j) for j, _ in assignments] != list(range(33)):
        raise AssertionError("SOURCE 33-index enumeration changed")
    lean_names = [name for _, name in assignments]
    lean_labels = [name_from_lean(s) for s in lean_names]
    # Also ensure all named rows appear as branches in the real residual
    # function and not merely in the index enumeration.
    rstart = src.index("noncomputable def localReducedPrefixResidual\n")
    rend = src.index("def LocalReducedPrefixEquationsHold", rstart)
    body = src[rstart:rend]
    for tag in lean_names:
        if not re.search(r"^\s*\|\s*\." + re.escape(tag) + r"\s*=>", body, re.M):
            raise AssertionError(f"Missing actual source residual arm {tag}")

    parsed = ast.parse(PYTHON.read_text(encoding="utf-8"))
    values = [
        ast.literal_eval(stmt.value)
        for stmt in parsed.body
        if isinstance(stmt, ast.Assign)
        and len(stmt.targets) == 1
        and isinstance(stmt.targets[0], ast.Name)
        and stmt.targets[0].id == "PREFIX_ROW_NAMES"
    ]
    if len(values) != 1:
        raise AssertionError("Expected one original Python row-label constant")
    py_labels = values[0]
    if len(py_labels) != 33 or len(set(py_labels)) != 33:
        raise AssertionError("Python 33-row names missing or duplicated")
    if sorted(lean_labels) != sorted(py_labels):
        raise AssertionError(
            f"Python and Lean have different named rows: "
            f"Python-only {sorted(set(py_labels)-set(lean_labels))}, "
            f"Lean-only {sorted(set(lean_labels)-set(py_labels))}"
        )
    lean_to_python = [py_labels.index(label) for label in lean_labels]
    python_to_lean = [lean_labels.index(label) for label in py_labels]
    if sorted(lean_to_python) != list(range(33)):
        raise AssertionError("33-row permutation is not bijective")
    if any(python_to_lean[lean_to_python[i]] != i for i in range(33)):
        raise AssertionError("Inverse permutation audit failed")
    # Known nontrivial firm-order difference must remain explicit.
    if lean_to_python[:6] != [0, 3, 1, 4, 2, 5]:
        raise AssertionError("Date-zero firm order changed unexpectedly")
    if lean_to_python[17:22] != [17, 19, 18, 20, 21]:
        raise AssertionError("Date-one firm order changed unexpectedly")
    report = {
        "status": "SYNTACTIC_33_ROW_PERMUTATION_VERIFIED_NOT_SEMANTIC_EQUALITY",
        "source_sha256": {
            str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in (LEAN, PYTHON)
        },
        "source_row_count": 33,
        "source_to_python_permutation": lean_to_python,
        "python_to_source_permutation": python_to_lean,
        "rows": [
            {
                "source_index": i,
                "source_constructor": lean_names[i],
                "python_index": lean_to_python[i],
                "python_label": lean_labels[i],
                "semantic_equality_verified": False,
            }
            for i in range(33)
        ],
        "pending": [
            "Economic residual equality row by row under positivity and units",
            "State and control coordinate alignment",
            "Source 34th normalized funding dual, KKT branch, and controls",
            "Nonlinear SOURCE Jacobian, infinite continuation and TVC",
        ],
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({
        "status": report["status"],
        "count": len(report["rows"]),
        "source_to_python_first_six": lean_to_python[:6],
        "source_to_python_date_one_first_five": lean_to_python[17:22],
        "output": str(OUT),
    }, indent=2))


if __name__ == "__main__":
    main()

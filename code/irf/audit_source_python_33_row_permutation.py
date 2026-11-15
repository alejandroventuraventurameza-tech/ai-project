#!/usr/bin/env python3
"""Guard original SOURCE/Python 33-residual equation ordering.

The original Lean EconomicModel orders firm equations by equation class
(H budgets, L budgets, H Euler, L Euler, H regime, L regime).
The original Python finite_irf orders first-date firm equations by
firm type (H budget/Euler/regime, then L budget/Euler/regime), and
second-date firm equations H budget/Euler then L budget/Euler.

This is a row permutation, not evidence of economic residual equality.
Detect unexpected row-layout drift and expose both permutations for
future Jacobian audits; no numerical root is certified by this script.
"""

from __future__ import annotations

import ast
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
LEAN = ROOT / "lean/checkpoint/modules/Ventura26LiquidityAllocation/EconomicModel.lean"
PYTHON = HERE / "finite_irf.py"

SOURCE_ORDER = (
    "firmBudgetZeroH", "firmBudgetZeroL", "firmCapitalEulerZeroH",
    "firmCapitalEulerZeroL", "firmRegimeZeroH", "firmRegimeZeroL",
    "bankEquityZero", "capitalSupplyZero", "resourcesZero",
    "workerLaborZero", "householdEulerZero", "nkpcZero",
    "reserveRateRuleZero", "reserveQuantityRuleZero",
    "loanPricingZero", "depositPricingZero", "bankBalanceZero",
    "firmBudgetOneH", "firmBudgetOneL",
    "firmCapitalEulerOneH", "firmCapitalEulerOneL",
    "commonPledgeOne", "bankEquityOne", "capitalSupplyOne",
    "resourcesOne", "workerLaborOne", "householdEulerOne",
    "nkpcOne", "reserveRateRuleOne", "reserveQuantityRuleOne",
    "loanPricingOne", "depositPricingOne", "bankBalanceOne",
)

TRANSLATION = {
    "firmBudgetZeroH": "firm_budget_0_H",
    "firmBudgetZeroL": "firm_budget_0_L",
    "firmCapitalEulerZeroH": "firm_capital_euler_0_H",
    "firmCapitalEulerZeroL": "firm_capital_euler_0_L",
    "firmRegimeZeroH": "firm_regime_0_H",
    "firmRegimeZeroL": "firm_regime_0_L",
    "firmBudgetOneH": "firm_budget_1_H",
    "firmBudgetOneL": "firm_budget_1_L",
    "firmCapitalEulerOneH": "firm_capital_euler_1_H",
    "firmCapitalEulerOneL": "firm_capital_euler_1_L",
}
for stem, py_stem in (
    ("bankEquity", "bank_equity"),
    ("capitalSupply", "capital_supply"),
    ("resources", "resources"),
    ("workerLabor", "worker_labor"),
    ("householdEuler", "household_euler"),
    ("nkpc", "nkpc"),
    ("reserveRateRule", "reserve_rate_rule"),
    ("reserveQuantityRule", "reserve_quantity_rule"),
    ("loanPricing", "loan_pricing"),
    ("depositPricing", "deposit_pricing"),
    ("bankBalance", "bank_balance"),
):
    TRANSLATION[stem + "Zero"] = py_stem + "_0"
    TRANSLATION[stem + "One"] = py_stem + "_1"
TRANSLATION["commonPledgeOne"] = "common_pledge_1"


def source_labels(text: str) -> list[str]:
    match = re.search(
        r"def localPrefixEquationOfIndex\s*:\s*Fin 33\s*→\s*LocalPrefixEquation"
        r"(.*?)\n\s*noncomputable def localReducedPrefixResidualVector",
        text,
        re.S,
    )
    assert match, "SOURCE equation-index definition not found"
    entries = re.findall(r"^\s*\|\s*(\d+)\s*=>\s*\.(\w+)\s*$",
                         match.group(1), re.M)
    indexed = [(int(i), label) for i, label in entries]
    assert indexed == list(enumerate(SOURCE_ORDER)), (
        "SOURCE 33-row dispatch drift", indexed
    )
    return [label for _, label in indexed]


def python_labels(text: str) -> list[str]:
    tree = ast.parse(text)
    for stmt in tree.body:
        if isinstance(stmt, ast.Assign) and any(
            isinstance(target, ast.Name) and target.id == "PREFIX_ROW_NAMES"
            for target in stmt.targets
        ):
            labels = ast.literal_eval(stmt.value)
            assert len(labels) == 33 and len(set(labels)) == 33
            return labels
    raise AssertionError("Python PREFIX_ROW_NAMES not found")


def audit() -> dict:
    source = source_labels(LEAN.read_text(encoding="utf-8"))
    python = python_labels(PYTHON.read_text(encoding="utf-8"))
    named = [TRANSLATION[label] for label in source]
    assert len(named) == len(set(named)) == len(python) == 33
    assert set(named) == set(python), "Economic equation names do not match"
    to_python = [python.index(label) for label in named]
    to_source = [named.index(label) for label in python]
    assert sorted(to_python) == sorted(to_source) == list(range(33))
    assert all(to_source[to_python[i]] == i for i in range(33))
    assert to_python == [
        0, 3, 1, 4, 2, 5,
        *range(6, 17),
        17, 19, 18, 20,
        *range(21, 33),
    ], "Original Python firm-equation ordering changed"
    assert all(to_python[i] == i for i in
               (12, 13, 14, 15, 16, 28, 29, 30, 31, 32))
    return {
        "kind": "equation_row_layout_only_not_residual_equivalence",
        "equations": 33,
        "source_to_python": to_python,
        "python_to_source": to_source,
        "moved_source_rows": [
            {"source": i, "python": j, "label": named[i]}
            for i, j in enumerate(to_python) if i != j
        ],
        "bank_rows_identity": True,
        "source_path": str(LEAN.relative_to(ROOT)),
        "python_path": str(PYTHON.relative_to(ROOT)),
    }


if __name__ == "__main__":
    print(json.dumps(audit(), indent=2))

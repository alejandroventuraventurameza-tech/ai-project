#!/usr/bin/env python3
"""Check the internal allocation-loss differential identity in the paper.

Reads the derivatives printed in the historical main technical dossier,
without silently replacing them with hand-picked floating point numbers.
This validates a reported table consistency, NOT solution of the economic
system, an empirical identification, nor a full Lean proof.
"""
from __future__ import annotations

from decimal import Decimal, getcontext
from pathlib import Path
import re
import json

getcontext().prec = 50
PAPER = Path(__file__).resolve().parent.parent / "paper" / "paper.tex"
source = PAPER.read_text(encoding="utf-8")
PATTERNS = {
    "capital_ratio": re.compile(
        r"(?m)^\s*(?P<branch>[SB]): \$\\log\(k_\{H1\}/k_\{L1\}\)\$\s*&\s*"
        r"\$(?P<value>-?\d+\.\d+)\$"
    ),
    "loss": re.compile(
        r"(?m)^\s*(?P<branch>[SB]): \$\\mathscr L_1\$\s*&\s*"
        r"\$(?P<value>-?\d+\.\d+)\$"
    ),
}
values: dict[str, dict[str, Decimal]] = {}
for name, pattern in PATTERNS.items():
    matches = list(pattern.finditer(source))
    assert len(matches) == 2, (
        f"Expected two source table entries for {name}, found {len(matches)}"
    )
    by_branch = {m.group("branch"): Decimal(m.group("value")) for m in matches}
    assert set(by_branch) == {"S", "B"}, f"{name}: repeated or absent branch"
    values[name] = by_branch

rate_shock = Decimal("-0.00001")
predicted_factor = {}
responses = {}
for branch in ("S", "B"):
    dk = values["capital_ratio"][branch]
    dl = values["loss"][branch]
    assert dk != 0, f"Zero relative-capital derivative in {branch}"
    predicted_factor[branch] = dl / dk
    responses[branch] = {
        "delta_log_kH_over_kL": dk * rate_shock,
        "delta_loss": dl * rate_shock,
    }

assert predicted_factor["S"] < 0 and predicted_factor["B"] < 0, (
    "The paper's output-share > capital-share condition is inconsistent "
    "with the reported derivatives."
)
# These are printed to nine decimal places, so require only that both
# give the same algebraic coefficient within reported rounding error.
difference = abs(predicted_factor["S"] - predicted_factor["B"])
scale = max(abs(predicted_factor["S"]), abs(predicted_factor["B"]))
relative = difference / scale
assert relative < Decimal("0.000001"), (
    f"Inconsistent loss-to-capital derivative ratio: relative={relative}"
)
assert responses["S"]["delta_log_kH_over_kL"] > 0
assert responses["S"]["delta_loss"] < 0
assert responses["B"]["delta_log_kH_over_kL"] < 0
assert responses["B"]["delta_loss"] > 0

print(json.dumps({
    "result": "PASS_PRINTED_TABLE_ALGEBRA_ONLY",
    "source": "paper/paper.tex: historical 4.3 derivative table",
    "shock": str(rate_shock),
    "factor_alpha_kappa_minus_omega_S": str(predicted_factor["S"]),
    "factor_alpha_kappa_minus_omega_B": str(predicted_factor["B"]),
    "relative_difference": str(relative),
    "S": {k: str(v) for k, v in responses["S"].items()},
    "B": {k: str(v) for k, v in responses["B"].items()},
    "interpretation": (
        "Checks only consistency of printed nonlinear-system derivatives "
        "with one common allocation-loss identity; does not reproduce "
        "the solver, certify the dynamic model, or establish welfare."
    ),
}, ensure_ascii=False, indent=2))

#!/usr/bin/env python3
"""Audit exact Lean finite robust majorant tables against pinned decimal F0.

Input is the literal decimal-string matrix, converted with Decimal->Fraction.
All calculations and assertions are rational/integer. Never silently rewrite
the Lean certificate; fail on any mismatch, including source hash/entry count.

The Python audit is INDEPENDENT replication. The corresponding row-norm and
majorant inequalities must *also* be checked by the Lean kernel.
"""
from __future__ import annotations
import hashlib
import re
from fractions import Fraction
from pathlib import Path
from decimal import Decimal
from exact_linear_tail_power_certificate import (
    SOURCE, EXPECTED_SOURCE_SHA256, BLOCK, SIZE, identity, infinity_norm,
    matmul, read_rational_matrix,
)

ROOT = Path(__file__).resolve().parents[2]
LEAN = ROOT / "lean/current/CurrentCompactRobustFiniteCertificate.lean"
SCALE = 10 ** 12
GAP = 10 ** 4


def ceil_div(a: int, b: int) -> int:
    assert b > 0
    return -((-a) // b)


def source_tables() -> tuple[list[int], list[int]]:
    digest = hashlib.sha256(SOURCE.read_bytes()).hexdigest()
    if digest != EXPECTED_SOURCE_SHA256:
        raise AssertionError(f"F0 SHA256 mismatch: {digest}")
    F0 = read_rational_matrix(SOURCE)
    if len(F0) != SIZE or any(len(x) != SIZE for x in F0):
        raise AssertionError("Source matrix dimensions changed")
    powers = identity()
    sharp = []
    robust = []
    for n in range(BLOCK + 1):
        rational_row_max = infinity_norm(powers)
        # strict outward bound, including exact multiples of 10^-12
        norm_num = (rational_row_max.numerator * SCALE) // rational_row_max.denominator + 1
        sharp.append(norm_num)
        if n == 0:
            robust.append(SCALE)
        else:
            conv = sum((sharp[j] * robust[n - 1 - j] for j in range(n)), 0)
            robust.append(norm_num + ceil_div(conv, GAP * SCALE))
        if n < BLOCK:
            powers = matmul(powers, F0)
    assert len(sharp) == len(robust) == 49
    assert robust[0] == SCALE
    for n in range(1, 49):
        lhs = GAP * SCALE * robust[n]
        rhs = GAP * SCALE * sharp[n] + sum(
            (sharp[j] * robust[n - 1 - j] for j in range(n)), 0
        )
        if lhs < rhs:
            raise AssertionError(f"Recurrence fails at n={n}")
    if not 50 * robust[48] < 49 * SCALE:
        raise AssertionError("Robust contraction fails")
    if not all(x < 7 * SCALE for x in robust[:48]):
        raise AssertionError("Robust transient fails")
    return sharp, robust


def parsed_array(source: str, start_tag: str, stop_tag: str) -> list[int]:
    try:
        code = source.split(start_tag, 1)[1].split(stop_tag, 1)[0]
        payload = code.split("![", 1)[1].split("]", 1)[0]
    except IndexError as exc:
        raise AssertionError(f"Could not parse table {start_tag}") from exc
    values = [int(s) for s in re.findall(r"\b\d+\b", payload)]
    if len(values) != 49:
        raise AssertionError(f"Table {start_tag} has {len(values)} cells, not 49")
    return values


def main() -> None:
    sharp, robust = source_tables()
    lean = LEAN.read_text(encoding="utf-8")
    m = parsed_array(lean, "-- BEGIN NORM_UPPER_49", "-- END NORM_UPPER_49")
    a = parsed_array(lean, "-- BEGIN ROBUST_UPPER_49", "-- END ROBUST_UPPER_49")
    if sharp != m:
        raise AssertionError("Lean norm table differs from exact source computation")
    if robust != a:
        raise AssertionError("Lean majorant table differs from exact rational convolution")
    print("ROBUST_TABLE_EXACT_SOURCE_MATCH: all 98 integers, 49 sharp row norms")
    print(f"robust_upper_48={robust[48]}/{SCALE}")
    print(f"robust_transient_max={max(robust[:48])}/{SCALE} at n={robust.index(max(robust[:48]))}")
    print("PYTHON_AUDIT_SUCCESS: Lean kernel decision is checked independently")


if __name__ == "__main__":
    main()

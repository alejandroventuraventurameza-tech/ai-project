#!/usr/bin/env python3
"""An EXACT rational power-norm certificate for the pinned decimal 6x6 F0.

All input entries are interpreted as rational numbers equal to the decimal
STRINGS in inputs/rational_preconditioners.json. Matrix multiplication,
row sums, threshold comparisons, and acceptance use fractions.Fraction
ONLY. The displayed decimals are outward-rounded *after* acceptance.

This proves a statement about the pinned, rationalized LOCAL-LINEAR GRAPH,
not the original DSGE's exact Jacobian nor any nonlinear infinite path.
"""
from __future__ import annotations

import hashlib
import json
from decimal import Decimal
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
SOURCE = HERE / "inputs" / "rational_preconditioners.json"
OUT = HERE / "output" / "exact_linear_tail_power_certificate.json"
EXPECTED_SOURCE_SHA256 = (
    "d0cef14050de9f4725e51e5cd28b1ea77e33733dfb2c78d2e38a193200337e94"
)

SIZE = 6
BLOCK = 48
Q_BOUND = Fraction(24, 25)  # strict upper bound on ||F0^48||_infinity
M_BOUND = Fraction(61, 10)  # strict upper bound on powers 0,...,47
DELTA_BOUND = Fraction(1, 10000)  # allowed ||A-F0||_infinity
ROBUST_Q = Fraction(49, 50)     # strict 48-step norm bound for ANY nearby A
ROBUST_M = Fraction(7)          # bound on the first 48 powers of ANY nearby A


def read_rational_matrix(path):
    obj = json.loads(path.read_text(encoding="utf-8"))
    rows = obj["F0"]
    if len(rows) != SIZE or any(len(row) != SIZE for row in rows):
        raise AssertionError("Pinned 6x6 local transition matrix changed")
    out = []
    for row in rows:
        current = []
        for value in row:
            if not isinstance(value, str):
                raise AssertionError("F0 must be supplied as decimal strings")
            frac = Fraction(Decimal(value))
            current.append(frac)
        out.append(tuple(current))
    return tuple(out)


def identity():
    return tuple(
        tuple(Fraction(int(i == j)) for j in range(SIZE))
        for i in range(SIZE)
    )


def matmul(a, b):
    return tuple(
        tuple(sum((a[i][k] * b[k][j] for k in range(SIZE)),
                  Fraction(0)) for j in range(SIZE))
        for i in range(SIZE)
    )


def infinity_norm(a):
    return max(sum((abs(x) for x in row), Fraction(0)) for row in a)


def ceil_div(numer, denom):
    if denom <= 0:
        raise AssertionError("Positive denominator expected")
    return -((-numer) // denom)


def directed_floor(x, decimal_places=12):
    scale = 10 ** decimal_places
    n = (x.numerator * scale) // x.denominator
    return f"{n // scale}.{n % scale:0{decimal_places}d}"


def directed_ceil(x, decimal_places=12):
    scale = 10 ** decimal_places
    n = ceil_div(x.numerator * scale, x.denominator)
    return f"{n // scale}.{n % scale:0{decimal_places}d}"


def main():
    source_hash = hashlib.sha256(SOURCE.read_bytes()).hexdigest()
    if source_hash != EXPECTED_SOURCE_SHA256:
        raise AssertionError("Pinned decimal F0 source hash changed")
    f0 = read_rational_matrix(SOURCE)
    powers = identity()
    entries = [{
        "n": 0,
        "norm_infinity_lower_12dp": directed_floor(Fraction(1)),
        "norm_infinity_upper_12dp": directed_ceil(Fraction(1)),
    }]
    transient_bound = Fraction(1)
    transient_at = 0
    seventh = None
    exact_power_norms = [Fraction(1)]
    for n in range(1, BLOCK + 1):
        powers = matmul(powers, f0)
        row_norm = infinity_norm(powers)
        exact_power_norms.append(row_norm)
        if n < BLOCK and row_norm > transient_bound:
            transient_bound = row_norm
            transient_at = n
        if n == 7:
            seventh = row_norm
        entries.append({
            "n": n,
            "norm_infinity_lower_12dp": directed_floor(row_norm),
            "norm_infinity_upper_12dp": directed_ceil(row_norm),
        })
    contraction = infinity_norm(powers)
    # Every acceptance check below uses EXACT rational arithmetic,
    # including decimal input conversion, powers, and comparison.
    if not contraction < Q_BOUND:
        raise AssertionError("Exact 48-step contraction bound failed")
    if not transient_bound < M_BOUND:
        raise AssertionError("Exact transient bound failed")
    if not seventh > Fraction(6):
        raise AssertionError("Expected large transient amplification missing")
    if transient_at != 7:
        raise AssertionError("Expected transient peak at power seven changed")
    if len(entries) != BLOCK + 1:
        raise AssertionError("Incomplete power certificate")

    # Stability is ROBUST to a small but UNPROVED source/decimal gap.
    # For any real matrix A with ||A-F0||_inf <= DELTA_BOUND, the
    # telescoping identity yields
    # A^n = F0^n + sum_(j=0)^(n-1) F0^(n-1-j)*(A-F0)*A^j.
    # Define a_0=1 and
    # a_n=||F0^n|| + delta*sum_(j=0)^(n-1)||F0^(n-1-j)||*a_j.
    # Induction and the operator norm inequality show ||A^n||<=a_n.
    # All a_n are FRACTIONS; no floating-point acceptance is involved.
    a = [Fraction(1)]
    for n in range(1, BLOCK + 1):
        convolution = sum((
            exact_power_norms[n - 1 - j]*a[j]
            for j in range(n)
        ), Fraction(0))
        a.append(exact_power_norms[n] + DELTA_BOUND*convolution)
    robust_transient = max(a[:BLOCK])
    robust_48 = a[BLOCK]
    if not robust_48 < ROBUST_Q:
        raise AssertionError("Exact robust 48-step matrix bound failed")
    if not robust_transient < ROBUST_M:
        raise AssertionError("Exact robust transient bound failed")

    # A separate strict bound on the sum of powers follows from
    # ||F^(48m+r)|| <= ||F^48||^m ||F^r||, for 0<=r<48.
    # The finite exact sum below is also provided, but the theorem is
    # proved by submultiplicativity rather than by floating-point fitting.
    s_power = Fraction(0)
    # Recover exactly the norm sums while preserving the existing loop
    # output without needing huge rational entries in the JSON.
    p = identity()
    for n in range(BLOCK):
        s_power += infinity_norm(p)
        p = matmul(p, f0)
    summability_upper = s_power / (Fraction(1) - contraction)
    gross_upper = BLOCK * M_BOUND / (Fraction(1) - Q_BOUND)
    if not (summability_upper < gross_upper):
        raise AssertionError("Infinite series coarse upper bound failed")
    payload = {
        "status": "EXACT_RATIONAL_LINEAR_GRAPH_POWER_CERTIFICATE",
        "scope": (
            "decimal literals of pinned 6x6 F0 interpreted as exact rationals; "
            "NOT the exact source DSGE nor nonlinear continuation"
        ),
        "source_sha256": source_hash,
        "block_power": BLOCK,
        "strict_contraction_norm_bound": "24/25",
        "norm_F0_48_lower_12dp": directed_floor(contraction),
        "norm_F0_48_upper_12dp": directed_ceil(contraction),
        "strict_transient_norm_bound": "61/10",
        "max_norm_power_before_48": transient_at,
        "max_norm_lower_12dp": directed_floor(transient_bound),
        "max_norm_upper_12dp": directed_ceil(transient_bound),
        "norm_F0_7_exceeds_exactly": "6",
        "source_gap_tolerance_for_ANY_real_6x6_matrix": "1/10000",
        "robust_power_48_majorant_upper_12dp": directed_ceil(robust_48),
        "robust_transient_majorant_upper_12dp": directed_ceil(robust_transient),
        "robust_strict_48_step_bound": "49/50",
        "robust_strict_max_0_to_47_bound": "7",
        "robust_statement": (
            "For ANY real 6x6 A such that ||A-F0||_infinity<=1/10000, "
            "||A^(48m+r)x||_infinity < "
            "7*(49/50)^m*||x||_infinity for each 0<=r<48 and x != 0. "
            "The SOURCE Jacobian has NOT been proved to satisfy this bound."
        ),
        "infinite_sum_of_norms_upper_12dp": directed_ceil(summability_upper),
        "coarse_summability_bound": "48*(61/10)/(1-24/25)=7320",
        "claim": (
            "For all k>=0 and x in R^6, "
            "||F0^k x||_infty <= (61/10)*(24/25)^floor(k/48)*||x||_infty. "
            "Consequently the local LINEAR graph series is absolutely "
            "summable with total coefficient <7320."
        ),
        "norms_0_to_48": entries,
        "not_established": [
            "the exact 6x6 source derivative equals this decimal matrix",
            "a stable nonlinear invariant manifold or a contraction radius",
            "S/B infinite-horizon equilibrium existence or uniqueness",
            "economic TVC and bank continuation optimality",
            "same infinite-horizon limit under distinct terminal closures",
        ],
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(json.dumps({
        "status": payload["status"],
        "source_sha256": payload["source_sha256"],
        "n": BLOCK,
        "norm_F0_48_upper_12dp": payload["norm_F0_48_upper_12dp"],
        "max_norm_before_48_upper_12dp": payload[
            "max_norm_upper_12dp"
        ],
        "robust_48_majorant_upper_12dp": payload[
            "robust_power_48_majorant_upper_12dp"
        ],
        "robust_norm_tolerance": payload[
            "source_gap_tolerance_for_ANY_real_6x6_matrix"
        ],
        "transient_max_at_n": transient_at,
        "infinite_sum_of_norms_upper_12dp": payload[
            "infinite_sum_of_norms_upper_12dp"
        ],
        "report": str(OUT),
    }, indent=2))


if __name__ == "__main__":
    main()

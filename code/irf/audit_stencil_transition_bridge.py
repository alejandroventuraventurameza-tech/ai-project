#!/usr/bin/env python3
"""Exact-rational transfer of the V0-M interval STENCIL F-error into IRF axes.

This is a CONDITIONAL transfer of a pinned directed-interval certificate:
  || R^(-1) (F_star - F0) R ||_infinity <= eps_weighted
implies, in the six original compact-state coordinates,
  ||F_star-F0||_infinity <= ||R||_infinity ||R^(-1)||_infinity eps_weighted.

The verifier uses the V0-M Rs basis, NOT the nearly equal IRF Rs basis.
F0/P0/Rv are checked exactly equal across both preconditioner files.
All matrix algebra and comparisons in THIS audit use fractions.Fraction.

This does NOT bridge the audited hand-linearization stencil to the
34 original EconomicModel.lean/SOURCE equilibrium equations; does not
prove a nonlinear C1 state map, a TVC, or any economic equilibrium.
"""
from __future__ import annotations

import hashlib
import json
from decimal import Decimal
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
IRF = ROOT / "code" / "irf" / "inputs" / "rational_preconditioners.json"
BASE = ROOT / "code" / "v0m" / "cotas_2026_10_15"
V0M = BASE / "rational_preconditioners.json"
BOUNDS = BASE / "verified_linear_bounds.json"
PRODUCER = BASE / "verified_linear_operator.py"
OUT = ROOT / "code" / "irf" / "output" / "stencil_transition_bridge.json"

# Pin the exact contents and the provenance of the directed bounds. A change
# must trigger manual re-auditing, not be treated as a cosmetic update.
EXPECTED_BLOBS = {
    IRF: "bef34b844836d01848b87145f1565ff84bd5071a",
    V0M: "74a44037f46a5f865c8123e6d059ef8342e46a19",
    BOUNDS: "ca7c2f8a49814fca0e3c6901b5ed22b506710662",
    PRODUCER: "aae0e13d86d6627216a5e53716a0f762b05b78c9",
}
N = 6
TARGET = Fraction(1, 10000)


def git_blob_sha1(path):
    payload = path.read_bytes()
    return hashlib.sha1(
        b"blob " + str(len(payload)).encode("ascii") + b"\0" + payload
    ).hexdigest()


def rational(value):
    if not isinstance(value, str):
        raise AssertionError("All certificate decimal coefficients must be strings")
    return Fraction(Decimal(value))


def matrix(rows, nrows, ncols):
    if len(rows) != nrows or any(len(row) != ncols for row in rows):
        raise AssertionError("Pinned rectangular matrix dimension changed")
    return [[rational(cell) for cell in row] for row in rows]


def inverse_rational(a):
    """Six-by-six Gauss-Jordan inverse with integer/rational arithmetic."""
    m = len(a)
    work = [
        list(a[i]) + [Fraction(int(i == j)) for j in range(m)]
        for i in range(m)
    ]
    for j in range(m):
        pivot = next((i for i in range(j, m) if work[i][j] != 0), None)
        if pivot is None:
            raise AssertionError("V0-M verified change-of-basis matrix singular")
        work[j], work[pivot] = work[pivot], work[j]
        p = work[j][j]
        work[j] = [x / p for x in work[j]]
        for i in range(m):
            if i == j:
                continue
            factor = work[i][j]
            if factor != 0:
                work[i] = [
                    work[i][k] - factor * work[j][k]
                    for k in range(2 * m)
                ]
    result = [row[m:] for row in work]
    for i in range(m):
        for j in range(m):
            observed = sum((a[i][k] * result[k][j]
                            for k in range(m)), Fraction(0))
            if observed != Fraction(int(i == j)):
                raise AssertionError("Exact rational inverse identity fails")
    return result


def norm_inf(m):
    return max(
        sum((abs(x) for x in row), Fraction(0))
        for row in m
    )


def directed_upper(q, places=15):
    scale = 10 ** places
    n = -((-q.numerator * scale) // q.denominator)
    return f"{n // scale}.{n % scale:0{places}d}"


def main():
    blobs = {}
    for p, expected in EXPECTED_BLOBS.items():
        observed = git_blob_sha1(p)
        blobs[str(p.relative_to(ROOT))] = observed
        if observed != expected:
            raise AssertionError(
                f"Pinned SOURCE or interval verifier input changed: {p}: "
                f"expected {expected}, got {observed}"
            )

    from_irf = json.loads(IRF.read_text(encoding="utf-8"))
    from_v0m = json.loads(V0M.read_text(encoding="utf-8"))
    for name, dims in (
        ("P0", (16, 6)), ("F0", (6, 6)), ("Rv", (10, 10)),
    ):
        left = matrix(from_irf[name], *dims)
        right = matrix(from_v0m[name], *dims)
        if left != right:
            raise AssertionError(
                f"IRF and verified hand-stencil {name} differ exactly"
            )
    v0m_rs = matrix(from_v0m["Rs"], N, N)
    irf_rs = matrix(from_irf["Rs"], N, N)
    different_rs = sum(
        irf_rs[i][j] != v0m_rs[i][j]
        for i in range(N) for j in range(N)
    )
    if different_rs != 11:
        raise AssertionError("Expected known 11-entry Rs rounding drift changed")
    rs_drift = norm_inf([
        [irf_rs[i][j] - v0m_rs[i][j] for j in range(N)]
        for i in range(N)
    ])
    # The verifier derives 'f_error' with the V0-M Rs and Rsi=Rs^(-1);
    # using the IRF Rs here without transport would be mathematically wrong.
    producer = PRODUCER.read_text(encoding="utf-8")
    for anchor in (
        "Rsi=solve(Rs,eye(6))",
        "Fs=Rsi@F0@Rs",
        "jv=upper_norm(Rsi@Jx@defect@Rs)",
        "f_error=sum_up([jv,product_up(coupling,p_error)])",
        "'exact_transition_coordinate_error_upper':str(f_error)",
    ):
        if anchor not in producer:
            raise AssertionError(
                f"Directed certificate's basis/meaning changed: {anchor}"
            )
    certificate = json.loads(BOUNDS.read_text(encoding="utf-8"))
    if certificate.get("precision_decimal_digits") != 80:
        raise AssertionError("Directed verification precision changed")
    eps = rational(certificate["exact_transition_coordinate_error_upper"])
    if eps <= 0:
        raise AssertionError("Expected strictly positive directed bound")
    rs_inverse = inverse_rational(v0m_rs)
    norm_rs = norm_inf(v0m_rs)
    norm_inverse = norm_inf(rs_inverse)
    cond = norm_rs * norm_inverse
    coordinate_gap_bound = cond * eps
    if not coordinate_gap_bound < TARGET:
        raise AssertionError(
            "Verified stencil F-error does not enter robust 1e-4 norm ball"
        )
    if not norm_rs > 1 or not norm_inverse > 1:
        raise AssertionError("Unexpected verified change-of-basis conditioning")
    payload = {
        "status": "EXACT_RATIONAL_TRANSPORT_OF_PINNED_DIRECTED_STENCIL_BOUND",
        "source_blob_sha1": blobs,
        "stencil_80_digit_cert_scope": certificate.get("scope"),
        "pinning_notice": (
            "The producer's 80-digit certificate is treated as an external "
            "directed-interval premise; this script independently transports "
            "it using exact rational arithmetic and verifies inputs/hashes."
        ),
        "irf_P0_F0_Rv_are_identical_to_v0m_source_literals": True,
        "verified_Rs_differs_from_IRF_Rs_in_entries": different_rs,
        "Rs_maximum_row_rounding_drift_upper_15dp": directed_upper(rs_drift),
        "verified_Rs_infinity_norm_upper_15dp": directed_upper(norm_rs),
        "verified_Rs_rational_inverse_norm_upper_15dp": directed_upper(norm_inverse),
        "change_of_basis_condition_upper_15dp": directed_upper(cond),
        "weighted_Fstar_minus_F0_upper_from_directed_certificate": (
            certificate["exact_transition_coordinate_error_upper"]
        ),
        "unweighted_six_state_Fstar_minus_F0_upper_15dp": (
            directed_upper(coordinate_gap_bound)
        ),
        "norm_gap_target": "1/10000",
        "strict_gap_gate_passes": True,
        "linear_conditional_consequence": (
            "IF the directed hand-stencil certificate correctly encloses "
            "the exact 16-row linear operator F_star in the pinned V0-M "
            "Rs coordinates, then in the ORIGINAL compact-state axes "
            "||F_star-F0||_infinity<1e-4. Therefore the separate robust "
            "48-step certificate implies ||F_star^48||_infinity<49/50."
        ),
        "not_established": [
            "SOURCE EconomicModel.lean 34-row Jacobian equals the hand stencil",
            "SOURCE six-state implicit transition exists globally or locally",
            "nonlinear graph and its invariant domain/radius",
            "bank optimality or economic transversality",
            "infinite S/B competitive equilibrium or long-run growth",
        ],
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(
        json.dumps(payload, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    print(json.dumps({
        "status": payload["status"],
        "verified_Rs_condition_upper_15dp": (
            payload["change_of_basis_condition_upper_15dp"]
        ),
        "unweighted_gap_upper_15dp": (
            payload["unweighted_six_state_Fstar_minus_F0_upper_15dp"]
        ),
        "source_operator_equivalence": "PENDING",
        "output": str(OUT),
    }, indent=2))


if __name__ == "__main__":
    main()

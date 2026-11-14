#!/usr/bin/env python3
"""Conditional, exact-rational 34x34 quantitative IFT/Banach audit.

Augments the 33-row modified binding-prefix F(z,s,v_R,v_M,v_rho,v_Delta)
with the normalized L funding dual mu(z), freeing v_R as a 34th unknown.
This checks arithmetic of Python-generated enclosures only. It does NOT
certify equivalence to Lean's literal economics, exact center normalization,
full optimality, or an infinite-horizon competitive equilibrium.
"""
import argparse
import hashlib
import json
import sys
from fractions import Fraction as Q
from pathlib import Path
from check_quantitative_ift import rat, box, plus, scale, magnitude, fraction

N = 33
DIM = 34
ROW_MAP = [0, 3, 1, 4, 2, 5, *range(6, 17), 17, 19, 18, 20, *range(21, 33)]
PROVENANCE_FLAGS = (
    "source_Lean_semantic_identity_proved",
    "uniform_box_contains_Lean_actual_derivatives_proved",
    "exact_zero_center_proved",
    "formal_Lean_IFT_witness_established",
)


def interval_sum(values):
    answer = (Q(0), Q(0))
    for v in values:
        answer = plus(answer, v)
    return answer


def mid(v):
    return (v[0] + v[1]) / 2


def validate(candidate):
    if candidate.get("schema") != "ie-quantitative-ift-v1":
        raise ValueError("Expected existing 33x5 source-box candidate schema")
    if candidate.get("dimension") != N or candidate.get("parameter_dimension") != 5:
        raise ValueError("Expected 33 endogenous coordinates and five policy directions")
    if candidate.get("rows_recomputed_as_source_style") != [4, 5, 21]:
        raise ValueError("Source-style row rewrites absent")
    if candidate.get("source_to_legacy_row_permutation") != ROW_MAP:
        raise ValueError("Source economic row permutation has changed")
    if any(candidate.get(key) is not False for key in PROVENANCE_FLAGS):
        raise ValueError("Economic/Lean provenance flags must remain false")
    meta = candidate.get("metadata", {})
    if not isinstance(meta, dict) or not meta.get("source_commit"):
        raise ValueError("Missing producer revision")
    if any(meta.get(key) is not False for key in PROVENANCE_FLAGS):
        raise ValueError("Unjustified economic/Lean provenance metadata")

    rz, rh = rat(candidate["radius"]), rat(candidate["parameter_radius"])
    if rz <= 0 or rh <= 0:
        raise ValueError("Positive state and policy radii required")
    if len(candidate["center"]) != N or any(rat(v) != 0 for v in candidate["center"]):
        raise ValueError("Expected origin as numerical reference for the augmented box")
    if len(candidate["preconditioner"]) != N:
        raise ValueError("Wrong state preconditioner row count")
    R = [[rat(v) for v in row] for row in candidate["preconditioner"]]
    if any(len(row) != N for row in R):
        raise ValueError("Wrong state preconditioner column count")
    F0 = [box(v) for v in candidate["f_center"]]
    J = [[box(v) for v in row] for row in candidate["jacobian_ball"]]
    Fy = [[box(v) for v in row] for row in candidate["fy_ball"]]
    mu_z = [box(v) for v in candidate["funding_dual_state_gradient_ball"]]
    mu_direct = [box(v) for v in candidate["funding_dual_direct_parameter_derivatives_ball"]]
    mu0 = box(candidate["funding_dual_center_box"])
    if any(len(x) != N for x in (F0, J, Fy, mu_z)):
        raise ValueError("Wrong number of economic rows")
    if any(len(row) != N for row in J) or any(len(row) != 5 for row in Fy):
        raise ValueError("Wrong economic Jacobian dimensions")
    if len(mu_direct) != 4 or any(v != (Q(0), Q(0)) for v in mu_direct):
        raise ValueError("Source mu has an unexpected direct policy dependence")
    if Fy[5][0] != (Q(-1), Q(-1)):
        raise ValueError("The source row 5 must have exact -1 direct slack derivative")
    return rz, rh, R, F0, J, Fy, mu_z, mu0


def audit(candidate):
    rz, rh, R, F0, J, Fy, mu_z, mu0 = validate(candidate)
    # H(z,h)=(F(z,(0,h,0,0,0)),mu_L(z)). Midpoints propose
    # a preconditioner; rigor comes from bounding I-R34*DH.
    p = [mid(Fy[i][1]) for i in range(N)]
    m = [mid(mu_z[i]) for i in range(N)]
    v = [sum(R[i][j] * p[j] for j in range(N)) for i in range(N)]
    w = [sum(m[i] * R[i][j] for i in range(N)) for j in range(N)]
    schur_nominal = -sum(m[i] * v[i] for i in range(N))
    if schur_nominal == 0:
        raise ValueError("Point candidate has zero Schur complement")
    R34 = [[R[i][j] + v[i] * w[j] / schur_nominal for j in range(N)]
           + [-v[i] / schur_nominal] for i in range(N)]
    R34.append([-w[j] / schur_nominal for j in range(N)]
               + [Q(1) / schur_nominal])

    A = [[*J[i], Fy[i][1]] for i in range(N)]
    A.append([*mu_z, (Q(0), Q(0))])
    center = [*F0, mu0]
    rad = [rz] * N + [rh]
    row_derivative_bounds = []
    row_center_bounds = []
    for i in range(DIM):
        defect = Q(0)
        for j in range(DIM):
            approx = interval_sum(scale(R34[i][k], A[k][j])
                                  for k in range(DIM))
            diff = plus((Q(int(i == j)), Q(int(i == j))), scale(-1, approx))
            defect += magnitude(diff) * rad[j] / rad[i]
        residual = interval_sum(scale(R34[i][k], center[k]) for k in range(DIM))
        row_derivative_bounds.append(defect)
        row_center_bounds.append(magnitude(residual) / rad[i])
    q = max(row_derivative_bounds)
    eta = max(row_center_bounds)
    passed = q < 1 and eta + q < 1
    bound = eta / (1 - q) if q < 1 else None
    return {
        "schema": "ventura-augmented34-conditional-arithmetic-v1",
        "augmented_dimension": DIM,
        "rows": "33 modified binding prefix rows plus normalized L funding dual",
        "unknowns": "33 log-coordinate deviations and reserve-remuneration innovation v_R",
        "slack_and_other_policy_innovations": "held at zero",
        "state_radius_rational": fraction(rz),
        "remuneration_innovation_radius_rational": fraction(rh),
        "nominal_schur_rational_not_an_enclosure": fraction(schur_nominal),
        "weighted_defect_bound_q": fraction(q),
        "weighted_center_residual_eta": fraction(eta),
        "contractive_uniform_ball_arithmetic_gate_pass": passed,
        "max_normalized_root_shift_bound_rational": fraction(bound) if bound is not None else None,
        "conditional_remuneration_center_shift_bound": fraction(rh * bound) if bound is not None else None,
        "state_coordinate_row_bounds_rational": [fraction(x) for x in row_derivative_bounds],
        "policy_row_bound_rational": fraction(row_derivative_bounds[-1]),
        "source_Lean_semantic_identity_proved": False,
        "uniform_box_contains_Lean_actual_derivatives_proved": False,
        "exact_zero_center_proved": False,
        "formal_Lean_IFT_witness_established": False,
        "full_competitive_equilibrium_proved": False,
        "interpretation": "IF Python boxes enclose a C1 source augmented H on the full anisotropic box, Banach supplies one exact nearby zero (z*,v_R*) in that box. It need not have v_R*=0. No Lean bridge, original zero normalization, firm/bank sufficiency, or infinite equilibrium is proved.",
    }


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--candidate", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    try:
        raw = args.candidate.read_bytes()
        inp = json.loads(raw.decode("utf-8"), parse_float=str)
        report = audit(inp)
        report["candidate_sha256"] = hashlib.sha256(raw).hexdigest()
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
        print("CONDITIONAL 34x34 ANISOTROPIC BANACH GATE:",
              "PASS" if report["contractive_uniform_ball_arithmetic_gate_pass"] else "FAIL")
        print("q approximately:", float(Q(report["weighted_defect_bound_q"])))
        print("eta approximately:", float(Q(report["weighted_center_residual_eta"])))
        print("LEAN source semantics and full equilibrium: NOT proved")
        return 0 if report["contractive_uniform_ball_arithmetic_gate_pass"] else 2
    except (OSError, TypeError, ValueError, KeyError, ZeroDivisionError) as exc:
        print("INVALID 34x34 CANDIDATE:", exc, file=sys.stderr)
        return 3


if __name__ == "__main__":
    sys.exit(main())

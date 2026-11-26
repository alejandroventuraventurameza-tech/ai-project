#!/usr/bin/env python3
"""Exact rational Neumann/Schur test for the forward-AD Python Jacobian.

The 34x34 AD matrix is computed by differentiating finite_irf.py, then
its float values are rounded to decimal fractions. All subsequent
Neumann, Schur and perturbation-budget inequalities use Fraction EXACTLY.
This still does NOT enclose the genuine Python or Lean SOURCE derivatives.
"""
from __future__ import annotations

import hashlib
import json
from fractions import Fraction
from pathlib import Path

from audit_frozen_python_34_rational_preconditioner import (
    N, FULL, approximate_inverse, flt_solve, norm_inf, q, require,
    witness,
)

HERE = Path(__file__).resolve().parent
AD = HERE / "output/frozen_python_augmented34_forward_ad.json"
FD_BASE = HERE / "output/frozen_python_augmented34_boundary_search.json"
FD_GATE = HERE / "output/frozen_python_augmented34_rational_preconditioner.json"
OUT = HERE / "output/frozen_python_augmented34_ad_rational_gate.json"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def conditional_schur_sign_enclosure(q33, c33norm, n, c, u, residual_norm,
                                     schur_center, eps):
    """Exact-rational *conditional* perturbation enclosure.

    Let a hypothetical real 34x34 Jacobian H be within eps ENTRYWISE of
    the rationalized forward-AD matrix Jq, in the same output ordering
    and coordinates. Its 33x33 block A differs from Aq by at most n*eps
    in infinity operator norm, its forcing b by at most eps in infinity
    norm, and its funding gradient c by at most n*eps in one-norm.
    Even allowing an arbitrary |H[33,33]| <= eps, the true Schur
    complement H[33,33] - c*(A^-1*b) is strictly negative whenever the
    returned rational upper bound is negative.

    This proves ONLY a perturbation implication. It does not certify
    the required entrywise distance from SOURCE, or that the real
    SOURCE Jacobian is evaluated in these Python coordinates.
    """
    require(eps >= 0, "Negative perturbation radius")
    require(q33 >= 0 and c33norm > 0 and q33 < 1,
            "Noninvertible rational reference A")
    defect = q33 + c33norm*n*eps
    require(defect < 1, "Perturbed 33-block not Neumann certified")
    inverse_norm_bound = c33norm/(1-defect)
    u_inf = max(abs(t) for t in u)
    c_one = sum(abs(t) for t in c)
    tangent_residual_bound = residual_norm + eps*(n*u_inf+1)
    tangent_error = inverse_norm_bound*tangent_residual_bound
    # |c_true u_true - c_ref u_ref|
    # <= ||c_ref||_1 ||u_true-u_ref||_inf
    #    + ||c_true-c_ref||_1 ||u_true||_inf.
    # The final eps encloses the true last-row policy derivative.
    schur_error = (c_one*tangent_error
                   + n*eps*(u_inf+tangent_error) + eps)
    return {
        "33_defect_upper": defect,
        "33_inverse_norm_upper": inverse_norm_bound,
        "tangent_residual_upper": tangent_residual_bound,
        "tangent_error_upper": tangent_error,
        "schur_lower": schur_center-schur_error,
        "schur_upper": schur_center+schur_error,
    }


def conditional_root_contraction_gate(q34, preconditioner_norm, n, eps,
                                      box_radius):
    """Exact-rational a posteriori zero gate, WITHOUT a SOURCE enclosure.

    For a hypothetical C1 map F on the closed sup-norm box B(x0,R)
    in R^n, assume a separately certified uniform bound
      max_ij |D F(x)[i,j] - Jq[i,j]| <= eps  for ALL x in B,
    where q34 = ||I-C Jq||_inf and ||C||_inf <= preconditioner_norm.
    Then T(x)=x-C F(x) has contraction bound
      delta=q34+n*||C||_inf*eps.
    A separate source residual bound ||F(x0)||_inf < (1-delta)*R/||C||
    makes T map B into itself. Banach yields a unique zero in B.
    This helper computes ONLY the exact conditional required threshold.
    """
    require(box_radius > 0 and eps >= 0 and preconditioner_norm > 0,
            "Invalid root-box or preconditioner parameters")
    delta = q34 + n*preconditioner_norm*eps
    require(delta < 1, "No valid contraction bound")
    cap = (1-delta)*box_radius/preconditioner_norm
    require(cap > 0, "No positive SOURCE residual budget")
    return {
        "box_radius": box_radius,
        "maximum_source_residual_sup_norm_strict": cap,
        "uniform_contraction_upper": delta,
    }


def main():
    require(all(path.is_file() for path in (AD, FD_BASE, FD_GATE)),
            "Regenerate AD/FD boundary and previous rational gate first")
    data = json.loads(AD.read_text(encoding="utf-8"))
    prior = json.loads(FD_GATE.read_text(encoding="utf-8"))
    base = json.loads(FD_BASE.read_text(encoding="utf-8"))
    require(data["status"] == "FLOAT64_FORWARD_AD_PYTHON_34_JACOBIAN_NOT_SOURCE",
            "Invalid AD input scope")
    require(prior["status"] ==
            "EXACT_RATIONAL_ROUNDED_PYTHON_34_MATRIX_CERTIFICATE_ONLY",
            "Previous independent FD rational test missing")
    require(data["parent_boundary_report_sha256"] == sha(FD_BASE)
            and prior["parent_report_sha256"] == sha(FD_BASE)
            and data["source_sha256"] == base["source_sha256"],
            "AD/FD point or economic SOURCE fingerprints disagree")

    J = data["forward_ad_jacobian_34"]
    require(len(J) == FULL and all(len(row) == FULL for row in J),
            "Forward AD Jacobian not 34x34")
    A = [list(row[:N]) for row in J[:N]]
    C33f, _pivot33 = approximate_inverse(A)
    C34f, _pivot34 = approximate_inverse(J)
    Aq, C33q, q33, n33, K33 = witness(A, C33f)
    Jq, C34q, q34, n34, K34 = witness(J, C34f)

    # Exact negativity of Schur for the RATIONALIZED forward-AD matrix.
    b_float = [J[i][-1] for i in range(N)]
    c_float = J[-1][:N]
    u_float, _ = flt_solve(A, [-v for v in b_float])
    u = [q(v) for v in u_float]
    bq = [q(v) for v in b_float]
    cq = [q(v) for v in c_float]
    residual = [
        sum(Aq[i][k]*u[k] for k in range(N)) + bq[i]
        for i in range(N)
    ]
    rn = max(abs(v) for v in residual)
    s = sum(cq[i]*u[i] for i in range(N))
    s_err = sum(abs(v) for v in cq)*K33*rn
    require(s+s_err < 0,
            "AD rationalized Schur scalar negative sign not certified")

    eps33 = (1-q33)/(4*N*n33)
    eps34 = (1-q34)/(4*FULL*n34)
    eps = min(eps33, eps34)
    require(eps > 0, "No uniform rational entrywise tolerance")

    # The old eps certifies only 33/34 Neumann invertibility for a
    # hypothetical Jacobian within eps entrywise of rounded forward AD.
    # Add a separate exact-rational STRONGER radius that additionally
    # encloses the sign of the *actual* Schur scalar of such a matrix.
    # This includes a possibly nonzero (34,34) coefficient, bounded
    # by eps, and perturbations of A,b,c simultaneously.
    sign_eps = eps
    sign_gate = None
    for _ in range(256):
        require(q34 + n34*FULL*sign_eps < 1,
                "Full 34x34 Neumann budget was lost")
        candidate = conditional_schur_sign_enclosure(
            q33, n33, N, cq, u, rn, s, sign_eps)
        if candidate["schur_upper"] < 0:
            sign_gate = candidate
            break
        sign_eps /= 2
    require(sign_gate is not None,
            "Could not derive a strictly negative robust Schur gate")
    require(sign_eps > 0 and sign_gate["schur_upper"] < 0,
            "Incorrect rational robust Schur certificate")
    require(sign_gate["33_defect_upper"] < 1
            and q34 + n34*FULL*sign_eps < 1,
            "Neumann test not strict at robust sign radius")

    # Exact conditional Banach contraction thresholds for an actual
    # SOURCE 34-dimensional root: these are NOT evaluated on SOURCE.
    # A valid future enclosure must cover the ENTIRE closed box,
    # not merely the centre Jacobian at the Python numerical root.
    root_radii = (Fraction(1, 1000000), Fraction(1, 100000),
                  Fraction(1, 10000))
    root_gates = [
        conditional_root_contraction_gate(q34, n34, FULL, sign_eps, radius)
        for radius in root_radii
    ]

    # A second algebraically exact cross-comparison: rationalized
    # forward-AD matrix sits strictly within the independently certified
    # finite-difference *rounded* Jacobian perturbation budget.
    old = base["numerical_candidate"]["float_jacobian_probe"]
    oldA = old["first33_jacobian"]
    oldb = old["policy_forcing_column_b"]
    oldc = old["sparse_funding_dual_gradient_c"]
    oldJ = [
        list(oldA[i]) + [oldb[i]] for i in range(N)
    ] + [[float(oldc.get(str(i),0.)) for i in range(N)] + [0.]]
    difference = max(abs(Jq[i][j] - q(oldJ[i][j]))
                     for i in range(FULL) for j in range(FULL))
    old_eps = Fraction(prior["conditional_per_entry_error_tolerance"])
    require(difference < old_eps,
            "AD rounded Jacobian is outside old FD Neumann budget")
    require(data["last_row_policy_derivative"] == 0,
            "AD SOURCE-shaped dual directly depends on h")

    report = {
        "status": "EXACT_RATIONAL_ROUNDED_FORWARD_AD_PYTHON_34_GATE_ONLY",
        "input_AD_sha256": sha(AD),
        "input_FD_boundary_sha256": sha(FD_BASE),
        "input_FD_rational_gate_sha256": sha(FD_GATE),
        "rounded_matrix_order_33": N,
        "rounded_matrix_order_34": FULL,
        "exact_rational_33_defect": str(q33),
        "exact_rational_34_defect": str(q34),
        "approx_33_defect_float": float(q33),
        "approx_34_defect_float": float(q34),
        "exact_rational_schur_lower": str(s-s_err),
        "exact_rational_schur_upper": str(s+s_err),
        "rational_schur_lower_float": float(s-s_err),
        "rational_schur_upper_float": float(s+s_err),
        "rational_33_inverse_upper": str(K33),
        "rational_34_inverse_upper": str(K34),
        "conditional_34_entry_error_tolerance": str(eps),
        "conditional_34_entry_error_tolerance_float": float(eps),
        "conditional_joint_inverse_and_negative_schur_entry_tolerance":
            str(sign_eps),
        "conditional_joint_inverse_and_negative_schur_entry_tolerance_float":
            float(sign_eps),
        "conditional_perturbed_33_neumann_defect_upper":
            str(sign_gate["33_defect_upper"]),
        "conditional_perturbed_34_neumann_defect_upper":
            str(q34 + n34*FULL*sign_eps),
        "conditional_perturbed_33_inverse_norm_upper":
            str(sign_gate["33_inverse_norm_upper"]),
        "conditional_perturbed_tangent_error_upper":
            str(sign_gate["tangent_error_upper"]),
        "conditional_perturbed_schur_lower":
            str(sign_gate["schur_lower"]),
        "conditional_perturbed_schur_upper":
            str(sign_gate["schur_upper"]),
        "conditional_perturbed_schur_lower_float":
            float(sign_gate["schur_lower"]),
        "conditional_perturbed_schur_upper_float":
            float(sign_gate["schur_upper"]),
        "conditional_neumann_and_schur_sign_uniformly_stable": True,
        "conditional_source_root_boxes": [
            {
                "box_radius_exact": str(g["box_radius"]),
                "box_radius_float": float(g["box_radius"]),
                "uniform_contraction_upper_exact":
                    str(g["uniform_contraction_upper"]),
                "uniform_contraction_upper_float":
                    float(g["uniform_contraction_upper"]),
                "source_center_residual_sup_norm_must_be_strictly_less_than":
                    str(g["maximum_source_residual_sup_norm_strict"]),
                "source_center_residual_budget_float":
                    float(g["maximum_source_residual_sup_norm_strict"]),
                "verified_SOURCE_box_derivative": False,
                "verified_SOURCE_center_residual": False,
                "certified_SOURCE_root": False,
            }
            for g in root_gates
        ],
        "conditional_root_proof_obligation":
            "For some displayed radius R, prove the actual SOURCE 34-map "
            "is C1 and uses the SAME residual rows and log coordinates "
            "throughout the closed ||w-wstar||_inf <= R ball; prove "
            "entrywise |D SOURCE(w)-Jq| <= joint epsilon UNIFORMLY on "
            "that ball, and rigorously bound the true SOURCE centre "
            "residual sup norm STRICTLY below the listed limit. Only "
            "then Banach contraction gives a unique 34-equation zero.",
        "conditional_hypothesis":
            "Any real 34x34 matrix H in the SAME ORDERING and "
            "COORDINATES as this rationalized forward-AD matrix, with "
            "entrywise |H[i,j]-Jq[i,j]| <= the joint tolerance, "
            "has invertible 33x33 and 34x34 blocks and a strictly "
            "negative Schur complement. No true SOURCE enclosure "
            "is provided by this script.",
        "AD_FD_rounded_max_entry_difference_exact": str(difference),
        "AD_FD_rounded_max_entry_difference_float": float(difference),
        "old_FD_entry_tolerance_exact": str(old_eps),
        "both_rationalized_33_matrices_invertible": True,
        "both_rationalized_34_matrices_invertible": True,
        "AD_rounded_schur_sign_negative": True,
        "same_point_same_inherited_state": True,
        "source_python_equality_proved": False,
        "true_SOURCE_derivative_enclosed": False,
        "true_Python_derivative_enclosed": False,
        "IFT_existence_proved": False,
        "full_dynamic_equilibrium_proved": False,
        "notes": [
            "Forward AD eliminates finite-difference truncation, but still uses float64.",
            "An exact Neumann test of rounded AD coefficients is NOT a directed-rounding derivative certificate.",
            "Both matrices are evaluated at the frozen-predecessor Python boundary h*.",
            "The new uniform entry radius preserves both invertibility and the "
            "strict Schur sign for an unspecified real matrix in precisely the "
            "same Jacobian coordinates as the rationalized Python AD matrix.",
            "SOURCE-to-Python/normalized-row derivative conversion and the "
            "genuine SOURCE entrywise enclosure are NOT established here.",
            "The exact contraction thresholds demand independently "
            "validated SOURCE residual AND derivative bounds throughout "
            "the selected 34-dimensional box; neither is available yet.",
            "The actual SOURCE 34-row derivative and nonlinear root require separate proof.",
        ],
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(report,indent=2,sort_keys=True)+"\n",encoding="utf-8")
    print(json.dumps({k:report[k] for k in (
        "status","approx_33_defect_float","approx_34_defect_float",
        "rational_schur_lower_float","rational_schur_upper_float",
        "conditional_34_entry_error_tolerance_float",
        "conditional_joint_inverse_and_negative_schur_entry_tolerance_float",
        "conditional_perturbed_schur_upper_float",
        "AD_FD_rounded_max_entry_difference_float",
    )}, indent=2))
    print(json.dumps({
        "conditional_root_boxes": [
            {
                "radius": float(g["box_radius"]),
                "source_center_residual_budget":
                    float(g["maximum_source_residual_sup_norm_strict"]),
                "contraction_upper": float(g["uniform_contraction_upper"]),
            } for g in root_gates
        ],
        "true_SOURCE_residual_and_box_derivative_enclosed": False,
    }, indent=2))


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Exact-fraction regression: 512 vertices of a 2x2 Schur perturbation cube.
This tests the certificate code, not an enclosure of the true SOURCE Jacobian.
"""
from fractions import Fraction
from itertools import product
from audit_frozen_python_34_ad_rational_gate import (
    conditional_schur_sign_enclosure, conditional_root_contraction_gate,
)

def verify_two_by_two_corners():
    eps = Fraction(1, 100)
    u0 = [Fraction(-1, 2), Fraction(-1, 2)]
    c0 = [Fraction(1), Fraction(1)]
    gate = conditional_schur_sign_enclosure(
        Fraction(0), Fraction(1, 2), 2, c0, u0, Fraction(0), Fraction(-1), eps)
    assert gate["33_defect_upper"] < 1
    assert gate["schur_upper"] < 0
    checks = 0
    for sg in product((-1, 1), repeat=9):
        a00 = 2 + sg[0]*eps
        a01 = sg[1]*eps
        a10 = sg[2]*eps
        a11 = 2 + sg[3]*eps
        b0 = 1 + sg[4]*eps
        b1 = 1 + sg[5]*eps
        c0_true = 1 + sg[6]*eps
        c1_true = 1 + sg[7]*eps
        d = sg[8]*eps
        det = a00*a11 - a01*a10
        assert det != 0
        u0_true = -(a11*b0 - a01*b1)/det
        u1_true = -(-a10*b0 + a00*b1)/det
        schur = d + c0_true*u0_true + c1_true*u1_true
        assert gate["schur_lower"] <= schur <= gate["schur_upper"]
        assert schur < 0
        checks += 1
    assert checks == 512
    return checks

def verify_source_root_budget_formula():
    # Jq = diag(2, 3), C=diag(1/2, 1/3): exact q=0,
    # infinity preconditioner norm 1/2. With entrywise derivative
    # error 1/100, the uniform norm contraction bound is 1/100.
    radius = Fraction(1, 1000)
    gate = conditional_root_contraction_gate(
        Fraction(0), Fraction(1, 2), 2, Fraction(1, 100), radius)
    assert gate["uniform_contraction_upper"] == Fraction(1, 100)
    assert gate["maximum_source_residual_sup_norm_strict"] == (
        Fraction(99, 50000))
    # This is a HYPOTHETICAL exact linear model, not SOURCE:
    # F(x)=diag(2,3)*x + (r,0). The unique root is
    # (-r/2,0), lies in the certified box if r<budget.
    r = gate["maximum_source_residual_sup_norm_strict"] / 2
    assert abs(-r / 2) < radius
    try:
        conditional_root_contraction_gate(
            Fraction(0), Fraction(1, 2), 2, Fraction(1), radius)
    except AssertionError:
        pass
    else:
        raise AssertionError("Non-contractive source-root gate was accepted")
    return True


if __name__ == "__main__":
    count = verify_two_by_two_corners()
    assert verify_source_root_budget_formula()
    print("EXACT_RATIONAL_SCHUR_CUBE_REGRESSION_PASSED", count)

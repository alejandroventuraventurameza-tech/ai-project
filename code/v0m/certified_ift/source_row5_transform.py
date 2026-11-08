"""Pointwise row-5 change of coordinates between two finite residuals.

Legacy binding row 5: g_log = log(face / collateral_value).
Lean modified row 5: g_mod = 1 - face / collateral_value - s.

At coverage ratio 1 and s=0, Dz g_mod = -Dz g_log. Therefore, when
J_mod = D J_log for D=diag(1,...,-1 at row 5,...), any old rational
point preconditioner R_log converts as R_mod=R_log D.

This is only a FIRST-ORDER, POINTWISE algebraic conversion. It is NOT
a uniform enclosure for finite disturbances; the nonlinear residuals
are different away from the exact frontier. Do not relabel the old
Jacobian box as the source modified Jacobian box on a neighborhood.
"""
from check_quantitative_ift import rat, box, fraction

N = 33
FACE_ROW = 5


def flip_binding_face_row_at_frontier(old_jacobian_boxes, old_preconditioner):
    if len(old_jacobian_boxes) != N or len(old_preconditioner) != N:
        raise ValueError("Expected 33 rows")
    if any(len(row) != N for row in old_jacobian_boxes + old_preconditioner):
        raise ValueError("Expected 33x33 arrays")
    J = [[box(v) for v in row] for row in old_jacobian_boxes]
    R = [[rat(v) for v in row] for row in old_preconditioner]
    # D J changes row 5; R D changes column 5.
    transformed_J = [
        [[fraction(-b), fraction(-a)] if i == FACE_ROW
         else [fraction(a), fraction(b)] for (a, b) in row]
        for i, row in enumerate(J)
    ]
    transformed_R = [[fraction(-v if j == FACE_ROW else v)
                       for j, v in enumerate(row)] for row in R]
    return transformed_J, transformed_R


def source_slack_direct_parameter_column():
    """Explicit derivative of g_mod with respect to prescribed slack s."""
    return ["-1" if i == FACE_ROW else "0" for i in range(N)]

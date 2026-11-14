#!/usr/bin/env python3
"""Exact rational bounds on converting pinned decimal P0 coefficients to floats.

This checks ONLY decimal-string -> correctly rounded Python float conversion
and its LINEAR 10x6 log-tail map; it does not include subsequent floating
matrix-vector arithmetic, exp/log rounding or SOURCE economic semantics.

The formula applies to all six-dimensional real z in the stated cube:
  |sum_k (float(C_jk)-decimal(C_jk))*z_k|
    <= radius * sum_k |float(C_jk)-decimal(C_jk)|.

Both sides and every inequality are computed using Fraction exact rationals.
"""
from __future__ import annotations

import hashlib
import json
from decimal import Decimal
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
INFILE = HERE / "inputs/rational_preconditioners.json"
OUT = HERE / "output/source_p0_exact_decimal_binary_conversion_bounds.json"
RADIUS = Fraction(1, 4)


def require(cond, message):
    if not cond:
        raise AssertionError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    data=json.loads(INFILE.read_text(encoding="utf-8"))
    matrix=data["P0"]
    require(len(matrix)==16 and all(len(row)==6 for row in matrix),
            "Pinned P0 is not 16x6")
    exact=[[Fraction(Decimal(str(x))) for x in row] for row in matrix]
    binary=[[Fraction.from_float(float(x)) for x in row] for row in matrix]
    require(all(exact[j][k]==binary[j][k]==int(j==k)
                for j in range(6) for k in range(6)),
            "P0 first six rows not exact identity in both representations")
    row_errors=[
        sum(abs(binary[j+6][k]-exact[j+6][k]) for k in range(6))
        for j in range(10)
    ]
    max_entry=max(abs(binary[j][k]-exact[j][k])
                  for j in range(16) for k in range(6))
    max_row=max(row_errors)
    max_output=RADIUS*max_row
    require(max_row>0 and max_output>0, "Expected nonzero conversion error")
    require(max_entry < Fraction(1,10**14)
            and max_output < Fraction(1,10**14),
            "Decimal-to-binary conversion error unexpectedly large")
    report={
        "status":"EXACT_RATIONAL_P0_DECIMAL_TO_BINARY64_CONVERSION_BOUND_ONLY",
        "p0_source_sha256":sha(INFILE),
        "source_model_sha256":
            sha(ROOT/"lean/checkpoint/modules/Ventura26LiquidityAllocation/EconomicModel.lean"),
        "P0_dimensions":[16,6],
        "first_six_rows_identity_in_both_exact_rational_representations":True,
        "ten_control_rows":list(range(6,16)),
        "state_log_cube_radius_exact":str(RADIUS),
        "state_log_cube_radius_float":float(RADIUS),
        "max_coefficient_abs_error_exact":str(max_entry),
        "max_coefficient_abs_error_float":float(max_entry),
        "max_control_row_l1_coefficient_error_exact":str(max_row),
        "max_control_row_l1_coefficient_error_float":float(max_row),
        "max_tail_log_response_abs_error_for_cube_exact":str(max_output),
        "max_tail_log_response_abs_error_for_cube_float":float(max_output),
        "per_control_tail_log_error_bounds_exact":[str(RADIUS*r) for r in row_errors],
        "error_type":"binary64 coefficient representation error ONLY",
        "all_inequalities_checked_with_exact_fraction_arithmetic":True,
        "original_python_matvec_rounding_enclosed":False,
        "original_python_exp_log_rounding_enclosed":False,
        "lean_real_p0_matrix_instantiated":False,
        "source_python_economic_operator_identity_proved":False,
        "infinite_horizon_continuation_proved":False,
    }
    OUT.parent.mkdir(parents=True,exist_ok=True)
    OUT.write_text(json.dumps(report,indent=2,sort_keys=True)+"\n",encoding="utf-8")
    print(json.dumps({k:report[k] for k in (
        "status","max_coefficient_abs_error_float",
        "max_control_row_l1_coefficient_error_float",
        "max_tail_log_response_abs_error_for_cube_float",
        "source_python_economic_operator_identity_proved",
    )},indent=2))


if __name__ == "__main__":
    main()

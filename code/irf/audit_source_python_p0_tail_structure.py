#!/usr/bin/env python3
"""Pin Python's finite 16x6 P0 as an identity-state + 10x6 control tail.

The exact decimal P0 coefficient STRINGS are parsed with Decimal, before
the original finite_irf.py float64 calculation. The first 6 rows
must be the identity. The last 10 rows produce the ten date-two control
log responses. This is a numerical/structural contract for the
finite P0 surrogate and a target for the SOURCE-typed Lean tail rule;
it is NOT the exact infinite-horizon policy function or full
SOURCE/Python operator equality.
"""
from __future__ import annotations

import hashlib
import json
import math
from decimal import Decimal, localcontext
from fractions import Fraction
from pathlib import Path

import finite_irf as engine
from frozen_stationary_prefix_audit import frozen_stationary_seed

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
SOURCE=ROOT/"lean/checkpoint/modules/Ventura26LiquidityAllocation/EconomicModel.lean"
ENGINE=HERE/"finite_irf.py"
PIN=HERE/"inputs/rational_preconditioners.json"
OUT=HERE/"output/source_python_p0_tail_structure.json"


def require(ok,msg):
    if not ok:
        raise AssertionError(msg)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    source=SOURCE.read_text(encoding="utf-8")
    pycode=ENGINE.read_text(encoding="utf-8")
    for anchor in (
        "abbrev LocalPrefixContinuationRule :=",
        "LocalPrefixStateSix → LocalPrefixControlsTen",
        "noncomputable def localContinuationLogResponse",
        "def localPrefixStateSixVector",
        "def localPrefixControlsTenVector",
        "noncomputable def localPrefixStateSixLogChart",
    ):
        require(anchor in source,"Genuine SOURCE tail definition drifted: "+anchor)
    for anchor in (
        "def decode_prefix(base, p0, z):",
        "tail_log = matvec(p0, z[17:23])",
        "u2 = [s.base[6 + i] * math.exp(tail_log[6 + i]) for i in range(10)]",
    ):
        require(anchor in pycode,"Original finite Python tail changed: "+anchor)
    raw=json.loads(PIN.read_text(encoding="utf-8"))
    p0=raw["P0"]
    require(len(p0)==16 and all(len(row)==6 for row in p0),
            "Expected immutable 16x6 finite P0 matrix")
    matrix=[[Fraction(Decimal(v)) for v in row] for row in p0]
    first_six_identity=all(
        matrix[i][j]==Fraction(int(i==j)) for i in range(6) for j in range(6)
    )
    require(first_six_identity, "First 6 P0 rows are not an exact identity")
    require(all(math.isfinite(float(v)) for row in matrix for v in row),
            "Nonfinite finite P0 coefficient")

    s=engine.steady_case()
    base=frozen_stationary_seed(s)
    require(len(base.X2)==6 and len(s.base)==16
            and all(v>0 for v in base.X2)
            and all(v>0 for v in s.base[6:16]),
            "Invalid positive-source finite tail reference")

    trials=[
        [0.]*33,
        [1.0e-4*math.sin(0.71*(j+1)) for j in range(33)],
        [-1.5e-4*math.cos(0.49*(j+1)) for j in range(33)],
        [2e-4*math.sin(0.31*(j+1))+1e-4*math.cos(0.7*j)
         for j in range(33)],
    ]
    max_tail_response_error=0.
    max_source_state_log_error=0.
    max_control_baseline_error=0.
    with localcontext() as ctx:
        ctx.prec=100
        for z in trials:
            _,_,x2,_,u2=engine.decode_prefix(
                base,[[float(v) for v in row] for row in matrix],z
            )
            for k in range(6):
                actual=math.log(x2[k]/base.X2[k])
                max_source_state_log_error=max(
                    max_source_state_log_error,abs(actual-z[17+k]))
            for j in range(10):
                exact_response=sum(
                    Decimal(p0[6+j][k])*Decimal(str(z[17+k]))
                    for k in range(6)
                )
                actual_response=math.log(u2[j]/s.base[6+j])
                max_tail_response_error=max(
                    max_tail_response_error,
                    abs(actual_response-float(exact_response))
                )
                if z is trials[0]:
                    max_control_baseline_error=max(
                        max_control_baseline_error,
                        abs(u2[j]-s.base[6+j])
                    )
    require(max_source_state_log_error<3e-12,
            "Six SOURCE-shaped state log deviations drift from Python")
    require(max_tail_response_error<3e-12,
            "Last 10 exact-decimal P0 control responses disagree with Python")
    require(max_control_baseline_error<1e-12,
            "Finite tail no longer returns baseline controls at z=0")
    result={
        "status":"FINITE_P0_6_STATE_PLUS_10_CONTROL_STRUCTURE_NUMERIC_ONLY",
        "source_sha256":sha(SOURCE),
        "python_engine_sha256":sha(ENGINE),
        "p0_coefficients_sha256":sha(PIN),
        "p0_rows":16,
        "source_carried_state_count":6,
        "source_date_two_control_count":10,
        "p0_first_six_rows_exact_rational_identity":first_six_identity,
        "p0_control_matrix_rows":list(range(6,16)),
        "tested_positive_log_chart_points":len(trials),
        "max_state_log_chart_error":max_source_state_log_error,
        "max_10_control_log_response_error":max_tail_response_error,
        "max_baseline_control_level_error":max_control_baseline_error,
        "coefficients_parsed_exactly_as_decimal_fractions":True,
        "original_python_evaluated_with_float64":True,
        "p0_full_equilibrium_continuation_proved":False,
        "p0_lean_real_coefficients_instantiated":False,
        "full_source_python_operator_equality_proved":False,
        "true_source_derivative_enclosure_proved":False,
        "claim":"P0 finite surrogate is a 6-state/10-control log-linear rule, not a certified infinite continuation.",
    }
    OUT.parent.mkdir(parents=True,exist_ok=True)
    OUT.write_text(json.dumps(result,indent=2,sort_keys=True)+"\n",
                   encoding="utf-8")
    print(json.dumps({k:result[k] for k in (
        "status","p0_first_six_rows_exact_rational_identity",
        "max_state_log_chart_error","max_10_control_log_response_error",
        "max_baseline_control_level_error","p0_full_equilibrium_continuation_proved",
    )},indent=2))


if __name__=="__main__":
    main()

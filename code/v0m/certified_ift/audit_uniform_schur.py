#!/usr/bin/env python3
"""Exact-rational conditional Schur sign enclosure on a 33x5 product box.

Uses verified arithmetic output for the source-style Python residual box.
This does NOT certify the semantic identity to Lean's EconomicModel,
the exact zero of its baseline marginal, an IFT witness in Lean or
any global/recursive equilibrium.
"""
import argparse
import json
import sys
from pathlib import Path
from audit_point_schur import audit


def audit_uniform(data, arithmetic):
    if data.get("schema") != "ie-quantitative-ift-v1":
        raise ValueError("Wrong nonlinear-box input schema")
    if arithmetic.get("schema") != "ie-quantitative-ift-audit-v1":
        raise ValueError("Wrong rational contraction report schema")
    if not arithmetic.get("requested_domain_arithmetic_gate_pass"):
        raise ValueError("The entire five-parameter contraction gate did not pass")
    if not arithmetic.get("uniform_family_gate_pass"):
        raise ValueError("No uniform family contraction gate")
    if data.get("rows_recomputed_as_source_style") != [4,5,21]:
        raise ValueError("Incorrect source row transformation")
    if any(data.get(k) is not False for k in (
        "source_Lean_semantic_identity_proved",
        "uniform_box_contains_Lean_actual_derivatives_proved",
        "exact_zero_center_proved",
        "formal_Lean_IFT_witness_established")):
        raise ValueError("Unjustified source-provenance flags")
    point_like = {
        "schema": "ventura-source-point-jacobian-CANDIDATE-v1",
        "state_dimension": 33,
        "parameter_dimension": 5,
        "rows_recomputed_as_source_style": [4,5,21],
        "source_to_legacy_row_permutation": data["source_to_legacy_row_permutation"],
        "preconditioner": data["preconditioner"],
        "point_jacobian_box": data["jacobian_ball"],
        "point_policy_derivative_box": data["fy_ball"],
        "funding_dual_state_gradient_box": data["funding_dual_state_gradient_ball"],
        "funding_dual_direct_parameter_derivatives":
            data["funding_dual_direct_parameter_derivatives_ball"],
        "point_preconditioned_defect_upper": arithmetic["defect_bound_q"],
        "uniform_ball_jacobian_enclosures_proven": False,
        "exact_zero_center_proven": False,
        "economic_source_row_map_proven": False,
        "formal_Lean_witness_established": False,
    }
    out=audit(point_like)
    out["schema"]="ventura-conditional-uniform-schur-audit-v1"
    out["domain"]="full 33-log-coordinate by five-policy parameter product box"
    out["conditional_python_box_contraction_pass"]=True
    out["state_radius"]=data["radius"]
    out["parameter_radius"]=data["parameter_radius"]
    out["source_Lean_semantic_identity_proved"]=False
    out["uniform_source_Lean_IFT_witness_proved"]=False
    out["root_baseline_funding_dual_exactly_zero_proved"]=False
    out["scope"]="All signs conditional on the interval AD expression-to-source semantic mapping and valid analytic domains. No Lean source bridge."
    return out


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--ball",required=True,type=Path)
    parser.add_argument("--arithmetic-report",required=True,type=Path)
    parser.add_argument("--output",required=True,type=Path)
    args=parser.parse_args()
    try:
        ball=json.loads(args.ball.read_text(),parse_float=str)
        arith=json.loads(args.arithmetic_report.read_text(),parse_float=str)
        report=audit_uniform(ball,arith)
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(report,indent=2)+"\n")
        derivs=report["policy_derivative_enclosures"]
        for x in derivs:
            print(x["parameter"],"UNIFORM sign minus?",
                  x["strict_negative_given_semantic_inputs"])
        ok=derivs[0]["strict_negative_given_semantic_inputs"] and derivs[1]["strict_negative_given_semantic_inputs"]
        print("CONDITIONAL UNIFORM SCHUR SIGN GATE:", "PASS" if ok else "FAIL")
        print("LEAN SOURCE SEMANTICS, EXACT ZERO BASE AND GLOBAL EQUILIBRIUM: NOT PROVED")
        return 0 if ok else 2
    except (OSError,ValueError,KeyError,ZeroDivisionError) as exc:
        print("UNIFORM SCHUR INPUT INVALID:",exc,file=sys.stderr)
        return 3

if __name__=="__main__":
    sys.exit(main())

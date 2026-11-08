#!/usr/bin/env python3
"""Conditional Schur signs from EXACT interval point-Jacobian data.

This certifies interval algebra ONLY. It assumes the provided 33x33
intervals enclose the exact source Jacobian, and the 33x5 columns enclose
the exact policy derivatives at the SAME reference. The semantic
identity with Lean's full source residual remains OPEN.

The source economic reduced marginal is mu(z(y)), so the derivative
is - D_z(mu) * (D_z F)^(-1) * D_y F. No direct policy derivative is
present at fixed endogenous z for the source definition.
"""
import argparse
import json
import sys
from fractions import Fraction as Q
from pathlib import Path
from check_quantitative_ift import box, plus, scale, magnitude, fraction
from verify_point_candidate import verify

N, K = 33, 5


def interval_multiply(a, b):
    terms=(a[0]*b[0],a[0]*b[1],a[1]*b[0],a[1]*b[1])
    return min(terms), max(terms)


def audit(data):
    q, reported_q = verify(data)  # requires q<1 and source row permutation
    mraw=data["funding_dual_state_gradient_box"]
    draw=data["funding_dual_direct_parameter_derivatives"]
    if len(mraw)!=N or len(draw)!=4:
        raise ValueError("Missing exact 33-gradient or four source direct derivatives")
    m=[box(v) for v in mraw]
    direct=[box(x) for x in draw]
    # Source mu does not depend directly on the prescribed slack or
    # monetary policy coordinates at fixed log state. Reject otherwise.
    if any(x != (Q(0),Q(0)) for x in direct):
        raise ValueError("Unexpected direct policy dependence of source L dual")
    R=[[Q(x) for x in row] for row in data["preconditioner"]]
    G=[[box(x) for x in row] for row in data["point_policy_derivative_box"]]
    mone=sum(magnitude(x) for x in m)
    Rinf=max(sum(abs(x) for x in row) for row in R)
    result=[]
    for j in range(K):
        # Directional policy forcing G_j and candidate z'=-R G_j.
        vg=[sum_interval(scale(R[i][k],G[k][j]) for k in range(N))
             for i in range(N)]
        nominal=sum_interval(scale(-1,interval_multiply(m[i],vg[i]))
                             for i in range(N))
        ginf=max(magnitude(G[i][j]) for i in range(N))
        err=mone * (q/(1-q)) * Rinf * ginf
        bound=(nominal[0]-err,nominal[1]+err)
        result.append({
            "parameter":["collateral_slack","reserve_remuneration",
                         "reserve_quantity","reserve_requirement",
                         "corridor_width"][j],
            "conditional_lower_rational":fraction(bound[0]),
            "conditional_upper_rational":fraction(bound[1]),
            "strict_negative_given_semantic_inputs":bound[1]<0,
            "strict_positive_given_semantic_inputs":bound[0]>0,
            "nominal_upper_rational":fraction(nominal[1]),
            "neumann_error_rational":fraction(err)
        })
    return {
        "schema":"ventura-conditional-point-schur-audit-v1",
        "source_point_inverse_interval_gate_pass":True,
        "direct_funding_dual_parameter_derivatives_zero":True,
        "state_dimension":33,
        "parameter_dimension":5,
        "jacobian_defect_bound_exact":fraction(q),
        "jacobian_defect_bound_reported":fraction(reported_q),
        "full_Lean_source_row_identity_proved":False,
        "uniform_nonlinear_IFT_box_proved":False,
        "root_normalization_exactly_zero_proved":False,
        "meaning":"If all source AD enclosures are sound for one common exact reference, these signs are rigorous at that point only.",
        "policy_derivative_enclosures":result,
    }


def sum_interval(xs):
    out=Q(0),Q(0)
    for x in xs:
        out=plus(out,x)
    return out


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("candidate",type=Path)
    ap.add_argument("--output",type=Path,required=True)
    args=ap.parse_args()
    try:
        data=json.loads(args.candidate.read_text(),parse_float=str)
        z=audit(data)
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(z,indent=2)+"\n")
        for value in z["policy_derivative_enclosures"]:
            print(value["parameter"],"negative?",value["strict_negative_given_semantic_inputs"])
            print("  upper =",float(Q(value["conditional_upper_rational"])))
        ok=(z["policy_derivative_enclosures"][0]["strict_negative_given_semantic_inputs"]
             and z["policy_derivative_enclosures"][1]["strict_negative_given_semantic_inputs"])
        print("CONDITIONAL POINT SCHUR SIGN GATE:", "PASS" if ok else "FAIL")
        print("FULL ECONOMIC SOURCE IDENTITY & IFT: NOT PROVED")
        return 0 if ok else 2
    except (ValueError,KeyError,OSError,ZeroDivisionError) as e:
        print("INVALID OR UNVERIFIED POINT-SCHUR INPUT:",e,file=sys.stderr)
        return 3


if __name__=="__main__":
    sys.exit(main())

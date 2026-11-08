#!/usr/bin/env python3
"""Exact-rational arithmetic gate for a conditional 33x33 quantitative IFT.

Requires justified interval enclosures of the ACTUAL source F, DzF, and DyF.
Checking JSON arithmetic does NOT establish their provenance, C1 regularity,
or any complete dynamic equilibrium. The synthetic test is NOT economic data.
"""
import argparse
import hashlib
import json
import sys
from fractions import Fraction as Q
from pathlib import Path


def rat(x):
    if isinstance(x, bool) or isinstance(x, float):
        raise TypeError("No booleans or binary floats; use rational strings")
    if isinstance(x, (str, int, Q)):
        return Q(x)
    raise TypeError("Unsupported rational value")


def box(x):
    if not isinstance(x, list) or len(x) != 2:
        raise ValueError("Each interval must be [lower, upper]")
    a, b = map(rat, x)
    if a > b:
        raise ValueError("Reversed interval")
    return (a, b)


def plus(a, b):
    return (a[0] + b[0], a[1] + b[1])


def scale(k, x):
    return (k*x[0], k*x[1]) if k >= 0 else (k*x[1], k*x[0])


def magnitude(x):
    return max(abs(x[0]), abs(x[1]))


def fraction(x):
    return str(x.numerator) if x.denominator == 1 else str(x.numerator)+"/"+str(x.denominator)


def matrix_product_row_box(R, B, i, j, n):
    result = (Q(0), Q(0))
    for k in range(n):
        result = plus(result, scale(R[i][k], B[k][j]))
    return result


def inspect_certificate(data):
    if data.get("schema") != "ie-quantitative-ift-v1":
        raise ValueError("Invalid schema")
    n = data.get("dimension")
    if type(n) is not int or n != 33:
        raise ValueError("Require exactly 33 economic rows")
    meta = data.get("metadata")
    if not isinstance(meta, dict) or not meta.get("source_commit"):
        raise ValueError("A source revision identifier is required")
    center = [rat(v) for v in data["center"]]
    rz = rat(data["radius"])
    R = [[rat(x) for x in row] for row in data["preconditioner"]]
    F = [box(x) for x in data["f_center"]]
    J = [[box(x) for x in row] for row in data["jacobian_ball"]]
    if rz <= 0 or any(len(x) != n for x in (center, R, J, F)):
        raise ValueError("Invalid center, radius or matrix rows")
    if any(len(row) != n for row in R+J):
        raise ValueError("Expected 33x33 matrices")
    # Interval defect I-R*DzF: all operations exact in Q.
    q = max(sum(magnitude(plus((Q(int(i == j)),)*2,
                scale(-1, matrix_product_row_box(R,J,i,j,n))))
                for j in range(n)) for i in range(n))
    eta = max(magnitude(sum_box(scale(R[i][k],F[k])
                                for k in range(n))) for i in range(n))
    nr = max(sum(map(abs, row)) for row in R)
    base_pass = q < 1 and eta+q*rz < rz
    report = dict(schema="ie-quantitative-ift-audit-v1",
        metadata=meta, dimension=n,
        norm="sup/induced infinity",
        exact_arithmetic="Fractions, no binary floats",
        defect_bound_q=fraction(q),
        preconditioned_center_residual_eta=fraction(eta),
        preconditioner_norm=fraction(nr),
        state_radius=fraction(rz),
        base_ball_gate_pass=base_pass,
        normalized_zero_reference_condition=(all(v==0 for v in center)
                            and all(lo==0 and hi==0 for lo,hi in F)),
        requested_domain="base_ball",
        requested_domain_arithmetic_gate_pass=base_pass,
        verified_economic_source_enclosures=False,
        formal_Lean_witness_established=False,
        note="Sound ONLY IF all input boxes enclose the exact source functions on the stated full domains.")
    if ("parameter_radius" in data) != ("fy_ball" in data):
        raise ValueError("Both parameter_radius and fy_ball required")
    if "parameter_radius" in data:
        m=data.get("parameter_dimension")
        ry=rat(data["parameter_radius"])
        G=[[box(v) for v in row] for row in data["fy_ball"]]
        if type(m) is not int or m!=5 or ry<=0 or len(G)!=n or any(len(row)!=m for row in G):
            raise ValueError("Need positive radius and 33x5 parameter-derivative boxes")
        ly=max(sum(magnitude(matrix_product_row_box(R,G,i,j,n)) for j in range(m))
               for i in range(n))
        uniform_eta=eta+ly*ry
        family_pass=q<1 and uniform_eta+q*rz<rz
        report.update(requested_domain="five_parameter_family",
          requested_domain_arithmetic_gate_pass=family_pass,
          uniform_family_gate_pass=family_pass,
          parameter_radius=fraction(ry),
          uniform_preconditioned_residual_bound=fraction(uniform_eta),
          preconditioned_parameter_derivative_bound=fraction(ly),
          root_distance_bound=fraction(uniform_eta/(1-q)) if q<1 else None)
    if q<1:
        report["conditional_inverse_norm_bound"]=fraction(nr/(1-q))
        report["conditional_base_root_distance_bound"]=fraction(eta/(1-q))
    return report


def sum_box(xs):
    a=(Q(0),Q(0))
    for x in xs:
        a=plus(a,x)
    return a


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--certificate",type=Path,required=True)
    ap.add_argument("--output",type=Path,required=True)
    args=ap.parse_args()
    try:
        raw=args.certificate.read_bytes()
        d=json.loads(raw.decode("utf-8"),parse_float=str)
        out=inspect_certificate(d)
        out["certificate_sha256"]=hashlib.sha256(raw).hexdigest()
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(out,indent=2,ensure_ascii=False)+"\n")
        ok=out["requested_domain_arithmetic_gate_pass"]
        print("BASE:",out["base_ball_gate_pass"],"REQUESTED:",ok)
        print("ECONOMIC SOURCE ENCLOSURES: NOT VERIFIED")
        return 0 if ok else 2
    except (OSError,TypeError,ValueError,KeyError,ZeroDivisionError) as e:
        print("INVALID CERTIFICATE:",e,file=sys.stderr)
        return 3


if __name__=="__main__":
    sys.exit(main())

#!/usr/bin/env python3
"""Independently recompute an interval POINT Jacobian defect over Q.

This is a strict source-provenance guard: it refuses to promote an
isolated Jacobian into a uniform nonlinear implicit-function certificate.
"""
import argparse
import json
from fractions import Fraction as Q
from pathlib import Path


def verify(data):
    if data.get("schema") != "ventura-source-point-jacobian-CANDIDATE-v1":
        raise ValueError("Expected point-only candidate schema")
    if data.get("state_dimension") != 33 or data.get("parameter_dimension") != 5:
        raise ValueError("Expected 33 states and 5 policy parameters")
    if data.get("rows_recomputed_as_source_style") != [4, 5, 21]:
        raise ValueError("Expected source-style AD in rows 4, 5 and 21; legacy hybrid is rejected")
    for key in ("uniform_ball_jacobian_enclosures_proven",
                "exact_zero_center_proven",
                "economic_source_row_map_proven",
                "formal_Lean_witness_established"):
        if data.get(key) is not False:
            raise ValueError("Unjustified source-proof flag: " + key)
    J=[[(Q(a),Q(b)) for a,b in row]
       for row in data["point_jacobian_box"]]
    R=[[Q(v) for v in row] for row in data["preconditioner"]]
    G=data["point_policy_derivative_box"]
    if len(J)!=33 or len(R)!=33 or len(G)!=33:
        raise ValueError("Wrong row count")
    if any(len(row)!=33 for row in J+R) or any(len(row)!=5 for row in G):
        raise ValueError("Wrong column count")
    if any(a>b for row in J for a,b in row):
        raise ValueError("Reversed point Jacobian interval")
    if G[5][0] != ["-1","-1"]:
        raise ValueError("Expected exact source slack derivative -1 in row five")
    norm_rows=[]
    for i in range(33):
        row_norm=Q(0)
        for j in range(33):
            lo=hi=Q(int(i==j))
            for k in range(33):
                a,b=J[k][j]
                v,w=R[i][k]*a,R[i][k]*b
                lo-=max(v,w)
                hi-=min(v,w)
            row_norm += max(abs(lo),abs(hi))
        norm_rows.append(row_norm)
    q=max(norm_rows)
    exported=Q(data["point_preconditioned_defect_upper"])
    if exported<q or q>=1:
        raise ValueError("Point inverse defect not enclosed or not contractive")
    return q, exported


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("candidate",type=Path)
    args=ap.parse_args()
    d=json.loads(args.candidate.read_text(),parse_float=str)
    q,exported=verify(d)
    print("POINT MATRIX DEFECT VALIDATED EXACTLY")
    print("q_exact =",q)
    print("q_exported_upper =",exported)
    print("UNIFORM NONLINEAR BALL ENCLOSURE: NOT ESTABLISHED")
    print("SOURCE ROW IDENTITY IN LEAN: NOT ESTABLISHED")


if __name__=="__main__":
    main()

#!/usr/bin/env python3
"""Construct INVERTIBLE CANDIDATE row transform for each S/B branch.

Inputs are generated artifacts from the same verify run: nine root scales,
sixteen source-shaped identity rows, eight firm rows with two Euler pledge
shears, the verified 33-index row permutation and positive coordinate chart.
This certifies an algebraic matrix inverse GIVEN the candidate row rules,
not economic SOURCE/Python equality or a SOURCE Jacobian inverse.
"""
from __future__ import annotations
import csv
import hashlib
import json
import math
from pathlib import Path
from finite_irf import steady_case

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
OUTPUT=HERE/"output"
PARTIAL=OUTPUT/"partial_source_jacobian_row_scale_ledger.json"
IDENTITY=OUTPUT/"source_identity_row_candidates.json"
FIRM=OUTPUT/"source_firm_budget_euler_shear_audit.json"
CHART=OUTPUT/"source_python_log_chart_alignment.json"
ROW_MAP=OUTPUT/"lean_python_33_row_permutation.json"
CSV=OUTPUT/"main/finite_irf_paths.csv"
REPORT=OUTPUT/"conditional_source_33_row_transform_inverse.json"
N=33


def require(ok,msg):
    if not ok: raise AssertionError(msg)


def sha(file):
    return hashlib.sha256(file.read_bytes()).hexdigest()


def jload(file):
    require(file.exists(),"Missing regenerated prerequisite: "+str(file))
    return json.loads(file.read_text(encoding="utf-8"))


def matmul(A,B):
    return [[sum(A[i][k]*B[k][j] for k in range(N))
             for j in range(N)] for i in range(N)]


def max_identity_error(A):
    return max(abs(A[i][j]-(1. if i==j else 0.))
               for i in range(N) for j in range(N))


def main():
    scale=jload(PARTIAL); identities=jload(IDENTITY)
    firms=jload(FIRM); chart=jload(CHART); maps=jload(ROW_MAP)
    require(scale["source_row_count"]==N and
            len(scale["known_source_indices"])==9,"Bad nine factors")
    require(identities["distinct_row_shape_candidates_total"]==25 and
            len(identities["source_to_python_rows"])==16,
            "Bad sixteen identity rows")
    require(set(firms["direct_indices"])=={0,1,2,3,17,18}
            and set(firms["pledge_shear_indices"])=={19,20},
            "Firm shear partition changed")
    require(chart["source_chart_dimension"]==N and
            chart["baseline_positive"],"Bad coordinate-chart prerequisite")
    perm=maps["source_to_python_permutation"]
    require(len(perm)==N and sorted(perm)==list(range(N)),
            "Source-to-Python permutation invalid")
    cover=set(scale["known_source_indices"])
    cover2={int(row["source"]) for row in identities["source_to_python_rows"]}
    cover3=set(firms["direct_indices"])|set(firms["pledge_shear_indices"])
    require(not (cover&cover2 or cover&cover3 or cover2&cover3)
            and cover|cover2|cover3==set(range(N)),
            "The three candidate row classes do not partition 33 rows")
    s=steady_case()
    require(s.sigmaE==1 and s.delta<1 and
            all(theta>0 for theta in s.pledge),
            "Illustrative firm parameters changed")
    require(CSV.is_file(),"Missing regenerated main IRF CSV")
    with CSV.open(newline="",encoding="utf-8") as f:
        rows=list(csv.DictReader(f))
    bykey={(r["branch"],int(r["period"])):r for r in rows}
    require(len(bykey)==len(rows),"Duplicate path observations")
    result={}
    for branch in ("binding","slack"):
        diag=[1.]*N
        for entry in scale["branches"][branch]["coefficient_rows"]:
            i=entry["source_index"]; fac=float(entry["factor_candidate"])
            require(i in cover and math.isfinite(fac) and fac!=0,
                    "Invalid SOURCE scalar root factor")
            diag[i]=fac
        # The two Euler source-minus-Python differences are a_i*g21.
        # On the common-pledge root DG21=lambda21*DF21:
        # Python Euler = SOURCE Euler - a_i*lambda21*SOURCE pledge.
        # Coefficients MUST be evaluated at this branch's OWN solution,
        # not copied from the common stationary z=0 reference.
        t1=bykey[(branch,1)]
        t2=bykey[(branch,2)]
        def n(row,key):
            x=float(row[key+"_baseline"])
            require(math.isfinite(x) and x>0,
                    "Nonpositive branch baseline "+branch+"/"+key)
            return x
        rl=n(t1,"loan_rate")
        pi2=n(t2,"inflation")
        q2=n(t2,"capital_price")
        physical=(1-s.delta)*pi2*q2
        a={}
        for i,which in ((19,"H"),(20,"L")):
            m=s.be*(n(t1,"consumption_"+which)/
                    n(t2,"consumption_"+which))**s.sigmaE
            dual=(1/rl-m/pi2)
            a[i]=s.pledge[0 if i==19 else 1]*physical*dual
        T=[[0.]*N for _ in range(N)]
        Ti=[[0.]*N for _ in range(N)]
        for i in range(N):
            T[i][i]=diag[i]
            Ti[i][i]=1/diag[i]
        for i in (19,20):
            require(diag[i]==1.,"Firm Euler diagonal normalization changed")
            T[i][21]=-a[i]*diag[21]
            Ti[i][21]=a[i]
        err1=max_identity_error(matmul(T,Ti))
        err2=max_identity_error(matmul(Ti,T))
        require(err1<1e-12 and err2<1e-12,
                "Candidate T and explicit inverse do not multiply to I")
        determinant=math.prod(diag)
        require(math.isfinite(determinant) and determinant!=0.,
                "Candidate transformation has zero determinant")
        result[branch]={
            "candidate_diagonal_factors":diag,
            "source_common_pledge_row":21,
            "date_one_euler_shear_source_rows":[19,20],
            "branch_specific_level_common_pledge":physical,
            "branch_specific_log_shear_coefficients":{
                str(k):v for k,v in a.items()},
            "nonzero_diagonal_product":determinant,
            "minimum_abs_diagonal":min(abs(x) for x in diag),
            "max_T_Tinv_identity_error":err1,
            "max_Tinv_T_identity_error":err2,
            "source_33x33_economic_derivative_proved":False
        }
    # Both S/B inputs are read separately, but the main IRF originates in a
    # shared make_boundary(s) switching-frontier experiment. The distinct
    # same-predecessor roots are NOT tested here.
    compared_fields=("loan_rate","consumption_H","consumption_L",
                     "inflation","capital_price")
    baseline_difference=0.
    for t in (1,2):
        for field in compared_fields:
            xs=float(bykey[("slack",t)][field+"_baseline"])
            xb=float(bykey[("binding",t)][field+"_baseline"])
            require(math.isfinite(xs) and math.isfinite(xb),
                    "Nonfinite baseline metric")
            baseline_difference=max(baseline_difference,abs(xs-xb))
    shear_difference=max(abs(
        result["binding"]["branch_specific_log_shear_coefficients"][str(i)] -
        result["slack"]["branch_specific_log_shear_coefficients"][str(i)])
        for i in (19,20))
    report={
        "status":"CONDITIONAL_EXPLICIT_33_ROW_CANDIDATE_T_INVERTIBLE_NOT_SOURCE_EQUIVALENCE",
        "data_origin":"main/finite_irf_paths.csv: make_boundary switching frontier",
        "distinct_frozen_same_predecessor_roots_studied_here":False,
        "main_frontier_max_abs_branch_baseline_difference_in_10_metrics":baseline_difference,
        "max_abs_main_frontier_euler_shear_coefficient_difference":shear_difference,
        "do_not_infer_distinct_root_matrix_certificate":True,
        "row_count":N,
        "source_to_python_permutation":perm,
        "candidate_row_partition":{"nine_scalar":sorted(cover),
                                  "sixteen_identity":sorted(cover2),
                                  "eight_firm":sorted(cover3)},
        "algebraic_inverse_formula":
            "T=(I+K)D, K[19,21]=-aH, K[20,21]=-aL, K^2=0; "
            "Tinv=D^-1(I-K); det T=product(diag D)",
        "not_copied_branch_coefficients":True,
        "branches":result,
        "input_sha256":{str(p.relative_to(ROOT)):sha(p)
                        for p in (PARTIAL,IDENTITY,FIRM,CHART,ROW_MAP,CSV)},
        "not_proved":[
            "Literal equality of 33 SOURCE economic residuals with transcribed Python under common primitives",
            "Equality of all 33 source Fréchet derivatives and the candidate T",
            "SOURCE Jacobian inverse and quantitative norm radius",
            "Bank/firm/global household optimality and full infinite equilibrium",
            "Permanent growth consequences",
        ]
    }
    REPORT.parent.mkdir(parents=True,exist_ok=True)
    REPORT.write_text(json.dumps(report,indent=2,sort_keys=True)+"\n",encoding="utf-8")
    print(json.dumps({
        "status":report["status"],
        "branch_max_identity_errors":{
            branch:max(b["max_T_Tinv_identity_error"],
                       b["max_Tinv_T_identity_error"])
            for branch,b in result.items()},
        "branch_log_shear_coefficients":{
            branch:b["branch_specific_log_shear_coefficients"]
            for branch,b in result.items()},
        "report":str(REPORT)
    },indent=2))


if __name__=="__main__":
    main()

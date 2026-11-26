#!/usr/bin/env python3
"""Source-indexed 33-coordinate log-chart audit; NOT an economic operator proof.

Read the *actual* SOURCE coordinate selectors and field constructors, check
their 33-vector round-trip naming, then test that the Python decoder is the
same positive diagonal log chart conditional on using its own baseline as
SOURCE Z0. This does not identify parameters, histories, tail or bank plans.
"""
from __future__ import annotations
import hashlib
import json
import math
import re
from pathlib import Path
import finite_irf as model

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
SOURCE=ROOT/"lean/checkpoint/modules/Ventura26LiquidityAllocation/EconomicModel.lean"
ENGINE=HERE/"finite_irf.py"
P0=HERE/"inputs/rational_preconditioners.json"
OUT=HERE/"output/source_python_log_chart_alignment.json"


def require(ok,msg):
    if not ok: raise AssertionError(msg)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_names():
    code=SOURCE.read_text(encoding="utf-8")
    a=code.index("def localPrefixCoordinatesVector\n")
    b=code.index("def localPrefixCoordinatesOfVector\n",a)
    body=code[a:b]
    labels=dict((int(n),group+"."+field)
                for n,group,field in re.findall(
                  r"^\s*\|\s*(\d+)\s*=>\s*Z\.(\w+)\.(\w+)\s*$",
                  body,re.M))
    require(set(labels)==set(range(33)),
            "Missing/doubled SOURCE literal coordinate selectors")
    a=b
    b=code.index("def localPrefixEquationOfIndex",a)
    body=code[a:b]
    constructor={}
    for group in ("stateOne","controlsZero","stateTwo","controlsOne"):
        m=re.search(r"\b"+group+r"\s*:=\s*\{(.*?)\}",body,re.S)
        require(m is not None,"Missing SOURCE coordinate construction "+group)
        for field,n in re.findall(r"(\w+)\s*:=\s*z\s+(\d+)",m.group(1)):
            k=int(n)
            require(k not in constructor,"Repeated SOURCE coordinate "+str(k))
            constructor[k]=group+"."+field
    require(labels==constructor,
            "SOURCE flatten/reconstruct fields are not inverse in order")
    chart=code[code.index("noncomputable def localPrefixLogChart\n"):
               code.index("noncomputable def localReducedPrefixLogResidualVector\n")]
    require("localPrefixCoordinatesOfVector" in chart
            and "localPrefixCoordinatesVector Z0 j * Real.exp (z j)" in chart,
            "Original SOURCE positive log chart formula changed")
    return [labels[j] for j in range(33)]


def main():
    labels=source_names()
    source_prefix_fields=[
        ("stateOne",7),("controlsZero",10),("stateTwo",6),("controlsOne",10)
    ]
    require([sum(n for _,n in source_prefix_fields[:i])
             for i in range(1,5)]==[7,17,23,33],
            "SOURCE block offsets changed")
    py=ENGINE.read_text(encoding="utf-8")
    for text in ("def decode_prefix(", "base.X1[i] * math.exp(z[i])",
                 "base.U0[i] * math.exp(z[7 + i])",
                 "base.X2[i] * math.exp(z[17 + i])",
                 "base.U1[i] * math.exp(z[23 + i])"):
        require(text in py,"Python 33-dimensional chart changed: "+text)
    p=json.loads(P0.read_text(encoding="utf-8"))
    p0=[[float(x) for x in row] for row in p["P0"]]
    require(len(p0)==16 and all(len(row)==6 for row in p0),"Bad P0")
    base=model.make_boundary(model.steady_case())
    baseline=[*base.X1,*base.U0,*base.X2,*base.U1]
    require(len(baseline)==33 and all(x>0 and math.isfinite(x) for x in baseline),
            "Nonpositive SOURCE candidate baseline")
    zs=[
        [0.]*33,
        [3e-4*math.sin(j+1) for j in range(33)],
        [-7e-4*math.cos(j/3+1) for j in range(33)],
    ]
    level_max=0.; inverse_max=0.; max_jac=0.
    for z in zs:
        x1,u0,x2,u1,_=model.decode_prefix(base,p0,z)
        actual=[*x1,*u0,*x2,*u1]
        require(len(actual)==33,"Decoded Python coordinate count changed")
        expected=[b*math.exp(t) for b,t in zip(baseline,z)]
        level_max=max(level_max,max(abs(x-y) for x,y in zip(actual,expected)))
        inverse_max=max(inverse_max,max(
            abs(math.log(x/b)-t) for x,b,t in zip(actual,baseline,z)))
    h=1e-6
    at=zs[1]
    for col in range(33):
        zp=at.copy();zm=at.copy()
        zp[col]+=h;zm[col]-=h
        fp=model.decode_prefix(base,p0,zp)
        fm=model.decode_prefix(base,p0,zm)
        xp=[*fp[0],*fp[1],*fp[2],*fp[3]]
        xm=[*fm[0],*fm[1],*fm[2],*fm[3]]
        for j in range(33):
            numerical=(xp[j]-xm[j])/(2*h)
            analytic=baseline[j]*math.exp(at[j]) if col==j else 0.
            max_jac=max(max_jac,abs(numerical-analytic)/
                        max(1.,abs(analytic)))
    require(level_max<1e-11,f"Coordinate-level audit mismatch {level_max}")
    require(inverse_max<1e-11,f"Log chart inverse mismatch {inverse_max}")
    require(max_jac<3e-7,f"Chart Jacobian numerical mismatch {max_jac}")
    report={
        "status":"SOURCE_LOG_CHART_SELECTORS_AND_PYTHON_DECODER_ALIGNED_CONDITIONALLY",
        "source_chart_dimension":33,
        "source_coordinate_selectors":labels,
        "source_coordinate_field_roundtrip_syntactically_checked":True,
        "python_chart_block_offsets":[0,7,17,23,33],
        "baseline_positive":True,
        "positive_chart_inverse_formula":"z_j=log(x_j/xstar_j)",
        "analytic_chart_derivative":"Dpsi(z)=diag(xstar_j*exp(z_j))",
        "analytic_chart_inverse":"diag(1/(xstar_j*exp(z_j)))",
        "candidate_log_chart_invertible_for_positive_baselines":True,
        "off_root_probe_count":len(zs),
        "max_chart_level_discrepancy":level_max,
        "max_inverse_log_discrepancy":inverse_max,
        "max_relative_diagonal_and_offdiagonal_derivative_discrepancy":max_jac,
        "source_file_sha256":sha(SOURCE),
        "python_file_sha256":sha(ENGINE),
        "preconditioner_sha256":sha(P0),
        "source_and_python_base_data_equivalence_proved":False,
        "source_economic_33x33_residual_equivalence_proved":False,
        "source_full_jacobian_inverse_proved":False,
        "source_tail_and_infinite_equilibrium_proved":False,
    }
    OUT.parent.mkdir(parents=True,exist_ok=True)
    OUT.write_text(json.dumps(report,indent=2,sort_keys=True)+"\n",encoding="utf-8")
    print(json.dumps({"status":report["status"],"dimension":33,
                      "max_level":level_max,"max_inverse":inverse_max,
                      "max_relative_jacobian_error":max_jac,"output":str(OUT)},indent=2))


if __name__=="__main__":
    main()

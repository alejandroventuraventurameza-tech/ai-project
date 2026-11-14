#!/usr/bin/env python3
"""Audit six Python log-row derivative scales at NUMERICAL Python roots.

Original Python prefix residual has six log normalization rows (bank
rollover, labor supply, deposit Euler) at 0-based positions:
  date0: 6, 9, 10
  date1: 22, 25, 26
Genuine SOURCE uses A-B for bank/labor and 1-A/B for deposit Euler.

At a shared positive zero the correct mathematical directional
differentials are:
  d(log(A/B)) = d(A-B)/B         (bank and labor)
  d(log(A/B)) = -d(1-A/B)       (deposit Euler)

This test reproduces ACTUAL original Python fixed-policy branch
roots, not the independent free-h frontier, then checks those
identities for deterministic off-root perturbation directions using
central differences. No Lean source real evaluation, interval
arithmetic, cross-language identity, SOURCE root or infinite
competitive equilibrium is asserted.
"""
from __future__ import annotations

import hashlib
import json
import math
from pathlib import Path

import finite_irf as engine

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PYTHON = HERE / "finite_irf.py"
P0_INPUT = HERE / "inputs/rational_preconditioners.json"
SOURCE = ROOT / "lean/checkpoint/modules/Ventura26LiquidityAllocation/EconomicModel.lean"
LEAN = ROOT / "lean/candidates/Ventura26LiquidityAllocation/SourceSixLogRowJacobianRankTransportCandidate.lean"
OUT = HERE / "output/six_log_row_directional_jacobian_python_roots.json"

def require(condition, reason):
    if not condition:
        raise AssertionError(reason)

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def remaining_parts(s, base, p0, z, h):
    x1 = [base.X1[i] * math.exp(z[i]) for i in range(7)]
    u0 = [base.U0[i] * math.exp(z[7 + i]) for i in range(10)]
    x2c = [base.X2[i] * math.exp(z[17 + i]) for i in range(6)]
    x2 = engine.expand_compact_state(s, x2c)
    u1 = [base.U1[i] * math.exp(z[23 + i]) for i in range(10)]
    tail = engine.matvec(p0, z[17:23])
    u2 = [s.base[6 + i] * math.exp(tail[6 + i]) for i in range(10)]
    e0 = [base.e0[0] + h, base.e0[1]]
    aux0 = engine.auxiliary(s, base.X0, u0, x1[:2], e0)
    aux1 = engine.auxiliary(s, x1, u1, x2[:2], base.e1)
    return ((base.X0,u0,x1,u1,aux0),(x1,u1,x2,u2,aux1))

def six_row_components(s,base,p0,z,h):
    records=remaining_parts(s,base,p0,z,h)
    result={}
    for period,(state,controls,next_state,next_controls,aux) in enumerate(records):
        cw,wage,_mc,inflation,_q,rd,rl,_tightness=controls[2:]
        base_pos=6 if period==0 else 22
        vals={
            base_pos: (next_state[4],
              s.aB*rl*state[4]/inflation, "A_minus_B"),
            base_pos+3:(wage,s.chiW*aux["L"]*cw,"A_minus_B"),
            base_pos+4:(rd*(s.bw*cw/next_controls[2]),
                        next_controls[5],"one_minus_ratio"),
        }
        for index,(A,B,kind) in vals.items():
            require(math.isfinite(A) and math.isfinite(B) and A>0 and B>0,
                    f"Row {index}: outside strictly positive comparison domain")
            source_shape=A-B if kind=="A_minus_B" else 1-A/B
            result[index]=(source_shape,B,kind)
    require(sorted(result)==[6,9,10,22,25,26],"Six-row index mismatch")
    return result

def directions():
    yield [math.sin(.21*(i+1)) for i in range(33)]
    yield [math.cos(.37*(i+1)) for i in range(33)]
    yield [math.sin(.17*(i+1))+math.cos(.11*(i+1)) for i in range(33)]
    yield [1.0 if i in (6,9,10,22,25,26) else 0.0 for i in range(33)]

def main():
    require(all(p.is_file() for p in (PYTHON,P0_INPUT,SOURCE,LEAN)),
            "Pinned original Python, SOURCE or exact row-scale module missing")
    lean=LEAN.read_text(encoding="utf-8")
    for label in (
        "sourceSixLogRowScale",
        "sourceSixLogRowReweight_injective",
        "sourceSixLogRowReweight_injective_iff",
    ):
        require(label in lean,"Missing Lean declaration: "+label)
    code=PYTHON.read_text(encoding="utf-8")
    require("return result" in code and "def prefix_residual" in code,
            "Original Python evaluator changed")
    p0=json.loads(P0_INPUT.read_text(encoding="utf-8"))["P0"]
    p0=[[float(v) for v in row] for row in p0]
    require(len(p0)==16 and all(len(row)==6 for row in p0),
            "Frozen P0 dimension changed")

    s=engine.steady_case()
    base=engine.make_boundary(s)
    max_scaled_error=0.0
    max_root_residual=0.0
    total=0
    roots={}
    eps=2e-5

    for branch in ("slack","binding"):
        baseline=None
        for h in (0.0,-1e-5):
            fn=lambda z,b=branch,v=h:engine.prefix_residual(base,p0,b,v,z)
            initial=[0.0]*33 if baseline is None else baseline
            z,history,_jac=engine.newton(fn,initial,tolerance=2e-12)
            if baseline is None:
                baseline=list(z)
            root_res=engine.max_abs(fn(z))
            require(root_res<5e-10,f"Python {branch},h={h}: Newton root drift")
            max_root_residual=max(max_root_residual,root_res)
            center=six_row_components(s,base,p0,z,h)
            require(max(abs(item[0]) for item in center.values())<1e-8,
                    "Six original Python normalized rows are not close to zero")
            roots[f"{branch}:{h}"]=root_res

            for d in directions():
                zp=[v+eps*t for v,t in zip(z,d)]
                zm=[v-eps*t for v,t in zip(z,d)]
                plus=fn(zp)
                minus=fn(zm)
                srcp=six_row_components(s,base,p0,zp,h)
                srcm=six_row_components(s,base,p0,zm,h)
                for i in (6,9,10,22,25,26):
                    py_der=(plus[i]-minus[i])/(2*eps)
                    src_der=(srcp[i][0]-srcm[i][0])/(2*eps)
                    _src_center,B,kind=center[i]
                    expected=src_der/B if kind=="A_minus_B" else -src_der
                    relative=abs(py_der-expected)/(1+abs(py_der)+abs(expected))
                    require(math.isfinite(relative) and relative<2e-7,
                            f"Python row {i}, branch={branch},h={h}: derivative transport drift {relative}")
                    max_scaled_error=max(max_scaled_error,relative)
                    total+=1

    report={
        "status":"NUMERICAL_ORIGINAL_PYTHON_SIX_ROW_DIRECTIONAL_TRANSPORT_ONLY",
        "original_python_fixed_policy_root_count":len(roots),
        "original_python_fixed_policy_branches":["slack","binding"],
        "original_python_policy_innovations":[0.0,-1e-5],
        "compared_zero_based_row_indices":[6,9,10,22,25,26],
        "directional_row_comparisons":total,
        "finite_difference_half_step":eps,
        "max_absolute_python_root_residual":max_root_residual,
        "maximum_relative_directional_scale_discrepancy":max_scaled_error,
        "individual_python_root_residuals":roots,
        "true_SOURCE_economic_functions_executed":False,
        "cross_language_33_row_jacobian_identity_certified":False,
        "SOURCE_root_at_fixed_negative_policy_certified":False,
        "full_infinite_horizon_equilibrium_certified":False,
        "limitation":"The source-shaped level functions are reconstructed from original Python fields; this is a float64 numerical consistency check conditional on near-zeros, not a SOURCE interval theorem.",
        "input_sha256":{str(p.relative_to(ROOT)):digest(p)
                        for p in (PYTHON,P0_INPUT,SOURCE,LEAN)},
    }
    OUT.parent.mkdir(parents=True,exist_ok=True)
    OUT.write_text(json.dumps(report,indent=2,sort_keys=True)+"\n",encoding="utf-8")
    print(json.dumps({key:report[key] for key in (
        "status","original_python_fixed_policy_root_count",
        "directional_row_comparisons",
        "max_absolute_python_root_residual",
        "maximum_relative_directional_scale_discrepancy",
        "SOURCE_root_at_fixed_negative_policy_certified",
    )},indent=2))

if __name__=="__main__":
    main()

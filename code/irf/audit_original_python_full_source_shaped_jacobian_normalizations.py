#!/usr/bin/env python3
"""Full 33x33 NORMALIZATION/SHEAR audit on a SOURCE-shaped Python proxy.

Source-like rows:
 * 6 bank rows written with REALIZED reserve price and quantity;
 * 2 date-one Euler rows written with actual terminal pi/q pledge;
 * 6 macro rows written as the original SOURCE LEVEL equations:
   bank-face renewal, worker labor and household Euler at each date.

At the frozen stationary 33-row Python root, check 1089 entries of
  J_originalPython = T J_sourceShapedPythonProxy,
where T combines SIX positive-domain log/level normalizations with
SIX banking and TWO firm common-pledge row shears.

All original Python primitive evaluation remains shared. This is NOT
a cross-language evaluation of Lean SOURCE, a certified nonlinear root,
or an interval proof of Jacobian nonsingularity.
"""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
import finite_irf as m
from audit_original_python_33_bank_jacobian_shear import (
    N,jacobian,python_and_realized_proxy)
from audit_original_python_source_shaped_firm_rows import firm_rows
from audit_original_python_source_shaped_macro_normalizations import check_date
from frozen_stationary_prefix_audit import frozen_stationary_seed

HERE=Path(__file__).resolve().parent
P0=HERE/"inputs/rational_preconditioners.json"
OUT=HERE/"output/original_python_full_source_shaped_normalized_jacobian.json"

def require(v,msg):
    if not v: raise AssertionError(msg)

def main():
    s=m.steady_case()
    base=frozen_stationary_seed(s)
    p0=[[float(v) for v in row]
        for row in json.loads(P0.read_text(encoding="utf-8"))["P0"]]
    require(len(p0)==16 and all(len(r)==6 for r in p0),"P0 drift")
    z0=[0.0]*N
    def source_shaped_python_proxy(z):
        original,proxy,_=python_and_realized_proxy(base,p0,z)
        x1,u0,compact,u1,u2=m.decode_prefix(base,p0,z)
        x2=m.expand_compact_state(s,compact)
        aux0=m.auxiliary(s,base.X0,u0,x1[:2],base.e0)
        aux1=m.auxiliary(s,x1,u1,x2[:2],base.e1)
        aux2=m.auxiliary(s,x2,u2,x2[:2],[0.,0.])
        # Genuine SOURCE-valued Euler shapes, with next pi/q pledge.
        rows,_=firm_rows(s,x1,u1,x2,u2,aux2,aux1,"binding")
        proxy[18],proxy[20]=rows[1],rows[4]
        # Genuine SOURCE-level macro shapes, not normalized Python logs.
        first,_=check_date(s,base.X0,u0,x1,u1,aux0,aux1,
                           base.e0,original,6,0)
        second,_=check_date(s,x1,u1,x2,u2,aux1,aux2,
                            base.e1,original,22,1)
        # check_date returns (errors, economic_levels), recompute explicitly.
        _,econ0=check_date(s,base.X0,u0,x1,u1,aux0,aux1,
                            base.e0,original,6,0)
        _,econ1=check_date(s,x1,u1,x2,u2,aux1,aux2,
                            base.e1,original,22,1)
        for start,econ in ((6,econ0),(22,econ1)):
            for row in (0,3,4):
                proxy[start+row]=econ[row]
        return original,proxy

    original,proxy=source_shaped_python_proxy(z0)
    gap=max(abs(a-b) for a,b in zip(original,proxy))
    require(gap<1e-9,"No shared stationary root")
    Jpy=jacobian(lambda z: source_shaped_python_proxy(z)[0],z0)
    Jsource=jacobian(lambda z: source_shaped_python_proxy(z)[1],z0)
    _,_,bank=python_and_realized_proxy(base,p0,z0)
    x1,u0,compact,u1,u2=m.decode_prefix(base,p0,z0)
    # The six SOURCE level-to-log row scalings at a common root.
    row_scale={
        6:1.0/x1[4],9:1.0/u0[3],10:-1.0,
        22:1.0/m.expand_compact_state(s,compact)[4],
        25:1.0/u1[3],26:-1.0
    }
    expected=[row[:] for row in Jsource]
    for idx,scale in row_scale.items():
        expected[idx]=[scale*v for v in expected[idx]]
    # Banking rows are sheared by their genuine reserve-rule drivers.
    bank_targets=[]
    for c in bank:
        r,q=c["rate_idx"],c["quantity_idx"]
        for row,key in ((c["loan_idx"],"loan_rate"),
                        (c["deposit_idx"],"deposit_rate"),
                        (c["bank_idx"],"balance_rate")):
            expected[row]=[
                expected[row][j]+c[key]*expected[r][j]
                for j in range(N)]
            bank_targets.append(row)
        expected[c["bank_idx"]]=[
            expected[c["bank_idx"]][j]+
            c["balance_quantity"]*expected[q][j]
            for j in range(N)]
    # Two date-one constrained Euler rows differ by common-pledge shear.
    firm_factors=[]
    for firm in range(2):
        sdf=s.be*u1[firm]/u2[firm]
        k=s.pledge[firm]*(-1/u1[8]+sdf/u2[5])*compact[2]
        row=18+2*firm
        expected[row]=[
            expected[row][j]+k*expected[21][j]
            for j in range(N)]
        firm_factors.append(k)
    diffs=[(abs(expected[i][j]-Jpy[i][j]),i,j)
           for i in range(N) for j in range(N)]
    max_error,wi,wj=max(diffs)
    require(max_error<3e-6,
            f"Full 33x33 normalization/shear error {max_error} at {(wi,wj)}")
    require(set(bank_targets)=={14,15,16,30,31,32},
            "Bank targets drift")
    require(not(set(row_scale)&(set(bank_targets)|{18,20,21})),
            "Non-disjoint normalization row sets")
    result={
        "status":"NUMERICAL_INTERNAL_FULL_33_SOURCE_SHAPED_PYTHON_ROW_NORMALIZATION",
        "rows":N,"compared_entries":N*N,
        "six_level_to_log_rows":row_scale,
        "six_bank_sheared_rows":sorted(set(bank_targets)),
        "two_enterprise_euler_sheared_rows":[18,20],
        "single_common_pledge_row":21,
        "four_monetary_driver_rows":[12,13,28,29],
        "max_abs_full_jacobian_discrepancy":max_error,
        "worst_row":wi,"worst_coord":wj,
        "root_original_proxy_gap_max_abs":gap,
        "firm_shear_coefficients":firm_factors,
        "original_Lean_SOURCE_residuals_directly_evaluated":False,
        "actual_SOURCE_Python_jacobian_equality_proved":False,
        "interval_jacobian_invertibility_proved":False,
        "full_equilibrium_proved":False,
        "original_python_sha256":hashlib.sha256(
            (HERE/"finite_irf.py").read_bytes()).hexdigest(),
        "preconditioner_sha256":hashlib.sha256(P0.read_bytes()).hexdigest()
    }
    OUT.parent.mkdir(parents=True,exist_ok=True)
    OUT.write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8")
    print(json.dumps(result,indent=2))

if __name__=="__main__":
    main()

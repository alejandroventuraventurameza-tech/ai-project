#!/usr/bin/env python3
"""Audit the date-one two-firm Euler/Jacobian common-pledge shear.

The TRUE original SOURCE Euler row uses pledgeability_i * (1-delta)
* next inflation * next q. The frozen Python finite_irf uses instead
pledgeability_i * compact common-pledge coordinate. The original
SOURCE/Python residual gap is proportional to the common-pledge gap.

At the stationary common-pledge root g=0,
D PythonEuler_i = D SOURCEEuler_i + k_i * C * D PythonLogPledge,
where k_i = pledgeability_i*(-1/loanRate+SDF_i/next inflation),
C = common pledge coordinate. Verify this JACOBIAN identity
numerically, explicitly evaluating both SOURCE-shaped Euler formulas
with original Python primitive values; it is NOT a proof of actual
Lean SOURCE derivative equality or of full-system invertibility.
"""
from __future__ import annotations

import hashlib
import json
import math
from pathlib import Path

import finite_irf as m
from audit_original_python_source_shaped_firm_rows import firm_rows
from frozen_stationary_prefix_audit import frozen_stationary_seed

HERE=Path(__file__).resolve().parent
OUT=HERE/"output/original_python_date_one_euler_jacobian_shear.json"
P0=HERE/"inputs/rational_preconditioners.json"


def require(ok, reason):
    if not ok:
        raise AssertionError(reason)


def main():
    s=m.steady_case()
    base=frozen_stationary_seed(s)
    p0=[[float(v) for v in row]
        for row in json.loads(P0.read_text(encoding="utf-8"))["P0"]]
    require(len(p0)==16 and all(len(row)==6 for row in p0),
            "Original finite continuation drifted")
    zero=[0.0]*33
    def original(z):
        return m.prefix_residual(base,p0,"binding",(0.,0.,0.,0.),z)
    def source_shape(z):
        x1,u0,compact,u1,u2=m.decode_prefix(base,p0,z)
        x2=m.expand_compact_state(s,compact)
        aux1=m.auxiliary(s,x1,u1,x2[:2],base.e1)
        aux2=m.auxiliary(s,x2,u2,x2[:2],[0.,0.])
        rows, _=firm_rows(s,x1,u1,x2,u2,aux2,aux1,"binding")
        result=original(z)
        result[18]=rows[1]
        result[20]=rows[4]
        return result
    Jp=m.numerical_jacobian(original,zero,step=2e-6)
    Js=m.numerical_jacobian(source_shape,zero,step=2e-6)
    x1,u0,compact,u1,u2=m.decode_prefix(base,p0,zero)
    require(abs(original(zero)[21])<1e-12,
            "Common pledge log residual not zero at stationary seed")
    C=compact[2]
    max_abs=0.0
    discrepancies=[]
    for firm in range(2):
        row=18+2*firm
        sdf=s.be*u1[firm]/u2[firm]
        k=s.pledge[firm]*(-1.0/u1[8]+sdf/u2[5])
        factor=k*C
        for j in range(33):
            predicted=Js[row][j]+factor*Jp[21][j]
            error=abs(Jp[row][j]-predicted)
            max_abs=max(error,max_abs)
            discrepancies.append({"firm":firm,"coord":j,
                                  "error":error,"shear_factor":factor})
    require(max_abs<2e-8, f"Firm common-pledge Jacobian shear failed: {max_abs!r}")
    report={
        "status":"NUMERICAL_PYTHON_INTERNAL_DATE_ONE_SOURCE_SHAPED_EULER_JACOBIAN_SHEAR_ONLY",
        "source_shaped_euler_rows":[18,20],
        "single_common_pledge_log_row":21,
        "checked_jacobian_entries":66,
        "max_abs_jacobian_shear_error":max_abs,
        "shear_factors_by_firm":[discrepancies[i*33]["shear_factor"] for i in range(2)],
        "stationary_common_pledge_coordinate":C,
        "full_33_source_jacobian_equality_proved":False,
        "root_invertibility_proved":False,
        "actual_Lean_SOURCE_fderiv_evaluated":False,
        "p0_sha256":hashlib.sha256(P0.read_bytes()).hexdigest(),
        "python_sha256":hashlib.sha256((HERE/"finite_irf.py").read_bytes()).hexdigest()
    }
    OUT.parent.mkdir(parents=True,exist_ok=True)
    OUT.write_text(json.dumps(report,indent=2)+"\n",encoding="utf-8")
    print(json.dumps(report,indent=2))


if __name__=="__main__":
    main()

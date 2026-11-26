#!/usr/bin/env python3
"""Fail-closed provenance firewall: frozen Python derivative != SOURCE certificate.

The candidate 33-row transform presently uses the switching-frontier
make_boundary(s) and branch-specific paths. The new 33x33 floating
diagnostic instead uses the frozen binding predecessor. They cannot be
multiplied into a certified SOURCE inverse without an additional
SAME-BASE operator identity on an open log chart.
"""
from pathlib import Path
import hashlib
import json

ROOT=Path(__file__).resolve().parents[2]
HERE=Path(__file__).resolve().parent
OUT=HERE/"output"
SOURCE=ROOT/"lean/checkpoint/modules/Ventura26LiquidityAllocation/EconomicModel.lean"
PY=HERE/"finite_irf.py"
P0=HERE/"inputs/rational_preconditioners.json"
FLOAT=OUT/"frozen_python_33_jacobian_float_diagnostic.json"
TRANSFORM=OUT/"conditional_source_33_row_transform_inverse.json"
READINESS=OUT/"source_python_33_row_claim_readiness.json"
SEED=HERE/"frozen_stationary_prefix_audit.py"
REPORT=OUT/"jacobian_provenance_cross_baseline_firewall.json"

def require(ok,message):
    if not ok:raise AssertionError(message)

def load(path):
    require(path.is_file(),"Missing generated report: "+str(path))
    return json.loads(path.read_text(encoding="utf-8"))

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    f=load(FLOAT); t=load(TRANSFORM); r=load(READINESS)
    require(f["operator"]=="finite_irf.prefix_residual"
            and f["base"]=="frozen_stationary_seed(steady_case())"
            and f["branch"]=="binding", "Float matrix is not frozen binding root")
    require(f["log_coordinates"]==33 and f["root_max_abs_residual"]<1e-9,
            "Float diagnostic shape/root check failed")
    require(f["source_jacobian_equality_proved"] is False
            and f["source_functional_identity_proved"] is False
            and f["interval_inverse_enclosure_proved"] is False,
            "A float diagnostic falsely asserts verified SOURCE equivalence")
    require(f["input_sha256"]=={
        str(p.relative_to(ROOT)):sha(p) for p in (SOURCE,PY,P0)},
        "Stale or foreign frozen Python Jacobian diagnostic")
    require(t["distinct_frozen_same_predecessor_roots_studied_here"] is False,
            "Candidate SOURCE row transform changed its baseline provenance")
    require(t["row_count"]==33 and set(t["branches"])=={"binding","slack"},
            "Candidate transform report changed")
    require(r["rows_with_candidate"]==33
            and r["full_33_row_functional_identity_proved"] is False
            and r["full_33x33_economic_jacobian_certificate"] is False
            and r["economic_inverse_bound_certified"] is False,
            "Readiness flags falsely elevate candidate SOURCE claims")
    require(f["max_abs_left_inverse_product_error"]<1e-5
            and f["max_abs_right_inverse_product_error"]<1e-5,
            "Float inverse-product diagnostics failed")
    require("base=model.make_boundary(s)" in
            (HERE/"audit_source_firm_budget_euler_shear.py").read_text(),
            "Source firm candidate no longer explicitly uses make_boundary(s)")
    require("seed=frozen_stationary_seed(steady_case())" in
            (HERE/"audit_frozen_python_jacobian_float_diagnostic.py").read_text(),
            "Frozen Python diagnostic lost fixed predecessor")
    report={
      "status":"CROSS_BASELINE_SOURCE_CERTIFICATION_FORBIDDEN",
      "candidate_source_transform_baseline":"switching-frontier make_boundary(s) branch paths",
      "python_float_jacobian_baseline":"stationary frozen predecessor binding root",
      "baseline_identical":False,
      "cross_baseline_matrix_product_is_source_inverse":False,
      "source_python_operator_identity_proved":False,
      "same_root_source_derivative_identified":False,
      "interval_source_inverse_bound_proved":False,
      "frozen_float_diagnostic":{
        "residual_max_abs":f["root_max_abs_residual"],
        "left_inverse_max_abs_entry_error":f["max_abs_left_inverse_product_error"],
        "right_inverse_max_abs_entry_error":f["max_abs_right_inverse_product_error"],
        "float_inverse_infinity_norm":f["float_inverse_infinity_norm"]
      },
      "source_and_python_sha256":{
        str(p.relative_to(ROOT)):sha(p) for p in (SOURCE,PY,P0)},
      "reports_sha256":{str(p.relative_to(ROOT)):sha(p)
                         for p in (FLOAT,TRANSFORM,READINESS)},
      "remaining_requirement":"Prove SOURCE/Python operator identity and row transform at the SAME positive root with SAME tail before Jacobian transport"
    }
    REPORT.write_text(json.dumps(report,indent=2,sort_keys=True)+"\n",encoding="utf-8")
    print(json.dumps({"status":report["status"],
                      "cross_baseline_inverse_certified":False,
                      "report":str(REPORT)},indent=2))

if __name__=="__main__":main()

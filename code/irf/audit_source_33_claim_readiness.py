#!/usr/bin/env python3
"""Audit whether 33 SOURCE/Python candidate row reports justify a full theorem.

This is a provenance and claim-scope gate, NOT an operator proof. It is
deliberately allowed to report NOT_CERTIFIED while exiting successfully,
but it fails hard on a false certification flag or incoherent source hashes.
"""
from pathlib import Path
import hashlib
import json
import math

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
OUT=HERE/"output"
SOURCE=ROOT/"lean/checkpoint/modules/Ventura26LiquidityAllocation/EconomicModel.lean"
PYTHON=HERE/"finite_irf.py"
P0=HERE/"inputs/rational_preconditioners.json"
INPUTS={
 "scalar":OUT/"partial_source_jacobian_row_scale_ledger.json",
 "identity":OUT/"source_identity_row_candidates.json",
 "firm":OUT/"source_firm_budget_euler_shear_audit.json",
 "chart":OUT/"source_python_log_chart_alignment.json",
 "transform":OUT/"conditional_source_33_row_transform_inverse.json",
 "map":OUT/"lean_python_33_row_permutation.json",
}
REPORT=OUT/"source_python_33_row_claim_readiness.json"

def check(test,message):
    if not test: raise AssertionError(message)

def load(path):
    check(path.is_file(),"Run code/verify.py prerequisite missing: "+str(path))
    return json.loads(path.read_text(encoding="utf-8"))

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    r={k:load(v) for k,v in INPUTS.items()}
    source_hash=sha(SOURCE);python_hash=sha(PYTHON);p0_hash=sha(P0)
    s=r["scalar"];identity=r["identity"];firm=r["firm"]
    chart=r["chart"];trans=r["transform"];mapping=r["map"]
    check(s["source_row_count"]==33 and s["known_source_row_count"]==9,
          "Nine-row source ledger changed")
    nine=set(s["known_source_indices"])
    sixteen={int(x["source"]) for x in identity["source_to_python_rows"]}
    eight=set(firm["direct_indices"])|set(firm["pledge_shear_indices"])
    check(len(nine)==9 and len(sixteen)==16 and len(eight)==8,
          "Expected exactly 9+16+8 independent row slots")
    check(not (nine & sixteen or nine & eight or sixteen & eight),
          "Source-row partition overlaps")
    check(nine|sixteen|eight==set(range(33)),
          "SOURCE rows are not exhausted")
    perm=mapping["source_to_python_permutation"]
    check(len(perm)==33 and sorted(perm)==list(range(33)),
          "SOURCE-Python row permutation not bijective")
    check(chart["source_chart_dimension"]==33 and chart["baseline_positive"],
          "Positive chart data not established")
    check(trans["row_count"]==33 and
          trans["distinct_frozen_same_predecessor_roots_studied_here"] is False,
          "Candidate operator scope or baseline provenance changed")
    check(trans["source_to_python_permutation"]==perm,
          "Candidate transform and source permutation disagree")
    for key, indices in (
        ("nine_scalar",nine),
        ("sixteen_identity",sixteen),
        ("eight_firm",eight)):
        check(set(trans["candidate_row_partition"][key])==indices,
              "Candidate transform partition drift: "+key)

    # Every report's source hashes MUST match the present source files.
    def checked_hash(hash_dict,path,digest):
        key=str(path.relative_to(ROOT))
        check(hash_dict.get(key)==digest,
              "Stale or mismatched source digest: "+key)
    checked_hash(firm["source_inputs_sha256"],SOURCE,source_hash)
    checked_hash(firm["source_inputs_sha256"],PYTHON,python_hash)
    checked_hash(firm["source_inputs_sha256"],P0,p0_hash)
    checked_hash(identity["inputs_sha256"],SOURCE,source_hash)
    checked_hash(identity["inputs_sha256"],PYTHON,python_hash)
    checked_hash(identity["inputs_sha256"],P0,p0_hash)
    check(chart["source_file_sha256"]==source_hash and
          chart["python_file_sha256"]==python_hash and
          chart["preconditioner_sha256"]==p0_hash,
          "Positive chart evidence is stale")
    checked_hash(s["source_sha256"],SOURCE,source_hash)
    checked_hash(s["source_sha256"],PYTHON,python_hash)
    for branch in ("binding","slack"):
        b=trans["branches"][branch]
        check(b["source_33x33_economic_derivative_proved"] is False,
              "Candidate T incorrectly claims SOURCE derivative proof")
        check(math.isfinite(b["candidate_T_inverse_infinity_norm"])
              and b["candidate_T_inverse_infinity_norm"]>0,
              "No finite candidate inverse norm")
    required_false={
      "scalar_source_operator":s["full_source_operator_equality_certified"],
      "source_chart_economics":chart["source_economic_33x33_residual_equivalence_proved"],
      "identity_operator":identity["source_to_python_full_operator_equivalence_proved"],
      "firm_operator":firm["literal_source_operator_equality_proved"],
      "transform_jacobian":trans["branches"]["binding"]["source_33x33_economic_derivative_proved"],
      "firm_full_jacobian":firm["complete_33x33_jacobian_bridge_proved"],
      "source_inverse":s["full_source_jacobian_inverse_certified"],
      "python_source_baseline":chart["source_and_python_base_data_equivalence_proved"],
    }
    check(all(v is False for v in required_false.values()),
          "A partial report incorrectly promotes SOURCE operator certification")
    report={
      "status":"ALL_33_CANDIDATE_ROWS_PRESENT_FULL_SOURCE_OPERATOR_NOT_CERTIFIED",
      "row_partition":{"nine_scalar":sorted(nine),
                       "sixteen_identity":sorted(sixteen),
                       "eight_firm":sorted(eight)},
      "rows_with_candidate":33,
      "source_to_python_permutation_verified_from_report":True,
      "input_source_sha256":source_hash,
      "input_python_sha256":python_hash,
      "input_p0_sha256":p0_hash,
      "report_input_sha256":{k:sha(p) for k,p in INPUTS.items()},
      "direct_source_lean_operator_executed":False,
      "full_33_row_functional_identity_proved":False,
      "full_33x33_economic_jacobian_certificate":False,
      "economic_inverse_bound_certified":False,
      "distinct_branch_equilibria_certified_by_this_audit":False,
      "gates_remaining":[
        "Common SOURCE Primitives, LocalPrefixDateData, inherited state and Python decoding",
        "Functional equality of all 33 residuals on one open positive chart",
        "Proof of the complete 33x33 Jacobian transport including product rule",
        "Validated numerical or formal bound for source Jacobian inverse",
        "Economic KKT, global sufficiency, transversality and infinite equilibrium"
      ],
    }
    REPORT.write_text(json.dumps(report,indent=2,sort_keys=True)+"\n",
                      encoding="utf-8")
    print(json.dumps({"status":report["status"],
                      "rows_with_candidate":33,
                      "full_operator_certified":False,
                      "report":str(REPORT)},indent=2))

if __name__=="__main__":
    main()

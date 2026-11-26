#!/usr/bin/env python3
"""Exact-support audit of four date-zero policy tools (conditional Lean/Python).

This is a fixed-33-coordinate audit of DIRECT SOURCE announcement timing,
not an impulse response or a theorem about ENDOGENOUS date-one outcomes.

Check the literal SOURCE Primitives record update and date-0/date-1 data
constructors, then evaluate both Python branches at positive off-root points.
No external packages and no changes to calibrated inputs or figures.
"""
from __future__ import annotations

import hashlib
import json
import math
from pathlib import Path

import finite_irf as model

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
SOURCE = ROOT / "lean/checkpoint/modules/Ventura26LiquidityAllocation/EconomicModel.lean"
ENGINE = HERE / "finite_irf.py"
P0 = HERE / "inputs/rational_preconditioners.json"
OUT = HERE / "output/source_four_tool_direct_support_audit.json"

N = 33
DATE_ONE_ROWS = tuple(range(17,33))
DIRECT_DATE_ZERO_ROWS = tuple(range(12))
POLICY_DATE_ZERO_ROWS = (12,13,14,15,16)
BRANCHES = ("slack","binding")


def require(ok, why):
    if not ok:
        raise AssertionError(why)


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def literal_source_guards():
    src = SOURCE.read_text(encoding="utf-8")
    a = src.index("noncomputable def initialIntervenedPrimitives\n")
    b = src.index("/-- The three supported calendar phases", a)
    intervention = src[a:b]
    expected = (
        "reserveRateInnovation := fun s",
        "reserveQuantityInnovation := fun s",
        "reserveRequirementPath := fun t h",
        "corridorWidthPath := fun t h",
        "if s = P.tree.initial then v.reserveRateInnovation else 0",
        "if s = P.tree.initial then v.reserveQuantityInnovation else 0",
        "if t = 0 then v.reserveRequirement else 0",
        "if t = 0 then v.corridorWidth else 0",
    )
    for tag in expected:
        require(tag in intervention, "SOURCE intervention changed: "+tag)
    a0 = src.index("noncomputable def localPrefixDateZeroData\n")
    a1 = src.index("noncomputable def localPrefixDateOneData\n", a0)
    end = src.index("noncomputable def localPrefixLabor\n",a1)
    d0, d1 = src[a0:a1],src[a1:end]
    zero = (
        "reserveRateInnovation := P.reserveRateInnovation P.tree.initial",
        "reserveQuantityInnovation := P.reserveQuantityInnovation P.tree.initial",
        "reserveRequirement := P.reserveRequirementPath 0",
        "corridorWidth := P.corridorWidthPath 0",
    )
    one = (
        "reserveRateInnovation := P.reserveRateInnovation dateOne",
        "reserveQuantityInnovation := P.reserveQuantityInnovation dateOne",
        "reserveRequirement :=\n    P.reserveRequirementPath 1",
        "corridorWidth := P.corridorWidthPath 1",
    )
    for tag in zero:
        require(tag in d0, "SOURCE date-0 mapping changed: "+tag)
    for tag in one:
        require(tag in d1, "SOURCE date-1 mapping changed: "+tag)
    for name in (
        "source_initial_policy_innovation_pair",
        "source_noninitial_policy_innovations_unchanged",
        "source_initial_policy_path_pair",
        "source_future_policy_paths_unchanged",
        "source_dateone_prefix_data_fixed_coordinates_unaffected",
    ):
        # Lemmata are checked independently by the pinned Lean workflow.
        require(name in (ROOT /
            "lean/candidates/Ventura26LiquidityAllocation/HandStencilPledgeRowEquivalenceCandidate.lean"
        ).read_text(encoding="utf-8"), "SOURCE policy-timing lemma missing: "+name)
    return {
        "source_date_zero_innovation_at_initial": True,
        "source_date_zero_requirement_and_corridor_only": True,
        "source_date_one_specification_uses_unmodified_date_one": True,
    }


def compute(base,p0,branch,z,shock):
    return model.prefix_residual(base,p0,branch,shock,z)


def main():
    guard = literal_source_guards()
    pp = json.loads(P0.read_text(encoding="utf-8"))
    p0 = [[float(x) for x in row] for row in pp["P0"]]
    require(len(p0)==16 and all(len(row)==6 for row in p0),
            "Pinned stable tail graph has wrong dimension")
    base = model.make_boundary(model.steady_case())
    zs = (
        [0.]*N,
        [1e-4*math.sin(1.17*(j+1)) for j in range(N)],
        [-2e-4*math.cos(.67*(j+1)) for j in range(N)],
    )
    shocks = {
        "zero": (0.,0.,0.,0.),
        "reserve_rate": (-1e-5,0.,0.,0.),
        "reserve_quantity": (0.,-1e-5,0.,0.),
        "reserve_requirement": (0.,0.,-1e-5,0.),
        "corridor": (0.,0.,0.,-1e-5),
        "combined": (2e-5,-1e-5,-1e-5,3e-5),
    }
    max_date_one_error = 0.
    max_direct_old_error = 0.
    max_rate_rule_error = 0.
    max_quantity_rule_error = 0.
    max_aggregate_direct_violation = 0.
    changed_family = {}
    comparisons = 0
    for branch in BRANCHES:
        for z in zs:
            zero = compute(base,p0,branch,z,shocks["zero"])
            require(len(zero)==N and all(map(math.isfinite,zero)),
                    "Invalid baseline 33-vector")
            for key,v in shocks.items():
                f = compute(base,p0,branch,z,v)
                require(len(f)==N and all(map(math.isfinite,f)),
                        "Invalid shock 33-vector")
                df = [f[j]-zero[j] for j in range(N)]
                max_date_one_error = max(max_date_one_error,
                    max(abs(df[j]) for j in DATE_ONE_ROWS))
                max_direct_old_error = max(max_direct_old_error,
                    max(abs(df[j]) for j in DIRECT_DATE_ZERO_ROWS))
                max_rate_rule_error = max(max_rate_rule_error,
                    abs(df[12]+v[0]))
                max_quantity_rule_error = max(max_quantity_rule_error,
                    abs(df[13]+v[1]))
                max_aggregate_direct_violation = max(
                    max_aggregate_direct_violation,
                    max(abs(df[j]) for j in range(N)
                        if j not in POLICY_DATE_ZERO_ROWS))
                comparisons += 1
                if key != "zero" and z == zs[0]:
                    changed_family.setdefault((branch,key),{
                        "date_zero_rows_changed": [
                           model.PREFIX_ROW_NAMES[j]
                           for j in POLICY_DATE_ZERO_ROWS if abs(df[j])>1e-12
                        ],
                        "date_one_rows_changed": [
                           model.PREFIX_ROW_NAMES[j]
                           for j in DATE_ONE_ROWS if abs(df[j])>1e-12
                        ],
                    })
            # Under fixed coordinates, auxiliary() uses only date-zero
            # policy arguments at t0. Verify direct exponential entry.
            x1,u0,x2,u1,_ = model.decode_prefix(base,p0,z)
            a_ref = model.auxiliary(base.s,base.X0,u0,x1[:2],base.e0)
            for key,v in shocks.items():
                aux = model.auxiliary(base.s,base.X0,u0,x1[:2],
                    [base.e0[0]+v[0],base.e0[1]+v[1]],
                    rho=base.s.rho+v[2],corridor=base.s.Delta+v[3])
                require(abs(math.log(aux["rr"]/a_ref["rr"])-v[0])<2e-12,
                        "Rate innovation log multiplier is not literal vR")
                require(abs(math.log(aux["money"]/a_ref["money"])-v[1])<2e-12,
                        "Reserve quantity log multiplier is not literal vM")
                require(abs((aux["rho"]-a_ref["rho"])-v[2])<2e-12,
                        "Reserve requirement is not a level intervention")
                require(abs((aux["corridor"]-a_ref["corridor"])-v[3])<2e-12,
                        "Corridor width is not a level intervention")

    require(max_date_one_error<1e-13,
            "Date-one fixed-coordinate residual directly changed by v0")
    require(max_direct_old_error<1e-13,
            "Date-zero firm/household real rows directly contaminated")
    require(max_rate_rule_error<2e-12,
            "Rate policy rule must shift by minus the log innovation")
    require(max_quantity_rule_error<2e-12,
            "Reserve-quantity rule must shift by minus the log innovation")
    require(max_aggregate_direct_violation<1e-13,
            "Unexpected direct shock support outside policy date-zero rows")
    required = {
        "reserve_rate": (12,14,15),
        "reserve_quantity": (13,16),
        "reserve_requirement": (15,16),
        "corridor": (14,15),
    }
    for branch in BRANCHES:
        for kind,indices in required.items():
            observed=changed_family[(branch,kind)]["date_zero_rows_changed"]
            for j in indices:
                require(model.PREFIX_ROW_NAMES[j] in observed,
                    "Expected immediate policy row did not move: "+kind+
                    "/"+model.PREFIX_ROW_NAMES[j])

    report = {
        "status": "PASS_SOURCE_AND_PYTHON_FOUR_TOOL_DATE_ZERO_DIRECT_SUPPORT_NOT_DYNAMIC_EQUILIBRIUM",
        "source_guard": guard,
        "intervention_order": ["reserve_rate_log_innovation",
                               "reserve_quantity_log_innovation",
                               "reserve_requirement_level_shift",
                               "corridor_width_level_shift"],
        "branch_count": len(BRANCHES),
        "positive_coordinate_probe_count": len(zs),
        "policy_vectors_per_probe": len(shocks),
        "fixed_coordinate_evaluations": comparisons,
        "date_zero_support_indices": list(POLICY_DATE_ZERO_ROWS),
        "max_abs_date_one_residual_direct_shift": max_date_one_error,
        "max_abs_date_zero_real_rows_direct_shift": max_direct_old_error,
        "max_abs_rate_rule_delta_plus_vR": max_rate_rule_error,
        "max_abs_quantity_rule_delta_plus_vM": max_quantity_rule_error,
        "max_abs_shift_outside_direct_policy_rows":max_aggregate_direct_violation,
        "changed_policy_rows": {branch:{
             k:changed_family[(branch,k)] for k in shocks if k != "zero"
        } for branch in BRANCHES},
        "input_sha256": {
            str(p.relative_to(ROOT)):sha256(p)
            for p in (SOURCE,ENGINE,P0)
        },
        "source_lean_kernel_tested_in_this_python_script":False,
        "source_python_full_equilibrium_operator_identified":False,
        "date_one_endogenous_impulse_response_zero":False,
        "literal_date_one_policy_data_equality_requires_noninitial_state":True,
        "full_bank_optimization_and_infinite_horizon_TVC_verified":False,
    }
    OUT.parent.mkdir(parents=True,exist_ok=True)
    OUT.write_text(json.dumps(report,ensure_ascii=False,indent=2,sort_keys=True)
                   +"\n",encoding="utf-8")
    print(json.dumps({
       "status": report["status"],
       "evaluations": comparisons,
       "max_direct_date_one":max_date_one_error,
       "max_direct_date_zero_other":max_direct_old_error,
       "max_rule_rate_err":max_rate_rule_error,
       "max_rule_quantity_err":max_quantity_rule_error,
       "output":str(OUT)
    },indent=2))


if __name__=="__main__":
    main()

#!/usr/bin/env python3
"""Audit data provenance of the fully pinned SOURCE 33-log reference.

The exact SOURCE stationary Primitives, InheritedState, 33-vector
reference and 10x6 P0 continuation are now named in Lean source.
This audit reads their ACTUAL Lean declarations and compares their
coordinate/order contracts against the original Python
frozen_stationary_seed(steady_case()) representation.

This is not a computation of the original Lean real expressions.
Numerical checks here are original Python binary64 consistency,
not a SOURCE/Python functional equality, derivative certificate,
or original infinite-horizon equilibrium construction.
"""
from __future__ import annotations

import hashlib
import json
import math
from pathlib import Path

import finite_irf as model
from frozen_stationary_prefix_audit import frozen_stationary_seed

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
SOURCE = ROOT / "lean/checkpoint/modules/Ventura26LiquidityAllocation/EconomicModel.lean"
REAL = ROOT / "lean/candidates/Ventura26LiquidityAllocation/StationaryRealScaleCandidate.lean"
INHERITED = ROOT / "lean/candidates/Ventura26LiquidityAllocation/StationaryInheritedStateCandidate.lean"
PRIMITIVES = ROOT / "lean/candidates/Ventura26LiquidityAllocation/StationaryPrimitivesCandidate.lean"
CONCRETE = ROOT / "lean/candidates/Ventura26LiquidityAllocation/SourceStationaryFrozenP0ConcreteOperatorCandidate.lean"
PINNED = ROOT / "lean/candidates/Ventura26LiquidityAllocation/SourceFullyPinnedStationaryP0OperatorCandidate.lean"
PYTHON = HERE / "finite_irf.py"
SEED = HERE / "frozen_stationary_prefix_audit.py"
P0 = HERE / "inputs/rational_preconditioners.json"
OUT = HERE / "output/fully_pinned_source_python_reference_contract.json"

def require(ok, message):
    if not ok:
        raise AssertionError(message)

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def between(source, start, end):
    require(source.count(start) == 1 and source.count(end) >= 1,
            "Declared SOURCE section is missing or ambiguous: " + start)
    return source.split(start, 1)[1].split(end, 1)[0]

def main():
    files = (SOURCE, REAL, INHERITED, PRIMITIVES, CONCRETE, PINNED, PYTHON, SEED, P0)
    require(all(f.is_file() for f in files), "Missing original SOURCE/Python artifact")
    src = SOURCE.read_text(encoding="utf-8")
    code = PINNED.read_text(encoding="utf-8")
    real = REAL.read_text(encoding="utf-8")
    inherited = INHERITED.read_text(encoding="utf-8")
    prim = PRIMITIVES.read_text(encoding="utf-8")
    concrete = CONCRETE.read_text(encoding="utf-8")

    block = between(code,
        "noncomputable def fullyPinnedStationarySOURCEZ0 :",
        "/-- All 33 SOURCE log-reference levels")
    expected = [
        "stateOne := {", 
        "capitalH := ProposedStationaryRealScale.capital .H",
        "capitalL := ProposedStationaryRealScale.capital .L",
        "firmFaceH := ProposedStationaryRealScale.firmFace .H",
        "firmFaceL := ProposedStationaryRealScale.firmFace .L",
        "bankFace := ProposedStationaryRealScale.bankEquity",
        "reserveRateLag := ProposedStationaryBank.reserveRate",
        "reservesPreLag := ProposedStationaryRealScale.reservesPre",
        "controlsZero := ProposedStationaryRealScale.controls",
        "stateTwo := ProposedStationaryRealScale.stateSix",
        "controlsOne := ProposedStationaryRealScale.controls",
    ]
    require(all(anchor in block for anchor in expected),
            "Pinned SOURCE 33-coordinate stationary reference drifted")
    require("LocalPrefixCoordinatesPositive fullyPinnedStationarySOURCEZ0"
            in code, "33-dimensional source positivity lemma missing")
    require("fullyPinnedStationaryP0SOURCE_root_exists_iff" in code,
            "Fully pinned SOURCE 34-to-33 root equivalence missing")
    require("concreteStationaryP0SOURCE34 G fullyPinnedStationarySOURCEZ0" in code,
            "Fully pinned SOURCE residual no longer uses pinned Z0")
    for anchor in (
        "ProposedStationaryPrimitives.primitives G",
        "ProposedStationaryInheritedState.inheritedState G",
        "sourceLogLinearContinuation x0 u0 sourceFrozenP0TenControls",
        "Z0 .dateOne .recurrent",
    ):
        require(anchor in concrete,
                "Concrete SOURCE original economic data drifted: " + anchor)

    for source, anchors in (
        (src, ("def localPrefixCoordinatesVector", 
               "noncomputable def localPrefixDateZeroData",
               "noncomputable def localPrefixDateOneData")),
        (real, ("noncomputable def stateSix : LocalPrefixStateSix where",
                "noncomputable def controls : LocalPrefixControlsTen where",
                "theorem stateSix_positive", "theorem controls_positive")),
        (inherited, ("noncomputable def inheritedState (G : ℝ) : InheritedState where",
                     "capital := capital", "firmFace := firmFace",
                     "bankFace := bankEquity", "reserveRateLag :=")),
        (prim, ("noncomputable def primitives (G : ℝ)", 
                "entrepreneurDiscount := 24 / 25",
                "entrepreneurRiskAversion := 1")),
    ):
        require(all(a in source for a in anchors),
                "SOURCE stationary or original constructor contract drifted")

    s = model.steady_case()
    frozen = frozen_stationary_seed(s)
    old = model.make_boundary(s)
    source_index_order = [
        "capital_H_t1", "capital_L_t1", "firm_face_H_t1",
        "firm_face_L_t1", "bank_face_t1", "lag_rr_t1",
        "lag_m_pre_t1", "consumption_H_t0", "consumption_L_t0",
        "worker_consumption_t0", "wage_t0", "input_price_t0",
        "inflation_t0", "capital_price_t0", "deposit_rate_t0",
        "loan_rate_t0", "bank_tightness_t0", "capital_H_t2",
        "capital_L_t2", "common_pledge_t2", "bank_face_t2",
        "lag_rr_t2", "lag_m_pre_t2", "consumption_H_t1",
        "consumption_L_t1", "worker_consumption_t1",
        "wage_t1", "input_price_t1", "inflation_t1",
        "capital_price_t1", "deposit_rate_t1", "loan_rate_t1",
        "bank_tightness_t1",
    ]
    chart = [*frozen.X1, *frozen.U0, *frozen.X2, *frozen.U1]
    require(len(chart) == len(source_index_order) == 33
            and all(math.isfinite(q) and q > 0 for q in chart),
            "Original Python frozen baseline is not a positive 33-level chart")
    require(frozen.X0 == frozen.X1 and frozen.U0 == frozen.U1,
            "Original Python frozen seed no longer uses one inherited predecessor")
    require(frozen.X1 == [*s.k,*s.F,s.E,s.rr,s.M]
            and frozen.X2 == list(s.base[:6])
            and frozen.U0 == list(s.base[6:]),
            "Original frozen Python 7+10+6+10 ordering drifted")
    require(frozen.e0 == [0.0,0.0] and frozen.e1 == [0.0,0.0],
            "Original frozen Python zero-intervention baseline drifted")

    old_vs_frozen = max(abs(a-b) for a,b in zip(old.X0,frozen.X0))
    require(old_vs_frozen > 1e-8 and max(abs(v) for v in old.e1) > 1e-8,
            "Old scalar boundary baseline was inadvertently relabeled stationary")

    result = {
        "status":"PINNED_33_LEVEL_SOURCE_STATIONARY_REFERENCE_TO_FROZEN_PYTHON_ORDER_SCOPE_ONLY",
        "source_coordinate_count":33,
        "source_control_count_each_date":10,
        "source_state_one_count":7,
        "source_state_two_count":6,
        "source_33_reference_lean_declaration_anchors_checked":len(expected),
        "python_frozen_reference_positive_33_entries":True,
        "python_frozen_baseline_date_zero_and_one_controls_equal":True,
        "python_frozen_inherited_positions_same_across_dates":True,
        "date_zero_and_date_one_zero_innovations_in_python_baseline":True,
        "old_python_scalar_boundary_is_not_frozen_predecessor":True,
        "old_vs_frozen_max_inherited_state_difference":old_vs_frozen,
        "ordered_33_log_coordinates":source_index_order,
        "source_lean_real_values_numerically_executed":False,
        "source_python_33_baseline_equality_proved":False,
        "source_python_full_33_operator_functional_equivalence_proved":False,
        "source_true_33_jacobian_interval_enclosure_certified":False,
        "source_economic_root_certified":False,
        "full_infinite_horizon_equilibrium_certified":False,
        "inputs_sha256":{str(p.relative_to(ROOT)):digest(p) for p in files},
        "limitations":"Anchored SOURCE declaration order and genuine Python frozen baseline, not equality of Lean real values with float64 or an economic proof.",
    }
    OUT.parent.mkdir(parents=True,exist_ok=True)
    OUT.write_text(json.dumps(result, indent=2, sort_keys=True)+"\n",encoding="utf-8")
    print(json.dumps({k:result[k] for k in (
        "status","source_coordinate_count","python_frozen_reference_positive_33_entries",
        "old_python_scalar_boundary_is_not_frozen_predecessor",
        "source_python_full_33_operator_functional_equivalence_proved",
    )},indent=2))

if __name__ == "__main__":
    main()

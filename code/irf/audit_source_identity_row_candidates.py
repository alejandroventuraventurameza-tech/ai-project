#!/usr/bin/env python3
"""Audit 16 additional SOURCE/Python row-shape candidates on the positive chart.

This is a conditional transcription audit. SOURCE Lean is not executed here:
the code uses the same aggregate intermediates as finite_irf. It tests the
eight literal reduced SOURCE row formulas at t=0 and t=1, including policy
innovations and non-root perturbations, against the Python residual vector.
It also checks their directional derivatives in every one of 33 coordinates.

Passing DOES NOT establish equality of the 33-dimensional SOURCE operator,
an invertible coordinate chart, the four firm budget/Euler pairs, or an
infinite-horizon equilibrium. See docs/PUENTE_FILAS_IDENTIDAD_20261110.md.
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
P0_FILE = HERE / "inputs/rational_preconditioners.json"
OUT = HERE / "output/source_identity_row_candidates.json"

# (SOURCE index, Python index, Python label, localReducedRemainingResidual row)
ROWS = [
    (7, 7, "capital_supply_0", 1), (23, 23, "capital_supply_1", 1),
    (8, 8, "resources_0", 2), (24, 24, "resources_1", 2),
    (11, 11, "nkpc_0", 5), (27, 27, "nkpc_1", 5),
    (12, 12, "reserve_rate_rule_0", 6), (28, 28, "reserve_rate_rule_1", 6),
    (13, 13, "reserve_quantity_rule_0", 7),
    (29, 29, "reserve_quantity_rule_1", 7),
    (14, 14, "loan_pricing_0", 8), (30, 30, "loan_pricing_1", 8),
    (15, 15, "deposit_pricing_0", 9), (31, 31, "deposit_pricing_1", 9),
    (16, 16, "bank_balance_0", 10), (32, 32, "bank_balance_1", 10),
]
PRIOR_SCALAR_ROWS = {4, 5, 6, 9, 10, 21, 22, 25, 26}
FIRM_ROWS_OPEN = {0, 1, 2, 3, 17, 18, 19, 20}
ANCHORS = {
    1: "| 1 => d.controls.capitalPrice - 1 -",
    2: "| 2 => d.controls.workerConsumption +",
    5: "| 5 => 1 - P.priceElasticity +",
    6: "| 6 => Real.log d.currentReserveRate -",
    7: "| 7 => Real.log d.currentReservesPre -",
    8: "| 8 => d.controls.loanRate - d.currentReserveRate - averageSlope",
    9: "| 9 => d.currentReserveRate +",
    10: "| 10 => bankLoans -",
}
SOURCE_ARM = {
    "capital_supply": "capitalSupply",
    "resources": "resources",
    "nkpc": "nkpc",
    "reserve_rate_rule": "reserveRateRule",
    "reserve_quantity_rule": "reserveQuantityRule",
    "loan_pricing": "loanPricing",
    "deposit_pricing": "depositPricing",
    "bank_balance": "bankBalance",
}


def require(ok, message):
    if not ok:
        raise AssertionError(message)


def hash_file(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_shape_rows(s, state, controls, next_state, next_controls, aux, aux_next, eps):
    """Independent transcription of SOURCE remaining rows 1,2,5,...,10.

    Conditional identification of source P with s and source LocalPrefixDateData
    with these arguments is NOT proved by evaluating this function.
    """
    cw, wage, mc, pi, q, rd, rl, _ = controls[2:]
    sdf = s.bw * (cw / next_controls[2])  # sigma_W=1 only
    slope_minus, slope_plus = aux["cm"], aux["cp"]
    average_slope = (slope_minus + slope_plus) / 2.0
    difference = slope_minus - slope_plus
    rr, money, rho = aux["rr"], aux["money"], aux["rho"]
    reserve_ratio = aux["h"]
    xi = rd / rr
    ratio_y = aux["Y"] / s.Y
    require(min(rr, money, reserve_ratio, pi, ratio_y,
                next_state[5], next_state[6]) > 0,
            "Positive reserve-rule/balance chart is required")
    current_rate_rule = (
        .5 * math.log(state[5])
        + .5 * (math.log(s.rr) + 1.5 * math.log(pi)
                + .125 * math.log(ratio_y)) + eps[0]
    )
    current_quantity_rule = (
        .5 * math.log(state[6]) + .5 * math.log(s.M) + eps[1]
    )
    loans = sum(s.mass[i] * next_state[2+i]/rl for i in range(2))
    return {
        1: q - 1.0 - s.phiI * aux["inv"] / aux["K"],
        2: cw + sum(s.mass[i]*controls[i] for i in range(2))
            + aux["Gamma"] + aux["Rot"] - aux["Y"],
        5: (1.0 - s.eps + s.eps*mc
            - 150.0*pi*(pi-1.0)
            + sdf*150.0*aux_next["Y"]/aux["Y"]
              *next_controls[5]*(next_controls[5]-1.0)),
        6: math.log(next_state[5]) - current_rate_rule,
        7: math.log(next_state[6]) - current_quantity_rule,
        8: rl - rr - average_slope,
        9: (rr + (1.0-rho)*average_slope
            - (xi-rho)*s.zeta*difference/2.0 - rd),
        10: loans - (state[4]/pi + (1.0/reserve_ratio-1.0)*money),
    }


def transcribed_prefix_rows(base, p0, z, intervention):
    s = base.s
    x1 = [base.X1[i] * math.exp(z[i]) for i in range(7)]
    u0 = [base.U0[i] * math.exp(z[7+i]) for i in range(10)]
    x2c = [base.X2[i] * math.exp(z[17+i]) for i in range(6)]
    u1 = [base.U1[i] * math.exp(z[23+i]) for i in range(10)]
    u2log = model.matvec(p0, z[17:23])
    u2 = [s.base[6+i]*math.exp(u2log[6+i]) for i in range(10)]
    x2 = model.expand_compact_state(s, x2c)
    v_rate, v_quantity, v_rho, v_corridor = intervention
    eps0 = [base.e0[0]+v_rate, base.e0[1]+v_quantity]
    aux0 = model.auxiliary(
        s, base.X0, u0, x1[:2], eps0,
        rho=s.rho+v_rho, corridor=s.Delta+v_corridor)
    aux1 = model.auxiliary(s, x1, u1, x2[:2], base.e1)
    aux2 = model.auxiliary(s, x2, u2, x2[:2], [0.0, 0.0])
    bydate = (
        source_shape_rows(s, base.X0, u0, x1, u1, aux0, aux1, eps0),
        source_shape_rows(s, x1, u1, x2, u2, aux1, aux2, base.e1),
    )
    return [bydate[int(name.endswith("_1"))][remaining]
            for _, _, name, remaining in ROWS]


def main():
    source_text = SOURCE.read_text(encoding="utf-8")
    start = source_text.index("noncomputable def localReducedRemainingResidual\n")
    end = source_text.index("/-- Bank loans reconstructed", start)
    block = source_text[start:end]
    for row, anchor in ANCHORS.items():
        require(anchor in block, f"SOURCE row {row} changed: {anchor}")
    for kind, arm in SOURCE_ARM.items():
        for date, d in (("Zero", "d0"), ("One", "d1")):
            need = f"| .{arm}{date} => localReducedRemainingResidual P {d} "
            index = {"capital_supply":1, "resources":2, "nkpc":5,
                     "reserve_rate_rule":6, "reserve_quantity_rule":7,
                     "loan_pricing":8, "deposit_pricing":9, "bank_balance":10}[kind]
            require(need+str(index) in source_text,
                    f"Source row link changed: {arm}{date}")
    require(len(ROWS)==16 and len({i for i, *_ in ROWS})==16,
            "Duplicate or missing audited SOURCE indices")
    require(PRIOR_SCALAR_ROWS.isdisjoint({i for i,*_ in ROWS}),
            "New candidates overlap nine existing chart rows")
    require(set(range(33))-(PRIOR_SCALAR_ROWS |
            {i for i,*_ in ROWS})==FIRM_ROWS_OPEN,
            "Unexpected residual SOURCE indices changed")
    require(len(model.PREFIX_ROW_NAMES)==33, "Python row count drift")
    for _, pyidx, label, _ in ROWS:
        require(model.PREFIX_ROW_NAMES[pyidx]==label,
                "Python label/index mismatch for "+label)
    s = model.steady_case()
    require(s.sigmaW==1 and s.varphi==1 and s.phiI==.5
            and s.eps==6 and s.bw==.99 and s.zeta==.2
            and s.rho==.1 and s.Delta==.02,
            "Source-shaped transcription requires the pinned illustration")
    require(ENGINE.is_file() and P0_FILE.is_file(),
            "Finite engine/pinned P0 not found")
    p=json.loads(P0_FILE.read_text(encoding="utf-8"))
    p0=[[float(v) for v in row] for row in p["P0"]]
    require(len(p0)==16 and all(len(row)==6 for row in p0),
            "Pinned tail graph changed")
    base=model.make_boundary(s)
    probes=[
        (0.0,0.0,0.0,0.0),
        (-1e-5,0.0,0.0,0.0),
        (0.0,-1e-5,0.0,0.0),
        (0.0,0.0,-1e-5,0.0),
        (0.0,0.0,0.0,-1e-5),
    ]
    directions=[
        [0.0]*33,
        [5e-4*math.sin((i+1)*1.71) for i in range(33)],
        [-8e-4*math.cos((i+1)*.81) for i in range(33)]
    ]
    max_level_error=0.0
    evaluations=0
    for branch in ("slack","binding"):
        for v in probes:
            for z in directions:
                source_values=transcribed_prefix_rows(base,p0,z,v)
                python_values=model.prefix_residual(base,p0,branch,v,z)
                for n,(_,j,_,_) in enumerate(ROWS):
                    err=abs(source_values[n]-python_values[j])
                    require(math.isfinite(err), "Nonfinite audit discrepancy")
                    max_level_error=max(max_level_error,err)
                evaluations+=1

    # All 33 log coordinates are perturbed, not just a scalar illustration.
    # This is still a numerical derivative of a conditional transcription.
    h=1e-6
    z0=directions[1]
    v=probes[1]
    max_derivative_error=0.0
    for branch in ("slack","binding"):
        for col in range(33):
            zp=z0.copy(); zm=z0.copy()
            zp[col]+=h; zm[col]-=h
            fp=transcribed_prefix_rows(base,p0,zp,v)
            fm=transcribed_prefix_rows(base,p0,zm,v)
            gp=model.prefix_residual(base,p0,branch,v,zp)
            gm=model.prefix_residual(base,p0,branch,v,zm)
            for n,(_,j,_,_) in enumerate(ROWS):
                src_d=(fp[n]-fm[n])/(2*h)
                py_d=(gp[j]-gm[j])/(2*h)
                err=abs(src_d-py_d)
                require(math.isfinite(err), "Nonfinite directional Jacobian")
                max_derivative_error=max(max_derivative_error,err)
    require(max_level_error<2e-10,
            f"SOURCE-shaped residuals mismatch: {max_level_error:.3g}")
    require(max_derivative_error<5e-7,
            f"SOURCE-shaped derivatives mismatch: {max_derivative_error:.3g}")
    report={
        "status":"CONDITIONAL_16_ADDITIONAL_IDENTITY_ROW_SHAPES_NOT_SOURCE_OPERATOR_PROOF",
        "source_to_python_rows":[{"source":i,"python":j,"name":name,
                                  "source_remaining_row":k,
                                  "root_factor_candidate":1.0}
                                 for i,j,name,k in ROWS],
        "existing_nine_scalar_candidates":sorted(PRIOR_SCALAR_ROWS),
        "distinct_row_shape_candidates_total":25,
        "rows_without_a_transcription_candidate":sorted(FIRM_ROWS_OPEN),
        "off_root_scenarios_checked":evaluations,
        "full_chart_columns_checked":33,
        "derivative_branches_checked":2,
        "max_abs_conditional_level_error":max_level_error,
        "max_abs_conditional_derivative_error":max_derivative_error,
        "inputs_sha256":{str(path.relative_to(ROOT)):hash_file(path)
                         for path in (SOURCE,ENGINE,P0_FILE)},
        "source_lean_executed":False,
        "source_parameter_and_auxiliary_function_identification_proved":False,
        "source_full_33_by_33_jacobian_invertibility_proved":False,
        "source_to_python_full_operator_equivalence_proved":False,
        "firm_euler_shears_integrated":False,
        "branch_S_equilibrium_existence_proved":False,
        "infinite_horizon_equilibrium_or_permanent_growth_proved":False,
    }
    OUT.parent.mkdir(parents=True,exist_ok=True)
    OUT.write_text(json.dumps(report,indent=2,sort_keys=True)+"\n",
                   encoding="utf-8")
    print(json.dumps({
        "status":report["status"],
        "additional_candidate_rows":len(ROWS),
        "total_candidates":25,
        "still_without_candidate":len(FIRM_ROWS_OPEN),
        "off_root_evaluations":evaluations,
        "max_level_error":max_level_error,
        "max_derivative_error":max_derivative_error,
        "output":str(OUT),
    },indent=2))


if __name__=="__main__":
    main()

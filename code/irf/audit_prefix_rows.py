#!/usr/bin/env python3
"""Independent 33-row ordering/formula audit of the reduced IRF prefix.

This is a deterministic algebraic regression test, not an independent
verification of the primitives in auxiliary()/production(), nor a
certificate of full equilibrium or the 640-period nonlinear tail.

Tests every named row at perturbed *off-solution* states for both
active sets, including the slack-L loan FOC and common pledge in t=1.
Uses standard library only; does not modify figures or economic inputs.
"""
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import finite_irf as model

# Independent transcription of the residual stack, not read from PREFIX_ROW_NAMES.
DATE0 = [
    "firm_budget_0_H", "firm_capital_euler_0_H", "firm_regime_0_H",
    "firm_budget_0_L", "firm_capital_euler_0_L", "firm_regime_0_L",
    "bank_equity_0", "capital_supply_0", "resources_0", "worker_labor_0",
    "household_euler_0", "nkpc_0", "reserve_rate_rule_0",
    "reserve_quantity_rule_0", "loan_pricing_0", "deposit_pricing_0",
    "bank_balance_0",
]
DATE1 = [
    "firm_budget_1_H", "firm_capital_euler_1_H",
    "firm_budget_1_L", "firm_capital_euler_1_L", "common_pledge_1",
    "bank_equity_1", "capital_supply_1", "resources_1", "worker_labor_1",
    "household_euler_1", "nkpc_1", "reserve_rate_rule_1",
    "reserve_quantity_rule_1", "loan_pricing_1", "deposit_pricing_1",
    "bank_balance_1",
]
EXPECTED = DATE0 + DATE1

SOURCE_LABELS = {
    "firm_budget": ("eq:firmbudget", "eq:wealth"),
    "firm_capital_euler": ("eq:capitalFOC", "eq:loanFOC"),
    "firm_regime": ("eq:collateral", "eq:complementarity", "eq:loanFOC"),
    "bank_equity": ("eq:bankwealth", "eq:equityidentity"),
    "capital_supply": ("eq:q",),
    "resources": ("eq:resources",),
    "worker_labor": ("eq:household",),
    "household_euler": ("eq:household",),
    "nkpc": ("eq:nkpc",),
    "reserve_rate_rule": ("sec:v0m_source_11",),
    "reserve_quantity_rule": ("sec:v0m_source_11",),
    "loan_pricing": ("eq:bankFOCL",),
    "deposit_pricing": ("eq:bankFOCD",),
    "bank_balance": ("eq:bankbalance", "eq:IBclearing"),
    "common_pledge": ("eq:H", "eq:initial_faces_manifold"),
}


def independent_common(s, x, u, xp, up, aux, axp, date):
    """Reconstruct the 11 aggregate row values without remaining_residuals()."""
    c_w, wage, m, pi, q, r_d, r_l, tight = u[2:]
    sdf = s.bw * c_w / up[2]
    chi_m, chi_p = aux["cm"], aux["cp"]
    chi_bar = (chi_m + chi_p) / 2
    chi_gap = chi_m - chi_p
    wealth = x[4] / pi
    loan_principals = sum(s.mass[i] * xp[2+i] / r_l for i in range(2))
    return {
        f"bank_equity_{date}": math.log(xp[4] / (s.aB * r_l * x[4] / pi)),
        f"capital_supply_{date}": q - 1 - s.phiI * aux["inv"] / aux["K"],
        f"resources_{date}": c_w + sum(s.mass[i]*u[i] for i in range(2))
            + aux["Gamma"] + aux["Rot"] - aux["Y"],
        f"worker_labor_{date}": math.log(wage/(s.chiW*aux["L"]*c_w)),
        f"household_euler_{date}": math.log(r_d * sdf / up[5]),
        f"nkpc_{date}": (1-s.eps+s.eps*m
            - s.phiI*0 + -150*pi*(pi-1)
            + 150*sdf*axp["Y"]/aux["Y"] * up[5]*(up[5]-1)),
        f"reserve_rate_rule_{date}": math.log(xp[5]/aux["rr"]),
        f"reserve_quantity_rule_{date}": math.log(xp[6]/aux["money"]),
        f"loan_pricing_{date}": r_l-aux["rr"]-chi_bar,
        f"deposit_pricing_{date}": aux["rr"]+(1-aux["rho"])*chi_bar
            -(aux["xi"]-aux["rho"])*s.zeta*chi_gap/2-r_d,
        f"bank_balance_{date}": loan_principals -
            (wealth+(1/aux["h"]-1)*aux["money"]),
    }


def independent_rows(base, p0, branch, intervention, z):
    s = base.s
    x1 = [base.X1[i] * math.exp(z[i]) for i in range(7)]
    u0 = [base.U0[i] * math.exp(z[7+i]) for i in range(10)]
    x2 = [base.X2[i] * math.exp(z[17+i]) for i in range(6)]
    u1 = [base.U1[i] * math.exp(z[23+i]) for i in range(10)]
    tail = model.matvec(p0, z[17:23])
    u2 = [s.base[6+i] * math.exp(tail[6+i]) for i in range(10)]
    state2 = model.expand_compact_state(s, x2)
    aux0 = model.auxiliary(s, base.X0, u0, x1[:2],
                           [base.e0[0]+intervention, base.e0[1]])
    aux1 = model.auxiliary(s, x1, u1, state2[:2], base.e1)
    aux2 = model.auxiliary(s, state2, u2, state2[:2], [0., 0.])
    result = {}
    # t=0: borrowers' inherited promise is face F_{i,1}; principal F/R^L.
    for i, label in enumerate(("H", "L")):
        discount = s.be * u0[i] / u1[i]
        h_i = s.pledge[i] * s.ad * u1[5] * u1[6]
        r = u0[8]
        result[f"firm_budget_0_{label}"] = (
            u0[i]+u0[6]*x1[i]-x1[2+i]/r-aux0["N"][i])
        if branch == "slack" and i == 1:
            result[f"firm_capital_euler_0_{label}"] = (
                u0[6]-discount*(aux1["uk"][i]+s.ad*u1[6]))
            result[f"firm_regime_0_{label}"] = math.log(r*discount/u1[5])
        else:
            result[f"firm_capital_euler_0_{label}"] = (
                (u0[6]-h_i/r)-discount*
                (aux1["uk"][i]+s.ad*u1[6]-h_i/u1[5]))
            result[f"firm_regime_0_{label}"] = math.log(
                x1[2+i]/(h_i*x1[i]))
    result.update(independent_common(s, base.X0, u0, x1, u1, aux0, aux1, 0))
    # t=1: both firms are binding. They share J_2, an aggregate pledge factor.
    for i, label in enumerate(("H", "L")):
        discount = s.be * u1[i]/u2[i]
        h_i = s.pledge[i] * x2[2]
        effective = u1[6]-h_i/u1[8]
        result[f"firm_budget_1_{label}"] = (
            u1[i]+effective*state2[i]-aux1["N"][i])
        result[f"firm_capital_euler_1_{label}"] = (
            effective-discount*(aux2["uk"][i]+s.ad*u2[6]-h_i/u2[5]))
    result["common_pledge_1"] = math.log(x2[2]/(s.ad*u2[5]*u2[6]))
    result.update(independent_common(s, x1, u1, state2, u2, aux1, aux2, 1))
    return result


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--json",type=Path,default=None,help="optional report destination")
    args=parser.parse_args()
    assert len(DATE0)==17 and len(DATE1)==16 and len(EXPECTED)==33
    assert EXPECTED==model.PREFIX_ROW_NAMES, "Row names/order drifted"
    assert len(set(EXPECTED))==33
    text=(HERE.parents[1]/"paper/paper.tex").read_text(encoding="utf-8")
    for name in EXPECTED:
        group=next((k for k in SOURCE_LABELS if name.startswith(k)),None)
        assert group, f"No source map for {name}"
        for label in SOURCE_LABELS[group]:
            assert "\\label{"+label+"}" in text, f"Broken source label {name}: {label}"
    p=json.loads((HERE/"inputs/rational_preconditioners.json").read_text())
    p0=p["P0"]
    assert len(p0)==16 and all(len(row)==6 for row in p0)
    s=model.steady_case()
    base=model.make_boundary(s)
    z=[1e-4*math.sin((j+1)*1.73) for j in range(33)]
    errs={}
    for branch in ("slack","binding"):
        for shock in (0.,-1e-5):
            direct=independent_rows(base,p0,branch,shock,z)
            actual=model.prefix_residual(base,p0,branch,shock,z)
            assert set(direct)==set(EXPECTED)
            signed=[(name,a-direct[name]) for name,a in zip(EXPECTED,actual)]
            err=max(abs(v) for _,v in signed)
            assert math.isfinite(err) and err<1e-11, (
                f"row mapping drift: {branch}, {shock}, {sorted(signed,key=lambda x: -abs(x[1]))[:5]}")
            errs[f"{branch}/shock_{shock:g}"]=err
    # The S and B rows have deliberately different *structural* meaning for L.
    dS=independent_rows(base,p0,"slack",-1e-5,z)
    dB=independent_rows(base,p0,"binding",-1e-5,z)
    assert abs(dS["firm_regime_0_L"]-dB["firm_regime_0_L"])>1e-5
    assert abs(dS["firm_capital_euler_0_L"]-dB["firm_capital_euler_0_L"])>1e-5
    for name in DATE1:
        assert abs(dS[name]-dB[name])<1e-14, "Future active-set formulas diverged"
    output={
        "status":"pass_reduced_prefix_row_order_and_off_solution_algebra",
        "scope":"33 residual formulas, not full optimality/equilibrium/Lean",
        "date_0_rows":len(DATE0),"date_1_rows":len(DATE1),
        "max_abs_difference_by_branch":errs,
        "S_and_B_have_distinct_L_date0_equations":True,
        "common_date1_formulas":True,
    }
    if args.json is not None:
        args.json.parent.mkdir(parents=True,exist_ok=True)
        args.json.write_text(json.dumps(output,ensure_ascii=False,indent=2)+"\n",encoding="utf-8")
    print(json.dumps(output,ensure_ascii=False,indent=2))


if __name__=="__main__":
    main()

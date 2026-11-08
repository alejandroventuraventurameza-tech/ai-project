#!/usr/bin/env python3
"""Independent boundary wage/labor identities on the numerical scalar bridge.

Checks, without invoking prefix_residual or the 33-row verifier, the
homogeneity law L0/Lbar = scale^(4/5)*(wbar/w0)^2 and
w0/(wbar) cubed = (C0/Cbar)*scale^(4/5).
These necessary identities justify the written algebraic date-zero
labor closure; they DO NOT construct the Lean BoundaryWorkerLaborPackage,
nor imply a complete competitive equilibrium.
"""
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

from finite_irf import dot, scalar_boundary, steady_case


def require(ok, message):
    if not ok:
        raise AssertionError(message)


def audit(grid=15):
    s = steady_case()
    require(abs(s.alpha - .4) < 1e-15, "Unexpected capital elasticity")
    require(abs(s.beta - .5) < 1e-15, "Unexpected labor elasticity")
    require(abs(s.sigmaW-1)<1e-15 and abs(s.varphi-1)<1e-15,
            "Worker cubic closure requires log utility and unit labor curvature")
    require(all(x > 0 for x in (s.w, s.CW, s.L, s.mc)), "Nonpositive parent")
    residuals = {
        "stationary_parent_household": abs(s.w-s.chiW*s.CW*s.L),
        "firm_labor_foc": 0.0,
        "aggregate_labor_scaling": 0.0,
        "wage_cubic_equation": 0.0,
        "household_labor_foc": 0.0,
        "capital_scaling": 0.0,
    }
    for j in range(grid+1):
        rate = 1.025 + .007*j/grid
        _, z = scalar_boundary(s, rate)
        require(all(z[k] > 0 for k in ("w", "cw", "scale")), "Nonpositive bridge")
        labor=[]
        for i in range(2):
            capital = z["k"][i]
            ell = ((s.beta*s.mc*s.technology[i]*capital**s.alpha)/z["w"])**(1.0/(1.0-s.beta))
            require(ell > 0, f"Nonpositive labor {i}")
            labor.append(ell)
            firm_wage = s.beta*s.mc*s.technology[i]*capital**s.alpha*ell**(s.beta-1.0)
            residuals["firm_labor_foc"] = max(residuals["firm_labor_foc"],
                                               abs(firm_wage-z["w"]))
            residuals["capital_scaling"] = max(residuals["capital_scaling"],
                                               abs(capital/s.k[i]-z["scale"]))
        total_labor = dot(s.mass,labor)
        predicted_labor_ratio=z["scale"]**(s.alpha/(1.0-s.beta))*(s.w/z["w"])**(1.0/(1.0-s.beta))
        residuals["aggregate_labor_scaling"]=max(residuals["aggregate_labor_scaling"],
            abs(total_labor/s.L-predicted_labor_ratio))
        x=z["w"]/s.w
        y=z["cw"]/s.CW
        residuals["wage_cubic_equation"]=max(residuals["wage_cubic_equation"],
            abs(x**3-y*z["scale"]**(4.0/5.0)))
        residuals["household_labor_foc"]=max(residuals["household_labor_foc"],
            abs(z["w"]-s.chiW*z["cw"]*total_labor))
    require(max(residuals.values()) < 1e-11,
            f"Boundary labor scaling or household FOC failed: {residuals}")
    return {
        "status": "passed_conditional_numerical_wage_bridge_only",
        "samples": grid+1,
        "bracket_loan_rate": [1.025,1.032],
        "max_absolute_errors": residuals,
        "analytical_cubic": "(w0/wbar)^3 = (CW0/CWbar)*scale^(4/5)",
        "lean_source_package_fulfilled": False,
        "full_competitive_equilibrium_established": False,
    }


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--grid", type=int, default=15)
    parser.add_argument("--output", type=Path, default=None)
    args=parser.parse_args()
    require(args.grid >= 2, "grid requires >=2")
    result=audit(args.grid)
    if args.output is not None:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8")
    print(json.dumps(result,indent=2))


if __name__=="__main__":
    main()

#!/usr/bin/env python3
"""Compare B/S active sets using the SAME stationary inherited state.

B: both firms' date-zero collateral constraints bind.
S: H binds and L is slack at date zero; both bind at date one.

Two distinct gates:
  (i) exact-rational local exclusion of S in a stated coordinate ball;
  (ii) bounded, deterministic numerical search for distant S roots.
A numerical failure to find S does NOT prove global nonexistence.

No source-level competitive equilibrium, infinite-horizon optimality, bank
value, causal IRF, identification, or growth result is established.
"""
from __future__ import annotations

import json
import math
from fractions import Fraction as Q
from pathlib import Path

from finite_irf import (
    PREFIX_ROW_NAMES, auxiliary, decode_prefix, expand_compact_state,
    max_abs, newton, period_metrics, prefix_residual, steady_case,
)
from frozen_stationary_prefix_audit import frozen_stationary_seed
from frozen_four_tool_impact_audit import SHOCKS

HERE = Path(__file__).resolve().parent
OUT = HERE / "output" / "same_predecessor_branch_audit.json"
RADIUS = Q(1, 500)
TOL = 1.0e-8


def exact_local_exclusion(s):
    """Exact rational outer inequalities for the stationary L dual.

    Model literals: RD=100/99, be=24/25, Delta=1/50,
    rho=1/10, zeta=1/5, aa=tight=1/2.
    sqrt(3/2)>1 implies vv=1/(1+sqrt(3/2))<1/2.
    Thus cm<3/200, cp<1/400, cbar<7/800,
    0<cd<3/200, and 0<ar<RD.
    Since RD^2+2*RD*zeta*(3/200)<(51/50)^2,
    rr<(RD+51/50)/2; RL=rr+cbar<41/40.
    For ||z||_inf<=1/500, the SOURCE normalized L dual
       1/RL(z) - be*cL0(z)/(cL1(z)*Pi1(z))
    is bounded below by
       (40/41)*(1-r) - (24/25)/(1-3*r)>0.
    Here exp(-r)>=1-r and exp(3r)<=1/(1-3r).
    S requires this same dual be zero, so no S root exists
    inside this ball for ANY intervention vector.
    This certifies rational arithmetic in an independently
    translated analytic argument, not a Lean source theorem.
    """
    params = {
        "rd": (s.rd, Q(100, 99)),
        "be": (s.be, Q(24, 25)),
        "Delta": (s.Delta, Q(1, 50)),
        "rho": (s.rho, Q(1, 10)),
        "zeta": (s.zeta, Q(1, 5)),
        "aa": (s.aa, Q(1, 2)),
        "tight": (s.tight, Q(1, 2)),
        "steady_inflation": (s.base[9], Q(1, 1)),
        "steady_C_L_0_equals_C_L_1": (s.cc[1], Q(str(s.cc[1]))),
    }
    for name, (value, expected) in params.items():
        if not math.isclose(value, float(expected), rel_tol=1e-13, abs_tol=1e-14):
            raise AssertionError(f"Stationary source parameter changed: {name}")
    rd, zeta = Q(100, 99), Q(1, 5)
    cm_ub, cp_ub, cbar_ub = Q(3, 200), Q(1, 400), Q(7, 800)
    sqrt_ub, rate_ub = Q(51, 50), Q(41, 40)
    if not ((cm_ub + cp_ub)/2 == cbar_ub):
        raise AssertionError("Incorrect corridor price bound")
    if not (rd*rd + 2*rd*zeta*cm_ub < sqrt_ub*sqrt_ub):
        raise AssertionError("Gross reserve rate radicand bound failed")
    derived_rate_ub = (rd + sqrt_ub)/2 + cbar_ub
    if not derived_rate_ub < rate_ub:
        raise AssertionError("Stationary loan gross rate bound failed")
    if not (0 < s.cm < float(cm_ub)
            and 0 < s.cp < float(cp_ub)
            and 0 < s.cd < float(cm_ub)
            and 0 < s.ar if hasattr(s, "ar") else
            (0 < s.cm < float(cm_ub)
             and 0 < s.cp < float(cp_ub)
             and 0 < s.cd < float(cm_ub))):
        raise AssertionError("Float consistency of corridor slope bounds failed")
    if not s.rate < float(derived_rate_ub):
        raise AssertionError("Float source rate violates rational outer bound")
    r = RADIUS
    if not (r > 0 and 3*r < 1):
        raise AssertionError("Invalid coordinate-ball radius")
    dual_floor = 1/rate_ub*(1-r) - Q(24, 25)/(1-3*r)
    if not dual_floor > 0:
        raise AssertionError("No strict rational lower bound on L dual")
    return {
        "translation": "independent exact rational outer inequalities",
        "status": "EXACT_RATIONAL_LOCAL_OBSTRUCTION_CONDITIONAL_ON_SOURCE_FORMULAS",
        "radius_linf_log_coordinates": str(r),
        "coordinate_radius_float": float(r),
        "derived_stationary_gross_loan_rate_upper": str(derived_rate_ub),
        "assumed_simple_gross_loan_rate_upper": str(rate_ub),
        "source_stationary_gross_loan_rate_float_sanity": s.rate,
        "exact_L_normalized_collateral_dual_lower": str(dual_floor),
        "exact_L_normalized_collateral_dual_lower_decimal": float(dual_floor),
        "implication": (
            "No root of L-slack row 06 in the closed 33-coordinate ball, "
            "for any four-tool shock, if SOURCE definitions match translation"
        ),
        "not_established": "global nonexistence of S or Lean kernel reflection",
    }


def numeric_candidate(s, seed, p0, policy, z, branch):
    """Independently audit date 0 and date 1 KKT necessary sign conditions."""
    x1, u0, x2, u1, u2 = decode_prefix(seed, p0, z)
    state2 = expand_compact_state(s, x2)
    a0 = auxiliary(
        s, seed.X0, u0, x1[:2],
        [seed.e0[0] + policy[0], seed.e0[1] + policy[1]],
        rho=s.rho + policy[2], corridor=s.Delta + policy[3],
    )
    a1 = auxiliary(s, x1, u1, state2[:2], seed.e1)
    m0 = period_metrics(
        s, seed.X0, u0, x1, u1,
        [seed.e0[0] + policy[0], seed.e0[1] + policy[1]],
        branch, rho=s.rho + policy[2], corridor=s.Delta + policy[3],
    )
    m1 = period_metrics(s, x1, u1, state2, u2, seed.e1, "binding")
    necessary = {}
    for t, (state, controls, nxt, controls_next, a, m) in enumerate((
        (seed.X0, u0, x1, u1, a0, m0),
        (x1, u1, state2, u2, a1, m1),
    )):
        for i, name in enumerate(("H", "L")):
            sdf = s.be*controls[i]/controls_next[i]
            h = s.pledge[i]*s.ad*controls_next[5]*controls_next[6]
            normdual = 1/controls[8]-sdf/controls_next[5]
            gap = h*nxt[i]-nxt[2+i]
            capital_foc = (
                controls[6]
                - sdf*(m["next_marginal_product_"+name]
                       + s.ad*controls_next[6])
                - normdual*h
            )
            budget = (
                controls[i]+controls[6]*nxt[i]
                - nxt[2+i]/controls[8]-a["N"][i]
            )
            deposit_corner_dual = 1.0 - sdf*controls[7]/controls_next[5]
            require_active = (t > 0 or name == "H" or branch == "binding")
            ok = (
                normdual > TOL and abs(gap) < TOL
                if require_active else
                abs(normdual) < TOL and gap > TOL
            )
            necessary[f"{t}_{name}"] = {
                "active_set": "binding" if require_active else "slack",
                "dual_normalized": normdual,
                "pledge_gap_face_units": gap,
                "capital_foc_residual": capital_foc,
                "firm_budget_residual": budget,
                "deposit_corner_dual": deposit_corner_dual,
                "satisfies_complementarity": bool(ok),
                "satisfies_other_firm_FOCs": bool(
                    abs(capital_foc) < TOL
                    and abs(budget) < TOL
                    and deposit_corner_dual > -TOL
                    and a["N"][i] > 0
                ),
            }
    margin_checks = {
        "bank_caps_date0": m0["deposit_cap_slack"] > TOL
                             and m0["loan_cap_slack"] > TOL,
        "bank_caps_date1": m1["deposit_cap_slack"] > TOL
                             and m1["loan_cap_slack"] > TOL,
        "payment_sign_date0": m0["payment_sign_minus"] > TOL
                              and m0["payment_sign_plus"] > TOL,
        "payment_sign_date1": m1["payment_sign_minus"] > TOL
                              and m1["payment_sign_plus"] > TOL,
        "bank_solvency_date0": m0["bank_solvency_minus"] > 0
                              and m0["bank_solvency_plus"] > 0,
        "bank_solvency_date1": m1["bank_solvency_minus"] > 0
                              and m1["bank_solvency_plus"] > 0,
        "positive_spreads": m0["xi_minus_rho"] > TOL
                            and m1["xi_minus_rho"] > TOL,
    }
    admissible = (
        all(v["satisfies_complementarity"] and v["satisfies_other_firm_FOCs"]
            for v in necessary.values())
        and all(margin_checks.values())
    )
    return {
        "admissible_necessary_conditions_only": bool(admissible),
        "firm_KKT_date0_date1": necessary,
        "bank_and_payment_margin_checks": margin_checks,
        "date0_output": m0["output"],
        "date0_loan_rate": m0["loan_rate"],
        "date0_capital_next_H_L": [x1[0], x1[1]],
        "date0_credit_H_L": [m0["credit_H"], m0["credit_L"]],
        "next_L_collateral_slack_ratio": m0["collateral_slack_L"],
        "next_L_normalized_collateral_dual": m0["collateral_dual_L"],
    }


def slack_seeds(binding_z, s, seed):
    """Start from B and enforce the L loan Euler equality in 3 distinct ways."""
    x1, u0, x2, u1, u2 = decode_prefix(seed, [[0.0]*6]*16, binding_z)
    loan_foc_log = math.log(u0[8] * s.be*u0[1]/u1[1]/u1[5])
    variants = [("binding_root", list(binding_z))]
    for label, coordinate, delta in (
        ("shift_current_L_consumption", 8, -loan_foc_log),
        ("shift_future_L_consumption", 24, +loan_foc_log),
        ("shift_future_inflation", 28, +loan_foc_log),
    ):
        trial = list(binding_z)
        trial[coordinate] += delta
        variants.append((label, trial))
    return variants


def main():
    s = steady_case()
    seed = frozen_stationary_seed(s)
    p0_data = json.loads(
        (HERE / "inputs/rational_preconditioners.json").read_text(
            encoding="utf-8"
        )
    )
    p0 = [[float(x) for x in row] for row in p0_data["P0"]]
    if len(p0) != 16 or any(len(r) != 6 for r in p0):
        raise AssertionError("Pinned 16x6 tail graph changed")
    if len(PREFIX_ROW_NAMES) != 33:
        raise AssertionError("Expected original 33-row system")
    theorem = exact_local_exclusion(s)
    snapshot = tuple(seed.X0)
    experiments = {
        "zero_shock": (0.0, 0.0, 0.0, 0.0),
        **SHOCKS,
    }
    results = {}
    for name, shock in experiments.items():
        fB = lambda z: prefix_residual(seed, p0, "binding", shock, z)
        b_root, _, _ = newton(fB, [0.0]*33, tolerance=2e-12)
        b_resid = max_abs(fB(b_root))
        if not b_resid < 1e-10:
            raise AssertionError(f"{name}: no B numerical root")
        bcheck = numeric_candidate(s, seed, p0, shock, b_root, "binding")
        if not bcheck["admissible_necessary_conditions_only"]:
            raise AssertionError(f"{name}: B numerical KKT sign gate failed")
        if max_abs(b_root) >= float(RADIUS):
            raise AssertionError(f"{name}: B root outside local ball")
        fS = lambda z: prefix_residual(seed, p0, "slack", shock, z)
        candidates = []
        errors = []
        for trial_name, trial in slack_seeds(b_root, s, seed):
            try:
                s_root, history, _ = newton(
                    fS, trial, tolerance=2e-12, max_iterations=25
                )
                s_resid = max_abs(fS(s_root))
                if s_resid >= 1e-9:
                    errors.append({
                        "trial": trial_name,
                        "failure": "nonlinear residual above 1e-9",
                        "max_abs": s_resid,
                    })
                    continue
                local_distance = max_abs(s_root)
                if local_distance <= float(RADIUS):
                    raise AssertionError(
                        f"{name}: S root would contradict rational exclusion"
                    )
                sc = numeric_candidate(s, seed, p0, shock, s_root, "slack")
                candidates.append({
                    "trial": trial_name,
                    "log_coordinate_norm_inf": local_distance,
                    "maximum_residual_33_rows": s_resid,
                    "candidate": sc,
                })
                if sc["admissible_necessary_conditions_only"]:
                    break
            except (ArithmeticError, ValueError, OverflowError,
                    ZeroDivisionError) as exc:
                errors.append({
                    "trial": trial_name,
                    "solver_error_type": type(exc).__name__,
                    "message": str(exc)[:280],
                })
        valid = [x for x in candidates
                 if x["candidate"]["admissible_necessary_conditions_only"]]
        results[name] = {
            "policy_vector_vR_vM_vRho_vDelta": list(shock),
            "same_initial_X0_for_both_active_sets": True,
            "B": {
                "maximum_residual_33_rows": b_resid,
                "log_coordinate_norm_inf": max_abs(b_root),
                "necessary_condition_gate": bcheck,
            },
            "S": {
                "algebraic_roots_found": len(candidates),
                "economically_admissible_necessary_condition_roots": len(valid),
                "qualified_candidate": valid[0] if valid else None,
                "other_converged_roots": (
                    [x for x in candidates
                     if not x["candidate"]["admissible_necessary_conditions_only"]][:2]
                ),
                "failed_trial_diagnostics": errors,
                "status": (
                    "NUMERICAL_KKT_NECESSARY_CANDIDATE_FOUND"
                    if valid else
                    "NO_ADMISSIBLE_S_CANDIDATE_FOUND_IN_BOUNDED_SEARCH"
                ),
                "global_nonexistence_proved": False,
            },
        }
        print(json.dumps({
            "scenario": name,
            "B_max_33_residual": b_resid,
            "B_norm_inf": max_abs(b_root),
            "S_admissible_candidates": len(valid),
            "S_algebraic_roots": len(candidates),
            "S_trials_failed": len(errors),
        }), flush=True)
        if tuple(seed.X0) != snapshot:
            raise AssertionError(f"{name}: inherited state changed")
    payload = {
        "status": "NUMERICAL_SAME_PREDECESSOR_BRANCH_DIAGNOSTIC_ONLY",
        "source_code_row_count": 33,
        "fixed_inherited_X0": list(snapshot),
        "date_one_rule_innovations": list(seed.e1),
        "linear_tail": "pinned local P0 16-by-6",
        "rational_local_S_exclusion": theorem,
        "scenarios": results,
        "not_established": [
            "global nonexistence of the S branch if no solver finds it",
            "validity of either branch as an infinite-horizon equilibrium",
            "structural identification or policy effect on trend growth",
        ],
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    content = json.dumps(payload, indent=2, ensure_ascii=False) + "\n"
    OUT.write_text(content, encoding="utf-8")
    print(json.dumps({
        "report_path": str(OUT),
        "local_S_exclusion_radius": float(RADIUS),
        "exact_dual_lower_bound": theorem[
            "exact_L_normalized_collateral_dual_lower"
        ],
        "scenarios": {name: {
            "S": r["S"]["status"],
            "S_qualified_candidate": bool(r["S"]["qualified_candidate"]),
        } for name, r in results.items()},
    }, indent=2))


if __name__ == "__main__":
    main()

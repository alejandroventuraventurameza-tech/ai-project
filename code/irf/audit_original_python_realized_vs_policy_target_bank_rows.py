#!/usr/bin/env python3
"""Audit ORIGINAL Python banking rows where SOURCE uses REALIZED monetary states.

In the original Lean SOURCE economic model, bank pricing/balance rows
8,9,10 depend on currentReserveRate and/or currentReservesPre, i.e. the
realized current date monetary-state levels. In original Python,
auxiliary() computes reserve-rate and reserve-quantity policy TARGETS
and the banking equations substitute those targets OFF ROOT.

This audit measures the exact algebraic cross-row gaps in the ORIGINAL
Python engine at both dates and under off-root perturbations. It
reconstructs SOURCE-shaped counterparts only using ORIGINAL Python
primitives and bank intermediary functions. Crucially it holds the OTC
slope values at the original Python auxiliary values; equality of
those slopes to their Lean SOURCE counterparts remains UNPROVEN.

Not a SOURCE/Python function theorem, not a rigorous interval error
bound, not a SOURCE root, and not an infinite-horizon equilibrium.
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
PYTHON = HERE / "finite_irf.py"
SOURCE = ROOT / "lean/checkpoint/modules/Ventura26LiquidityAllocation/EconomicModel.lean"
LEAN = ROOT / "lean/candidates/Ventura26LiquidityAllocation/SourceReserveRuleTargetSubstitutionCandidate.lean"
P0 = HERE / "inputs/rational_preconditioners.json"
OUT = HERE / "output/original_python_realized_vs_policy_target_bank_rows.json"

def require(condition, message):
    if not condition:
        raise AssertionError(message)

def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def assert_near(actual, expected, label, tol=2e-11):
    require(math.isfinite(actual) and math.isfinite(expected)
            and abs(actual-expected) <= tol*(1+abs(actual)+abs(expected)),
            f"{label}: {actual} != {expected}")
    return abs(actual-expected)

def check_date(s, state, controls, next_state, next_controls, aux, aux_next):
    """Check actual original-Python rows against same-aux SOURCE-shaped proxy."""
    rows = model.remaining_residuals(
        s, state, controls, next_state, next_controls, aux, aux_next)
    require(len(rows)==11, "Unexpected original Python remaining row count")
    realized_R = next_state[5]
    realized_M = next_state[6]
    target_R = aux["rr"]
    target_M = aux["money"]
    rd,rl = controls[7],controls[8]
    inflation = controls[5]
    tightness = controls[9]
    cb,cd,rho = aux["cb"],aux["cd"],aux["rho"]
    require(all(math.isfinite(x) and x>0 for x in
                (realized_R,realized_M,target_R,target_M,
                 rd,rl,inflation,aux["h"])),
            "Nonpositive log/ratio bank domain in original Python")
    h_actual = rho+(rd/realized_R-rho)*s.zeta*(
        1-tightness)/(1+tightness)
    require(h_actual>0 and math.isfinite(h_actual),
            "Nonpositive source-shaped realized-rate reserve ratio")

    bank_loans = model.dot(s.mass,
        [next_state[2+i]/rl for i in range(2)])
    bank_face_real = state[4]/inflation
    proxy_source_loan = rl-realized_R-cb
    proxy_source_deposit = (realized_R+(1-rho)*cb
        -(rd/realized_R-rho)*s.zeta*cd/2-rd)
    proxy_source_balance = (bank_loans -
        (bank_face_real+(1/h_actual-1)*realized_M))

    rate_gap = target_R*math.expm1(rows[6])
    money_gap = target_M*math.expm1(rows[7])
    errors=[
        assert_near(realized_R-target_R,rate_gap,
                    "policy-rate realized-target exact exponential gap"),
        assert_near(realized_M-target_M,money_gap,
                    "reserve-quantity realized-target exact exponential gap"),
    ]
    # P - SRC: loan price substitutes target for realized rate.
    loan_gap = rate_gap
    # Deposit price substitutes target rate both directly and in xi=rd/R.
    deposit_gap = -rate_gap*(
        1+rd*s.zeta*cd/(2*realized_R*target_R))
    # Balance substitutes BOTH the target reserve amount and reserve ratio
    # computed at target R. The omitted SOURCE/Python OTC-slope bridge does
    # not enter this balance expression.
    balance_gap = (
        (1/h_actual-1)*money_gap +
        (1/h_actual-1/aux["h"])*target_M
    )
    errors += [
        assert_near(rows[8]-proxy_source_loan,loan_gap,
                    "source-shaped loan-pricing correction"),
        assert_near(rows[9]-proxy_source_deposit,deposit_gap,
                    "source-shaped deposit-pricing correction"),
        assert_near(rows[10]-proxy_source_balance,balance_gap,
                    "source-shaped balance correction"),
    ]
    # Original Python policy equations are the zero-test for collapsing
    # these substitutions at a genuine common policy-rule root.
    return {
        "max_identity_error":max(errors),
        "max_realized_target_gap":max(abs(realized_R-target_R),
                                       abs(realized_M-target_M)),
        "max_banking_row_gap":max(abs(rows[8]-proxy_source_loan),
            abs(rows[9]-proxy_source_deposit),
            abs(rows[10]-proxy_source_balance)),
        "rate_gap":realized_R-target_R,
        "money_gap":realized_M-target_M,
    }

def main():
    files=(PYTHON,SOURCE,LEAN,P0)
    require(all(p.is_file() for p in files), "Missing economic source inputs")
    source=SOURCE.read_text(encoding="utf-8")
    proofs=LEAN.read_text(encoding="utf-8")
    anchors=(
        "currentReserveRate := Z.stateOne.reserveRateLag",
        "currentReservesPre := Z.stateOne.reservesPreLag",
        "currentReserveRate := Z.stateTwo.reserveRateLag",
        "currentReservesPre := Z.stateTwo.reservesPreLag",
        "| 8 => d.controls.loanRate - d.currentReserveRate - averageSlope",
        "let xi := d.controls.depositRate / d.currentReserveRate",
        "let reserveDepositRatio := localPrefixReserveDepositRatio P d",
        "(1 / reserveDepositRatio - 1) * d.currentReservesPre",
    )
    require(all(x in source for x in anchors),
            "ACTUAL SOURCE realized monetary-state contract changed")
    for name in ("sourceActualReserveRate_target_gap",
                 "sourceActualReserves_target_gap",
                 "sourceLoanPricing_rateTarget_substitution",
                 "sourceBankBalance_quantityTarget_substitution"):
        require("theorem "+name in proofs, "Lean candidate missing: "+name)

    matrix = [[float(v) for v in row]
              for row in json.loads(P0.read_text(encoding="utf-8"))["P0"]]
    require(len(matrix)==16 and all(len(row)==6 for row in matrix),
            "Original frozen 16x6 P0 changed")
    s=model.steady_case()
    base=frozen_stationary_seed(s)
    require(base.e0==[0.,0.] and base.e1==[0.,0.],
            "Stationary source-like predecessor drift")
    charts=(
        [0.0]*33,
        [4e-4*math.sin(.47*(i+1)) for i in range(33)],
        [-5e-4*math.cos(.31*(i+1)) for i in range(33)],
    )
    shocks=(
        (0.,0.,0.,0.),
        (-1e-5,0.,0.,0.),
        (0.,-1e-5,0.,0.),
        (0.,0.,-1e-5,0.),
        (0.,0.,0.,-1e-5),
    )
    count=0
    max_id=max_gap=max_row=0.0
    largest=None
    nonzero=0
    for branch in ("binding","slack"):
        for shock in shocks:
            for n,z in enumerate(charts):
                x1=[base.X1[i]*math.exp(z[i]) for i in range(7)]
                u0=[base.U0[i]*math.exp(z[7+i]) for i in range(10)]
                x2c=[base.X2[i]*math.exp(z[17+i]) for i in range(6)]
                x2=model.expand_compact_state(s,x2c)
                u1=[base.U1[i]*math.exp(z[23+i]) for i in range(10)]
                tail=model.matvec(matrix,z[17:23])
                u2=[s.base[6+i]*math.exp(tail[6+i]) for i in range(10)]
                e0=[base.e0[0]+shock[0],base.e0[1]+shock[1]]
                aux0=model.auxiliary(s,base.X0,u0,x1[:2],e0,
                                      rho=s.rho+shock[2],
                                      corridor=s.Delta+shock[3])
                aux1=model.auxiliary(s,x1,u1,x2[:2],base.e1)
                aux2=model.auxiliary(s,x2,u2,x2[:2],[0.,0.])
                pairs=(
                    (base.X0,u0,x1,u1,aux0,aux1),
                    (x1,u1,x2,u2,aux1,aux2)
                )
                for t,data in enumerate(pairs):
                    stat=check_date(s,*data)
                    max_id=max(max_id,stat["max_identity_error"])
                    max_gap=max(max_gap,stat["max_realized_target_gap"])
                    if stat["max_banking_row_gap"]>max_row:
                        max_row=stat["max_banking_row_gap"]
                        largest={"branch":branch,"shock":list(shock),
                                 "chart":n,"date":t}
                    if stat["max_banking_row_gap"]>1e-11:
                        nonzero+=1
                    count+=1
                orig=model.prefix_residual(base,matrix,branch,shock,z)
                require(len(orig)==33 and all(math.isfinite(x) for x in orig),
                        "Original Python finite-prefix residual drift")
    require(count==60,"Unexpected number of two-date banking records")
    require(nonzero>0,
            "No off-root target-vs-realized bank gap: unexpected evaluator change")
    report={
        "status":"EXPOSED_OFF_ROOT_SOURCE_VS_PYTHON_MONETARY_STATE_TARGET_MISMATCH",
        "date_records":count,
        "original_source_currentReserveRate_is_realized":True,
        "original_source_currentReservesPre_is_realized":True,
        "original_python_bank_rows_use_policy_targets":True,
        "proxy_slope_model":"Hold original Python OTC slopes fixed; NOT an executed Lean SOURCE slope",
        "source_bank_rate_target_substitution_claim_proved_by_this_script":False,
        "source_python_33_row_offroot_literal_identity":False,
        "source_python_33_root_set_equivalence_certified":False,
        "max_relative_polynomial_exponential_identity_error":max_id,
        "max_abs_realized_target_rate_or_reserve_gap":max_gap,
        "max_abs_original_python_vs_realized_proxy_banking_row_gap":max_row,
        "nonzero_banking_row_mismatch_records":nonzero,
        "largest_gap_case":largest,
        "missing_bridge":"Prove SOURCE OTC slopes, reserve ratio, realized/target substitution and their derivatives match original Python formula on a common calibrated chart",
        "true_SOURCE_real_residual_executed":False,
        "true_SOURCE_fixed_policy_root_certified":False,
        "full_infinite_horizon_equilibrium_certified":False,
        "input_sha256":{str(p.relative_to(ROOT)):digest(p) for p in files},
    }
    OUT.parent.mkdir(parents=True,exist_ok=True)
    OUT.write_text(json.dumps(report,indent=2,sort_keys=True)+"\n",
                   encoding="utf-8")
    print(json.dumps({k:report[k] for k in
        ("status","date_records","max_relative_polynomial_exponential_identity_error",
         "max_abs_original_python_vs_realized_proxy_banking_row_gap",
         "nonzero_banking_row_mismatch_records",
         "true_SOURCE_fixed_policy_root_certified")},indent=2))

if __name__=="__main__":
    main()

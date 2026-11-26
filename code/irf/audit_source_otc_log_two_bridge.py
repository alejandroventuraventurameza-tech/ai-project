#!/usr/bin/env python3
"""Conditional SOURCE OTC / Python slope bridge with a domain boundary guard.

SOURCE uses structural lambda and cumulative share a_lambda=1-exp(-lambda).
The Python illustration uses aa=.5 as the SHARE, so lambda=log(2).
For tightness <= 1 we check SOURCE OTC rates and slopes against the
actual finite_irf.auxiliary output, off-root and under corridor perturbations.
For tightness > 1 we record a concrete mismatch and DO NOT certify equality.
This is not a Lean compilation or an economic equilibrium certificate.
"""
from __future__ import annotations

import hashlib
import json
import math
from pathlib import Path
import finite_irf as model

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
SOURCE=ROOT/"lean/checkpoint/modules/Ventura26LiquidityAllocation/EconomicModel.lean"
PYTHON=HERE/"finite_irf.py"
OUT=HERE/"output/source_python_otc_log_two_bridge.json"


def require(ok,msg):
    if not ok:
        raise AssertionError(msg)


def hashfile(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_otc(lambda_,rate,corridor,tau):
    """Independent literal transcription of SOURCE's two tau branches."""
    share=1.0-math.exp(-lambda_)
    if tau <= 1.0:
        w=1.0/(1.0+math.sqrt(tau+(1.0-tau)*math.exp(lambda_)))
        frac_def=share
        frac_sur=tau*share
    else:
        radicand=1.0/tau+(1.0-1.0/tau)*math.exp(lambda_)
        sqrt_rad=math.sqrt(radicand)
        w=sqrt_rad/(1.0+sqrt_rad)
        frac_def=share/tau
        frac_sur=share
    interbank=rate+corridor*w
    chi_minus=frac_def*(interbank-rate)+(1.0-frac_def)*corridor
    chi_plus=frac_sur*(interbank-rate)
    return {"share":share,"weight":w,"interbank_rate":interbank,
            "cm":chi_minus,"cp":chi_plus}


def py_otc(s,base,tau,corridor):
    controls=list(base.U0)
    controls[9]=tau
    return model.auxiliary(s,base.X0,controls,base.X1[:2],
                           base.e0,rho=s.rho,corridor=corridor)


def main():
    src=SOURCE.read_text(encoding="utf-8")
    py=PYTHON.read_text(encoding="utf-8")
    for anchor in (
        "noncomputable def otcMatchIntensityShare",
        "1 - Real.exp (-matchingIntensity)",
        "noncomputable def otcCorridorWeight",
        "tightness + (1 - tightness) * Real.exp matchingIntensity",
        "tightness⁻¹ + (1 - tightness⁻¹) * Real.exp matchingIntensity",
        "noncomputable def otcDeficitMatchFraction",
        "noncomputable def otcSurplusMatchFraction",
        "noncomputable def otcDeficitSlope",
        "noncomputable def otcSurplusSlope",
        "noncomputable def otcNegotiatedRate",
    ):
        require(anchor in src, "SOURCE OTC primitive changed: "+anchor)
    for anchor in (
        "match_value = 1.0 / (1.0 + math.sqrt(2.0 - tightness))",
        "chi_minus = corridor * (1.0 - s.aa + s.aa * match_value)",
        "chi_plus = corridor * tightness * s.aa * match_value",
    ):
        require(anchor in py, "Python OTC implementation changed: "+anchor)
    s=model.steady_case()
    require(s.aa==0.5 and 0.0<s.aa<1.0,
            "Python OTC share changed; lambda mapping must be revisited")
    structural_lambda=-math.log1p(-s.aa)
    require(abs(structural_lambda-math.log(2.0))<1e-15,
            "SOURCE log-two lambda witness changed")
    base=model.make_boundary(s)
    low_taus=(0.25,0.50,0.83,1.0)
    corridors=(0.01,0.02,0.033)
    max_weight=0.0
    max_slope=0.0
    max_match=0.0
    checked=0
    for tau in low_taus:
        for delta in corridors:
            aux=py_otc(s,base,tau,delta)
            source=source_otc(structural_lambda,aux["rr"],delta,tau)
            python_weight=1.0/(1.0+math.sqrt(2.0-tau))
            max_weight=max(max_weight,abs(source["weight"]-python_weight))
            max_slope=max(max_slope,abs(source["cm"]-aux["cm"]),
                          abs(source["cp"]-aux["cp"]))
            max_match=max(max_match,abs(source["share"]-s.aa))
            checked+=1

    # Analytic t derivatives of the two SOURCE low-tau closed forms
    # compared with finite differences of the ACTUAL Python auxiliary.
    h=1e-6
    max_tau_derivative=0.0
    max_corridor_derivative=0.0
    for tau in (0.35,0.50,0.81):
        delta=0.02
        root=math.sqrt(2.0-tau)
        weight=1.0/(1.0+root)
        wprime=1.0/(2.0*root*(1.0+root)**2)
        slope_expected=(delta*s.aa*wprime,
                        delta*s.aa*(weight+tau*wprime))
        plus=py_otc(s,base,tau+h,delta)
        minus=py_otc(s,base,tau-h,delta)
        numeric=((plus["cm"]-minus["cm"])/(2*h),
                 (plus["cp"]-minus["cp"])/(2*h))
        max_tau_derivative=max(max_tau_derivative,
            max(abs(a-b) for a,b in zip(slope_expected,numeric)))
        slope_delt=(1.0-s.aa+s.aa*weight,
                    tau*s.aa*weight)
        plusD=py_otc(s,base,tau,delta+h)
        minusD=py_otc(s,base,tau,delta-h)
        numericD=((plusD["cm"]-minusD["cm"])/(2*h),
                  (plusD["cp"]-minusD["cp"])/(2*h))
        max_corridor_derivative=max(max_corridor_derivative,
            max(abs(a-b) for a,b in zip(slope_delt,numericD)))
    require(max_weight<2e-15 and max_match<2e-15 and max_slope<2e-15,
            "SOURCE low-tau OTC weights/slopes do not match Python")
    require(max_tau_derivative<3e-8 and max_corridor_derivative<3e-9,
            "OTC local first derivatives do not match source formulas")

    # Source HIGH-tightness branch is truly different. Python has NO
    # matching high-tightness branch, so source equality must be scoped.
    tau_high=1.20
    delta_high=0.02
    py_high=py_otc(s,base,tau_high,delta_high)
    src_high=source_otc(structural_lambda,py_high["rr"],
                        delta_high,tau_high)
    mismatch=max(abs(src_high["cm"]-py_high["cm"]),
                 abs(src_high["cp"]-py_high["cp"]))
    require(mismatch>1e-5,
            "High-tightness domain guard failed: expected counterexample")

    report={
        "status":"CONDITIONAL_OTC_SOURCE_PYTHON_LOW_TIGHTNESS_EQUALITY_AND_HIGH_TAU_MISMATCH",
        "source_structural_matching_intensity_lambda":structural_lambda,
        "python_effective_share_aa":s.aa,
        "source_share_function":"1-exp(-lambda)",
        "identification":"lambda=-log(1-aa)=log(2) for aa=0.5",
        "low_tightness_domain":"0<tau<=1",
        "low_tightness_weight":"1/(1+sqrt(2-tau))",
        "low_tightness_checks":checked,
        "max_low_tightness_weight_error":max_weight,
        "max_low_tightness_share_error":max_match,
        "max_low_tightness_chi_slope_error":max_slope,
        "max_low_tightness_tau_derivative_error":max_tau_derivative,
        "max_low_tightness_corridor_derivative_error":max_corridor_derivative,
        "high_tightness_counterexample":{
            "tau":tau_high, "corridor":delta_high,
            "source":src_high, "python_cm":py_high["cm"],
            "python_cp":py_high["cp"],
            "max_slope_discrepancy":mismatch,
        },
        "source_to_python_full_otc_global_equivalence_proved":False,
        "source_bank_optimization_and_equilibrium_proved":False,
        "lean_kernel_executed_in_this_python_test":False,
        "source_sha256":hashfile(SOURCE),
        "python_sha256":hashfile(PYTHON),
    }
    OUT.parent.mkdir(parents=True,exist_ok=True)
    OUT.write_text(json.dumps(report,indent=2,sort_keys=True)+"\n",
                   encoding="utf-8")
    print(json.dumps({
        "status":report["status"],
        "source_lambda":structural_lambda,
        "low_branch_checks":checked,
        "max_low_slope_err":max_slope,
        "max_tau_derivative_err":max_tau_derivative,
        "counterexample_tau":tau_high,
        "high_tau_mismatch":mismatch,
        "report":str(OUT)},indent=2))


if __name__=="__main__":
    main()

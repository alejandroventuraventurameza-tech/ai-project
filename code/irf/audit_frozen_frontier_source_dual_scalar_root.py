#!/usr/bin/env python3
"""Exact rational strict-sign bracket for ONE SOURCE L-dual scalar zero.

The three frontier log coordinates (8,24,28) are held fixed. Only the
loan-rate log coordinate 15 varies. The SOURCE formula is
exp(-z15)/R0 - (24/25)*exp(z8-z24-z28) at sigmaE=1 and under pinned
stationary parameters. Rational Taylor and rate enclosures prove
strict opposite signs. This is NOT a SOURCE 34-equation root.
"""
from __future__ import annotations
import json
import math
from fractions import Fraction as Q
from pathlib import Path

from audit_frozen_stationary_dual_rational import Box, bounds
from audit_frozen_frontier_source_dual_interval import (
    FRONTIER, OUT as DUAL_INTERVAL, digest, require, exp_rational_interval,
)

HERE = Path(__file__).resolve().parent
OUT = HERE / "output/frozen_frontier_source_dual_scalar_root_bracket.json"

def source_scalar_interval(z15, exponent_others, rate):
    return (exp_rational_interval(-z15)/rate -
            Box(Q(24,25))*exp_rational_interval(exponent_others))

def scalar_bracket(z15, exponent_others, rate):
    lo, hi = z15, z15+Q(1,10**9)
    vlo = source_scalar_interval(lo,exponent_others,rate)
    vhi = source_scalar_interval(hi,exponent_others,rate)
    require(vlo.lo>0 and vhi.hi<0,"No strict root sign bracket")
    evaluations=2
    ambiguous=False
    for _ in range(60):
        mid=(lo+hi)/2
        vm=source_scalar_interval(mid,exponent_others,rate)
        evaluations+=1
        if vm.lo>0:
            lo,vlo=mid,vm
        elif vm.hi<0:
            hi,vhi=mid,vm
        else:
            ambiguous=True
            break
    require(lo<hi and hi-lo<Q(1,10**11),
            "Rigorous scalar bracket did not narrow below 1e-11")
    require(vlo.lo>0 and vhi.hi<0,
            "Exact endpoint signs did not survive bisection")
    return lo,hi,vlo,vhi,evaluations,ambiguous

def main():
    require(FRONTIER.is_file() and DUAL_INTERVAL.is_file(),
            "Parent frontier and SOURCE-formula interval required")
    frontier=json.loads(FRONTIER.read_text(encoding="utf-8"))
    prior=json.loads(DUAL_INTERVAL.read_text(encoding="utf-8"))
    require(prior["status"]==
            "EXACT_RATIONAL_FRONTIER_SOURCE_FORMULA_L_DUAL_POSITIVE_CONDITIONAL_INPUTS",
            "Unexpected parent formula proof status")
    require(prior["frontier_report_sha256"]==digest(FRONTIER),
            "Wrong frontier version")
    z=frontier["numerical_candidate"]["baseline_33_unknowns"]
    require(len(z)==33 and all(math.isfinite(v) for v in z),
            "Invalid numeric log coordinates")
    z8,z15,z24,z28=[Q.from_float(z[i]) for i in (8,15,24,28)]
    rate=bounds()["rate"]
    lo,hi,vlo,vhi,n,ambiguous=scalar_bracket(z15,z8-z24-z28,rate)
    report={
        "status":"EXACT_RATIONAL_CONDITIONAL_SOURCE_FORMULA_SCALAR_ZERO_BRACKET",
        "scope":"four-log SOURCE L dual; fixed three Python coordinates",
        "frontier_report_sha256":digest(FRONTIER),
        "parent_interval_sha256":digest(DUAL_INTERVAL),
        "original_z15_exact":str(z15),
        "root_z15_lower_exact":str(lo),
        "root_z15_upper_exact":str(hi),
        "root_z15_lower_float":float(lo),
        "root_z15_upper_float":float(hi),
        "z15_offset_lower_float":float(lo-z15),
        "z15_offset_upper_float":float(hi-z15),
        "root_interval_width_exact":str(hi-lo),
        "root_interval_width_float":float(hi-lo),
        "positive_endpoint_lower_exact":str(vlo.lo),
        "negative_endpoint_upper_exact":str(vhi.hi),
        "fraction_interval_evaluations":n,
        "bisection_stopped_at_interval_sign_ambiguity":ambiguous,
        "unique_zero_between_endpoints_of_scalar_formula":True,
        "strict_monotonicity":"-exp(-z15)/R0 < 0 for positive R0",
        "other_33_economic_residuals_at_corrected_coordinate_checked":False,
        "source_primitives_and_Z0_instantiated_in_Lean":False,
        "SOURCE_augmented_34_root_certified":False,
        "full_dynamic_equilibrium_certified":False,
    }
    OUT.parent.mkdir(parents=True,exist_ok=True)
    OUT.write_text(json.dumps(report,sort_keys=True,indent=2)+"\n",encoding="utf-8")
    print(json.dumps({k:report[k] for k in (
        "status","z15_offset_lower_float","z15_offset_upper_float",
        "root_interval_width_float","fraction_interval_evaluations",
        "SOURCE_augmented_34_root_certified")},indent=2))

if __name__=="__main__":
    main()

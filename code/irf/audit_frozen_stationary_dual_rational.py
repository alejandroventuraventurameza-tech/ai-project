#!/usr/bin/env python3
"""Exact rational enclosure for the frozen steady_case B funding-dual value.

Covers only the analytic steady_case rate formula with exact rational inputs.
The SOURCE/Python operator identity and 33-row root remain independent gaps.
"""
from fractions import Fraction as Q
from math import isqrt
import json
from pathlib import Path

DENOM = 10**12

class Box:
    def __init__(self, lo, hi=None):
        self.lo = Q(lo)
        self.hi = Q(hi if hi is not None else lo)
        assert self.lo <= self.hi
    def __add__(self, other):
        other = box(other)
        return Box(self.lo + other.lo, self.hi + other.hi)
    __radd__ = __add__
    def __neg__(self):
        return Box(-self.hi, -self.lo)
    def __sub__(self, other):
        return self + (-box(other))
    def __rsub__(self, other):
        return box(other) + (-self)
    def __mul__(self, other):
        other = box(other)
        vals = [self.lo * other.lo, self.lo * other.hi,
                self.hi * other.lo, self.hi * other.hi]
        return Box(min(vals), max(vals))
    __rmul__ = __mul__
    def reciprocal(self):
        assert self.lo > 0
        return Box(1 / self.hi, 1 / self.lo)
    def __truediv__(self, other):
        return self * box(other).reciprocal()
    def __rtruediv__(self, other):
        return box(other) * self.reciprocal()
    def sqrt(self):
        assert self.lo >= 0
        def lo_sqrt(x):
            n = isqrt(x.numerator * DENOM * DENOM // x.denominator)
            return Q(n, DENOM)
        a = lo_sqrt(self.lo)
        b = lo_sqrt(self.hi)
        assert a*a <= self.lo
        assert self.hi < (b + Q(1, DENOM))**2
        return Box(a, b + Q(1, DENOM))

def box(x):
    return x if isinstance(x, Box) else Box(x)

def bounds():
    bw, be = Box(Q(99,100)), Q(24,25)
    rho, zeta = Q(1,10), Q(1,5)
    tight, Delta, aa = Q(1,2), Q(1,50), Q(1,2)
    rd = 1 / bw
    vv = 1 / (1 + Box(Q(3,2)).sqrt())
    cm = Delta * (1 - aa + aa * vv)
    cp = Delta * tight * aa * vv
    cbar = (cm + cp)/2
    cdiff = cm - cp
    ar = rd - (1-rho)*cbar - rho*zeta*cdiff/2
    disc = ar*ar + 2*rd*zeta*cdiff
    assert ar.lo > 0 and disc.lo > 0
    rr = (ar + disc.sqrt())/2
    rate = rr + cbar
    nu = 1/rate - be
    assert nu.lo > 0
    assert rate.hi < Q(25,24)
    return {"rate":rate,"nu":nu,"rr":rr,"vv":vv,"ar":ar}

if __name__ == "__main__":
    from finite_irf import steady_case
    s = steady_case()
    b = bounds()
    rate, nu = b["rate"], b["nu"]
    # Cross-check the independent rational enclosure against the original
    # float implementation. This cross-check is not itself the sign proof.
    assert rate.lo < Q.from_float(s.rate) < rate.hi
    assert nu.lo < Q.from_float(1 / s.rate - s.be) < nu.hi
    report = {
        "status": "EXACT_RATIONAL_STEADY_CASE_DUAL_POSITIVE_NOT_SOURCE_ROOT",
        "method": "Fraction interval arithmetic, integer-square-root enclosures",
        "sqrt_enclosure_denominator": DENOM,
        "rational_input_parameters": {
            "beta_worker": "99/100", "beta_entrepreneur": "24/25",
            "reserve_requirement": "1/10", "payment_fraction": "1/5",
            "tightness": "1/2", "corridor": "1/50", "matching": "1/2",
        },
        "loan_rate_rational_lower": str(rate.lo),
        "loan_rate_rational_upper": str(rate.hi),
        "dual_L_rational_lower": str(nu.lo),
        "dual_L_rational_upper": str(nu.hi),
        "dual_lower_float_display": float(nu.lo),
        "dual_upper_float_display": float(nu.hi),
        "strict_positive_proved_for_python_parameter_formula": nu.lo > 0,
        "source_python_semantic_equality_proved": False,
        "economic_33_root_certified": False,
        "source_augmented_34_root_certified": False,
    }
    out = Path(__file__).resolve().parent / "output/frozen_stationary_dual_rational_enclosure.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(report, indent=2, sort_keys=True)+"\n",encoding="utf-8")
    print(json.dumps({
        "status": report["status"],
        "loan_rate_float_enclosure": [float(rate.lo), float(rate.hi)],
        "dual_L_float_enclosure": [float(nu.lo), float(nu.hi)],
        "output": str(out),
    }, indent=2))

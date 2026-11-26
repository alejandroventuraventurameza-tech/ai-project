"""Exact-rational interval certificate for the ten boundary endpoint boxes.

Independent arithmetic counterpart of BoundaryEndpointBoxesCandidate.lean.
The branch model/parameter formulas are transcribed explicitly; compare them
against the Lean source before using this as a formal theorem. No binary
floating-point calculations decide any inequality; roots use integer powers.

Run: python code/boundary/verify_endpoint_boxes_exact.py
Status: rational interval check, NOT yet a Lean kernel certificate.
"""
from __future__ import annotations
from fractions import Fraction as Q
from dataclasses import dataclass
from math import isqrt
from decimal import Decimal, localcontext

DEN = 10**14


def floor_approx(x: Q) -> Q:
    return Q(x.numerator * DEN // x.denominator, DEN)


def ceil_approx(x: Q) -> Q:
    return Q(-((-x.numerator * DEN) // x.denominator), DEN)


def floor_nth_root(a: int, n: int) -> int:
    assert a >= 0 and n > 0
    if n == 2:
        return isqrt(a)
    if a < 2:
        return a
    lo, hi = 0, 1 << ((a.bit_length() + n - 1) // n + 1)
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if mid**n <= a:
            lo = mid
        else:
            hi = mid
    return lo


@dataclass(frozen=True)
class I:
    lo: Q
    hi: Q

    def __post_init__(self):
        assert self.lo <= self.hi

    @staticmethod
    def q(x) -> "I":
        if isinstance(x, I):
            return x
        if not isinstance(x, Q):
            x = Q(x)
        return I(floor_approx(x), ceil_approx(x))

    @staticmethod
    def encl(lo: Q, hi: Q) -> "I":
        return I(floor_approx(lo), ceil_approx(hi))

    def __add__(self, other):
        other = I.q(other)
        return I.encl(self.lo + other.lo, self.hi + other.hi)

    __radd__ = __add__

    def __neg__(self):
        return I.encl(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + (-I.q(other))

    def __rsub__(self, other):
        return I.q(other) - self

    def __mul__(self, other):
        other = I.q(other)
        candidates = [x * y for x in (self.lo, self.hi)
                      for y in (other.lo, other.hi)]
        return I.encl(min(candidates), max(candidates))

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = I.q(other)
        assert other.lo > 0 or other.hi < 0, "divisor interval spans zero"
        reciprocal = I.encl(Q(1, other.hi), Q(1, other.lo))
        return self * reciprocal

    def __rtruediv__(self, other):
        return I.q(other) / self

    def __pow__(self, n: int):
        assert isinstance(n, int) and n >= 0
        out = I.q(1)
        for _ in range(n):
            out = out * self
        return out

    def root(self, n: int) -> "I":
        assert self.lo >= 0 and n >= 1
        lo_int = self.lo.numerator * DEN**n // self.lo.denominator
        hi_int = self.hi.numerator * DEN**n // self.hi.denominator
        lower = floor_nth_root(lo_int, n)
        upper = floor_nth_root(hi_int, n) + 1
        assert Q(lower, DEN)**n <= self.lo
        assert Q(upper, DEN)**n >= self.hi
        return I(Q(lower, DEN), Q(upper, DEN))

    def display(self) -> str:
        with localcontext() as ctx:
            ctx.prec = 36
            a = Decimal(self.lo.numerator) / Decimal(self.lo.denominator)
            b = Decimal(self.hi.numerator) / Decimal(self.hi.denominator)
            return f"[{a}, {b}]"


H, L = 0, 1
theta = [I.q(Q(3, 20)), I.q(Q(2, 5))]
A = [I.q(Q(101, 100)), I.q(1)]
weight = 1 / (1 + I.q(Q(3, 2)).root(2))
RD = I.q(Q(100, 99))
mean_slope = (2 + 3 * weight) / 400
slope_gap = (2 + weight) / 200
root_coefficient = RD - Q(9, 10) * mean_slope - slope_gap / 100
RR = (root_coefficient
      + (root_coefficient**2 + Q(2, 5) * RD * slope_gap).root(2)) / 2
RL = RR + mean_slope
q = I.q(Q(81, 80))
J = Q(39, 40) * q
user_cost = [
    q * ((1 - theta[i] * Q(39, 40) / RL) / Q(24, 25)
         - Q(39, 40) * (1 - theta[i]))
    for i in (H, L)
]
profit_coefficient = [((Q(5, 6) * A[i])**2) / 4 for i in (H, L)]
capital_scale = [
    ((Q(4, 5) * profit_coefficient[i] / user_cost[i])**5)
    for i in (H, L)
]


def avg(xs):
    return (xs[0] + xs[1]) / 2


output_scale = avg([user_cost[i] * capital_scale[i] * 3 for i in (H, L)])
credit_scale = avg([
    theta[i] * J * capital_scale[i] / RL for i in (H, L)
])
worker_consumption_scale = (
    Q(7, 12) * output_scale + avg(capital_scale) / 6400
    + (RL - 1) * credit_scale
)
firm_coefficient = [
    Q(5, 12) * user_cost[i] * capital_scale[i] * 3
    - Q(1, 40) * q * capital_scale[i]
    - (RL - 1) * theta[i] * J * capital_scale[i] / RL
    for i in (H, L)
]
parent_effective_H = q - theta[H] * J / RL


def endpoint(R: Q):
    r = I.q(R)
    rr = r - mean_slope
    payment_term = slope_gap / 10
    rd = (rr + Q(9, 10) * mean_slope + payment_term / 10) / (
        1 + payment_term / rr
    )
    scale = 1 / (Q(39, 40) + ((user_cost[L] + J) / r - 1) / Q(1, 2))
    root = (scale**8 * (Q(99, 100) * rd)**5).root(15)
    norm_y = output_scale * root
    norm_cw = worker_consumption_scale / (Q(99, 100) * rd)
    norm_h = firm_coefficient[H] * (
        user_cost[L] + J - theta[H] * J
    ) / (r * parent_effective_H)
    norm_l = firm_coefficient[L] / (Q(24, 25) * r)
    norm_gamma = avg(capital_scale) * (
        Q(41, 80) + 1 / (4 * scale) - Q(4719, 6400) * scale
    )
    return {
        "Y": norm_y, "CW": norm_cw, "CH": norm_h,
        "CL": norm_l, "Gamma": norm_gamma,
        "Phi": norm_y - norm_cw - (norm_h + norm_l) / 2 - norm_gamma,
    }


checks = [
    ("lo", Q(41, 40), [
        ("Y", "lt", Q(1327678, 100000)),
        ("CW", "gt", Q(793630, 100000)),
        ("CH", "gt", Q(296932, 100000)),
        ("CL", "gt", Q(382592, 100000)),
        ("Gamma", "gt", Q(266849, 100000)),
    ]),
    ("hi", Q(129, 125), [
        ("Y", "gt", Q(1340498, 100000)),
        ("CW", "lt", Q(788240, 100000)),
        ("CH", "lt", Q(294921, 100000)),
        ("CL", "lt", Q(380000, 100000)),
        ("Gamma", "lt", Q(164406, 100000)),
    ]),
]

for name, R, components in checks:
    values = endpoint(R)
    print("\nENDPOINT", name, R)
    for field, kind, bound in components:
        value = values[field]
        margin = bound - value.hi if kind == "lt" else value.lo - bound
        print(field, kind, bound, value.display(), "positive_margin", margin)
        assert margin > 0, (name, field, value.display(), bound)
    print("Phi", values["Phi"].display())

assert endpoint(Q(41, 40))["Phi"].hi < Q(-7, 10)
assert endpoint(Q(129, 125))["Phi"].lo > Q(1, 2)
print("\nEXACT RATIONAL INTERVAL CHECK PASSED: 10/10 BOXES AND 2 RESIDUAL SIGNS")

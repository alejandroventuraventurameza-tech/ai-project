#!/usr/bin/env python3
"""Exact standalone SOURCE bank-rate boundary certificate.

Every decision uses Fraction, integer squares, or exact rational
comparisons; binary floats are used only to display already-validated
values. Source definitions: ProposedStationaryBank in
lean/candidates/Ventura26LiquidityAllocation/InterbankCancellationCandidate.lean.

Status: independent rational-arithmetic test, not a Lean kernel theorem.
"""
from fractions import Fraction as F
from math import isqrt

D = 10 ** 11
sqrt_lo, sqrt_hi = F(122474487139, D), F(122474487140, D)
assert 0 < sqrt_lo and sqrt_lo**2 < F(3, 2) < sqrt_hi**2

w_lo, w_hi = F(44948974278, D), F(44948974279, D)
assert w_lo * (1 + sqrt_hi) < 1
assert 1 < w_hi * (1 + sqrt_lo)

m_lo, m_hi = F(8371173070, 10**12), F(8371173072, 10**12)
g_lo, g_hi = F(12247448713, 10**12), F(12247448715, 10**12)
assert m_lo < (2 + 3 * w_lo) / 400
assert (2 + 3 * w_hi) / 400 < m_hi
assert g_lo < (2 + w_lo) / 200
assert (2 + w_hi) / 200 < g_hi

r_d = F(100, 99)
a_lo, a_hi = F(100244447, 10**8), F(100244449, 10**8)
a_from_hi = r_d - F(9, 10) * m_hi - g_hi / 100
a_from_lo = r_d - F(9, 10) * m_lo - g_lo / 100
assert a_lo < a_from_hi and a_from_lo < a_hi and 0 < a_lo < a_hi < 2

p = lambda x, a, g: x**2 - a * x - r_d * g / 10
r_r_lo, r_r_hi = F(100367704, 10**8), F(100367709, 10**8)
assert r_r_lo > 1
assert p(r_r_lo, a_lo, g_lo) < 0
assert p(r_r_hi, a_hi, g_hi) > 0

# On [1, infinity), p(y)-p(x)=(y-x)(x+y-a)>0 for y>x
# since a<a_hi<2: the positive SOURCE quadratic root is unique.
assert 2 - a_hi > 0

# Direct independent enclosure of the SOURCE explicit positive root:
# for 0 <= z, k/Q <= sqrt(z) < (k+1)/Q by integer squares.
def floor_sqrt_fraction(z: F, scale: int) -> int:
    assert z >= 0
    k = isqrt((z.numerator * scale * scale) // z.denominator)
    assert F(k * k, scale * scale) <= z
    assert z < F((k + 1)**2, scale * scale)
    return k

rad_lo = a_lo**2 + F(2, 5) * r_d * g_lo
rad_hi = a_hi**2 + F(2, 5) * r_d * g_hi
scale = 10**15
sqrt_rad_lo = F(floor_sqrt_fraction(rad_lo, scale), scale)
sqrt_rad_hi = F(floor_sqrt_fraction(rad_hi, scale) + 1, scale)
root_low = (a_lo + sqrt_rad_lo) / 2
root_high = (a_hi + sqrt_rad_hi) / 2
assert r_r_lo < root_low < root_high < r_r_hi

r_l_lo, r_l_hi = F(101204821, 10**8), F(101204827, 10**8)
assert r_l_lo < r_r_lo + m_lo
assert r_r_hi + m_hi < r_l_hi

# Sharper exact source quadratic enclosure, proved independently in Lean.
sharp_a_lo, sharp_a_hi = F(1002444479849, 10**12), F(1002444479851, 10**12)
assert sharp_a_lo < a_from_hi and a_from_lo < sharp_a_hi
sharp_rr_lo, sharp_rr_hi = F(1003677063, 10**9), F(1003677065, 10**9)
assert p(sharp_rr_lo, sharp_a_lo, g_lo) < 0
assert p(sharp_rr_hi, sharp_a_hi, g_hi) > 0
assert 1 < sharp_rr_lo < sharp_rr_hi < r_d
sharp_loan_rate_lo, sharp_loan_rate_hi = (
    F(101204823607, 10**11), F(101204823808, 10**11)
)
assert sharp_loan_rate_lo == sharp_rr_lo + m_lo
assert sharp_rr_hi + m_hi < sharp_loan_rate_hi

for name, value in [
    ("otc_weight_lo", w_lo), ("otc_weight_hi", w_hi),
    ("mean_slope_lo", m_lo), ("mean_slope_hi", m_hi),
    ("slope_gap_lo", g_lo), ("slope_gap_hi", g_hi),
    ("quadratic_coefficient_lo", a_lo), ("quadratic_coefficient_hi", a_hi),
    ("reserve_rate_lo", r_r_lo), ("reserve_rate_hi", r_r_hi),
    ("loan_rate_lo", r_l_lo), ("loan_rate_hi", r_l_hi),
    ("sharp_reserve_rate_lo", sharp_rr_lo), ("sharp_reserve_rate_hi", sharp_rr_hi),
    ("sharp_loan_rate_lo", sharp_loan_rate_lo), ("sharp_loan_rate_hi", sharp_loan_rate_hi),
]:
    print(f"{name}: {value} = {float(value):.12f}")
print("p(reserve_rate_lo) upper:", p(r_r_lo, a_lo, g_lo))
print("p(reserve_rate_hi) lower:", p(r_r_hi, a_hi, g_hi))
print("explicit root inner enclosure:", root_low, root_high)
print("EXACT SOURCE BANK-RATE CERTIFICATE PASS: sqrt, weight, slopes, quadratic, root, loan")

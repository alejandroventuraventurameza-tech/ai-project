#!/usr/bin/env python3
"""Exact-rational SOURCE stationary firm user-cost and capital-scale boxes.

Consequence of the previously verified SOURCE gross-loan-rate envelope.
Every accept/reject decision uses Fraction; no floating-point tolerance.
Not a Lean proof and not a full GE allocation/optimality certificate.

SOURCE: StationaryRealScaleCandidate.lean (pledgeability, technology,
capitalPrice, userCost, profitCoefficient, capitalScale).
"""
from fractions import Fraction as Q

RLO, RHI = Q(101204821, 10**8), Q(101204827, 10**8)
PRICE = Q(81, 80)
FIRMS = {
    "H": {"theta": Q(3, 20), "A": Q(101, 100),
          "user_cost": (Q(6316636, 10**8), Q(6316638, 10**8)),
          "capital_scale": (Q(567703, 10**4), Q(567705, 10**4))},
    "L": {"theta": Q(2, 5), "A": Q(1),
          "user_cost": (Q(5594364, 10**8), Q(5594368, 10**8)),
          "capital_scale": (Q(943153, 10**4), Q(943158, 10**4))},
}

assert 1 < RLO < RHI
for name, p in FIRMS.items():
    theta, productivity = p["theta"], p["A"]
    alpha = PRICE * (Q(1, 15) + theta * Q(39, 40))
    beta = PRICE * theta * Q(65, 64)

    def user_cost(r):
        source = PRICE * (
            (1 - theta * Q(39, 40) / r) / Q(24, 25)
            - Q(39, 40) * (1 - theta)
        )
        assert source == alpha - beta / r
        return source

    assert alpha > 0 and beta > 0
    cost_lo, cost_hi = user_cost(RLO), user_cost(RHI)
    assert cost_lo < cost_hi
    cl, cu = p["user_cost"]
    assert cl < cost_lo < cost_hi < cu, name

    profit_coefficient = (Q(5, 6) * productivity)**2 / 4
    def capital_scale(r):
        return (Q(4, 5) * profit_coefficient / user_cost(r))**5

    scale_lo, scale_hi = capital_scale(RHI), capital_scale(RLO)
    assert scale_lo < scale_hi
    kl, ku = p["capital_scale"]
    assert kl < scale_lo < scale_hi < ku, name

    print(f"Firm {name}; theta={theta}, A={productivity}")
    print(f"  userCost exact enclosing interval: ({cl}, {cu})")
    print(f"  capitalScale exact enclosing interval: ({kl}, {ku})")
    print(f"  source scaled identity: userCost * RL = {alpha} * RL - {beta}")

assert FIRMS["H"]["A"] > FIRMS["L"]["A"]
assert FIRMS["H"]["theta"] < FIRMS["L"]["theta"]
assert FIRMS["L"]["user_cost"][1] < FIRMS["H"]["user_cost"][0]
assert FIRMS["H"]["capital_scale"][1] < FIRMS["L"]["capital_scale"][0]

# A structural, *partial-formula* threshold independent of narrow boxes:
# k_H^scale < k_L^scale iff u_H > (A_H/A_L)^2 * u_L when both
# user costs and returns are positive. Using the SOURCE definitions:
# u_H(r) = (81/80)*(511/2400-39/(256*r))
# u_L(r) = (81/80)*(137/300-13/(32*r)).
productivity_ratio_sq = (FIRMS["H"]["A"] / FIRMS["L"]["A"]) ** 2
assert productivity_ratio_sq == Q(10201, 10000)
coeff_r = productivity_ratio_sq * Q(137, 300) - Q(511, 2400)
coeff_const = productivity_ratio_sq * Q(13, 32) - Q(39, 256)
assert coeff_r > 0 and coeff_const > 0
critical_loan_rate = coeff_const / coeff_r
assert critical_loan_rate == Q(2096575, 2023432)
broad_loan_upper = Q(100, 99) + Q(7, 800)  # SOURCE reserve<deposit, slope<7/800
assert 1 < broad_loan_upper < critical_loan_rate < Q(25, 24)
for r in (RLO, RHI, broad_loan_upper):
    h_cost = PRICE * (Q(511, 2400) - Q(39, 256) / r)
    l_cost = PRICE * (Q(137, 300) - Q(13, 32) / r)
    assert 0 < l_cost < h_cost
    assert (h_cost - productivity_ratio_sq * l_cost) * r == (
        PRICE * (coeff_const - coeff_r * r))
    assert h_cost > productivity_ratio_sq * l_cost

print("Capital reversal threshold (exact):", critical_loan_rate)
print("SOURCE broad bank upper < reversal threshold:",
      broad_loan_upper, "<", critical_loan_rate)
print("PASS: structural firm ranking holds across broad SOURCE bank bounds")

print("PASS: stationary high-productivity, low-pledgeability firm has")
print("      higher user cost and smaller capital scale (exact rational boxes)")

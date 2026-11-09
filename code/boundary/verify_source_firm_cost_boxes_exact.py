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

print("PASS: stationary high-productivity, low-pledgeability firm has")
print("      higher user cost and smaller capital scale (exact rational boxes)")

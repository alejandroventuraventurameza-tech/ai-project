#!/usr/bin/env python3
"""Reproduce the numerical SOURCE inherited nominal-face diagnostic (not Lean).

Formulas: InterbankCancellationCandidate.lean, StationaryRealScaleCandidate.lean,
BoundaryFirmBridgeCandidate.lean, BoundaryResourceRootCandidate.lean,
StationaryInheritedStateCandidate.lean, EconomicModel.lean.
No external libraries. The steady-state identity is a control test.
"""
from decimal import Decimal as D, getcontext
from json import dumps

getcontext().prec = 70

def q(a, b=1):
    return D(a) / D(b)

def mean(xs):
    return sum(xs) / D(len(xs))

v = 1 / (1 + q(3,2).sqrt())
m = (2+3*v)/400
gap = (2+v)/200
rd = q(100,99)
a = rd-q(9,10)*m-gap/100
rr = (a+(a*a+q(2,5)*rd*gap).sqrt())/2
rl = rr+m
rmd = q(1,10)+(rd/rr-q(1,10))/15
theta = [q(3,20), q(2,5)]
tech = [q(101,100), D(1)]
price = q(81,80)
J = q(39,40)*price
usercost = [price*((1-x*q(39,40)/rl)/q(24,25)-q(39,40)*(1-x)) for x in theta]
pc = [(q(5,6)*t)**2/4 for t in tech]
cs = [(q(4,5)*pc[i]/usercost[i])**5 for i in range(2)]
ys = mean([3*usercost[i]*cs[i] for i in range(2)])
ls = mean([q(5,4)*usercost[i]*cs[i] for i in range(2)])
bs = mean([theta[i]*J*cs[i]/rl for i in range(2)])
cws = q(7,12)*ys+mean(cs)/6400+(rl-1)*bs
w = (ls*cws)**q(1,12)
k = [x/w**5 for x in cs]
y = [3*usercost[i]*k[i] for i in range(2)]
face = [theta[i]*J*k[i] for i in range(2)]
loan = [fi/rl for fi in face]
cf = [q(5,12)*y[i]-q(1,40)*price*k[i]-(rl-1)*loan[i] for i in range(2)]
K, Y, B = mean(k), mean(y), mean(loan)
cw = Y-mean(cf)-q(161,6400)*K
E = B/(3-2*rmd)
Db = 2*E
M = 2*rmd*E
F = (rd/rr-q(1,10))*Db/30
Mpost = M+F
rf = rr+q(1,50)
ab = 1/rl

def at_boundary(R):
    continuation_return = [u+J for u in usercost]
    price0 = continuation_return[1]/R
    effective0 = [price0-theta[i]*J/R for i in range(2)]
    effective_parent = [price-theta[i]*J/rl for i in range(2)]
    c0 = [cf[0]*effective0[0]/effective_parent[0], cf[1]/(q(24,25)*R)]
    scale = 1/(q(39,40)+(price0-1)/q(1,2))
    k0 = [scale*x for x in k]
    rr0 = R-m
    term = gap/10
    rd0 = (rr0+q(9,10)*m+q(1,10)*term)/(1+term/rr0)
    cw0 = cw/(q(99,100)*rd0)
    w0 = w*((cw0/cw)*scale**q(4,5))**q(1,3)
    labor0 = [(q(1,2)*q(5,6)*tech[i]*(k0[i]**q(2,5))/w0)**2 for i in range(2)]
    output0 = [tech[i]*k0[i]**q(2,5)*labor0[i]**q(1,2) for i in range(2)]
    profit0 = [q(5,6)*output0[i]-w0*labor0[i] for i in range(2)]
    inherited_faces = [profit0[i]+q(39,40)*price0*k0[i]-c0[i]-effective0[i]*k[i] for i in range(2)]
    investment = K-q(39,40)*scale*K
    capital_cost = investment+q(1,2)*investment**2/(2*scale*K)
    resource_residual = mean(output0)-cw0-mean(c0)-capital_cost
    initial_bank_face = E*rl/R
    face_gap = rd*Db-mean(inherited_faces)-rr*Mpost+rf*F+initial_bank_face/ab
    return resource_residual, face_gap, inherited_faces

lo, hi = q(41,40), q(129,125)
assert at_boundary(lo)[0] < 0 < at_boundary(hi)[0]
for i in range(245):
    mid = (lo+hi)/2
    if mid == lo or mid == hi:
        break
    if at_boundary(mid)[0] > 0:
        hi = mid
    else:
        lo = mid
root = (lo+hi)/2
resource_gap, face_gap, impact_faces = at_boundary(root)
parent_gap = rd*Db-mean(face)-rr*Mpost+rf*F+E/ab

assert abs(resource_gap) < D("1e-60")
assert abs(parent_gap) < D("1e-60")
assert D("0.08") < face_gap < D("0.09")

print(dumps({
    "status": "NUMERICO: source boundary inherited face violation; not Lean-certified",
    "root_gross_loan_rate": str(root),
    "root_resource_residual": str(resource_gap),
    "stationary_inherited_face_gap": str(parent_gap),
    "source_boundary_inherited_face_gap": str(face_gap),
    "impact_inherited_firm_faces_H_L": [str(x) for x in impact_faces],
    "hypothetical_inherited_deposit_adjustment": str(-face_gap/rd),
    "note": "A successful diagnostic run confirms detection of a nonzero economic residual, NOT a valid competitive equilibrium."
}, indent=2))

# SOURCE 34 -> 33: exact operator and conditional reduced-Jacobian gate

Checkpoint 2026-11-14. This file distinguishes formal SOURCE claims, numerical Python evidence, and remaining proof obligations.

## Economics and exact dimension

Write F(z,h)=(B(z,h),nuL(z)), with z in R^33 and policy innovation h. Under stationary SOURCE sigmaE=1, C0L=C1L>0, Pi1=1, R0>0 and betaE>0, Lean establishes:

    nuL(z)=exp(-z15)/R0 - betaE*exp(z8-z24-z28).
    z15*=-log(R0*betaE)-z8+z24+z28.

Let u in R^32 collect the 32 log coordinates other than z15. The analytic lift L(u) inserts u in the correct SOURCE indices and uses z15* at index 15. Define the genuine SOURCE reduced economic map

    G(u,h)=B(L(u),h) in R^33.

The new Lean modules SourceFundingDualExact33FreeCoordinatesCandidate and SourceReduced33ActualEconomicMapCandidate formalize the exact 32+policy parameterization and the conditional root-set equivalence (exists z,h: F(z,h)=0) iff (exists u,h: G(u,h)=0). Mark these as CANDIDATE until their dedicated pinned Lean audit passes. The earlier scalar elimination theorem passed Lean audit #43637950046.

## Reduced Jacobian and sign

Under regularity of the SOURCE B map, the chain rule gives:

    d z15* / d u8 = -1;  d z15* / d u24 = +1;
    d z15* / d u28 = +1; all other free-log derivatives = 0.

If A=D_z B and b=D_h B, then

    D G[i,k] = A[i,k] + A[i,15]*(d z15*/d u_k), k!=15;
    D G[i,h] = b[i].

This formula is analytic. The 34th SOURCE funding-dual derivative along L is zero by construction. An exact lean derivative proof and complete SOURCE/Python semantic matching remain open.

## Rational numerical gate and its limits

The Python verifier code/irf/audit_frozen_python_reduced33_ad_rational_gate.py calculates a 34-row forward-AD derivative at the UPDATED reduced Newton candidate, applies the formula to get a 33x33 matrix, and compares with independent finite differences. The result is rounded to an exact rational matrix M. A separate approximate inverse C is rounded to rationals; a strict Neumann defect q=||I-CM||_infinity<1, if verified, certifies the ROUNDED MATRIX only.

With eps=(1-q)/(4*33*||C||), any hypothetical SOURCE reduced map whose derivative is within eps ENTRYWISE of M across the ENTIRE closed box B_R has a contraction bound delta=q+33*||C||*eps<1. A separately validated true SOURCE centre residual below (1-delta)*R/||C|| then gives a unique zero by Banach. These remain conditional thresholds; binary64 AD and finite differences do not enclose SOURCE.

Remaining: identify SOURCE/Python functions row by row (8 firm, 9 scalar and 16 other rows), match inherited states and finite tail, prove SOURCE interval residual/derivative bounds on a full box, verify regime KKT, and only then interpret structural IRFs or long-run growth.

Status: SOURCE scalar elimination DEMOSTRADO, direct 32+policy operator CANDIDATE, reduced Python root NUMERICO, rational reduced-AD Jacobian audit PENDIENTE CI, real SOURCE reduced root PENDIENTE.
# SOURCE L funding dual: exact analytical 34-to-33 reduction

Status 14 November 2026: sigma=1 stationary SOURCE formula and scalar existence are DEMOSTRADO in Lean; exact 34/33 root-set reduction is a NEW CANDIDATE until its specific CI audit passes.

## Exact economic assumptions

Let the original augmented SOURCE map be F(z,h)=(B(z,h),nuL(z)) with 33 endogenous log coordinates z and remuneration innovation h. Assume entrepreneur CRRA sigmaE=1; reference consumptions C0L=C1L>0; reference inflation Pi1=1; reference loan rate R0>0; and discount betaE>0.

The last SOURCE equation is nuL(z)=exp(-z15)/R0 - betaE*exp(z8-z24-z28). All indices are 0-based indices of the genuine SOURCE log chart.

## Explicit elimination

For given z8,z24,z28, the sole zero in z15 is

    z15* = -log(R0*betaE) - z8 + z24 + z28.

Define E(z) as z with only coordinate 15 replaced by z15*. Then nuL(E(z))=0 exactly, and all other 32 coordinates are unchanged. If F(z,h)=0, then E(z)=z. Thus, conditionally on the stationary assumptions:

    exists (z,h), F(z,h)=0
       iff exists (z,h), B(E(z),h)=0.

The right side is 33 economic equations in 32 free log coordinates and one policy innovation. This is an EXACT ELIMINATION, not a constructive 33-root proof.

Partial derivatives of z15* are -1 in z8, +1 in z24 and z28, and zero in h when the other economic coordinates are held fixed. This does NOT imply a zero equilibrium policy response of the interest rate.

## Verification status and key limitations

The independent exact-rational sign audit at the Python frontier brackets the one-scalar coordinate correction strictly between 8.88671875e-11 and 8.984375e-11. The companion Python diagnostic recomputes all 33 other *numerical* residuals after that update; it is NOT a validated Lean SOURCE evaluator.

Module SourceFundingDualScalarEliminationCandidate.lean formalizes the uniqueness, exact cancellation and root-set equivalence, awaiting Lean audit. The corresponding Python diagnostic is code/irf/audit_frozen_python_34_analytic_dual_elimination.py.

Crucial open requirements: match all 33 SOURCE/Python row functions in a single positive chart and frozen inherited state; enclose the full 33-vector residual and its derivative on a validated box; prove a genuine SOURCE root; verify KKT and the dynamic continuation and long-run economic mechanism.

DEMOSTRADO: SOURCE stationary four-log scalar formula and existence of one scalar zero under positivity. NUMERICO: corrected Python frontier test. PENDIENTE: full 34-to-33 Lean CI, SOURCE/Python identity, original economic root, global equilibrium and IRFs.
# SOURCE funding dual at the frozen Python 34-boundary: exact rational interval

Date: 2026-11-14. Status: EXACT RATIONAL SCALAR-FORMULA EVALUATION, with unresolved SOURCE parameter-instance and 33-row obligations.

## Analytic SOURCE formula and reduction

The genuine SOURCE theorem sourceFundingDual_four_log_coordinate_formula
shows that the normalized firm-L funding dual depends on exactly four of
the 33 original log-chart coordinates: 8 (C0L), 15 (date-zero loan rate),
24 (C1L), and 28 (date-one inflation). Its date-zero policy innovation
h does not appear directly.

For entrepreneur CRRA curvature sigmaE=1, equal stationary C0L=C1L>0,
date-one baseline inflation Pi1=1, baseline loan rate R0>0 and
entrepreneur discount betaE=24/25, this scalar function reduces to:

    nuL(z) = (1/R0)*exp(-z15) - (24/25)*exp(z8-z24-z28).

The candidate SOURCE Lean theorem
sourceFundingDual_sigmaOne_stationary_fourLog expresses an equivalent
two-exponential formula, conditional on those exact economic assumptions.
Its CI result is pending unless the exact terminal Lean logs and axiom
audit have been checked.

## Exact arithmetic evaluation

The script code/irf/audit_frozen_frontier_source_dual_interval.py
interprets the four numeric Python log coordinates as *exact binary64
rationals* via Fraction.from_float and reuses the exact rational
stationary loan-rate box from audit_frozen_stationary_dual_rational.py.

For any rational x with |x|<=1, the exponential interval uses a Taylor
polynomial of degree 20 with the exact bound

    |exp(x) - sum(x^k/k!, k=0..20)|
       <= 3*|x|^21/21!,

since the Lagrange remainder has a factor exp(t) with |t|<=1 and
exp(1)<3. The rate box uses exact fractions and integer-square-root
enclosures. No float64 arithmetic decides the inequality signs.

At the numerical Python 34-boundary centre, whose reserve-remuneration
innovation is h=0.007616947889328002, the certified rational
SOURCE-FORMULA interval reported by successful Python verification job
132572287320 in build #43635827149 is:

    lower: 8.761568990768139e-11
    upper: 8.810276575090167e-11
    width: 4.870758432202767e-13.

This interval is strictly positive, and contains the numeric Python
funding-dual scalar 8.767064851866735e-11.

## Interpretation and firewall

The point obtained by reading the Python float candidate coordinates
as exact rationals is NOT itself a zero of this scalar analytic formula
under the pinned numeric parameter conditions. This is expected: an
approximate Newton boundary solve need not land on an exact zero.

The scalar result does NOT prove any of the following:
- that a concrete Lean Primitives, InheritedState and
  LocalPrefixCoordinates instance has been shown definitionally or
  mathematically equal to the Python frozen input;
- that the remaining 33 genuine SOURCE equations match or are enclosed
  by the Python residual;
- that any full SOURCE 34-equation root exists, is locally unique, or
  satisfies all regime KKT inequalities;
- that the finite P0 tail is the infinite-horizon continuation.

The rational scalar bound is below the conditional Banach residual budget
1.1298503741097344e-7 for radius R=1e-5. HOWEVER the required
SOURCE 34-vector residual enclosure and UNIFORM 34x34 derivative
enclosure on the entire box have not been established, so the root
certificate remains PENDING.

Reproducibility: the successful Python verifier generated
code/irf/output/frozen_frontier_source_dual_rational_interval.json,
which is retained in the build artifact named
frozen-python-34-boundary-and-rational-sign.


## Exact-rational single-row zero bracket (reproducible new result)

A second auditor, code/irf/audit_frozen_frontier_source_dual_scalar_root.py,
was executed successfully in build
https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43637042030
at SHA b5c3d3498522f3b09b83563faf2c7f5f42b8462f.

Keeping the OTHER three funding-dual log coordinates exactly at their
binary64-as-rational Python frontier values, change ONLY z15. The
strict exact-rational Taylor/rate endpoint signs prove that the
stationary sigmaE=1 SOURCE-formula scalar

    g(t) = exp(-t)/R0 - (24/25)*exp(z8-z24-z28)

has one and only one real zero with offset

    8.8867187500000e-11 < t-z15 < 8.9843750000000e-11.

The rational bracket width is exactly 9.765625e-13. The 13 exact
interval evaluations in GitHub Actions checked that the lower
endpoint residual is strictly positive and the upper endpoint is
strictly negative, and retained exact Fraction sign witnesses.
Continuity and strict negativity of
g'(t) = -exp(-t)/R0 (for positive R0) imply unique scalar zero.

Proof-status firewall:
- DEMOSTRADO BY EXACT RATIONAL SIGN ENCLOSURES: one zero of this
  analytic *scalar formula* at pinned numerical input coordinates.
- PENDIENTE: same-coordinate identification of the scalar numerical
  values with an exact Lean SOURCE parameter instance and all of its
  other 33 equations, an actual SOURCE 34-equation root, a uniform
  derivative enclosure and complete KKT/equilibrium validity.
- Candidate Lean theorem
  sourceFundingDual_scalar_zero_by_adjusting_log_loan_rate shows a
  formal one-coordinate existential zero at positive stationary
  SOURCE parameters, but must not be marked DEMOSTRADO until its
  dedicated Lean CI run succeeds with an axiom audit.
- Changing z15 alone generally destroys other SOURCE equalities,
  so this is NOT a root of the economic 34-vector.

These results together isolate the financial scalar obstruction,
rather than closing the SOURCE system.

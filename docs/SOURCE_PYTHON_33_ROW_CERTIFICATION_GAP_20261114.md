# SOURCE-to-Python 33-row bridge: current verification gap

Date: 2026-11-14. This ledger is grounded in the saved CI artifacts
`source_python_33_row_claim_readiness.json` and
`partial_source_jacobian_row_scale_ledger.json` extracted from
[build #43637042030](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43637042030).

## Exact scope

The 33 SOURCE equation labels and their permutation into Python order
have been checked. Candidate numerical transcriptions exist for all 33
rows, but NO full functional equality with the exact
`EconomicModel.lean` operator and no validated SOURCE Jacobian bound
has been certified.

The equation partition recorded in the audit is:

- 8 heterogeneous-firm rows, SOURCE indices:
  `0,1,2,3,17,18,19,20`.
- 9 scalar normalization rows, SOURCE indices:
  `4,5,6,9,10,21,22,25,26`.
- 16 identity / other economic rows, SOURCE indices:
  `7,8,11,12,13,14,15,16,23,24,27,28,29,30,31,32`.

The partial 9-row scalar chart reports float numerical derivative
errors of order 5.54e-12. These are *diagnostics*, not directed interval
errors and not proofs of all 33 derivative rows. The partial scalar
factors' numerical nonzero product does NOT prove invertibility of
the complete 33x33 row map.

## What the recent Lean theorem DOES and DOES NOT prove

The actual two-collateral-log 34-row SOURCE map and the original 34-row
SOURCE map are related by a formally checked exact two-row rescaling
plus the verified SOURCE-to-Python **index** permutation under a genuine
SOURCE positive binding root. Their conditional Jacobian bijectivity
equivalence and Schur criteria were axiom audited.

But the second SOURCE map is still a SOURCE map; its index order does
not prove that `finite_irf.py` computes the exact same economic
functions, nor that its fixed binary64 P0 continuation equals the
actual SOURCE continuation. The cross-language economic identity
must include all 33 rows, especially the 8 firm Euler/pledge row
shears, the 16 untouched identities, and the OTHER scalar logarithmic
normalizations used in the Python solver.

## Next verification sequence

1. Supply ONE explicit exact SOURCE `Primitives`,
   `InheritedState`, `LocalPrefixCoordinates`, intervention slice
   and finite-tail rule corresponding to the pinned numerical values.
   Do not confuse binary64 floats with exact decimal rationals.
2. Prove 16 exact SOURCE/Python identity-row functional equalities
   on a common positive open chart. No Jacobian step should precede
   the functional identification.
3. Prove 9 scalar normalization formulas with positive nonzero factors
   in the correct branch, beyond float derivative comparisons.
4. Prove the 8 firm equations' exact cross-operator shears and the
   full invertible left row transform, including its off-root product
   rule and the 34th funding-dual equation.
5. Construct validated enclosures of the transformed true SOURCE
   34-residual at the candidate centre and the true Jacobian
   uniformly over a 34-dimensional closed box. Compare with the
   exact-rational sign-and-inverse budget
   1.989339369548391e-05 per entry only in compatible coordinates.
6. Apply the conditional Banach root box gate, then check regime KKT,
   dynamic continuation and the wider equilibrium conditions.

## Separate scalar advance

The literal SOURCE funding-dual stationary sigmaE=1 formula,
with Python frontier log values interpreted as exact rationals,
has a unique scalar zero when only log loan-rate coordinate 15 is
modified by an offset strictly between
8.88671875e-11 and 8.984375e-11, as shown with exact rational
opposite-sign bounds. This does NOT provide the missing 33-row
SOURCE root. Its Lean algebraic existence candidate is independent
and requires its own terminal CI check.

Statuses: DEMOSTRADO (the SOURCE/SOURCE Jacobian transport and
conditional Schur theorem); NUMERICO (the Python-boundary and
source-shaped normalization audits); EXACT RATIONAL CONDITIONAL
(the sign interval and Banach budgets); PENDIENTE (the full
SOURCE/Python semantic bridge, root, inverse, equilibrium and growth).

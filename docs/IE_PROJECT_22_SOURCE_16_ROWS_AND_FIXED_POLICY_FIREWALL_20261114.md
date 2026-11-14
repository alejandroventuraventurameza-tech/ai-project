# IE Project 22 — SOURCE remaining rows, policy-fixed fiber and boundary firewall

Checkpoint: 2026-11-14. Dedicated branch:
`work/lean-ci-validation-source-33-row-20261114`.
Status in this note is deliberately version-scoped: the new Lean candidates
are **pending their exact GitHub Actions run**, independently of prior
green Lean campaigns. No full equilibrium certification is asserted.

## 1. SOURCE augmented object versus the IRF object

The original SOURCE augmented boundary is

```text
F(z,h) = (B(z,h), nuL(z)),  z in R^33, h in R.
```

Here B is the original 33-row binding-prefix SOURCE residual with the
L collateral row expressed as zero normalized slack, and nuL is the
actual financing dual of firm L. A zero of F simultaneously imposes:

- Both H and L collateral faces binding at date zero (the original
  L face is B's row 5).
- The L normalized funding dual equal to zero (34th row).

This is a **switching-frontier** configuration, not a routine root of
the S (L slack) or B (strict L dual) IRF equations. The reduced
32-log-plus-h construction G = B o L is a square 33x33 system
only because h is ENDOGENOUS in that boundary root search.
For a preassigned h_target, G(u,h_target) has 32 free economic log
coordinates but still 33 equations; it need not have a zero.

The finite IRF code solves the distinct 33-log, 33-equation
branch-specific Python prefix residual at fixed shock v_R=-1e-5,
with L's initial regime equation specialized separately to S/B.
No unproved cross-equilibrium equivalence is permitted.

## 2. Observed distinct innovations

The saved [Python build 43646342640](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43646342640)
reports a numerical free-h boundary solution

```text
hStar = +0.007616947910146871
max reduced33 residual = 8.43769498715119e-15 (binary64)
```

The production IRF source `code/irf/finite_irf.py` uses a fixed,
negative `v_R=-0.00001` (approximately -0.1 basis points).
These are distinct policies, and the boundary root does not prove
an IRF root at the second value. Even exact equality of h would
leave additional inherited-state and continuation correspondence
obligations: the free-h Python boundary uses
`frozen_stationary_seed(steady_case())`, whereas the production
IRF main experiment uses `make_boundary(steady_case())`.
Their economic identity is not assumed.

The new runtime firewall
`code/irf/audit_reduced33_fixed_policy_fiber.py` compares the generated
JSON witnesses, their SHA256 provenance and policy instrument, and
writes `frozen_reduced33_fixed_policy_fiber_gate.json`.
It fails on an unreviewed sign/scale change and explicitly sets the
SOURCE root and full-equilibrium flags to false.
This is an audit of interpretations, not an interval proof.

## 3. Exact 16 SOURCE other-row interface

The candidate
`lean/candidates/Ventura26LiquidityAllocation/SourceSixteenRemainingActualRowsCandidate.lean`
maps the actual augmented SOURCE equations to
`localReducedRemainingResidual`, for every z,h off root and
with the ORIGINAL two date-data objects and inherited state.

| SOURCE row/date 0 | SOURCE row/date 1 | Internal remaining row | Economic equation |
|---:|---:|---:|---|
| 7 | 23 | 1 | Capital supply |
| 8 | 24 | 2 | Aggregate resources |
| 11 | 27 | 5 | Rotemberg NK Phillips |
| 12 | 28 | 6 | Reserve remuneration rule |
| 13 | 29 | 7 | Reserve quantity rule |
| 14 | 30 | 8 | Loan pricing |
| 15 | 31 | 9 | Deposit pricing |
| 16 | 32 | 10 | Bank balance |

The candidate also checks that these sixteen indices are fixed by
the previously audited SOURCE-to-Python output permutation.
This means ONLY that the SOURCE rows and their indexing are
traceable to original definitions. It does **not** establish
functional equality to Python `remaining_residuals` or validate
its binary64 derivatives and inherited continuation.

The 16 rows together with 8 firm rows and 9 scalar/normalization rows
exhaust all 33 original SOURCE positions. Exhausting index positions
is not a proof of cross-language equivalence.

## 4. Necessary next scientific bridge

1. Fix literal SOURCE `Primitives`, `InheritedState`, `Z0`,
   `dateOne`, `recurrent`, `tail` and the exact calibration
   interpretation (real-decimal versus binary64).
2. Identify source date-zero and date-one `LocalPrefixDateData`
   with Python `state, controls, next_state, next_controls, aux`
   on an OPEN positive chart, including `P0` date-two continuation.
3. Compare 16 SOURCE economic formulas with the corresponding
   original Python formulas, not merely with a second Python
   source-shaped transcription. Handle exact log normalization,
   firm Euler shears and relevant positive domains separately.
4. Derive a certified SOURCE center residual and 33x33 Jacobian
   enclosure on a common closed box with rigorous rounding.
5. Only then apply the already prepared conditional rational
   Neumann/Banach test to a genuine SOURCE root; separately examine
   KKT, supported histories and terminality.

No structural IRF at fixed negative remuneration, original infinite
competitive equilibrium or permanent-growth theorem is certified
by the present 16-row identity or free-h boundary search.

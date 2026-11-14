# IE project 27 — SOURCE/Python collateral rows 5 and 21: proof ledger

Date: 2026-11-14. Branch: `work/lean-ci-validation-source-33-row-20261114`.
This is a **research checkpoint**, not an existence proof for economic
equilibrium. Nothing is merged to `main`.

## Previously closed foundations

- The pinned [Lean run #43592079851](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43592079851),
  SHA `a9b75b5687367df44e4cbd46bc7bb400fab15d43`,
  finished **SUCCESS**, including full candidate compilation and explicit
  axiom audit of seven designated theorems. Their dependencies are the
  ordinary Lean/Mathlib foundations `propext`, `Classical.choice`,
  `Quot.sound`, with no `sorryAx`.
- The exact SOURCE-typed 10-by-6 surrogate continuation and the
  specialization to the **60 exact decimal** P0 coefficients are
  kernel checked. The latter does NOT turn a finite surrogate tail
  into a full infinite-horizon continuation.
- [Build #43592139342](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43592139342)
  finished **SUCCESS**: 70 original-Python/source-shaped nonlinear
  probes around the same frozen predecessor and reserve-rate h* had
  maximum reconstructed equation difference `3.552713678800501e-15`.
  This is float64 Python code agreement, not a SOURCE kernel evaluation.

## A. Collateral row 5, firm L at date zero

At a positive SOURCE log chart and any reserve-rate innovation h,

`r5 = log(F_L1 / (theta_L * (1-delta) * Pi_1 * q_1 * K_L1))`.

The original `finite_irf.prefix_residual` binding branch evaluates
`math.log(x1[2+i] / (collateral * x1[i]))` for firm `i=1` with
`collateral=s.pledge[i]*s.ad*u1[5]*u1[6]`, hence OUTPUT row 5.

The four SOURCE log coordinates are:

- `z[1]`: firm L capital K_L1;
- `z[3]`: firm L nominal face F_L1;
- `z[28]`: inflation Pi_1;
- `z[29]`: capital price q_1.

At the level of positive REAL-ARITHMETIC logarithms, the exact
gradient on this chart is `-e_1 + e_3 - e_28 - e_29`. All other
29 coordinate derivatives and the DIRECT derivative in h vanish.
This does NOT assert the equilibrium response dz/dh vanishes.

- SOURCE candidate `SourceCanonicalPythonCollateralFourCoordinatesCandidate.lean`,
  SHA `e798d7d3dccbf3f93fb2d312e045504bf3f0712e`:
  attempts a genuine SOURCE functional identity for all z,h plus
  exact dependence on only the four coordinate inputs. Its
  [Lean run #43593221199](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43593221199)
  and the extended explicit-axioms
  [#43593289318](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43593289318)
  require terminal success before promoting the new proof status.
- Original Python SOURCE-coordinate AST guard
  `audit_source_python_l_collateral_row5_ast.py` **PASSED**
  in the `code/verify.py` job of
  [build #43593278129](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43593278129).
- Forward-AD test of the actual Python residual, at the boundary
  and 12 additional positive-chart points, **PASSED**
  [build #43593423891](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43593423891):
  maximal value error `2.9583811528982595e-16`, maximal forward AD
  gradient error `2.220446049250313e-16`, and maximal direct h
  independence error `0.0`. These are numerical floating errors,
  not directed interval rounding enclosures.

## B. Collateral row 21, date-one common pledge

The original SOURCE `commonPledgeOne` is the LEVEL equation

`R21 = J_2 - (1-delta) * Pi_2 * q_2`.

The original `finite_irf.binding_period_residual` instead appends

`math.log(next_compact[2]/(s.ad*next_controls[5]*next_controls[6]))`.

In the full 33-prefix output, the date-zero block contains 17
equations; two firm date-one budgets and two firm date-one Euler rows
precede common pledge, placing it in Python row **21**. SOURCE's
index is also 21.

- New `SourceCanonicalTwoPledgeLogBoundaryCandidate.lean`,
  SHA `a28d62d30f6f6cd043cd71359e527d95b38249a1`,
  defines the genuine SOURCE 34-map with *both* row 5 and row 21
  log-normalized. The intended theorem is exact zero-set equivalence
  to SOURCE's original 34 boundary, at any h, assuming positive
  face ratio in row 5, and positive level and future valuation
  in row 21. It makes **no** claim about derivative equality
  away from a root.
- Candidate compiled under
  [Lean #43593555252](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43593555252)
  and separate expanded axiom audit
  [Lean #43593665074](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43593665074):
  **PENDING until inspected terminal result**.
- `audit_source_python_common_pledge_row21_ast.py` extracts the
  original binding-period equation AST and checks SOURCE's level
  row, the original 33-prefix row ordering and the new Lean
  log-ratio expression. This is wired to `code/verify.py`,
  [build #43593665098](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43593665098):
  **PENDING until terminal result**.

## C. What is proved, what is NOT

- Exact Lean SOURCE zero-set and linear-derivative identities established
  in previous pinned successful runs are **DEMOSTRADO** under their
  written hypotheses.
- Actual Python AST match and AD probes are **NUMERICO / CODE-CONTRACT**.
- Cross-language equality at all 33 economically matched rows,
  exact floating-point roundoff enclosure of every 34x34 derivative,
  and an actual SOURCE root are still **PENDIENTE**.
- At `S_L=nu_L=0` strict complementarity fails: a branch-specific
  inverse/Schur certificate is insufficient to establish smooth
  regime crossing or long-run monetary transmission.
- Independent exact rational inversion of the two ROUNDED Python
  34x34 matrices is NOT an economic SOURCE Jacobian certificate.

## Next critical obligations

1. Upgrade new source row-5 and row-21 claims only after the exact pinned
   Lean CI is green and the declared axioms are clean. Fix the first
   failed module if necessary.
2. Formalize the derivative scaling of SOURCE date-one common pledge
   `log(J2/V2)` relative to the raw level residual `J2-V2` at a
   genuine root, and its row transport.
3. Complete exact REAL SOURCE/Python formula mapping for other
   economic rows and identify the baseline primitives, inherited state
   and finite `P0` with actual SOURCE objects.
4. Produce directed interval bounds on the transformed true SOURCE
   34x34 Jacobian and rigorously certify existence of a SOURCE zero.
5. Extend to the true infinite-horizon continuation, all KKT and
   accounting restrictions, multiple monetary instruments and genuine
   long-run growth effects.

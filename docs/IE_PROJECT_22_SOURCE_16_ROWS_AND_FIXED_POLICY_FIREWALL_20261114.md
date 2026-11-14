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


## 5. Lean compiler follow-up and SOURCE date-two P0 contract

CI evidence is revision-scoped. The first 16-row audit
[43647651031](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43647651031)
FAILED before proof verification with a syntax error at line 79:
`expected ';' or line break`. This is a **source code parser error** in
the four term-level `let` bindings preceding the conjunction of 16
SOURCE rows, not a counterexample to the economics.

Commit `3fbf263521fc89a548ca72bdf3ea80655f49cf73` adds explicit
terminators to those binders. The dedicated pinned Lean audit is
[43649204171](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43649204171);
do NOT label the theorem verified unless that run is a success and
its axiom printouts are inspected.

Separately the exact SOURCE-typed date-one P0 continuation candidate,
`SourceFrozenP0LiteralDateCalendarCandidate.lean` (commit
`e63f1d17a02d8b64fb8ed8253581b8fa88c9bd22`), targets the original
`localPrefixDateZeroData` and `localPrefixDateOneData` builders. It
proposes four proof obligations, all requiring a separate kernel audit:

- date-zero next controls are exactly the PREFIX date-one controls
  `Z.controlsOne`, not the finite P0 continuation;
- actual SOURCE date-one future control levels equal
  `u0_j*exp(sum_k sourceFrozenP0TenControls[j,k]*z_k)` when the six
  date-two state coordinates are on the positive log chart;
- log deviations of all ten controls are exact P0 matrix products
  with the baseline positivity hypotheses; and
- the date-two controls are strictly positive on that chart.

The corresponding combined Lean/axiom run was launched as
[43649329765](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43649329765).
None of these proves the numerical binary64 `matvec` or `exp`
operations equal real arithmetic, nor the unproved infinite terminal
continuation or the 33-row SOURCE/Python operator equality.

**Independent QA issue:** Editorial QA
[43649204206](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43649204206)
failed to push compiled PDFs because another commit advanced the
development branch between its head check and push. This is not a
LaTeX compilation error. Commit `0bc07c40662010b3584a7fb2d0cca03476d2b5a6`
adds a guarded re-fetch and preserves a hard failure if push fails
without a concurrent branch-head change. The new exact-sha editorial
run must be checked rather than retroactively changing the old status.

The original Python/free-h versus fixed-negative-h audit remains
confirmed by the successful
[build 43647840851](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43647840851).
Neither the parser fix, the P0 controls identity, nor PDF QA has
promoted Python's reduced33 residual to a true SOURCE root.

Next scientific gate (unchanged): instantiate SAME source primitives,
inherited base, date-one data and tail as Python; prove off-root
functional equality of economic rows and a certified full SOURCE
derivative enclosure before any existence, policy IRF or growth claim.


## 6. Follow-up: compiled original rows, original Python P0 wiring, P0 composite candidate

Exact source-commit scope for this checkpoint:

- SOURCE 16-row parser repair: commit `3fbf263521fc89a548ca72bdf3ea80655f49cf73`.
  The pinned Lean audit
  [#43649204171](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43649204171)
  has status **success**, including original SOURCE 16-row identities,
  unchanged source/Python row permutation positions, and the
  fixed-policy SOURCE root subtype equivalence. Axiom printouts list
  standard Lean `propext`, `Classical.choice` and `Quot.sound`
  for the nontrivial source correspondences. This does **not** imply a
  SOURCE economic root.
- Finite P0 SOURCE calendar candidate:
  `SourceFrozenP0LiteralDateCalendarCandidate.lean`, added at
  `e63f1d17a02d8b64fb8ed8253581b8fa88c9bd22`. The exact-run Lean audit
  [#43649329765](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43649329765)
  was in progress when this note was written; no success is inferred.
- Direct same-engine Python structural path:
  `code/irf/audit_source_dateone_p0_operational_wiring.py` at
  `125e4e6d56c14a8b22d2bdc744350ebafd4604f8`. The script verifies
  with Python AST that the original `prefix_residual` computes
  `u2 = s.base[6+i]*exp((P0 @ z[17:23])[6+i])` for every i=0,...,9
  and passes those SAME ten controls to `binding_period_residual`,
  which uses `remaining_residuals` for the eight non-firm economic
  equations. Original Python code, not a rewritten surrogate, is used.
  The [build #43650031798](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43650031798)
  completed its `Run code/verify.py` job successfully. The audit's
  12 off-root cases (2 regimes x 2 policy vectors x 3 charts) have
  zero internal Python-call discrepancy and the JSON explicitly
  retains `SOURCE_Python_16_row_functional_equality_proved=false`.
  The [latest build #43650031798](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43650031798)
  must be used for full aggregate workflow status.
- Composite Lean SOURCE/P0 module:
  `SourceSixteenRowsFrozenP0CompositeCandidate.lean` at
  `5927bd541a7f72919af6a7e454a7d32856c96c67`, which submits
  one proposition jointly covering the eight original SOURCE
  date-one economic rows and the exact future control evaluation
  from the frozen real P0 matrix under explicit positivity and
  date-two log-chart hypotheses. CI print-axiom registration at
  `02b84392355d253b43fffc8ea476c5bb9f09895f`.
  Its dedicated Lean run must PASS before it is marked DEMOSTRADO.

**Scientific implication and remaining gate.** These three improvements
make the calendar/policy/continuation contract more explicit in both
source and numerical code. They do not yet instantiate the same
`Primitives`, `InheritedState`, `Z0` and exact real-versus-float
calibration for all 33 economic rows. A complete cross-language
functional identity (or rigorous interval discrepancy on a common
box) and the true SOURCE Jacobian enclosure remain mandatory before
claiming a certified root, equilibrium IRF, or permanent growth effect.

## 7. Fully pinned stationary SOURCE baseline (exact Lean input target)

The original SOURCE 34-equation boundary previously retained arbitrary
`Primitives`, `InheritedState`, `Z0`, time labels and a generic
continuation. This makes it impossible to identify a specific numerical
SOURCE root merely by calling a Python evaluator.

Two new candidate modules eliminate those discretionary choices:

1. `SourceStationaryFrozenP0ConcreteOperatorCandidate.lean`
   (commit `bef0b3e575eb0950b37e0c73effd9fae1377a06c`):
   instantiates the ACTUAL SOURCE 34 and 33 residual maps with
   `ProposedStationaryPrimitives.primitives G`,
   `ProposedStationaryInheritedState.inheritedState G`,
   the literal `.dateOne`/`.recurrent` calendar and
   `sourceLogLinearContinuation x0 u0 sourceFrozenP0TenControls`.
   Proposes exact 34-to-33 root-set equivalence and distinguishes
   the date-zero remuneration policy innovation from unchanged
   date-one primitive fields at *fixed* economic coordinates.
2. `SourceFullyPinnedStationaryP0OperatorCandidate.lean`
   (commit `2e52075c7641ba42bc77cae307939b2cfd876f59`):
   constructs the actual 33-component stationary SOURCE reference
   `fullyPinnedStationarySOURCEZ0` from the already proved stationary
   capital, nominal promises, bank face, reserve lags and all ten
   controls at dates zero and one; the date-two compact state uses
   `ProposedStationaryRealScale.stateSix`. Proposes:
   `LocalPrefixCoordinatesPositive fullyPinnedStationarySOURCEZ0`,
   the conditional exact SOURCE root-set equivalence with no
   arbitrary Z0, and the exact P0 return to baseline controls.

The resulting concrete original-SOURCE object is

```text
P_G = ProposedStationaryPrimitives.primitives G
I_G = ProposedStationaryInheritedState.inheritedState G
Z0  = fullyPinnedStationarySOURCEZ0           -- 7+10+6+10 levels
tail = sourceLogLinearContinuation stateSix controls frozenP0Ten
F_G(z,h) = augmentedBoundaryZeroResidual P_G I_G Z0
             .dateOne .recurrent tail z h
L_G(u) = sourceFundingDualLift32 P_G Z0 u
R_G(u,h) = (F_G(L_G(u),h)).1                -- 33 genuine economic rows
```

Only the public-debt supply parameter `G` remains a stationary
SOURCE parameter; neither `Z0` nor the inherited state nor finite
tail is a caller-chosen surrogate. The free-h switching frontier is
**not** the fixed-negative-IRF shock experiment.

A new Python provenance audit
`code/irf/audit_fully_pinned_source_python_reference.py`
(commit `ec97cceb28282feb7799c1983ed6e780be4a6e03`) checks the
actual SOURCE Lean declaration anchors, the original Python
`frozen_stationary_seed(steady_case())` 7+10+6+10 ordering, its 33
positive binary64 reference values, and the fact that the OLD
`make_boundary()` baseline is a different inherited economy.
`code/verify.py` runs it and build archives its JSON. This audit
does **NOT** evaluate Lean real expressions in Python, certify
SOURCE/Python cross-language function equality or supply a root.

Status boundary at note-writing time: the new proofs and audit are
**submitted**, not promoted to DEMOSTRADO/NUMERICO until their
specific GitHub Actions runs conclude and outputs are inspected.
The last independently established Lean gate was
[#43650128978](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43650128978)
for the SOURCE/P0 8-row composite, with green pinned compilation
and `#print axioms`.

Next obligations are substantive: compare the actual SOURCE
`R_G(u,h)` with original Python's 33-row evaluator under exactly
this stationary inherited reference; reconcile real decimal/rational
constants with binary64 and normalized rows, then rigorously bound
the SOURCE residual and Jacobian on a full box. Only after these
can a rational Neumann/Banach result establish a true SOURCE root.

## 8. Discharging the date-two log-index/P0 premise

The previous eight-date-one-row composite needed the hypothesis

```text
(localPrefixLogChart Z0 z).stateTwo
  = localPrefixStateSixLogChart x0 z2.
```

The SOURCE basepoint `fullyPinnedStationarySOURCEZ0` is now defined
literally, so this hypothesis can be discharged rather than assumed.
The new candidate
`SourcePinnedDateTwoLogIndexP0Candidate.lean` (commit
`691e83571fd7ea4681b7c536469028a19437626d`)
defines the six-state SOURCE extraction by original log indices

```text
z2 = (z17, z18, z19, z20, z21, z22)
```

and submits the exact real identity of the original SOURCE 33-log
date-two state with the six-coordinate log state. It then applies the
previous audited `sourceFrozenP0_dateOne_nextControl_level` and
`source16_dateOne_actual_rows_with_exact_frozenP0` to establish that
the ACTUAL date-one SOURCE economic equations 23,24,27,28,29,30,31,32
use the P0 future controls with those six exact SOURCE logs at every
`z,h`, with NO new chart-matching premise.

These declarations have been added to `#print axioms` in
`.github/workflows/lean-candidates.yml` at
`bbdd5f692a29978a2733bd5f181c24224797ce7a`.
Their audited CI run is
[GitHub Actions #43652154747](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43652154747).
**Do not promote them to DEMOSTRADO until that particular run
completes successfully.** They do not make any claim about binary64
numerical equality, an infinite-horizon P0 continuation, a SOURCE
root, or a fixed-shock equilibrium.

For the previous fully pinned reference, the fail-closed Python
data provenance script is
`code/irf/audit_fully_pinned_source_python_reference.py`,
wired into `code/verify.py` and archived by `build.yml`. It checks
all 33 original Python frozen baseline levels are positive and in
the 7+10+6+10 order, while explicitly rejecting the older
`make_boundary()` baseline as the stationary predecessor.
This is only an AST/declaration/data-order guard, not execution of
SOURCE real arithmetic in Python. Source economic operator equality,
certified derivative bounds and root existence still require
an independent proof.

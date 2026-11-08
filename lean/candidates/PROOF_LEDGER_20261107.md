# IE Project 2 — Lean proof ledger (2026-11-07)

## Repository and validation contract

- Repository: `alejandroventuraventurameza-tech/ai-project`.
- Review branch: `work/lean-ci-validation-otc-20261106`.
- The pinned source and checkpoint are NOT edited in this branch.
- Lean toolchain: `leanprover/lean4:v4.30.0-rc2`; upstream and mathlib revisions are checked by `.github/workflows/lean-candidates.yml`.
- Last verified candidate-code commit: `5719e8432cee4a9cd96ca32b4e12947a9f5b27e4`, workflow run `42352997659` (success, including the stochastic vector theorem and its axioms).
- Stochastic vector candidate and subsequent changes must be verified separately using the run corresponding to their exact SHA. Do not inherit a green status from an older commit.

## Source-model limitation: the stored dual is not automatically endogenous

The source `FirmOptimal` is invariant under changing only `Allocation.collateralDual`. In particular,
`ProposedFirmOptimalVariation.firmOptimal_replaceCollateralDual_iff` and
`exists_firmOptimal_without_capitalEuler` show that `FirmOptimal` by itself
**cannot** imply the Euler residual involving an arbitrarily stored dual.

The original `PaperInterface.localMacroMultiplicitySpec` also has a formal
refutation because of a literal allocation-uniqueness requirement with
an unconstrained collateral-dual carrier. The proposed primal repair does
not yet prove the existence of both branches.

This limitation is logical/economic, not a Lean tactic deficiency.

## Date-zero capital optimality chain

1. `DateZeroCapitalDeviationCandidate`, `DateZeroCapitalUtilityCandidate`,
   `DateZeroCapitalNeighborhoodCandidate`, and
   `DateZeroCapitalGainContinuityCandidate` construct genuine perturbations,
   preserve the source budgets/wealth transitions, handle objective convergence,
   and establish two-sided feasibility in the strictly slack regime.
2. `DateZeroCapitalEulerDerivativeCandidate` differentiates the literal CRRA
   objective and nonlinear Cobb-Douglas capital gains. No infinite sum is
   differentiated without first cancelling its unaffected tail.
3. `DateZeroCapitalExpectedEulerCandidate.firmOptimal_expectedCapitalEuler`
   derives the equality in expectation from `FirmOptimal`, positive capital,
   and strict collateral slack.
4. `DateZeroDeterministicEulerBridgeCandidate`,
   `DateZeroDeterministicMarkovBridgeCandidate`, and
   `DateZeroCalendarEulerBridgeCandidate` discharge singleton-history
   weights from the original Markov law when the source calendar transition
   has probability one. This is conditional on a deterministic calendar,
   NOT a new global restriction on the stochastic model.
5. `DateZeroPrimalKKTBridgeCandidate` derives the zero primal capital gap
   and, in the original source strict-slack regime, a zero ORIGINAL capital
   Euler residual because `DateZeroSlackBorrower` explicitly sets the
   dual to zero.

## Binding collateral: one-sided and scalar certificates

1. `OneSidedCollateralMonotonicityCandidate` shows that increasing capital
   with fixed financing preserves robust collateral constraints when its
   coefficient is nonnegative.
2. `DateZeroOneSidedFeasibilityCandidate` and `RightSidedFermatCandidate`
   give right-sided feasible plans and the necessary inequality for a
   one-sided local optimum.
3. `DateZeroOneSidedEulerInequalityCandidate` derives the EXPECTED weak
   Euler gradient inequality from the original dynamic objective.
4. `DateZeroOneSidedDeterministicCostCandidate` and
   `DateZeroOneSidedPrimalGapCandidate` show a nonnegative primal Euler gap
   under deterministic history weights.
5. `ScalarKKTMultiplierConstructionCandidate` constructs the scalar
   `mu = primalGap / collateralUnit` for a strictly positive unit coefficient.
   It satisfies the algebraic capital row, but its economic identification
   with the source dual is NOT automatic.
6. `DateZeroScalarKKTFromOptimalCandidate`,
   `DateZeroScalarBindingComplementarityCandidate`, and
   `DateZeroCalendarScalarKKTCandidate` build the source-calendar binding
   scalar *capital-row* and complementary-slackness witness. These modules
   were compiled successfully on run `42352834967`. The positive-prices
   variant uses positive pledgeability, inflation and next capital price,
   together with the source depreciation bound.
7. `firmOptimal_binding_actualDual_identified_of_sourceRow` identifies
   the constructed and stored duals ONLY WHEN the original capital Euler
   residual is explicitly assumed zero. That premise remains a missing
   economic derivation for the binding regime.

## Stochastic statewise candidate (validated on run 42352997659)

`DateZeroStatewiseCapitalMultiplierCandidate.lean` represents the
nonpositive expected capital-direction gradient with a *vector* of
successor multipliers `mu : S -> Real`. When one supported collateral
constraint is active with positive coefficient, a sparse nonnegative vector
can satisfy the expected stationarity identity and per-state complementary
slackness. The construction does not assert a per-state Euler equation,
a complete multi-control KKT system, or identification with the source
`Allocation.collateralDual`. The candidate compiled on the specified run and its principal theorem's
printed axioms were `propext`, `Classical.choice`, and `Quot.sound`.

## Remaining mathematical proof obligations

- Derive the binding-case **source** multiplier from joint capital-and-loan
  perturbations, the loan first-order condition, and an explicit constraint
  qualification/normalization. The existing capital-only scalar certificate
  does not by itself prove all firm KKT conditions. Never infer the freely
  stored source dual from `FirmOptimal` alone.
- For genuinely stochastic aggregate transitions, preserve expectation
  structure and distinguish statewise constraint multipliers from a single
  stored scalar dual.
- Construct exact competitive-equilibrium witnesses for the distinct S/B
  allocations, prove primal separation, and audit Jacobian/implicit-function
  and boundary certificates without assuming the conclusion.
- Establish infinite-horizon feasibility, terminality, households/banks/
  retailers' optimality, market clearing, and correspondence between reduced
  equations and the source full model.
- Reconcile the final paper claims with the formal theorems and rerun
  `#print axioms` for each principal theorem.

## Validation commands

The GitHub Actions workflow `lean-candidates.yml` clones the pinned upstream,
reconstructs the checkpoint and candidate modules in dependency order, compiles
all `*Candidate.lean` files, and prints principal theorem axioms.
Inspect the **candidate-audit** workflow rather than the generic `build`
workflow and use the run with the exact head commit SHA. A previous green run
does not certify subsequent commits.

## Adenda verificable — complementariedad escalar (7 de noviembre de 2026)

Nuevo módulo independiente: `ScalarComplementarityMultiplicityCandidate.lean`, recompilado en [GitHub Actions 42430587348](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42430587348) al commit `ab86ddfc0b9220ff7aa7f8fe8fa3856cfe4f182b`. Ambos resultados `scalar_complementarity_exactly_two` y `no_scalar_complementarity_of_negative_boundary` compilan y su `#print axioms` retorna `[propext, Classical.choice, Quot.sound]`. **Alcance:** argumento escalar con `StrictAntiOn M (Set.Ici 0)` y raíz interior asumida; no demuestra monotonía de la marginal de 33 ecuaciones, existencia real del régimen, `CompetitiveEquilibriumWithInitialIntervention`, ni corrige la unicidad literal de `Allocation`. La interfaz del paper original sigue sin testigo completo. Las referencias históricas de esta bitácora a trabajos anteriores permanecen deliberadamente conservadas.

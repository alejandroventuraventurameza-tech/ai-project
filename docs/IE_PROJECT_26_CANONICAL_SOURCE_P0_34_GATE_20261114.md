# IE project 26 — canonical SOURCE 34-row bridge and finite P0 provenance

Date: 2026-11-14. Branch:
`work/lean-ci-validation-source-33-row-20261114`.
**Research checkpoint, not a claim of economic equilibrium existence.**

## 1. Lean compile status and corrected blockers

- [#43589767500](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43589767500) **SUCCESS** for `SourceAugmented34CanonicalLogBoundaryCandidate` at SHA `7cd8a83ca8b8068e26ab06f6592d9181884ed104`. On the positive collateral face/pledge domain, using `log(face_L/Gamma_L)` in the genuine SOURCE 34-system preserves its exact zero set for all monetary innovations h.
- [#43591095735](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43591095735) **FAILED in the generic finite-tail module**, *not* in the two preceding new canonical SOURCE modules. Compiler logged `COMPILED SourceAugmented34CanonicalLogFrechetCandidate` and `COMPILED SourceAugmented34PythonOrderSourceCanonicalCandidate`. This individual run's overall status was failure; do not promote the full proof ledger without a successful follow-up axiom audit.
- The last tail module's two errors (`No goals to be solved` after `field_simp [hne]`) were removed from `SourceLogLinearContinuationRuleCandidate.lean` in commit `3b59ce06f3d72bdb133981254cfbc3953b68744e`. Its new pinned Lean run is [#43591803307](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43591803307); status must be checked before promotion.

The mathematical sequence so far:
1. Genuine SOURCE 33 raw-binding equations under nonzero h.
2. Normalized slack `S_L=1-face_L/Gamma_L` at the same h.
3. Exact log residual `log(face_L/Gamma_L)=log(1-S_L)`, with positivity hypotheses.
4. Reindex the same SOURCE first 33 equation rows into Python's OUTPUT order, retaining the exact 34th L funding dual.
5. At a true binding root, the exact SOURCE row-5 Fréchet map obeys
   `D_z log(face_L/Gamma_L)=(1/Gamma_L)D_z(face_L-Gamma_L)`.
6. The bottom-right h derivative of the SOURCE dual row is identically zero at fixed z.

**A verified zero-set reparameterization inside SOURCE is not yet a
cross-language equivalence with floating Python functions.**

## 2. The 16x6 finite P0 tail: EXACT decimal coefficient contract

The original pinned `code/irf/inputs/rational_preconditioners.json`
has 16 rows x 6 columns. The first six are the identity and the final
ten are the date-two control log responses. `steady_case()` and
`finite_irf.prefix_residual()` use Python float64 values.

- `SourceLogLinearContinuationRuleCandidate.lean` defines an
  arbitrary SOURCE-compatible 10x6 log-tail response C as a real map
  `LocalPrefixStateSix -> LocalPrefixControlsTen`.
  At strictly positive baseline states and controls, it attempts to
  prove exact log deviation `C*z` and baseline preservation.
  This is a **finite surrogate** tail, not a globally valid
  equilibrium policy.
- `SourceFrozenP0ExactDecimalTailCandidate.lean`, commit
  `5e363bb5f1860789258a5f18a080d6b029a9084c`,
  literally instantiates each of the **60 pinned decimal strings**
  as real-rational Lean decimal literals. Its specialized log-response
  theorem requires the generic continuation contract, and is a
  **candidate pending kernel compilation**.
- `audit_source_frozen_p0_lean_decimal_literals.py`, commit
  `addb843412ad7c498dd989b0f872bdb24c71e53b`,
  checks the 60 SOURCE-typed literals against the 60 corresponding
  JSON strings using exact `Fraction(Decimal(..))` and rejects any
  data drift. It is wired into `code/verify.py` and CI artifacts.
- This exact-decimal SOURCE representation is **not** an assertion
  that Python binary64 floats are equal to those mathematical real
  numbers. The conversion error and arithmetic error are separate.

## 3. Rational conversion error in the actual Python frontier

[Build #43591340435](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43591340435),
SHA `9d39558e9445af8586b243e413435f0050c9d574`,
completed successfully. The exact rational coefficient-representation
audit gave:

- Maximum discrepancy between one exact decimal input coefficient
  and its binary64 representation: approximately
  `3.3015089685632464e-16`.
- Maximum 10-control row sum of absolute coefficient discrepancies:
  `7.227604516605787e-16`.
- Uniform 10-control log-response error bound over the six-state log
  cube `||z_2||_inf <= 1/4`: `1.8069011291514467e-16`.
- At the **numerical Python 34-boundary candidate**
  `h*=0.007616947889328002`, the date-two state log-vector
  has maximum absolute coordinate `0.015299863841544074`.
  The exact rational coefficient-representation contribution to
  each of the 10 finite-tail log responses is at most
  `6.805672531788971e-18`.

Every displayed decimal is a human-readable approximation to the
actual exact Fraction bounds checked by the audit. **Not included**:
rounding in Python matrix multiplication and exp/log, economic
parameter mapping, the true SOURCE operator Jacobian, existence
of an exact SOURCE root, and the long-run equilibrium continuation.

## 4. Additional SOURCE Jacobian lemma

`SourceCanonical34Row5ActualFrechetCandidate.lean`,
commit `a844fd5b6c75ba31636f3bdc111d6629e16fb702`,
attempts two more SOURCE-exact claims in the Python output ordering:

- At a genuine SOURCE binding root, its reindexed row 5 has the exact
  Fréchet derivative `Gamma_L^(-1) * D_z R_L`.
- The policy-to-funding-dual direct lower-right Jacobian entry is zero
  when fixing the SOURCE economic log coordinates.

This module is **PENDIENTE** until the pinned CI of the exact commit
successfully checks the declaration and its axiom audit.

## 5. Next steps / hard barriers

1. Verify a full Lean success on both the generic 10x6 tail and the
   SOURCE-typed 60 coefficient specialization, with clean `#print axioms`.
2. Prove real-arithmetic SOURCE vs. Python-formula equality for the
   remaining 32 SOURCE equations under the exact same primitives,
   inherited nominal variables, timing, P0 and log charts. Indexed
   labels and numerical agreement are insufficient.
3. Enclose the 34x34 SOURCE Jacobian **after** the correct nonlinear
   row normalization/shears and the exact P0 coefficient lift.
4. Use a validated root existence theorem (e.g. Krawczyk/Newton
   interval conditions) to upgrade the Python candidate to an actual
   economic SOURCE root; nonsingularity alone does not imply a zero.
5. Check the other regime KKT constraints, infinite tail, market
   clearing and policy IRFs. At the switch `S_L=nu_L=0`,
   strict complementarity fails; do not infer smooth cross-regime
   dependence from a single branch Jacobian.

**Evidence statuses:** `DEMOSTRADO` applies only to the exact
Lean results on their successful pinned jobs and exact rational
coefficient comparisons in Python; `NUMERICO` to h*, forward AD
and Python finite-prefix roots; `PENDIENTE` to functional
SOURCE-Python equality, exact SOURCE root, economic Jacobian and
full equilibrium.

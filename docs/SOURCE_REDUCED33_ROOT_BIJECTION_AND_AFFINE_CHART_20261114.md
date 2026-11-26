# SOURCE 34 -> 33: root bijection, affine chart and remaining existence gate

Checkpoint 2026-11-14. Review branch:
`work/lean-ci-validation-source-33-row-20261114`.
These statements concern the ORIGINAL Lean SOURCE augmented residual, not a claimed
functional identity with the binary64 Python implementation.

## 1. Actual economic object and hypotheses

Let `F(z,h) = (B(z,h),nu_L(z))`, where
`z : Fin 33 -> Real`, `h : Real`, `B : Fin 33 -> Real`.
The added scalar equation is the actual SOURCE L funding dual, not an
arbitrary collateral or transformed row. The innovation `h` belongs to
**reserve remuneration**; reserve quantity, reserve requirement and corridor
innovations are fixed in this experiment.

For the analytic elimination require:

- Entrepreneur CRRA curvature `sigma_E = 1`.
- Equal date-zero and date-one L entrepreneur consumption, with `C_L > 0`.
- Unit date-one inflation.
- Strictly positive inherited date-zero lending rate `R_0`.
- Strictly positive entrepreneurial discount `beta_E`.

The scalar SOURCE condition is

```text
nu_L(z) = exp(-z15)/R_0 - beta_E * exp(z8 - z24 - z28) = 0.
```

It has the unique eliminated log loan-rate coordinate

```text
z15* = -log(R_0) - log(beta_E) - z8 + z24 + z28.
```

This is an identity conditional on the displayed stationary SOURCE domain,
not a statement that all other economic equations are satisfied.

## 2. Canonical nonredundant 33-dimensional parameterization

Let `u : Fin 32 -> Real` be the free log vector obtained by removing original
SOURCE index 15; let `L(u) : Fin 33 -> Real` insert the eliminated scalar.
After removing index 15, old SOURCE indices `8,24,28` become free indices
`8,23,27`, respectively.

```text
L(u)[15] = -log(R_0) - log(beta_E) - u[8] + u[23] + u[27].
L(u)[i] = u[removeIndex15(i)] for i != 15.
G(u,h) = B(L(u),h).
```

The correct original-coordinate derivative factors are
`dz15/dz8=-1`, `dz15/dz24=+1`, `dz15/dz28=+1`.
Equivalently, in reduced-coordinate notation:

```text
L(u+d)[15]-L(u)[15] = -d[8] + d[23] + d[27].
```

This affine finite-increment identity implies the coefficients exactly in
real arithmetic; it does not rely on finite differences or forward AD.

## 3. Formal equivalence and its limit

Already passed in pinned Lean candidate audits:

- `SourceReduced33PointwiseChartCandidate.lean`: the canonical lift is
  injective and `F(L(u),h)=(G(u,h),0)` pointwise;
  audit #43643814672 on commit `8a079b6`.
- `SourceReduced33FrechetChartTransportCandidate.lean`: conditional
  differentiability transport, exact Frechet derivative identity and
  full-column-rank/injectivity equivalence;
  audit #43645426794 on commit `7583a9e`.

New candidate code, **pending dedicated compiler/axiom audit when written**:

- `SourceReduced33RootEquivCandidate.lean`: an explicit `Equiv` between
  the SOURCE reduced root subtype and the original augmented SOURCE root
  subtype. This establishes no spurious or missing roots **if Lean accepts
  the module**; it does NOT construct any root.
- `SourceFundingDualAffineIncrementCandidate.lean`: expands the SOURCE
  `Real.log` target into the exact affine formula and proves the
  finite-increment identities **if Lean accepts the module**.

These candidates have explicit `#print axioms` entries in
`.github/workflows/lean-candidates.yml`. A green build from an earlier
revision must never be substituted for the audit of the new commit.

## 4. Numerical witness versus exact economic root

The Python reduced33 Newton candidate has residual
`8.43769498715119e-15` (binary64) and regime diagnostics; the
rounded 33x33 Python Jacobian has rational Neumann defect
`2.8052425878694e-10`. The conditional entrywise tolerance is
`9.137410321981649e-05`, **for a hypothetical true SOURCE Jacobian
in identical coordinates**.

The strict true-SOURCE center residual budget is approximately
`9.046036218761833e-08` for a sup-norm radius of `1e-5`,
**provided** the uniform SOURCE derivative enclosure over the entire
box is proved. The Python residual is not that enclosure.

Reference: `docs/SOURCE_REDUCED33_REAL_OPERATOR_AND_AD_GATE_20261114.md`
and `code/irf/audit_frozen_python_reduced33_ad_rational_gate.py`.

## 5. Blocking obligations for an existence claim

1. Instantiate exact SOURCE `Primitives`, inherited state, `Z0`, date-one
   and recurrent states and continuation rule using the pinned numerical
   contract, with explicit binary64-versus-exact-real interpretation.
2. Establish functional SOURCE/Python identity (or certified interval
   discrepancy) for **all 33 economic rows**, grouped as 8 firm, 9 scalar
   and 16 remaining identities. A permutation alone is not identity.
3. Bound the actual SOURCE center residual and all actual SOURCE
   reduced Jacobian entries over a common 33-dimensional closed box.
4. Apply the rational Neumann/Banach gate to the **same** exact SOURCE
   33-map and constants; construct a true root and prove the regime
   signs/KKT at that point.
5. Separately establish dynamic continuation, global agent optimality,
   feasibility and terminal conditions. None follows from a local root
   automatically.

## 6. Evidence-status rule

- **DEMOSTRADO:** theorems compiled and axiom audited on the specific
  associated commit, with exact economic scope.
- **NUMERICO:** Python Newton, forward AD, finite differences and
  sensitivity experiments; cannot be promoted to exact SOURCE proof.
- **CONDICIONAL EXACT RATIONAL:** statements about the rounded rational
  matrix and if-then SOURCE root thresholds, not about a true SOURCE root.
- **PENDIENTE:** cross-language functional identity, verified SOURCE box,
  true SOURCE root, full infinite competitive equilibrium and any
  permanent endogenous-growth claim.

This note is an auditable handoff, not an assertion of project completion.

# IE project: exact SOURCE economic rows at nonzero remuneration innovation

Date: 2026-11-14. Work branch:
`work/lean-ci-validation-source-33-row-20261114`.
No merge into `main`, no claim of complete dynamic equilibrium.

## Why this gate matters

The previously checked zero-policy SOURCE Jacobian was based on the
benchmark h=0. The candidate Python 34-equation boundary instead occurs at
`h*=0.007616947889328002`, with the SAME inherited state and P0 frozen
finite continuation. **The difference is substantive:** at h* the
intervened primitives `Pv(h)`, not `P`, determine the other economic
equations.

The exact genuine SOURCE first block is

`F_mod(row,z,h) = localBindingResidualWithSlack P I Z0 dateOne recurrent tail (reserveRemunerationSlice 0 h) z row`.

It uses `Pv(h) = initialIntervenedPrimitives P (localScalarParameterIntervention (reserveRemunerationSlice 0 h))`.
For each row other than the L-collateral row (SOURCE index 5),
`F_mod(row,z,h) = localReducedPrefixResidual binding Pv(h) I Z ... row`.
The collateral row is
`S_L = 1-face_L / Gamma_L`, with
`Gamma_L = pledgeability_L * (1-delta) * pi_1 * q_1 * k_{L,1}`.

The reserve-remuneration innovation changes no pledgeability or depreciation
primitive, so the pledge face at fixed coordinates is unchanged. For
`Gamma_L != 0`, SOURCE's raw row is `R_L=face_L-Gamma_L` and

`S_L=-R_L/Gamma_L`.

At a genuine root `R_L(z*,h*)=0`, assuming the required Fréchet
regularity,
`D_z S_L(z*,h*)=-(1/Gamma_L(z*,h*)) D_z R_L(z*,h*)`.

Thus the 33-row Jacobian of the modified source system and the original
binding system under **the same Pv(h*)** have identical rank. This is an
equivalence, not proof of invertibility or existence.

## SOURCE 34th row and KKT

The 34th row is the genuine normalized L financing dual
`nu_L=1/Rloan_0 - betaE * MU_E(cL_1)/MU_E(cL_0)/pi_1`.
It is unchanged at fixed economic coordinates if calculated with
`P` or `Pv(h)`, because intervention changes neither `betaE` nor
`sigmaE`.

The 34 SOURCE boundary equations at arbitrary h and nonzero pledge
face are therefore equivalent to the **original binding-branch
33 SOURCE equations under Pv(h)** plus `nu_L(Pv(h),Z)=0`.
Under an exact root, L's collateral slack is also zero, so its
normalized complementarity is satisfied. This does NOT establish
all H/bank Kuhn–Tucker inequalities, terminality or market clearing
beyond the 33 reduced conditions.

## Exact log normalization and SOURCE/Python row permutation

The Python binding branch uses `log(face_L/Gamma_L)`; the exact
SOURCE identity is

`log(face_L/Gamma_L) = log(1-S_L)`.

With positive nominal face ratio this logarithmic row is zero iff
the normalized SOURCE slack row is zero. The derivative changes sign
relative to the slack row at the root; the original *raw* collateral
row and the Python log row instead have the same positive factor
`1/Gamma_L` at a binding root.

The SOURCE→Python index permutation has six nonidentity moves:

| SOURCE row | Python row |
|---:|---:|
| 1 | 3 |
| 2 | 1 |
| 3 | 4 |
| 4 | 2 |
| 18 | 19 |
| 19 | 18 |

All remaining 27 indices stay fixed. A Lean candidate defines this
bijection and its two-sided inverse. A complementary Python gate
compares the **actual 33 original SOURCE row labels**, this Lean
permutation manifest and the 33 Python residual labels. A verified
row-index contract by itself is NOT functional equality of the
economic equations.

## Critical numeric diagnostic corrected

The earlier report `root_source_shaped_max_abs = 32` was **not**
an economic residual. The diagnostic iterated the dictionary's
integer keys (0..32) instead of its residual values. Direct inspection
of the independent GitHub Actions artifact
`frozen-python-34-boundary-and-rational-sign` ID 14111565390
found the true maximum raw residual:
`3.681499549657019e-13`, in SOURCE row 11 (`nkpcZero`).
This matches the reported normalized maximum in magnitude.
The script now computes
`max(abs(v) for v in src.values())` and rejects both unnormalized
and normalized residuals larger than `1e-8`. It also asserts
consistency with the top-five raw-residual diagnostic.

**This correction changes neither the Python root nor the
previous 34x34 AD/FD rational Neumann bounds.** It corrects only
the raw-residual reporting variable and a false interpretation.

## Proof and audit ledger

New Lean candidates, requiring pinned CI verification on their
individual exact commits before status can be upgraded to DEMOSTRADO:

- `SourceBinding33NonzeroRemunerationCandidate.lean`:
  nonzero-policy primitive and row semantics, 33-row zero set,
  row-5 Fréchet scaling and Jacobian rank transport
- `SourceAugmented34NonzeroRemunerationBoundaryCandidate.lean`:
  genuine 34-equation root iff 33 original binding equations +
  vanishing L funding dual under the SAME intervention, with
  conditional L complementarity
- `SourceBinding33NonzeroPolicyLogRow5Candidate.lean`:
  fixed-coordinate policy invariance, log/slack identities and
  strict-positive-domain zero-set equivalence
- `SourcePython33RowIndexPermutationCandidate.lean`:
  exact SOURCE/Python row-index bijection (index only)

Python regression: `code/irf/audit_source_python_33_index_contract.py`.
The proof files and Python regression were **submitted**, not yet
kernel-certified at the moment this note was created.

The earlier Python boundary and Schur certificate remain
**NUMERICAL / EXACT RATIONAL FOR ROUNDED MATRICES**:
`h*=0.007616947889328002`,
`max|34 residual|=8.767064851866735e-11`,
forward-AD Schur `-4.212023217372646`,
rationalized forward-AD Schur in the negative interval
`[-4.212023236694934,-4.212023198052517]`.
The interval and matrix Neumann bounds are exact only for the
rounded Python matrices, not for the true SOURCE Jacobian.

## Obligations still OPEN

1. Kernel-verify each new exact declaration without `sorryAx`.
2. Prove SOURCE/Python **full functional row identity** given explicit
   matching primitives, inherited state, log chart and exact tail,
   not merely numeric transcription and row ordering.
3. Produce rigorous directed-interval enclosures for all 34x34
   SOURCE derivatives after the verified row permutation,
   scaling and Euler shears. The target entry budget from the
   rounded forward-AD matrix is approximately `7.957357478e-05`.
4. Prove a **genuine SOURCE zero exists** inside the specified
   economic box; Jacobian nonsingularity alone does not imply this.
5. Validate all remaining KKT constraints, the entire continuation
   and long-horizon policy effects. A finite P0 tail does not by
   itself prove the infinite-horizon competitive equilibrium or
   long-run growth.

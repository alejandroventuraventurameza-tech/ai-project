# SOURCE row 21: exact log-Jacobian transport gate

Date: 2026-11-14. Research branch: `work/lean-ci-validation-source-33-row-20261114`.
This checkpoint distinguishes a proved zero-set identity from a still-unproved derivative transport for the genuine SOURCE operator.

## Verified prerequisite

At SHA `0f063e84e216a5464e8deab7c996d604fb42fcbc`,
[Lean candidate audit #43610772601](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43610772601) succeeded.
The exact SOURCE `sourceCanonicalTwoPledgeLog34_eq_zero_iff_original_source_boundary`
was compiled and its axiom audit reported only `propext`, `Classical.choice`,
`Quot.sound`. It is conditional on a positive row-5 face ratio and positive
common-pledge level/valuation. It does *not* establish any root or nonsingularity.

## Derivative identity to formalize

Fix the policy innovation h and inherited state I. On the genuine SOURCE
33-coordinate positive logarithmic chart define

- `J(z) := (localPrefixLogChart Z0 z).stateTwo.commonPledgeValue`;
- `V(z) := sourceDateOneCommonPledgeValuation (sourceReserveSlicePrimitives P h) (localPrefixLogChart Z0 z) dateOne recurrent tail`;
- `r(z) := J(z) - V(z)`, the genuine unnormalized row 21;
- `ell(z) := log (J(z) / V(z))`, the transformed row 21.

Assume `J(z*) = V(z*)`, `V(z*) > 0`, and both real-valued functions
are Frechet differentiable at z*. Positivity and continuity furnish a
neighborhood where the ratio is positive. For every direction d:

`D ell(z*)[d] = DJ(z*)[d] / J(z*) - DV(z*)[d] / V(z*)
                 = (DJ(z*)[d] - DV(z*)[d]) / V(z*)
                 = (1 / V(z*)) Dr(z*)[d]`.

Thus `D ell(z*) = (V(z*))^(-1) • Dr(z*)` as continuous linear maps.
The coefficient is strictly positive. Hence replacing row 21 of a genuine
34x34 source Jacobian with this logarithmic row preserves its rank;
the explicit row-5 scaling is `+1/Gamma_L` only **relative to the raw binding-L level residual**. Relative to the `augmentedBoundaryZeroResidual` normalized slack row, it is **-1**. The reference operator must be named before invoking a rank-transport theorem.

**No off-root equality of derivatives** is claimed; away from the root the
two log-quotient derivative terms have distinct denominators.

## Next Lean proof gate

1. Create a generic positive-root log-quotient Frechet lemma in the pinned
   Mathlib environment, with explicit differentiability/positivity/root hypotheses.
2. Instantiate it with the genuine `sourceDateOneCommonPledgeValuation`
   (not a Python surrogate) and the row-21 identity proved in
   `SourceCanonicalTwoPledgeLogBoundaryCandidate.lean`.
3. Prove equality of all 34 derivative rows: unchanged rows, the previously
   verified row-5 positive scaling, row-21 positive scaling, and the unchanged
   funding-dual scalar component.
4. Obtain an explicit bijectivity biconditional for both 34-output Jacobians.
5. Run exact candidate compilation and `#print axioms`; reject any `sorryAx`.

## Remaining independent economic obligations

Actual regularity of SOURCE primitives, an economic zero with frozen inherited
state, bounded inverse of the **true** 33/34 SOURCE Jacobian, Schur interval
separation, infinite-horizon continuation and KKT/terminal conditions remain open.
A zero-set equivalence or a rank-preserving row change alone does not prove IFT
applicability, competitive equilibrium, IRFs, or long-run growth.

## Verified rank transport and new 34-dimensional source obligations (14 November 2026)

- The abstract 34-output two-row rescaling was certified in Lean at
  SHA `879a995f38c548f7ef1d70f41784bcb3d0363f40`,
  [audit #43621242591](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43621242591),
  with the usual three axioms only.
- The *conditional* Jacobian bijectivity transport was certified at
  SHA `99e681ae2ddf15e08e4de28b9e422e8958f88977`,
  [audit #43622255233](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43622255233),
  again without `sorryAx`. It still **assumes** an exact derivative-row identity.
- Candidate `SourceRow21LogQuotientDirectCandidate.lean` now attempts the
  root log-quotient identity *without assuming a quotient derivative formula*.
  `SourceRow21ActualLogFrechetCandidate.lean` substitutes the genuine SOURCE
  functions at fixed h. `SourceRow21Joint34FrechetCandidate.lean` instead
  differentiates the full pair `(z,h)` and is the correct interface for
  the augmented 34x34 Jacobian. All three were submitted for pinned compilation;
  their statuses remain **PENDING until exact terminal Lean logs are inspected**.

**Mandatory sign and row-order convention before the next 34x34 claim.**
The SOURCE augmented original `augmentedBoundaryZeroResidual` uses the
**normalized slack** in row 5. Thus at a binding root
`D log(face/Gamma) = - D slack`; this factor is `-1`. By contrast,
relative to the unnormalized binding LEVEL residual `raw = face-Gamma`,
`D log(face/Gamma) = + Gamma^(-1) D raw`. In row 21 the original
LEVEL residual is `J2 - V2`, so the positive-root factor is `+V2^(-1)`.
These are mathematically compatible but define two different reference matrices.

Furthermore, `sourceCanonicalPythonOrder34` permutes the first 33 SOURCE
row indices via `sourceRowsInPython33Order`. An honest equality with the
original SOURCE 34-output Jacobian therefore requires the **correct
permutation composed with the correct two nonzero row scalings**, not just
an unqualified diagonal factor. The 34th funding-dual component is unchanged.
No claim of a full SOURCE derivative identity may be promoted until the
permutation, row-5 reference, row-21 joint derivative, and other 31 row
identities are all established for the exact functions and parameters.

## Checkpoint: compiled 34-coordinate rows and pending full operator (2026-11-14)

### DEMOSTRADO / checked in pinned Lean

1. The direct positive-root Frechet log-quotient identity requires NO
   separately assumed quotient derivative formula. Together with the
   genuine SOURCE instantiations at fixed h and joint (z,h), the proof
   appears without `sorryAx` in
   [Lean audit #43625072852](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43625072852),
   SHA `c6ca9c859b3eb7734663be0919c6a2b4f5942bcd`.
2. Joint SOURCE row 5: `D log(faceL/pledgeL) = -D(normalizedSlackL)`
   at a binding root. Joint SOURCE row 21: `D log(J2/V2) =
   V2^(-1) * D(J2-V2)`. Both were compiled and audited in
   [Lean audit #43625217245](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43625217245),
   SHA `43674e2addd8f33a3edd276cecf288f009b92d6e`.
3. The SOURCE-to-Python **index** permutation, two-row rank-preserving
   scaling, and unchanged other SOURCE rows and unchanged final dual
   were checked in
   [Lean audit #43626670403](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43626670403),
   SHA `c447e4321b95448c8af47256a9cd87b6792e4280`.
4. The exact 34 SOURCE derivative-row identities (33 scalar rows
   and one funding-dual row) were checked in
   [Lean audit #43626744848](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43626744848),
   SHA `3638cb0ee1699f51eacea49302fe051c065989e1`.

### PENDIENTE / never promote a failed build

- [Lean audit #43626878574](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43626878574)
  and [#43626917712](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43626917712)
  both FAILED at `SourceAugmented34FullFrechetFactorizationCandidate.lean:139`.
  The row-21 branch had an incorrectly invoked `simp` that
  converted a scaled equality to a disjunction on a zero factor.
  In SHA `2695a401b64e70895567215006874b7ae8bf95f1`,
  the proof was modified to apply `congrArg` to the already
  certified scalar derivative equality before simplification.
  [Lean audit #43631356189](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43631356189)
  must finish SUCCESS and its specific `#print axioms` be inspected
  before certifying full Jacobian factorization or the economic
  invertibility biconditional.
- `SourceAugmented34LogRegularityCandidate.lean` at
  SHA `cbd5fee14d1c3f2c713ccd06fa0ca56b73bb4543`
  is an additional candidate that derives differentiability of the
  SOURCE two-log-collateral vector map from regularity of the
  original map plus J2 and V2. Its
  [pinned workflow](https://github.com/alejandroventuraventurameza-tech/ai-project/actions)
  must be inspected separately. If proved, the later Jacobian
  result can avoid an independent differentiability premise for
  the log-transformed map.
- All exact results concern two **SOURCE-defined** economic maps,
  not an already verified SOURCE/Python floating operator identity.
  Nor do they prove an actual SOURCE root, a verified bounded inverse
  of its 34x34 derivative, the Schur transversality interval,
  nonlinear continuation or long-run growth effects.

## Latest certified checkpoint: full Frechet factorization (2026-11-14)

The row-21 tactic error documented above was corrected in commit
`2695a401b64e70895567215006874b7ae8bf95f1`. Its
[Lean candidate audit #43631356189](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43631356189)
completed **SUCCESS**, and the precise `#print axioms` checks for

- `source34_actual_full_fderiv_factorization_at_root`; and
- `source34_actual_source_jacobian_bijective_iff_log_normalized`

reported **only** `propext`, `Classical.choice`, and `Quot.sound`,
with no `sorryAx`. This promotes the exact conditional identity

`D G(w*) = P · diag(1, ..., -1 [source row 5], ...,
  V2(w*)^-1 [source row 21], ..., 1) · D F(w*)`

and its bijectivity biconditional to **DEMOSTRADO**, *conditional on*
`F` and `G` differentiability, differentiability of the original
L slack, `J2` and `V2` differentiability, `V2(w*)>0`, and a genuine
`F(w*)=0` SOURCE root. The Python-style `P` here only reorders SOURCE
equations; this is not a cross-language numerical identity.

The follow-up `SourceAugmented34LogRegularityCandidate` seeks to
derive `G` differentiability from the original `F` regularity
and `J2,V2` regularity, rather than assuming it. The
`SourceAugmented34MinimalRegularityRankCandidate` additionally derives
the slack-row regularity directly from `F`; its audit is pending.
`SourceAugmented34LogSchurTransportCandidate` is a pending direct
connection to the genuine SOURCE 33+1 Schur-transversality gate,
still conditional on an invertible economic 33-block. None supplies
a numerical existence or inverse certificate.

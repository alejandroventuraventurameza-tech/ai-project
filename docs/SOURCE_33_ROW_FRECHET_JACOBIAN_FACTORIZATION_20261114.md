# SOURCE 33-row Frechet Jacobian factorization — research checkpoint

Date: 2026-11-14 (Lima). Branch: work/lean-ci-validation-otc-20261106.
Parent verified local Lean checkpoint: cc7288458f06b64be823ac23e459f7c33bac811e.

## Exact objects, not surrogate equations

Let E = (Fin 33 -> Real), and let F : E -> E be the actual
`localReducedPrefixLogResidualVector branch P I Z0 dateOne recurrent tail`.
Let G : E -> E be the actual
`sourceNominalPledgeShearedLogResidualVector branch P I Z0 dateOne recurrent tail`.
Define a_H(z), a_L(z) with `sourceDateOneEulerShearCoefficient` composed
with `localPrefixLogChart Z0`. Genuine row indices are Euler H=19,
Euler L=20, and common nominal pledge=21, each in `Fin 33`.

The previously checked source bridge gives, pointwise for all z:

G_19(z) = F_19(z) + a_H(z) F_21(z),
G_20(z) = F_20(z) + a_L(z) F_21(z),
G_j(z)  = F_j(z) for j other than 19 and 20.

The last equality must be explicitly rechecked against the actual
`sourceEulerRowsForward` definition in the full 33-row Lean theorem.

## Mathematical derivative argument

Suppose F is Frechet differentiable at z*, a_H and a_L are Frechet
differentiable at z*, and F_21(z*) = 0. For an arbitrary perturbation h:

DG_19(z*)[h] = DF_19(z*)[h] + a_H(z*) DF_21(z*)[h],
DG_20(z*)[h] = DF_20(z*)[h] + a_L(z*) DF_21(z*)[h],
DG_j(z*)[h]  = DF_j(z*)[h] (other rows).

The omitted product-rule terms are Da_i(z*)[h] F_21(z*),
which vanish under the stated pledge-row zero hypothesis.

Define S(z*) : E ->_Real E by the row operation
(Sv)_19 = v_19 + a_H(z*)v_21,
(Sv)_20 = v_20 + a_L(z*)v_21,
(Sv)_j = v_j otherwise.
Then **DG(z*) = S(z*) o DF(z*)** as bounded real linear maps.
The inverse row operation subtracts the two multiples of row 21,
so S is invertible for arbitrary finite coefficients. Hence
DG(z*) invertible iff DF(z*) invertible; the row shear itself neither
creates nor eliminates Jacobian singularity. In matrix form det S = 1.

Crucial logical distinction: this is a *conditional equivalence of
invertibility*, NOT a proof that the economic Jacobian is invertible.
No implicit function theorem, local uniqueness, competitive equilibrium,
or long-run growth result follows from this step alone.

## Lean implementation gate

1. Add a new candidate module importing
   `SourceEulerLogEconomicFrechetCandidate`.
2. Prove the unaffected-row identity for all `j != 19,20` by unfolding
   the **actual** SOURCE row enumeration and `sourceEulerRowsForward`.
3. Assemble componentwise `HasFDerivAt` into a vector `HasFDerivAt`
   using the finite `Pi` product rule, preserving explicit hypotheses.
4. Define the SOURCE row shear as a continuous linear equivalence,
   with inverse subtracting from rows 19 and 20. Check the composition
   `DG = S.comp DF` at a point where `F_21 = 0`.
5. Audit `#print axioms` and compile the exact module in CI on this
   branch, with a recorded SHA and full build result.
6. Only afterwards attempt a source-strength, interval-audited bound
   on the inverse of DF, with verified parameter region and dimensions.

## Verified checkpoint (14 November 2026)

**DEMOSTRADO EN LEAN, CON HIPOTESIS EXPLICITAS:** commit
`40e7ed41d9eb0fdc3a54c50028000d057693f284` and
[GitHub Actions candidate audit #43567568344](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43567568344)
successfully compiled:

- `sourceEulerRowsFrechetForward_apply`: lifting the SOURCE scalar row
  map to the continuous-linear derivative rows;
- `sourceNominalPledgeShearedLog_all_rows_hasFDerivAt`: derivative of
  every actual SOURCE row at a common-pledge zero, conditional on
  differentiability of all 33 original economic rows and both
  state-dependent shear coefficients;
- `sourceEulerRowsFrechetForward_bijective_iff`: equivalence of
  bijectivity of the sheared and original derivative-row operators;
- `sourceEconomicLogJacobian_bijective_iff_at_pledge_zero`: economic
  source-level instantiation in the genuine positive log chart.

The exact compiled logs for the two last modules report 2142 and 2143
build jobs respectively and for each of the four cited declarations
`#print axioms` returned precisely
`[propext, Classical.choice, Quot.sound]`. No `sorryAx` was reported
for these declarations.

**Scope:** the proof is componentwise across the genuine 33 SOURCE
rows, and the assembled map from log-coordinate directions to SOURCE
row derivatives has a bijectivity biconditional. This is the
`DG=S*DF` property at the level of all directions/rows. A separate
vector-valued `fderiv` lemma and an explicit continuous-linear
equivalence of the output row space could improve the interface but
are not necessary to state the verified bijectivity biconditional.

**NOT DEMONSTRATED:** differentiability of the economic primitives
from their definitions (currently premises), the existence of a
SOURCE common-pledge root, nonsingularity of the original 33x33 SOURCE
Jacobian, semantic equality with a numerically evaluated Python
surrogate, invertibility of the distinct 34x34 augmented
funding-dual system, a full dynamic competitive equilibrium or a
long-run growth theorem. The earlier algebraic derivation is now
formally supported *only to the conditional extent above*.

The subsequent 34-by-34 boundary gate is tracked separately in
`docs/SOURCE_AUGMENTED_34_JACOBIAN_SCHUR_GATE_20261114.md`.

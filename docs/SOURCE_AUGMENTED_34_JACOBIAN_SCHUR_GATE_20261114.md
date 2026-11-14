# SOURCE augmented 34-by-34 regularity gate: exact block structure and Schur complement

Date: 2026-11-14 (America/Lima).
Branch: work/lean-ci-validation-otc-20261106.
Origin: `lean/candidates/Ventura26LiquidityAllocation/LocalScalarAugmented34SourceCandidate.lean`.

## 1. SOURCE object, not a Python surrogate

The genuine economic SOURCE augmented boundary operator is

`augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail z h`,

with domain `(Fin 33 -> Real) x Real` and codomain
`(Fin 33 -> Real) x Real`. Its value is

    R(z,h) = (B(z,h), lambda_L(z)),

where the first 33 entries are `localBindingResidualWithSlack`,
evaluated at `reserveRemunerationSlice 0 h`, and the final entry is
`localNormalizedCollateralDualL P (localPrefixLogChart Z0 z)`.

In particular the source theorem
`augmentedBoundaryZeroResidual_dual_fixed_state`
shows that lambda_L(z) does not depend **directly** on h when z is held
fixed. Its *equilibrium* total derivative may be nonzero.

This 34-equation object is NOT automatically the 33-equation SOURCE
Euler-sheared map treated by
`sourceEconomicLogJacobian_bijective_iff_at_pledge_zero`.
A separate exact bridge between their respective residuals,
normalizations, regime assumptions and coordinates would be required.

## 2. Block derivative at a genuine SOURCE reference point

Provided the exact SOURCE derivatives exist at (z*,h*), set

    A = D_z B(z*,h*)                  (33 x 33),
    b = D_h B(z*,h*)                  (33 x 1),
    c' = D_z lambda_L(z*)            (1 x 33).

The 34-by-34 derivative is

         [ A   b ]
    J =  [       ] .
         [ c'  0 ]

The zero in the bottom-right entry is structural (the SOURCE dual has
no direct h dependence); differentiation of that literal independence
is still to be assembled in Lean with the required smoothness.

## 3. Schur-complement gate, only IF A is invertible

Suppose A is invertible. Define the scalar

    s = - c' A^{-1} b.

Then the determinant factorization reads

    det J = det A * s = -det A * (c' A^{-1} b).

Therefore, under the *explicit* A-invertibility hypothesis,

    J is invertible  <=>  c' A^{-1} b != 0.

The scalar response along the 33-row manifold B(z(h),h)=0 is

    dz/dh = -A^{-1} b,
    d(lambda_L(z(h)))/dh = -c' A^{-1} b = s.

Thus s != 0 is the local **transversality of the funding-dual
boundary** along an internally equilibrated 33-equation continuation.
This is stronger than, and distinct from, the Euler row-shear
invertibility equivalence. No sign of s is implied.

Important nuance: if A is singular, the full 34x34 J might still be
invertible. This particular Schur route is a sufficient certificate
*strategy* and a biconditional conditional on A invertible, not a
necessary prerequisite for every possible full-rank J.

## 3a. Link to the actual reduced policy multiplier in EconomicModel

`EconomicModel.lean` already defines
`localScalarReducedMap P Z0 solutionLog y` as
`localNormalizedCollateralDualL P (localPrefixLogChart Z0 (solutionLog y))`.
The five-dimensional intervention coordinate
`localScalarReserveRateDirection` selects the remuneration innovation,
while `LocalScalarImplicitReduction` contains the **assumed** strict
inequality

    (fderiv Real (localScalarReducedMap ...) 0)
      localScalarReserveRateDirection < 0.

Provided the exact augmented SOURCE 33-row equation `B(z,h)=0`
coincides with the appropriate slice of the five-dimensional reduced
system and the verified local solution map is differentiable, the chain
rule together with the implicit derivative yields

    D_h M(0) = c'(-A^{-1}b) = s.

Therefore a *verified* strict negativity of `D_h M(0)` would imply
`s < 0` and certify the nonzero Schur gate when A is already certified
invertible. The existing `LocalScalarImplicitReduction` includes this
strict derivative sign only as part of a PROP/PREMISE, not as an
independently numerically proven theorem. Do not report it as achieved.

The exact identification of the policy slice, normalization,
economic derivative and inverse is the next SOURCE bridge to construct.
This equivalence is independent of the Euler-shear preservation of
33-row invertibility; the two statements have different logical roles.

## 3b. Exact sparse funding-dual gradient: four original SOURCE coordinates

The literal source definition is

    nu_L = 1/R^L_0
           - beta_E * (c_L1^(-sigma_E)/c_L0^(-sigma_E))/Pi_1.

In the SOURCE positive log chart, set

    R(z) = Z0.controlsZero.loanRate * exp(z_15),
    C0(z) = Z0.controlsZero.consumptionL * exp(z_8),
    C1(z) = Z0.controlsOne.consumptionL * exp(z_24),
    Pi(z) = Z0.controlsOne.inflation * exp(z_28),
    G(z) = beta_E * C1(z)^(-sigma_E) / C0(z)^(-sigma_E) / Pi(z).

Then nu_L(z) = 1/R(z) - G(z). Under strict positivity
of those four economic levels, its partial derivatives are:

    partial_8 nu_L  = -sigma_E * G(z),
    partial_15 nu_L = -1 / R(z),
    partial_24 nu_L = +sigma_E * G(z),
    partial_28 nu_L = +G(z),
    partial_j nu_L  = 0 for all other 29 SOURCE log indices j.

No sign of G or sigma_E is inferred here without explicit primitive
restrictions. The four coordinate indices are from the literal SOURCE
`localPrefixCoordinatesVector` definition (not the distinct Python
residual-row permutation). The equalities are mathematical
differentiation identities; their explicit coefficients are not yet
presented as kernel-certified derivative formulas.

The zero-coordinate sparsity gives a practical **SOURCE-focused
interval certificate**: writing w = A^{-1}b for the actual 33-row
Jacobian system, the exact Schur scalar is

    s = -c' w
      = sigma_E * G * w_8 + (1/R) * w_15
        - sigma_E * G * w_24 - G * w_28.

Only four components of the rigorously enclosed *solution* w are
needed in the final scalar contraction. This does **not** mean
that the other 29 variables or residuals can be omitted from the
33x33 solve: all equations contribute indirectly to w through A.

SOURCE Lean proof milestones added for review:
`SourceFundingDualFourLogCoordinatesCandidate.lean` and
`SourceFundingDualPositiveLogRegularityCandidate.lean`; do not
classify them as verified until the exact CI run and axiom audit
are recorded.

## 3b2. Primal/adjoint certification strategy

At the same SOURCE point and with the same exact bounded 33x33
economic derivative, there are two algebraically equivalent ways
to enclose the Schur scalar:

    A w = b,       s = -c' w  (primal response solve),
    A' y = c,      s = -y' b  (adjoint response solve).

For each route, directed interval arithmetic must enclose the
**same true** A,b,c with explicit log/level scaling. Compare the two
independently enclosed intervals for s and verify that at least one
rigorously excludes zero (the intersection may tighten an enclosure
only when both contain the same true scalar).

The sparse exact SOURCE c row needs only coordinates 8,15,24,28,
but the 33-by-33 equations in A still couple all coordinates.
A 16-by-16 recurrent hand stencil or a synthetic inverse regression
is not an admissible substitute for either verified SOURCE solve.

## 3c. A genuine regularity blocker in the 33-row SOURCE subsystem

The source declares

    abbrev LocalPrefixContinuationRule :=
      LocalPrefixStateSix -> LocalPrefixControlsTen

and the date-one economic data explicitly include

    nextControls := tail Z.stateTwo.

Consequently, the original 33-row SOURCE derivative is NOT automatically
differentiable for an arbitrary continuation rule: the type of `tail`
places no continuity, differentiability, or fixed-regime restriction on
that function. Merely proving positive coordinates or smoothness of
finite algebraic primitives does not supply that missing regularity.

To discharge `hB : HasFDerivAt sourceAugmented34Rows dB (z*,h*)`,
the proof must identify a genuine smooth continuation rule on a
neighborhood of the state-two coordinates, verify the required
`D(tail)` including dimensions and log/level scaling, and ensure
denominators and nonsmooth OTC/collateral regime switches do not
invalidate differentiation. The SOURCE normalized L funding-dual is
special: its literal formula is independent of `tail`, which is
why its differentiability can be attacked separately by positive-log
calculus.

Even if `hB` is eventually established, a root, the 33x33 inverse
and its interval norm, and the nonzero 34th-row Schur scalar must be
independently verified. This regularity firewall prevents any claim
that a vector-level derivative identity plus a synthetic 16x16
transition stability check already proves the nonlinear equilibrium.

## 4. Numerically auditable SOURCE certificate

An eventual rigorous inverse check must evaluate and enclose the
**SOURCE** Jacobian entries and their coordinate scales, not the
separate 16x16 recurrent hand stencil. Given a rational candidate
preconditioner C and exact interval enclosure [A] containing every
true A_ij, require

    q = sup_{M in [A]} ||Id - C M||_infty < 1.

Then every real matrix M in that box is invertible, and

    ||M^{-1}||_infty <= ||C||_infty / (1-q).

For the 34th row and 34th coordinate, additionally bound the interval
for `s=-c' A^{-1}b` away from zero. One may instead certify the full
34x34 inverse directly, provided the input is the exact SOURCE
derivative enclosure with independently verified error bounds.

The existing pinned 80-digit and 48-step certificates concern the
HAND recurrent linear operator and a pinned rational transition.
The 33-row Lean/Python permutation audit validates indices only, not
semantic or derivative equality. Neither result alone is the SOURCE
34x34 inverse certificate.

## 5. Proof obligations and statuses

- DEMOSTRADO Lean (SHA 40e7ed41): 33 genuine SOURCE log rows' Frechet
  shears and conditional biconditional of Jacobian bijectivity, given
  differentiability and common pledge zero; CI #43567568344.
- DEMOSTRADO Lean (pre-existing SOURCE): fixed-z independence of the
  34th funding-dual residual from the remuneration innovation.
- DEMOSTRADO EN LEAN (ABSTRACTO, CON A INVERTIBLE): the
  `sourceAugmentedSchurBlock_bijective_iff` theorem establishes the
  33+1 Schur transversality equivalence. Exact verification SHA
  `ab6d20087ef08b550fea4f0d2fde11c1f8b1e045`,
  [CI #43569087322](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43569087322),
  2168 build jobs, `#print axioms` =
  `[propext, Classical.choice, Quot.sound]`. This is an abstract
  linear-algebra theorem, NOT a SOURCE derivative/rank certificate.
- PENDIENTE: actual SOURCE C1 regularity; source-sensitive interval
  enclosure of A,b,c; rigorous inverse defect bound; nonzero interval
  for the Schur scalar; exact relation between original 33 sheared
  map and 33 modified binding-prefix rows in the 34 experiment.
- PENDIENTE: a full local IFT theorem (also parameter domain and
  branch selection), the nonlinear infinite continuation / terminal
  conditions, structural policy shock identification and verified
  long-run growth implications.

## 6. Economic caution

The tested policy dimension in this augmented operator is remuneration
of reserves. The code states reserve-quantity innovation, reserve
requirement and corridor width remain zero along the specified slice.
Results must not be labeled generically as a shock to encaje, policy
rate or corridor, nor extrapolated to long-run growth without the
corresponding full-equilibrium derivation.

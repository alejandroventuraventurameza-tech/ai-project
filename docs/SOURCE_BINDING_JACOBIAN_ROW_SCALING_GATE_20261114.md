# SOURCE binding-L collateral row scaling: bridge to the modified 33x33 Jacobian

Date: 2026-11-14 (Lima). Working branch: work/lean-ci-validation-otc-20261106.

## Exact SOURCE definitions and equation label

In `EconomicModel.lean` the genuine binding branch of the 33-row
SOURCE residual contains at equation index 5
(`LocalPrefixEquation.firmRegimeZeroL`) the nominal collateral face
residual

    R_L(P,Z) = Z.stateOne.firmFaceL - Gamma_L(P,Z),

    Gamma_L(P,Z) =
      P.pledgeability FirmType.L
        * (1 - P.depreciation)
        * Z.controlsOne.inflation
        * Z.controlsOne.capitalPrice
        * Z.stateOne.capitalL.

The distinct 33-row modified binding-prefix operator
`localBindingResidualWithSlack` replaces ONLY row 5 by the normalized
L slack minus the scalar slack intervention s:

    S_L(P,Z,s) = 1 - Z.stateOne.firmFaceL / Gamma_L(P,Z) - s.

At s=0 and Gamma_L != 0, exact algebra gives

    S_L(P,Z,0) = -R_L(P,Z) / Gamma_L(P,Z).

This is an identity of the *literal SOURCE economic expressions*, not
a generic or Python residual.

## Derivative identity at a SOURCE binding root

At a point z* with `R_L(P,Z(z*))=0`, provided Gamma_L(z*) != 0 and
the genuine SOURCE chart composite R_L, Gamma_L are differentiable:

    D_z S_L(z*,0) = -(1 / Gamma_L(z*)) D_z R_L(z*).

The derivative of the coefficient `-1/Gamma_L` multiplies
`R_L(z*)=0`, hence vanishes. This does not hold as a simple row
scaling at arbitrary off-root points; the full product rule must
be used there.

Let F_binding be the true original 33-residual SOURCE vector at
fixed policy y=0 and B the true modified binding-prefix SOURCE
33-vector at s=0, h=0. After checking that the zero intervention
preserves the exact SOURCE primitives and that the *other 32 rows*
coincide under identical coordinates and continuation, one gets:

    A := D_z B(z*,0) = D * J_binding,
    J_binding := D_z F_binding(z*),

where D is the 33x33 diagonal identity except at equation row 5,

    D[5,5] = -1/Gamma_L(z*).

If Gamma_L(z*) != 0, D is invertible, so A is invertible iff
J_binding is invertible. Importantly, this makes the **modified
33x33 economic block** logically different from the earlier
Euler-row shear: the row-5 normalization is a *different*
transformation at a collateral root.

If J_binding^{-1} and Gamma_L are certified from the exact SOURCE
economy, then

    A^{-1} = J_binding^{-1} D^{-1},
    ||A^{-1}||_infty <= ||J_binding^{-1}||_infty
                         * max(1, abs(Gamma_L(z*))).

The bound follows from operator submultiplicativity. The unit, norm
and coordinate scaling used by a future numerical enclosure must
match this exact representation. A certificate for the *slack branch*
of F, or for the 16x16 hand recurrent stencil, does not automatically
certify the *binding branch* Jacobian J_binding.

## Lean proof ledger

Candidate module:
`lean/candidates/Ventura26LiquidityAllocation/SourceBindingSlackRowScalingCandidate.lean`
(commit `0aca77066991b8727d47b701a992a3e14ffd513a`) proposes:

- definitional SOURCE raw L binding row;
- definitional SOURCE normalized L slack;
- exact algebraic quotient identity under nonzero pledge face;
- zero set equivalence of the two SOURCE collateral residuals.

**Status: PENDIENTE of exact SHA CI compile and axiom audit** as of
writing; the displayed derivative and full 33x33 diagonal transport
are mathematical derivations, NOT kernel-verified SOURCE theorems.

Independent future proof obligations:

1. Verify at y=0, `initialIntervenedPrimitives P v_0 = P`
   extensionally, not only a few changed fields.
2. Verify the other 32 row identities and the index-5 row
   replacement on the original SOURCE positive log chart.
3. Establish the required differentiability of P, Z(z), and the
   unrestricted continuation `tail` for the original SOURCE binding
   system (the latter has no regularity from its declared function type).
4. Establish a SOURCE binding reference root, including
   `R_L(z*)=0`, and Gamma_L(z*) != 0.
5. Apply exact SOURCE Fréchet product calculus to derive
   `D_z B = D * D_z F_binding` at the root.
6. Certify `J_binding^{-1}` by directed interval arithmetic
   with exact SOURCE semantics and a defensible inverse defect bound.
7. Independently certify the Schur scalar `-c^T A^{-1}b != 0`
   for the source 34x34 boundary operator.

Neither this row normalization nor the Schur algebra establishes
existence/uniqueness of full dynamic competitive equilibrium,
infinite-horizon continuation or long-run growth effects.

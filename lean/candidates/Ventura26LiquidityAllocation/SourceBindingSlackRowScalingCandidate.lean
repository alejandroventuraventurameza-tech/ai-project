import Ventura26LiquidityAllocation.LocalScalarAugmented34SourceCandidate

/-!
# Actual SOURCE binding L-regime row versus normalized collateral slack

The original 33-equation SOURCE binding residual for firm L is a raw
nominal-face minus pledge-value residual. The 33+1 augmented boundary
replaces precisely that row with normalized collateral slack.

This module establishes their exact algebraic relationship on the
genuine SOURCE economic coordinates and under the necessary nonzero
pledge denominator. This is not a numerical Jacobian certificate.
-/

namespace Ventura26LiquidityAllocation

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The literal SOURCE date-zero nominal collateral face that
normalizes firm L's binding collateral condition. -/
noncomputable def sourceBindingLPledgeFace
    (P : Primitives S) (Z : LocalPrefixCoordinates) : ℝ :=
  P.pledgeability FirmType.L * (1 - P.depreciation) *
    Z.controlsOne.inflation * Z.controlsOne.capitalPrice *
    Z.stateOne.capitalL

/-- Exact SOURCE equation for the unnormalized firm-L binding
regime row at date zero; no approximation and no Python surrogate. -/
theorem sourceBindingRawL_eq_face_minus_pledge
    (P : Primitives S) (I : InheritedState)
    (Z : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule) :
    localReducedPrefixResidual LocalPrefixBranch.binding P I Z
      dateOne recurrent tail LocalPrefixEquation.firmRegimeZeroL =
    Z.stateOne.firmFaceL - sourceBindingLPledgeFace P Z := by
  rfl

#print axioms sourceBindingRawL_eq_face_minus_pledge

/-- The actual normalized SOURCE L collateral slack has exactly
the same pledge value as its denominator. -/
theorem sourceBindingNormalizedSlackL_eq_one_minus_pledge_ratio
    (P : Primitives S) (Z : LocalPrefixCoordinates) :
    localNormalizedSlackL P Z =
    1 - Z.stateOne.firmFaceL / sourceBindingLPledgeFace P Z := by
  rfl

#print axioms sourceBindingNormalizedSlackL_eq_one_minus_pledge_ratio

/-- Away from zero pledge value, the normalized L slack is the
NEGATIVE raw binding SOURCE row divided by the very same true
pledge face. Consequently, a positive or negative nonzero scaling
cannot create or destroy zeroes of the economic collateral row. -/
theorem sourceBindingNormalizedSlackL_eq_neg_raw_div_pledge
    (P : Primitives S) (I : InheritedState)
    (Z : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (hK : sourceBindingLPledgeFace P Z ≠ 0) :
    localNormalizedSlackL P Z =
      -(localReducedPrefixResidual LocalPrefixBranch.binding P I Z
        dateOne recurrent tail LocalPrefixEquation.firmRegimeZeroL) /
        sourceBindingLPledgeFace P Z := by
  rw [sourceBindingNormalizedSlackL_eq_one_minus_pledge_ratio,
      sourceBindingRawL_eq_face_minus_pledge]
  field_simp [hK]
  ring

#print axioms sourceBindingNormalizedSlackL_eq_neg_raw_div_pledge

/-- Both exact SOURCE binding-L collateral equations have
the same zero set when the pledge denominator is nonzero. -/
theorem sourceBindingNormalizedSlackL_zero_iff_rawL_zero
    (P : Primitives S) (I : InheritedState)
    (Z : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (hK : sourceBindingLPledgeFace P Z ≠ 0) :
    localNormalizedSlackL P Z = 0 ↔
      localReducedPrefixResidual LocalPrefixBranch.binding P I Z
        dateOne recurrent tail LocalPrefixEquation.firmRegimeZeroL = 0 := by
  rw [sourceBindingNormalizedSlackL_eq_neg_raw_div_pledge
    P I Z dateOne recurrent tail hK]
  simp [hK]

#print axioms sourceBindingNormalizedSlackL_zero_iff_rawL_zero

end Ventura26LiquidityAllocation

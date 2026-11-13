import Ventura26LiquidityAllocation.SourceEulerRowLinearEquivalenceCandidate

/-!
# Fully explicit SOURCE 33-row pointwise rowmap identity

At every SOURCE coordinate Z (not just at roots), and for every SOURCE
branch, inherited state, and continuation, the genuinely economic
date-one nominal pledge Euler transformation is EXACTLY the real-linear
33-row shear acting on the original reduced SOURCE residual vector.
The coefficients are computed from actual EconomicModel.lean fields.

The inverse is given pointwise, not approximated numerically. This
proves nothing about SOURCE/Python functional equality, Frechet
differentiability of SOURCE, or invertibility of its 33x33 Jacobian.
-/

namespace Ventura26LiquidityAllocation

/-- State-dependent SOURCE coefficient for a date-one firm Euler. -/
noncomputable def sourceDateOneEulerShearCoefficient
    (P : Primitives LocalBridgePhase)
    (Z : LocalPrefixCoordinates)
    (dateOne recurrent : LocalBridgePhase)
    (tail : LocalPrefixContinuationRule)
    (i : FirmType) : ℝ :=
  let d := localPrefixDateOneData P Z dateOne recurrent tail
  P.pledgeability i *
    (localPrefixEntrepreneurSDF P d i / d.nextControls.inflation -
      1 / d.controls.loanRate)

/-- An exact source-definition bridge for H, with no root assumption. -/
theorem sourceDateOneEulerH_sheared_eq
    (branch : LocalPrefixBranch)
    (P : Primitives LocalBridgePhase) (I : InheritedState)
    (Z : LocalPrefixCoordinates)
    (dateOne recurrent : LocalBridgePhase)
    (tail : LocalPrefixContinuationRule) :
    sourceNominalPledgeShearedResidual branch P I Z dateOne recurrent tail
      .firmCapitalEulerOneH =
    localReducedPrefixResidual branch P I Z dateOne recurrent tail
      .firmCapitalEulerOneH +
    sourceDateOneEulerShearCoefficient P Z dateOne recurrent tail .H *
      localReducedPrefixResidual branch P I Z dateOne recurrent tail
        .commonPledgeOne := by
  rw [sourceNominalPledgeShearedResidual,
    sourceFirmEuler_dateOne_nominalPledge_shear,
    sourceFirmEuler_dateOne_H_binding]
  rfl

#print axioms sourceDateOneEulerH_sheared_eq

theorem sourceDateOneEulerL_sheared_eq
    (branch : LocalPrefixBranch)
    (P : Primitives LocalBridgePhase) (I : InheritedState)
    (Z : LocalPrefixCoordinates)
    (dateOne recurrent : LocalBridgePhase)
    (tail : LocalPrefixContinuationRule) :
    sourceNominalPledgeShearedResidual branch P I Z dateOne recurrent tail
      .firmCapitalEulerOneL =
    localReducedPrefixResidual branch P I Z dateOne recurrent tail
      .firmCapitalEulerOneL +
    sourceDateOneEulerShearCoefficient P Z dateOne recurrent tail .L *
      localReducedPrefixResidual branch P I Z dateOne recurrent tail
        .commonPledgeOne := by
  rw [sourceNominalPledgeShearedResidual,
    sourceFirmEuler_dateOne_nominalPledge_shear,
    sourceFirmEuler_dateOne_L_binding]
  rfl

#print axioms sourceDateOneEulerL_sheared_eq

/-- Economic SOURCE double shear equals the abstract 33-row linear
transform, for ALL coordinates and both branches, not only at a root. -/
theorem sourceNominalPledgeShearedResidual_eq_linear_rowmap
    (branch : LocalPrefixBranch)
    (P : Primitives LocalBridgePhase) (I : InheritedState)
    (Z : LocalPrefixCoordinates)
    (dateOne recurrent : LocalBridgePhase)
    (tail : LocalPrefixContinuationRule) :
    sourceNominalPledgeShearedResidual branch P I Z dateOne recurrent tail =
    sourceEulerRowsForward
      (sourceDateOneEulerShearCoefficient P Z dateOne recurrent tail .H)
      (sourceDateOneEulerShearCoefficient P Z dateOne recurrent tail .L)
      (localReducedPrefixResidual branch P I Z dateOne recurrent tail) := by
  funext row
  cases row <;> simp only
    [sourceNominalPledgeShearedResidual, sourceEulerRowsForward]
  · exact sourceDateOneEulerH_sheared_eq
      branch P I Z dateOne recurrent tail
  · exact sourceDateOneEulerL_sheared_eq
      branch P I Z dateOne recurrent tail

#print axioms sourceNominalPledgeShearedResidual_eq_linear_rowmap

/-- Hence the actual SOURCE residual vector can be recovered EXACTLY
from the economically sheared one at every Z, using the state-dependent
coefficient evaluated at the same Z. -/
theorem sourceReducedPrefixResidual_eq_inverse_rowmap
    (branch : LocalPrefixBranch)
    (P : Primitives LocalBridgePhase) (I : InheritedState)
    (Z : LocalPrefixCoordinates)
    (dateOne recurrent : LocalBridgePhase)
    (tail : LocalPrefixContinuationRule) :
    localReducedPrefixResidual branch P I Z dateOne recurrent tail =
    sourceEulerRowsBackward
      (sourceDateOneEulerShearCoefficient P Z dateOne recurrent tail .H)
      (sourceDateOneEulerShearCoefficient P Z dateOne recurrent tail .L)
      (sourceNominalPledgeShearedResidual branch P I Z dateOne recurrent tail) := by
  rw [sourceNominalPledgeShearedResidual_eq_linear_rowmap]
  exact (sourceEulerRows_backward_forward
    (sourceDateOneEulerShearCoefficient P Z dateOne recurrent tail .H)
    (sourceDateOneEulerShearCoefficient P Z dateOne recurrent tail .L)
    (localReducedPrefixResidual branch P I Z dateOne recurrent tail)).symm

#print axioms sourceReducedPrefixResidual_eq_inverse_rowmap

end Ventura26LiquidityAllocation

import Ventura26LiquidityAllocation.SourceFirmEulerCommonPledgeShearCandidate

/-!
# Exact three-equation SOURCE date-one zero-set equivalence

In genuine SOURCE, the date-one H and L Euler residuals and the
common nominal pledge residual form a three-equation block.
Replacing BOTH Euler rows by their nominal-common-pledge versions
preserves the entire zero set, conditional on NOTHING beyond
equality to zero of the explicitly retained pledge row.

The primitive economic SOURCE functions and an arbitrary actual
continuation tail are used directly.  No Python cartography,
numerical P0, global KKT, or Jacobian invertibility follows.
-/

namespace Ventura26LiquidityAllocation

/-- Date-one H SOURCE Euler equals its nominal-pledge counterpart
whenever the original SOURCE common pledge row clears. -/
theorem sourceFirmEuler_dateOne_H_nominal_eq_of_pledge_zero
    (branch : LocalPrefixBranch)
    (P : Primitives LocalBridgePhase) (I : InheritedState)
    (Z : LocalPrefixCoordinates)
    (dateOne recurrent : LocalBridgePhase)
    (tail : LocalPrefixContinuationRule)
    (hp : localReducedPrefixResidual branch P I Z dateOne recurrent tail
      .commonPledgeOne = 0) :
    localReducedPrefixResidual branch P I Z dateOne recurrent tail
      .firmCapitalEulerOneH =
    sourceFirmEulerNominalPledge P
      (localPrefixDateOneData P Z dateOne recurrent tail) .H
      Z.stateTwo.commonPledgeValue := by
  rw [sourceFirmEuler_dateOne_H_binding]
  exact (sourceFirmEuler_dateOne_equivalent_on_pledge_zero
    branch P I Z dateOne recurrent tail .H hp).symm

#print axioms sourceFirmEuler_dateOne_H_nominal_eq_of_pledge_zero

/-- Analogous genuine SOURCE row identity for firm L. -/
theorem sourceFirmEuler_dateOne_L_nominal_eq_of_pledge_zero
    (branch : LocalPrefixBranch)
    (P : Primitives LocalBridgePhase) (I : InheritedState)
    (Z : LocalPrefixCoordinates)
    (dateOne recurrent : LocalBridgePhase)
    (tail : LocalPrefixContinuationRule)
    (hp : localReducedPrefixResidual branch P I Z dateOne recurrent tail
      .commonPledgeOne = 0) :
    localReducedPrefixResidual branch P I Z dateOne recurrent tail
      .firmCapitalEulerOneL =
    sourceFirmEulerNominalPledge P
      (localPrefixDateOneData P Z dateOne recurrent tail) .L
      Z.stateTwo.commonPledgeValue := by
  rw [sourceFirmEuler_dateOne_L_binding]
  exact (sourceFirmEuler_dateOne_equivalent_on_pledge_zero
    branch P I Z dateOne recurrent tail .L hp).symm

#print axioms sourceFirmEuler_dateOne_L_nominal_eq_of_pledge_zero

/-- The full three-row SOURCE system has the SAME simultaneous zero set
after the state-dependent double Euler shear.  The common pledge row
is not deleted.  This is stronger than comparing a single row at a
calibrated root, but weaker than the 33-row SOURCE/Python identity. -/
theorem sourceFirmEuler_dateOne_threeRow_zeroSet_iff
    (branch : LocalPrefixBranch)
    (P : Primitives LocalBridgePhase) (I : InheritedState)
    (Z : LocalPrefixCoordinates)
    (dateOne recurrent : LocalBridgePhase)
    (tail : LocalPrefixContinuationRule) :
    (localReducedPrefixResidual branch P I Z dateOne recurrent tail
       .commonPledgeOne = 0 ∧
     localReducedPrefixResidual branch P I Z dateOne recurrent tail
       .firmCapitalEulerOneH = 0 ∧
     localReducedPrefixResidual branch P I Z dateOne recurrent tail
       .firmCapitalEulerOneL = 0) ↔
    (localReducedPrefixResidual branch P I Z dateOne recurrent tail
       .commonPledgeOne = 0 ∧
     sourceFirmEulerNominalPledge P
       (localPrefixDateOneData P Z dateOne recurrent tail) .H
       Z.stateTwo.commonPledgeValue = 0 ∧
     sourceFirmEulerNominalPledge P
       (localPrefixDateOneData P Z dateOne recurrent tail) .L
       Z.stateTwo.commonPledgeValue = 0) := by
  constructor
  · rintro ⟨hp, hH, hL⟩
    have hHEq := sourceFirmEuler_dateOne_H_nominal_eq_of_pledge_zero
      branch P I Z dateOne recurrent tail hp
    have hLEq := sourceFirmEuler_dateOne_L_nominal_eq_of_pledge_zero
      branch P I Z dateOne recurrent tail hp
    exact ⟨hp, hHEq ▸ hH, hLEq ▸ hL⟩
  · rintro ⟨hp, hH, hL⟩
    have hHEq := sourceFirmEuler_dateOne_H_nominal_eq_of_pledge_zero
      branch P I Z dateOne recurrent tail hp
    have hLEq := sourceFirmEuler_dateOne_L_nominal_eq_of_pledge_zero
      branch P I Z dateOne recurrent tail hp
    exact ⟨hp, hHEq.symm ▸ hH, hLEq.symm ▸ hL⟩

#print axioms sourceFirmEuler_dateOne_threeRow_zeroSet_iff

end Ventura26LiquidityAllocation

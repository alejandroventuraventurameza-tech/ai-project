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


/-- Full 33-row SOURCE operator after replacing the two date-one Euler rows
by their nominal common-pledge-coordinate versions, with all other rows
(including the actual pledge row) literally unchanged. -/
noncomputable def sourceNominalPledgeShearedResidual
    (branch : LocalPrefixBranch)
    (P : Primitives LocalBridgePhase) (I : InheritedState)
    (Z : LocalPrefixCoordinates)
    (dateOne recurrent : LocalBridgePhase)
    (tail : LocalPrefixContinuationRule)
    (equation : LocalPrefixEquation) : ℝ :=
  match equation with
  | .firmCapitalEulerOneH =>
      sourceFirmEulerNominalPledge P
        (localPrefixDateOneData P Z dateOne recurrent tail) .H
        Z.stateTwo.commonPledgeValue
  | .firmCapitalEulerOneL =>
      sourceFirmEulerNominalPledge P
        (localPrefixDateOneData P Z dateOne recurrent tail) .L
        Z.stateTwo.commonPledgeValue
  | _ => localReducedPrefixResidual branch P I Z dateOne recurrent tail equation

/-- Given genuine SOURCE pledge clearing, all 33 original and sheared
residuals agree pointwise. -/
theorem sourceNominalPledgeShearedResidual_eq_of_pledge_zero
    (branch : LocalPrefixBranch)
    (P : Primitives LocalBridgePhase) (I : InheritedState)
    (Z : LocalPrefixCoordinates)
    (dateOne recurrent : LocalBridgePhase)
    (tail : LocalPrefixContinuationRule)
    (hp : localReducedPrefixResidual branch P I Z dateOne recurrent tail
      .commonPledgeOne = 0)
    (equation : LocalPrefixEquation) :
    sourceNominalPledgeShearedResidual branch P I Z dateOne recurrent tail
      equation =
    localReducedPrefixResidual branch P I Z dateOne recurrent tail equation := by
  cases equation <;> simp only [sourceNominalPledgeShearedResidual]
  · exact (sourceFirmEuler_dateOne_H_nominal_eq_of_pledge_zero
      branch P I Z dateOne recurrent tail hp).symm
  · exact (sourceFirmEuler_dateOne_L_nominal_eq_of_pledge_zero
      branch P I Z dateOne recurrent tail hp).symm

#print axioms sourceNominalPledgeShearedResidual_eq_of_pledge_zero

/-- Full SOURCE 33-row simultaneous zero-set equivalence, EXACT and
without Python, a fixed root, or positive-log assumptions.

This is a zero-set result for a row operation; it does not assert that
the economic 33-row system has any zeros or that its Jacobian is
invertible. -/
theorem sourceNominalPledgeShearedResidual_all_zero_iff
    (branch : LocalPrefixBranch)
    (P : Primitives LocalBridgePhase) (I : InheritedState)
    (Z : LocalPrefixCoordinates)
    (dateOne recurrent : LocalBridgePhase)
    (tail : LocalPrefixContinuationRule) :
    (∀ equation : LocalPrefixEquation,
      sourceNominalPledgeShearedResidual branch P I Z
        dateOne recurrent tail equation = 0) ↔
    (∀ equation : LocalPrefixEquation,
      localReducedPrefixResidual branch P I Z
        dateOne recurrent tail equation = 0) := by
  constructor
  · intro h equation
    have hp : localReducedPrefixResidual branch P I Z dateOne recurrent tail
        .commonPledgeOne = 0 := by
      simpa only [sourceNominalPledgeShearedResidual] using
        (h .commonPledgeOne)
    rw [← sourceNominalPledgeShearedResidual_eq_of_pledge_zero
      branch P I Z dateOne recurrent tail hp equation]
    exact h equation
  · intro h equation
    have hp := h .commonPledgeOne
    rw [sourceNominalPledgeShearedResidual_eq_of_pledge_zero
      branch P I Z dateOne recurrent tail hp equation]
    exact h equation

#print axioms sourceNominalPledgeShearedResidual_all_zero_iff

end Ventura26LiquidityAllocation

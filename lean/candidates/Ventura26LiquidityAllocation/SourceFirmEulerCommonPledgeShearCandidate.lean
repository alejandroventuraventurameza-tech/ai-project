import Ventura26LiquidityAllocation.SourceFirmEulerPledgeWedgeCandidate

/-!
# Exact state-dependent SOURCE Euler/common-pledge shear (date one)

For SOURCE's binding date-one Euler, replace the physical pledge-unit
computed from date-two future prices by the common nominal pledge
coordinate carried in the 33-vector.

The difference is a MULTIPLE OF THE ACTUAL REDUCED SOURCE common-pledge
residual. Therefore the two Euler formulations share the same zero
set whenever the genuine common-pledge row vanishes.

This is exact algebra over SOURCE's own fields; it does not identify
Python's chart or the infinite-horizon tail P0, nor certify a Jacobian.
-/

namespace Ventura26LiquidityAllocation

noncomputable def sourceFirmEulerNominalPledge
    (P : Primitives LocalBridgePhase) (d : LocalPrefixDateData)
    (i : FirmType) (commonNominalPledge : ℝ) : ℝ :=
  sourceFirmEulerUnconstrained P d i +
    P.pledgeability i * commonNominalPledge *
      (localPrefixEntrepreneurSDF P d i / d.nextControls.inflation -
        1 / d.controls.loanRate)

/-- The nominal-pledge-coordinate Euler differs from the genuine SOURCE
binding Euler exactly by the nominal pledge discrepancy times its
state-dependent coefficient. No zero-residual premise is needed. -/
theorem sourceFirmEuler_nominalPledge_shear
    (P : Primitives LocalBridgePhase) (d : LocalPrefixDateData)
    (i : FirmType) (commonNominalPledge : ℝ) :
    sourceFirmEulerNominalPledge P d i commonNominalPledge =
      localReducedFirmCapitalEulerResidual .binding P d i +
      P.pledgeability i *
        (localPrefixEntrepreneurSDF P d i / d.nextControls.inflation -
          1 / d.controls.loanRate) *
        (commonNominalPledge -
          (1 - P.depreciation) * d.nextControls.inflation *
            d.nextControls.capitalPrice) := by
  rw [sourceFirmEuler_binding_decomposition]
  simp only [sourceFirmEulerNominalPledge,
    sourceFirmEulerPledgeWedge, localPrefixPledgeUnit]
  ring

#print axioms sourceFirmEuler_nominalPledge_shear

/-- The exact SOURCE pledge discrepancy at date one is
commonNominalPledge minus the physical collateral-unit target. -/
theorem sourceFirmEuler_dateOne_commonPledge_difference
    (branch : LocalPrefixBranch)
    (P : Primitives LocalBridgePhase) (I : InheritedState)
    (Z : LocalPrefixCoordinates)
    (dateOne recurrent : LocalBridgePhase)
    (tail : LocalPrefixContinuationRule) :
    Z.stateTwo.commonPledgeValue -
      (1 - P.depreciation) *
        (localPrefixDateOneData P Z dateOne recurrent tail).nextControls.inflation *
        (localPrefixDateOneData P Z dateOne recurrent tail).nextControls.capitalPrice =
      localReducedPrefixResidual branch P I Z dateOne recurrent tail
        .commonPledgeOne := by
  rw [sourceCommonPledgeResidual_exact_level]
  rfl

#print axioms sourceFirmEuler_dateOne_commonPledge_difference

/-- For both firms the source-shaped Euler using the common pledge
coordinate equals its genuine binding Euler plus an explicit multiple
of the genuine SOURCE common-pledge residual. -/
theorem sourceFirmEuler_dateOne_nominalPledge_shear
    (branch : LocalPrefixBranch)
    (P : Primitives LocalBridgePhase) (I : InheritedState)
    (Z : LocalPrefixCoordinates)
    (dateOne recurrent : LocalBridgePhase)
    (tail : LocalPrefixContinuationRule)
    (i : FirmType) :
    sourceFirmEulerNominalPledge P
      (localPrefixDateOneData P Z dateOne recurrent tail) i
      Z.stateTwo.commonPledgeValue =
      localReducedFirmCapitalEulerResidual .binding P
        (localPrefixDateOneData P Z dateOne recurrent tail) i +
      P.pledgeability i *
        (localPrefixEntrepreneurSDF P
          (localPrefixDateOneData P Z dateOne recurrent tail) i /
          (localPrefixDateOneData P Z dateOne recurrent tail).nextControls.inflation -
          1 / (localPrefixDateOneData P Z dateOne recurrent tail).controls.loanRate) *
        localReducedPrefixResidual branch P I Z dateOne recurrent tail
          .commonPledgeOne := by
  rw [sourceFirmEuler_nominalPledge_shear]
  rw [sourceFirmEuler_dateOne_commonPledge_difference]

#print axioms sourceFirmEuler_dateOne_nominalPledge_shear

/-- Once genuine common pledge clears, the two Euler residuals
are literally identical. This is NOT a full equilibrium proposition. -/
theorem sourceFirmEuler_dateOne_equivalent_on_pledge_zero
    (branch : LocalPrefixBranch)
    (P : Primitives LocalBridgePhase) (I : InheritedState)
    (Z : LocalPrefixCoordinates)
    (dateOne recurrent : LocalBridgePhase)
    (tail : LocalPrefixContinuationRule) (i : FirmType)
    (hpledge : localReducedPrefixResidual branch P I Z
      dateOne recurrent tail .commonPledgeOne = 0) :
    sourceFirmEulerNominalPledge P
      (localPrefixDateOneData P Z dateOne recurrent tail) i
      Z.stateTwo.commonPledgeValue =
      localReducedFirmCapitalEulerResidual .binding P
        (localPrefixDateOneData P Z dateOne recurrent tail) i := by
  rw [sourceFirmEuler_dateOne_nominalPledge_shear]
  rw [hpledge]
  ring

#print axioms sourceFirmEuler_dateOne_equivalent_on_pledge_zero

end Ventura26LiquidityAllocation

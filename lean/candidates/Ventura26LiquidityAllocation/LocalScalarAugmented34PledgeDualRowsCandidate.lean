import Ventura26LiquidityAllocation.LocalScalarCommonPledgeLogZeroCandidate
import Ventura26LiquidityAllocation.LocalScalarDualSigmaOneBridgeCandidate
import Ventura26LiquidityAllocation.LocalScalarAugmented34PolicyRecenterCandidate

/-!
# Augmented source row 21 (common pledge) and row 33 (firm-L funding dual)

Two further pieces of the actual 34-equation source operator are
matched to the shape of their illustrative Python counterparts:
- row 21 in date-one COMMON pledged capital is an equation in levels;
  the Python bridge uses log(J2 / ((1-depreciation)*Pi2*Q2)).
  Its zero set is identical on a strictly positive source domain.
- the extra row 33 is the original L funding marginal. Under
  entrepreneurRiskAversion=1, its CRRA ratio reduces to C0L/C1L.

Both statements are mathematical correspondences to the source
operator, not identities with unverified Python arrays or proofs of
a full competitive equilibrium. No derivative equality for the
level/log pledge row is claimed.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarAugmented34PledgeDualRows

open ProposedLocalScalarCommonPledgeLogZero
open ProposedLocalScalarDualSigmaOneBridge
open ProposedLocalScalarAugmented34Source
open ProposedLocalScalarAugmented34PolicyRecenter

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The date-one source pledge equation at augmented index 21 has
exactly the zero set of the positive Python-shaped log ratio,
conditional on the source depreciation bound and positivity. -/
theorem augmented_common_pledge_log_zero_iff
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (z : Fin 33 → ℝ) (h : ℝ)
    (hpledge : 0 < (localPrefixLogChart Z0 z).stateTwo.commonPledgeValue)
    (hdepr : P.depreciation < 1)
    (hinfl : 0 <
      (localPrefixDateOneData (reserveRemunerationShiftedPrimitives P h)
        (localPrefixLogChart Z0 z) dateOne recurrent tail).nextControls.inflation)
    (hprice : 0 <
      (localPrefixDateOneData (reserveRemunerationShiftedPrimitives P h)
        (localPrefixLogChart Z0 z) dateOne recurrent tail).nextControls.capitalPrice) :
    let Pv := reserveRemunerationShiftedPrimitives P h
    let Z := localPrefixLogChart Z0 z
    (Real.log
      (Z.stateTwo.commonPledgeValue /
        sourceDateOneCommonPledgeValuation Pv Z dateOne recurrent tail) = 0 ↔
      (augmentedBoundaryZeroResidual
        P I Z0 dateOne recurrent tail z h).1 (21 : Fin 33) = 0) := by
  let Pv := reserveRemunerationShiftedPrimitives P h
  let Z := localPrefixLogChart Z0 z
  have hdeprPv : Pv.depreciation < 1 := by
    simpa only [Pv, reserveRemunerationShiftedPrimitives,
      initialIntervenedPrimitives] using hdepr
  have hsource := source_common_pledge_log_zero_iff_of_positive
    Pv I Z dateOne recurrent tail hpledge hdeprPv hinfl hprice
  change Real.log
    (Z.stateTwo.commonPledgeValue /
      sourceDateOneCommonPledgeValuation Pv Z dateOne recurrent tail) = 0 ↔
    localReducedPrefixResidual LocalPrefixBranch.binding
      Pv I Z dateOne recurrent tail
      LocalPrefixEquation.commonPledgeOne = 0
  exact hsource

/-- The 34th component of the actual augmented source residual is
the Python-shaped funding marginal under CRRA sigmaE=1. It depends
on source consumption, gross lending rate and next gross inflation;
the external numerical values remain unverified. -/
theorem augmented_funding_dual_sigma_one
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (z : Fin 33 → ℝ) (h : ℝ)
    (hsigma : P.entrepreneurRiskAversion = 1)
    (hc0 : 0 < (localPrefixLogChart Z0 z).controlsZero.consumptionL)
    (hc1 : 0 < (localPrefixLogChart Z0 z).controlsOne.consumptionL) :
    let Z := localPrefixLogChart Z0 z
    (augmentedBoundaryZeroResidual
      P I Z0 dateOne recurrent tail z h).2 =
      1 / Z.controlsZero.loanRate -
      (P.entrepreneurDiscount *
        (Z.controlsZero.consumptionL / Z.controlsOne.consumptionL)) /
        Z.controlsOne.inflation := by
  change localNormalizedCollateralDualL P (localPrefixLogChart Z0 z) =
      1 / (localPrefixLogChart Z0 z).controlsZero.loanRate -
      (P.entrepreneurDiscount *
        ((localPrefixLogChart Z0 z).controlsZero.consumptionL /
          (localPrefixLogChart Z0 z).controlsOne.consumptionL)) /
          (localPrefixLogChart Z0 z).controlsOne.inflation
  exact source_normalized_L_dual_sigma_one
    P (localPrefixLogChart Z0 z) hsigma hc0 hc1

#print axioms augmented_common_pledge_log_zero_iff
#print axioms augmented_funding_dual_sigma_one

end ProposedLocalScalarAugmented34PledgeDualRows
end Ventura26LiquidityAllocation

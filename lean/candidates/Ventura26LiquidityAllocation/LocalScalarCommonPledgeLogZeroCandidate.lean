import Ventura26LiquidityAllocation.LocalScalarBankFaceLogZeroCandidate

/-!
# The date-one common collateral pledge row: source levels vs Python logs

The finite_bridge.py residual block has a date-one common pledge
condition log(J2/(ad * Pi2 * Q2)) = 0. In contrast, EconomicModel.lean
writes the source .commonPledgeOne row as
    J2 - (1 - depreciation) * Pi2 * Q2 = 0.

Under a positive pledge and a strictly positive promised collateral
valuation, their zero sets coincide. The mapping of numerical J2,
ad, Pi2 and Q2 to the source variables and primitives is still a
separate provenance obligation; this theorem never invents a
numerical calibration or a Banach root.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarCommonPledgeLogZero

open ProposedLocalScalarBankFaceLogZero

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Exact promised date-one common pledge valuation entering the
source date-two state and collateral row. -/
noncomputable def sourceDateOneCommonPledgeValuation
    (P : Primitives S) (Z : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule) : ℝ :=
  (1 - P.depreciation) *
    (localPrefixDateOneData P Z dateOne recurrent tail).nextControls.inflation *
    (localPrefixDateOneData P Z dateOne recurrent tail).nextControls.capitalPrice

/-- Exact source common pledge equation is in LEVELS. -/
theorem source_common_pledge_level_row
    (P : Primitives S) (I : InheritedState)
    (Z : LocalPrefixCoordinates) (dateOne recurrent : S)
    (tail : LocalPrefixContinuationRule) :
    localReducedPrefixResidual LocalPrefixBranch.binding P I Z
      dateOne recurrent tail LocalPrefixEquation.commonPledgeOne =
        Z.stateTwo.commonPledgeValue -
          sourceDateOneCommonPledgeValuation P Z dateOne recurrent tail := by
  rfl

/-- The date-one common pledge log ratio and its ORIGINAL source
level equation have precisely the same zeros on a positive domain. -/
theorem source_common_pledge_log_zero_iff
    (P : Primitives S) (I : InheritedState)
    (Z : LocalPrefixCoordinates) (dateOne recurrent : S)
    (tail : LocalPrefixContinuationRule)
    (hpledge : 0 < Z.stateTwo.commonPledgeValue)
    (hvaluation :
      0 < sourceDateOneCommonPledgeValuation P Z dateOne recurrent tail) :
    Real.log
      (Z.stateTwo.commonPledgeValue /
        sourceDateOneCommonPledgeValuation P Z dateOne recurrent tail) = 0 ↔
      localReducedPrefixResidual LocalPrefixBranch.binding P I Z
        dateOne recurrent tail LocalPrefixEquation.commonPledgeOne = 0 := by
  rw [source_common_pledge_level_row]
  exact log_ratio_zero_iff_level_zero _ _ hpledge hvaluation

/-- Positive depreciation wedge, next inflation and next capital
price establish the nonzero denominator without treating the
nominal funding-pledge level as automatically positive. -/
theorem source_common_pledge_valuation_pos
    (P : Primitives S) (Z : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (hdepr : P.depreciation < 1)
    (hinfl : 0 <
      (localPrefixDateOneData P Z dateOne recurrent tail).nextControls.inflation)
    (hprice : 0 <
      (localPrefixDateOneData P Z dateOne recurrent tail).nextControls.capitalPrice) :
    0 < sourceDateOneCommonPledgeValuation P Z dateOne recurrent tail := by
  unfold sourceDateOneCommonPledgeValuation
  exact mul_pos (mul_pos (sub_pos.mpr hdepr) hinfl) hprice

/-- Conditions with economically interpretable positive primitives
suffice for the exact log/level common-pledge zero-set bridge. -/
theorem source_common_pledge_log_zero_iff_of_positive
    (P : Primitives S) (I : InheritedState)
    (Z : LocalPrefixCoordinates) (dateOne recurrent : S)
    (tail : LocalPrefixContinuationRule)
    (hpledge : 0 < Z.stateTwo.commonPledgeValue)
    (hdepr : P.depreciation < 1)
    (hinfl : 0 <
      (localPrefixDateOneData P Z dateOne recurrent tail).nextControls.inflation)
    (hprice : 0 <
      (localPrefixDateOneData P Z dateOne recurrent tail).nextControls.capitalPrice) :
    Real.log
      (Z.stateTwo.commonPledgeValue /
        sourceDateOneCommonPledgeValuation P Z dateOne recurrent tail) = 0 ↔
      localReducedPrefixResidual LocalPrefixBranch.binding P I Z
        dateOne recurrent tail LocalPrefixEquation.commonPledgeOne = 0 := by
  exact source_common_pledge_log_zero_iff P I Z dateOne recurrent tail
    hpledge
    (source_common_pledge_valuation_pos
      P Z dateOne recurrent tail hdepr hinfl hprice)

#print axioms source_common_pledge_level_row
#print axioms source_common_pledge_log_zero_iff
#print axioms source_common_pledge_valuation_pos
#print axioms source_common_pledge_log_zero_iff_of_positive

end ProposedLocalScalarCommonPledgeLogZero
end Ventura26LiquidityAllocation

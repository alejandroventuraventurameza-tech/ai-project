import Ventura26LiquidityAllocation.SourceThreeBankRowsOffRootExponentialCrossCandidate

/-!
# Original SOURCE 33-equation bank-row identification, both dates

This checks that the ACTUAL localReducedPrefixResidual (not merely
abstract output vectors) uses original localReducedRemainingResidual
rows 6-10 for monetary-rate, monetary-quantity, loan-pricing,
deposit-pricing, bank-balance, at both date zero and date one.

It is the exact dispatch necessary to lift the certified single-date
SOURCE banking corrections to the date-zero/date-one 33-row layout.
The actual economic differentiation, parameter/coordinate equivalence
with Python and root regularity remain separate tasks.
-/

namespace Ventura26LiquidityAllocation

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The SOURCE date-zero rate rule is original local economic row 6. -/
theorem sourcePrefix33_rateRuleZero_originalRow
    (branch : LocalPrefixBranch) (P : Primitives S) (I : InheritedState)
    (Z : LocalPrefixCoordinates) (dateOne recurrent : S)
    (tail : LocalPrefixContinuationRule) :
    localReducedPrefixResidual branch P I Z dateOne recurrent tail
      LocalPrefixEquation.reserveRateRuleZero =
    localReducedRemainingResidual P (localPrefixDateZeroData P I Z dateOne) 6 := by
  rfl

/-- The SOURCE date-zero quantity rule is original local economic row 7. -/
theorem sourcePrefix33_quantityRuleZero_originalRow
    (branch : LocalPrefixBranch) (P : Primitives S) (I : InheritedState)
    (Z : LocalPrefixCoordinates) (dateOne recurrent : S)
    (tail : LocalPrefixContinuationRule) :
    localReducedPrefixResidual branch P I Z dateOne recurrent tail
      LocalPrefixEquation.reserveQuantityRuleZero =
    localReducedRemainingResidual P (localPrefixDateZeroData P I Z dateOne) 7 := by
  rfl

/-- Genuine original SOURCE pricing/balance rows are 8/9/10 at date zero. -/
theorem sourcePrefix33_bankRowsZero_original
    (branch : LocalPrefixBranch) (P : Primitives S) (I : InheritedState)
    (Z : LocalPrefixCoordinates) (dateOne recurrent : S)
    (tail : LocalPrefixContinuationRule) :
    (localReducedPrefixResidual branch P I Z dateOne recurrent tail
      LocalPrefixEquation.loanPricingZero =
        localReducedRemainingResidual P (localPrefixDateZeroData P I Z dateOne) 8) ∧
    (localReducedPrefixResidual branch P I Z dateOne recurrent tail
      LocalPrefixEquation.depositPricingZero =
        localReducedRemainingResidual P (localPrefixDateZeroData P I Z dateOne) 9) ∧
    (localReducedPrefixResidual branch P I Z dateOne recurrent tail
      LocalPrefixEquation.bankBalanceZero =
        localReducedRemainingResidual P (localPrefixDateZeroData P I Z dateOne) 10) := by
  exact ⟨rfl, rfl, rfl⟩

/-- The SOURCE date-one rate rule is local economic row 6. -/
theorem sourcePrefix33_rateRuleOne_originalRow
    (branch : LocalPrefixBranch) (P : Primitives S) (I : InheritedState)
    (Z : LocalPrefixCoordinates) (dateOne recurrent : S)
    (tail : LocalPrefixContinuationRule) :
    localReducedPrefixResidual branch P I Z dateOne recurrent tail
      LocalPrefixEquation.reserveRateRuleOne =
    localReducedRemainingResidual P
      (localPrefixDateOneData P Z dateOne recurrent tail) 6 := by
  rfl

/-- The SOURCE date-one quantity rule is local economic row 7. -/
theorem sourcePrefix33_quantityRuleOne_originalRow
    (branch : LocalPrefixBranch) (P : Primitives S) (I : InheritedState)
    (Z : LocalPrefixCoordinates) (dateOne recurrent : S)
    (tail : LocalPrefixContinuationRule) :
    localReducedPrefixResidual branch P I Z dateOne recurrent tail
      LocalPrefixEquation.reserveQuantityRuleOne =
    localReducedRemainingResidual P
      (localPrefixDateOneData P Z dateOne recurrent tail) 7 := by
  rfl

/-- Genuine original SOURCE pricing/balance rows are 8/9/10 at date one. -/
theorem sourcePrefix33_bankRowsOne_original
    (branch : LocalPrefixBranch) (P : Primitives S) (I : InheritedState)
    (Z : LocalPrefixCoordinates) (dateOne recurrent : S)
    (tail : LocalPrefixContinuationRule) :
    (localReducedPrefixResidual branch P I Z dateOne recurrent tail
      LocalPrefixEquation.loanPricingOne =
        localReducedRemainingResidual P
          (localPrefixDateOneData P Z dateOne recurrent tail) 8) ∧
    (localReducedPrefixResidual branch P I Z dateOne recurrent tail
      LocalPrefixEquation.depositPricingOne =
        localReducedRemainingResidual P
          (localPrefixDateOneData P Z dateOne recurrent tail) 9) ∧
    (localReducedPrefixResidual branch P I Z dateOne recurrent tail
      LocalPrefixEquation.bankBalanceOne =
        localReducedRemainingResidual P
          (localPrefixDateOneData P Z dateOne recurrent tail) 10) := by
  exact ⟨rfl, rfl, rfl⟩

#print axioms sourcePrefix33_bankRowsZero_original
#print axioms sourcePrefix33_bankRowsOne_original

end Ventura26LiquidityAllocation

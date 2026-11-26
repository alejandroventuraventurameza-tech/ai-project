import Ventura26LiquidityAllocation.SourceEconomicBankBalanceExponentialCrossRowsCandidate
import Ventura26LiquidityAllocation.SourceBankPricingPythonOTCCrossRowsCandidate

/-!
# Exact three-bank-row OFF-ROOT bridge for ORIGINAL SOURCE

At one original SOURCE economic date, low-tightness/log-two OTC
identification and positivity/nonzero ratio hypotheses produce
the THREE banking residual gaps simultaneously:
- loan target - SOURCE loan = T*(exp(rateResidual)-1)
- deposit target - SOURCE deposit =
     -T*(exp(rateResidual)-1)*(1+depositOTCcross)
- balance target - SOURCE balance =
     quantityCoefficient*(exp(quantityResidual)-1)
     + rateCoefficient*(exp(rateResidual)-1).

This composes already certified source-level statements with no
assumed SOURCE/Python full 33-row equality, no economic root and
no derivative identification. The original Python payment law and
other parameters remain separate bridge obligations.
-/

namespace Ventura26LiquidityAllocation

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Full genuine SOURCE banking off-root target substitution at one
date. Zero of policy rows makes all three RHS corrections vanish. -/
theorem sourceThreeBankRows_offRoot_exponentialCrossRows
    (P : Primitives S) (d : LocalPrefixDateData)
    (hmatch : P.matchingIntensity = Real.log 2)
    (htight : d.controls.tightness ≤ 1)
    (hR : 0 < d.currentReserveRate)
    (hM : 0 < d.currentReservesPre)
    (hRatio : localPrefixReserveDepositRatio P d ≠ 0)
    (hTargetRatio :
      sourceBankRatioAtRate d.reserveRequirement
        d.controls.depositRate
        (localPrefixMeanAbsolutePaymentShock P *
          (1 - d.controls.tightness) /
            (1 + d.controls.tightness))
        (sourceRateRuleTarget P d) ≠ 0) :
    (d.controls.loanRate - sourceRateRuleTarget P d -
        (sourceFrozenPythonDeficitSlope d +
          sourceFrozenPythonSurplusSlope d) / 2 -
        localReducedRemainingResidual P d (8 : Fin 11) =
      sourceRateRuleTarget P d *
        (Real.exp (localReducedRemainingResidual P d (6 : Fin 11)) - 1)) ∧
    (sourceRateRuleTarget P d +
        (1 - d.reserveRequirement) *
          (sourceFrozenPythonDeficitSlope d +
            sourceFrozenPythonSurplusSlope d) / 2 -
        (d.controls.depositRate / sourceRateRuleTarget P d -
          d.reserveRequirement) *
          localPrefixMeanAbsolutePaymentShock P *
            (sourceFrozenPythonDeficitSlope d -
              sourceFrozenPythonSurplusSlope d) / 2 -
        d.controls.depositRate -
        localReducedRemainingResidual P d (9 : Fin 11) =
      -sourceRateRuleTarget P d *
        (Real.exp (localReducedRemainingResidual P d (6 : Fin 11)) - 1) *
        (1 +
          d.controls.depositRate *
            localPrefixMeanAbsolutePaymentShock P *
              (sourceFrozenPythonDeficitSlope d -
                sourceFrozenPythonSurplusSlope d) /
                (2 * d.currentReserveRate *
                  sourceRateRuleTarget P d))) ∧
    ((localPrefixReducedBankLoans P d -
        d.currentBankFace / d.controls.inflation -
        sourceBankMultiplierAtRate d.reserveRequirement
          d.controls.depositRate
          (localPrefixMeanAbsolutePaymentShock P *
            (1 - d.controls.tightness) /
              (1 + d.controls.tightness))
          (sourceRateRuleTarget P d) *
            sourceQuantityRuleTarget P d) -
      (localPrefixReducedBankLoans P d -
        d.currentBankFace / d.controls.inflation -
        (1 / localPrefixReserveDepositRatio P d - 1) *
          d.currentReservesPre) =
      sourceBankQuantityCrossCoefficient P d *
        (Real.exp (localReducedRemainingResidual P d (7 : Fin 11)) - 1) +
      sourceBankRateCrossCoefficient P d *
        (Real.exp (localReducedRemainingResidual P d (6 : Fin 11)) - 1)) := by
  refine ⟨?_, ?_, ?_⟩
  · have h := sourceLoanPricing_frozenPythonOTC_crossRow
      P d hmatch htight hR
    linear_combination h
  · have h := sourceDepositPricing_frozenPythonOTC_crossRow
      P d hmatch htight hR
    linear_combination h
  · exact sourceEconomicBankBalance_twoPolicy_exponentialCrossRows
      P d hR hM hRatio hTargetRatio

#print axioms sourceThreeBankRows_offRoot_exponentialCrossRows

end Ventura26LiquidityAllocation

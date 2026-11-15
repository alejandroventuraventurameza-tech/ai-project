import Ventura26LiquidityAllocation.SourceBankPricingPythonOTCRootParityCandidate
import Ventura26LiquidityAllocation.SourceEconomicBankPolicyRootParityCandidate

/-!
# Integrated banking-row parity at a genuine SOURCE monetary-rule root

At ONE original SOURCE economic date, both monetary rules zero,
positive realized rate/quantity, and the log-two/low-tightness OTC
contract imply exact simultaneous parity for the three bank rows:
loan pricing, deposit pricing, and balance.

All RHS expressions refer to ORIGINAL EconomicModel local reduced
rows 8, 9, 10. Their left sides are target-rate/target-quantity
expressions with Python-calibrated OTC functions; no cross-language
full residual identity or economic root existence is asserted.
-/

namespace Ventura26LiquidityAllocation

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Conditional joint parity for all three original SOURCE banking
rows at a local monetary-rule root. The bank multiplier on the
balance side uses exact SOURCE primitives and matching statistics. -/
theorem sourceThreeBankRows_pythonOTC_targetParity_at_monetaryRoot
    (P : Primitives S) (d : LocalPrefixDateData)
    (hmatch : P.matchingIntensity = Real.log 2)
    (htight : d.controls.tightness ≤ 1)
    (hR : 0 < d.currentReserveRate)
    (hM : 0 < d.currentReservesPre)
    (hRowR : localReducedRemainingResidual P d (6 : Fin 11) = 0)
    (hRowM : localReducedRemainingResidual P d (7 : Fin 11) = 0) :
    (d.controls.loanRate - sourceRateRuleTarget P d -
        (sourceFrozenPythonDeficitSlope d +
          sourceFrozenPythonSurplusSlope d) / 2 =
        localReducedRemainingResidual P d (8 : Fin 11)) ∧
    (sourceRateRuleTarget P d +
        (1 - d.reserveRequirement) *
          (sourceFrozenPythonDeficitSlope d +
            sourceFrozenPythonSurplusSlope d) / 2 -
        (d.controls.depositRate / sourceRateRuleTarget P d -
          d.reserveRequirement) *
          localPrefixMeanAbsolutePaymentShock P *
            (sourceFrozenPythonDeficitSlope d -
              sourceFrozenPythonSurplusSlope d) / 2 -
        d.controls.depositRate =
        localReducedRemainingResidual P d (9 : Fin 11)) ∧
    (localPrefixReducedBankLoans P d -
        d.currentBankFace / d.controls.inflation -
        sourceBankMultiplierAtRate d.reserveRequirement
          d.controls.depositRate
          (localPrefixMeanAbsolutePaymentShock P *
            (1 - d.controls.tightness) /
              (1 + d.controls.tightness))
          (sourceRateRuleTarget P d) *
            sourceQuantityRuleTarget P d =
        localPrefixReducedBankLoans P d -
          d.currentBankFace / d.controls.inflation -
          (1 / localPrefixReserveDepositRatio P d - 1) *
            d.currentReservesPre) := by
  refine ⟨?_, ?_, ?_⟩
  · exact sourceLoanPricing_pythonOTC_eq_at_monetaryRoot
      P d hmatch htight hR hRowR
  · exact sourceDepositPricing_pythonOTC_eq_at_monetaryRoot
      P d hmatch htight hR hRowR
  · exact sourceEconomicBankBalance_target_eq_of_policyRows_zero
      P d hR hM hRowR hRowM

#print axioms sourceThreeBankRows_pythonOTC_targetParity_at_monetaryRoot

end Ventura26LiquidityAllocation

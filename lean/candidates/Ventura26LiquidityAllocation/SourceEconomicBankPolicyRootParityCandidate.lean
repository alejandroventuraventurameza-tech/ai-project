import Ventura26LiquidityAllocation.SourceEconomicBankTwoPolicyTargetCandidate

/-!
# Genuine SOURCE bank balance: zero monetary rows imply target parity

On the positive monetary domain, the SOURCE reserve-rate and
reserve-quantity rule residuals vanishing imply that realized values
equal their policy targets. Consequently the actual bank-balance
expression is equal to the same economic expression computed at
both targets, keeping the other SOURCE arguments fixed.

This is not a root-existence theorem, not a Python-auxiliary
identification, and not a full Jacobian equivalence.
-/

namespace Ventura26LiquidityAllocation

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- SOURCE monetary rate residual zero forces the current
realized rate to equal its exact policy target. -/
theorem sourceReserveRate_target_eq_of_policyRow_zero
    (P : Primitives S) (data : LocalPrefixDateData)
    (hR : 0 < data.currentReserveRate)
    (hrow : localReducedRemainingResidual P data (6 : Fin 11) = 0) :
    data.currentReserveRate = sourceRateRuleTarget P data := by
  have hgap := sourceActualReserveRate_target_gap P data hR
  rw [hrow] at hgap
  simp at hgap
  linarith

#print axioms sourceReserveRate_target_eq_of_policyRow_zero

/-- SOURCE monetary quantity residual zero forces realized reserves
to equal their exact policy quantity target. -/
theorem sourceReserveQuantity_target_eq_of_policyRow_zero
    (P : Primitives S) (data : LocalPrefixDateData)
    (hM : 0 < data.currentReservesPre)
    (hrow : localReducedRemainingResidual P data (7 : Fin 11) = 0) :
    data.currentReservesPre = sourceQuantityRuleTarget P data := by
  have hgap := sourceActualReserves_target_gap P data hM
  rw [hrow] at hgap
  simp at hgap
  linarith

#print axioms sourceReserveQuantity_target_eq_of_policyRow_zero

/-- At a common zero of the TWO authentic SOURCE monetary rules, the
bank balance with target rate and target quantity agrees exactly
with the bank balance using realized SOURCE data. The bank pricing
and OTC auxiliary correspondences are separate obligations. -/
theorem sourceEconomicBankBalance_target_eq_of_policyRows_zero
    (P : Primitives S) (data : LocalPrefixDateData)
    (hR : 0 < data.currentReserveRate)
    (hM : 0 < data.currentReservesPre)
    (hRowR : localReducedRemainingResidual P data (6 : Fin 11) = 0)
    (hRowM : localReducedRemainingResidual P data (7 : Fin 11) = 0) :
    (localPrefixReducedBankLoans P data -
        data.currentBankFace / data.controls.inflation -
        sourceBankMultiplierAtRate data.reserveRequirement
          data.controls.depositRate
          (localPrefixMeanAbsolutePaymentShock P *
            (1 - data.controls.tightness) /
              (1 + data.controls.tightness))
          (sourceRateRuleTarget P data) *
            sourceQuantityRuleTarget P data) =
      (localPrefixReducedBankLoans P data -
        data.currentBankFace / data.controls.inflation -
        (1 / localPrefixReserveDepositRatio P data - 1) *
          data.currentReservesPre) := by
  have hRate := sourceReserveRate_target_eq_of_policyRow_zero
    P data hR hRowR
  have hQuantity := sourceReserveQuantity_target_eq_of_policyRow_zero
    P data hM hRowM
  rw [← hRate, ← hQuantity]
  rw [sourceBankMultiplierAtRealized_eq_SOURCE P data]

#print axioms sourceEconomicBankBalance_target_eq_of_policyRows_zero

end Ventura26LiquidityAllocation

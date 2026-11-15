import Ventura26LiquidityAllocation.SourceConcreteReserveDepositRatioCandidate

/-!
# Economic SOURCE bank-balance realized/target correction

This theorem instantiates the abstract two-policy bridge with the
LITERAL SOURCE deposit ratio, actual monetary rule target and
SOURCE reserve-quantity rule residual.

The target-rate multiplier is the explicit candidate rate evaluation;
its equality with the ORIGINAL Python auxiliary still requires
separate verification. No numerical root, Jacobian bijectivity or
structural IRF is established here.
-/

namespace Ventura26LiquidityAllocation

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The actual economic bank-balance correction, changing realized
SOURCE reserves and reserve rate to their rule targets simultaneously.
All nonzero ratio requirements appear as assumptions. -/
theorem sourceEconomicBankBalance_twoPolicyTarget_gap
    (P : Primitives S) (data : LocalPrefixDateData)
    (hR : data.currentReserveRate ≠ 0)
    (hM : 0 < data.currentReservesPre)
    (hRho : localPrefixReserveDepositRatio P data ≠ 0)
    (hTargetRho :
      sourceBankRatioAtRate data.reserveRequirement
        data.controls.depositRate
        (localPrefixMeanAbsolutePaymentShock P *
          (1 - data.controls.tightness) /
            (1 + data.controls.tightness))
        (sourceRateRuleTarget P data) ≠ 0) :
    (localPrefixReducedBankLoans P data -
        data.currentBankFace / data.controls.inflation -
        sourceBankMultiplierAtRate data.reserveRequirement
          data.controls.depositRate
          (localPrefixMeanAbsolutePaymentShock P *
            (1 - data.controls.tightness) /
              (1 + data.controls.tightness))
          (sourceRateRuleTarget P data) *
            sourceQuantityRuleTarget P data) -
      (localPrefixReducedBankLoans P data -
        data.currentBankFace / data.controls.inflation -
        (1 / localPrefixReserveDepositRatio P data - 1) *
          data.currentReservesPre) =
      (1 / localPrefixReserveDepositRatio P data - 1) *
        sourceQuantityRuleTarget P data *
          (Real.exp (localReducedRemainingResidual P data (7 : Fin 11)) - 1) +
        sourceQuantityRuleTarget P data *
          (data.controls.depositRate *
            (localPrefixMeanAbsolutePaymentShock P *
              (1 - data.controls.tightness) /
                (1 + data.controls.tightness)) *
            (data.currentReserveRate - sourceRateRuleTarget P data) /
            (data.currentReserveRate * sourceRateRuleTarget P data *
              localPrefixReserveDepositRatio P data *
              sourceBankRatioAtRate data.reserveRequirement
                data.controls.depositRate
                (localPrefixMeanAbsolutePaymentShock P *
                  (1 - data.controls.tightness) /
                    (1 + data.controls.tightness))
                (sourceRateRuleTarget P data))) := by
  let c : ℝ := localPrefixMeanAbsolutePaymentShock P *
    (1 - data.controls.tightness) / (1 + data.controls.tightness)
  let C : ℝ := localPrefixReducedBankLoans P data -
    data.currentBankFace / data.controls.inflation
  have hRatio :
      sourceBankRatioAtRate data.reserveRequirement
        data.controls.depositRate c data.currentReserveRate =
        localPrefixReserveDepositRatio P data := by
    simpa only [c] using sourceBankRatioAtRealized_eq_SOURCE P data
  have hK :
      sourceBankMultiplierAtRate data.reserveRequirement
        data.controls.depositRate c data.currentReserveRate =
        1 / localPrefixReserveDepositRatio P data - 1 := by
    simpa only [c] using sourceBankMultiplierAtRealized_eq_SOURCE P data
  have hQuantity := sourceActualReserves_target_gap P data hM
  have hGeneric := sourceBankBalance_twoPolicyResiduals_exact
    C data.reserveRequirement data.controls.depositRate c
    data.currentReserveRate (sourceRateRuleTarget P data)
    data.currentReservesPre (sourceQuantityRuleTarget P data)
    (localReducedRemainingResidual P data (7 : Fin 11))
    hR (ne_of_gt (Real.exp_pos _))
    (by rw [hRatio]; exact hRho)
    (by simpa only [c] using hTargetRho)
    hQuantity
  rw [hK, hRatio] at hGeneric
  simpa only [C, c] using hGeneric

#print axioms sourceEconomicBankBalance_twoPolicyTarget_gap

end Ventura26LiquidityAllocation

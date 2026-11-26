import Ventura26LiquidityAllocation.SourceTwoDateBankFullRowShearInverseCandidate
import Ventura26LiquidityAllocation.SourceEconomicBankTwoPolicyTargetCandidate

/-!
# Exact economic SOURCE bank balance: two exponential monetary channels

The existing sourceEconomicBankBalance_twoPolicyTarget_gap theorem
expresses the original reduced bank-balance difference using
a quantity-policy residual and the realized-minus-target RATE gap.
This module eliminates the remaining raw rate gap using the ACTUAL
SOURCE reserve-rate policy residual. As a result the entire OFF-ROOT
economic correction decomposes into the two monetary row residuals
through exp(u)-1, exp(v)-1 with exact state-dependent coefficients.

This is a genuine SOURCE 11-row/date economic bridge, not just an
abstract row shear. Full frozen-Python auxiliary identification
still depends on matching the original payment law and other
normalizations, plus an exact 33-coordinate chart.
-/

namespace Ventura26LiquidityAllocation

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Source-target bank balance coefficient for the quantity-policy
gap, using the ACTUAL SOURCE reserve/deposit ratio. -/
noncomputable def sourceBankQuantityCrossCoefficient
    (P : Primitives S) (d : LocalPrefixDateData) : ℝ :=
  (1 / localPrefixReserveDepositRatio P d - 1) *
    sourceQuantityRuleTarget P d

/-- Source-target bank balance coefficient for the rate-policy
gap, with both realized and target reserve/deposit ratios. -/
noncomputable def sourceBankRateCrossCoefficient
    (P : Primitives S) (d : LocalPrefixDateData) : ℝ :=
  sourceQuantityRuleTarget P d *
    (d.controls.depositRate *
      (localPrefixMeanAbsolutePaymentShock P *
        (1 - d.controls.tightness) /
          (1 + d.controls.tightness)) *
      sourceRateRuleTarget P d /
      (d.currentReserveRate * sourceRateRuleTarget P d *
        localPrefixReserveDepositRatio P d *
        sourceBankRatioAtRate d.reserveRequirement
          d.controls.depositRate
          (localPrefixMeanAbsolutePaymentShock P *
            (1 - d.controls.tightness) /
              (1 + d.controls.tightness))
          (sourceRateRuleTarget P d)))

/-- Exact OFF-ROOT decomposition of the genuine SOURCE bank balance
after replacing realized rate/quantity with their monetary targets.
Neither correction coefficient is frozen outside the common root. -/
theorem sourceEconomicBankBalance_twoPolicy_exponentialCrossRows
    (P : Primitives S) (d : LocalPrefixDateData)
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
    (localPrefixReducedBankLoans P d -
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
        (Real.exp (localReducedRemainingResidual P d (6 : Fin 11)) - 1) := by
  have h := sourceEconomicBankBalance_twoPolicyTarget_gap
    P d (ne_of_gt hR) hM hRatio hTargetRatio
  rw [sourceActualReserveRate_target_gap P d hR] at h
  unfold sourceBankQuantityCrossCoefficient
    sourceBankRateCrossCoefficient
  convert h using 1 <;> ring

#print axioms sourceEconomicBankBalance_twoPolicy_exponentialCrossRows

end Ventura26LiquidityAllocation

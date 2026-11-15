import Ventura26LiquidityAllocation.SourceReserveRulesLogRatioBridgeCandidate
import Ventura26LiquidityAllocation.SourceActualLogNormalizationDomainCandidate

/-!
# Off-root SOURCE policy target substitution: loan pricing and bank balance

IMPORTANT cross-language discrepancy. Genuine SOURCE remaining rows
8,9,10 use REALIZED currentReserveRate/currentReservesPre. Original
Python auxiliary computes TARGET reserveRate and reserves, then
uses those targets in other banking equations. Those functions are
not literally equal OFF ROOT, even if their policy RULE residuals
log(realized/target) are included elsewhere and vanish at a root.

This file proves actual SOURCE policy target-minus-realized gaps as
exact state-dependent functions of original SOURCE monetary row
6 or 7, and propagates those gaps to loan pricing and bank balance.

The SOURCE non-bank rate-dependent OTC slopes and reserve/deposit
ratio are held at their original SOURCE date-data values in those
two partial bridge identities; hence this is NOT yet the full
Python banking formula transformation. It identifies a necessary
cross-row correction and no true root/IRF is asserted.
-/

namespace Ventura26LiquidityAllocation

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- True SOURCE reserve-rate rule target, built as a positive
real exponential from ACTUAL model primitives and date data. -/
noncomputable def sourceRateRuleTarget (P : Primitives S)
    (d : LocalPrefixDateData) : ℝ :=
  Real.exp (
    P.reserveRatePersistence * Real.log d.lagReserveRate +
      (1 - P.reserveRatePersistence) *
        (Real.log P.reserveRateSteady +
          P.inflationResponse * Real.log d.controls.inflation +
          P.outputResponse *
            Real.log (localPrefixAggregateOutput P d / P.outputReference)) +
      d.reserveRateInnovation)

/-- True SOURCE reserve-quantity target, not necessarily equal
to realized reserves unless its policy equation vanishes. -/
noncomputable def sourceQuantityRuleTarget (P : Primitives S)
    (d : LocalPrefixDateData) : ℝ :=
  Real.exp (
    P.reserveQuantityPersistence * Real.log d.lagReservesPre +
      (1 - P.reserveQuantityPersistence) * Real.log P.reserveQuantitySteady +
      d.reserveQuantityInnovation)

/-- The exact real target substitution correction: realized-target
is target times exp(log(realized/target))-1. -/
theorem sourceRealized_minus_target_eq_policy_exponential_gap
    (realized target : ℝ)
    (hr : 0 < realized) (ht : 0 < target) :
    realized - target =
      target * (Real.exp (Real.log (realized / target)) - 1) := by
  have htne : target ≠ 0 := ne_of_gt ht
  rw [Real.exp_log (div_pos hr ht)]
  field_simp [htne] <;> ring

#print axioms sourceRealized_minus_target_eq_policy_exponential_gap

/-- ORIGINAL SOURCE rate-rule residual measures exactly how
far the realized reserve RATE differs from its positive policy TARGET. -/
theorem sourceActualReserveRate_target_gap
    (P : Primitives S) (d : LocalPrefixDateData)
    (hr : 0 < d.currentReserveRate) :
    d.currentReserveRate - sourceRateRuleTarget P d =
      sourceRateRuleTarget P d *
        (Real.exp (localReducedRemainingResidual P d (6 : Fin 11)) - 1) := by
  have hrow :
      localReducedRemainingResidual P d (6 : Fin 11) =
        Real.log (d.currentReserveRate / sourceRateRuleTarget P d) := by
    simpa only [sourceRateRuleTarget] using
      (sourceReserveRateRule_actual_logRatio P d hr)
  rw [hrow]
  exact sourceRealized_minus_target_eq_policy_exponential_gap
    d.currentReserveRate (sourceRateRuleTarget P d) hr (Real.exp_pos _)

#print axioms sourceActualReserveRate_target_gap

/-- ORIGINAL SOURCE quantity-rule residual measures exactly how
far realized reserves differ from their positive policy TARGET. -/
theorem sourceActualReserves_target_gap
    (P : Primitives S) (d : LocalPrefixDateData)
    (hM : 0 < d.currentReservesPre) :
    d.currentReservesPre - sourceQuantityRuleTarget P d =
      sourceQuantityRuleTarget P d *
        (Real.exp (localReducedRemainingResidual P d (7 : Fin 11)) - 1) := by
  have hrow :
      localReducedRemainingResidual P d (7 : Fin 11) =
        Real.log (d.currentReservesPre / sourceQuantityRuleTarget P d) := by
    simpa only [sourceQuantityRuleTarget] using
      (sourceReserveQuantityRule_actual_logRatio P d hM)
  rw [hrow]
  exact sourceRealized_minus_target_eq_policy_exponential_gap
    d.currentReservesPre (sourceQuantityRuleTarget P d) hM (Real.exp_pos _)

#print axioms sourceActualReserves_target_gap

/-- In ORIGINAL SOURCE loan pricing row 8, replacing the
REALIZED reserve rate by its policy TARGET produces a correction
proportional to the original SOURCE reserve-rate rule residual.
The two OTC slopes here are the original SOURCE slopes evaluated
on the ORIGINAL realized reserve rate; Python's separate auxiliary
slope identity requires further work. -/
theorem sourceLoanPricing_rateTarget_substitution
    (P : Primitives S) (d : LocalPrefixDateData)
    (hr : 0 < d.currentReserveRate) :
    d.controls.loanRate - sourceRateRuleTarget P d -
      (localPrefixBankDeficitSlope P d +
        localPrefixBankSurplusSlope P d) / 2 =
      localReducedRemainingResidual P d (8 : Fin 11) +
        sourceRateRuleTarget P d *
          (Real.exp (localReducedRemainingResidual P d (6 : Fin 11)) - 1) := by
  have hrow : localReducedRemainingResidual P d (8 : Fin 11) =
      d.controls.loanRate - d.currentReserveRate -
        (localPrefixBankDeficitSlope P d +
          localPrefixBankSurplusSlope P d) / 2 := by
    rfl
  rw [hrow, ← sourceActualReserveRate_target_gap P d hr]
  ring

#print axioms sourceLoanPricing_rateTarget_substitution

/-- This partial banking balance bridge holds the SOURCE deposit
ratio FIXED at its genuine (realized-rate) definition and substitutes
only the quantity-rule target for realized money. Its gap is
proportional to the quantity policy residual, exactly OFF ROOT.
Python also uses a ratio computed at its reserve-rate TARGET; the
correction for that difference remains a separate open obligation. -/
theorem sourceBankBalance_quantityTarget_substitution
    (P : Primitives S) (d : LocalPrefixDateData)
    (hM : 0 < d.currentReservesPre) :
    localPrefixReducedBankLoans P d -
      (d.currentBankFace / d.controls.inflation +
        (1 / localPrefixReserveDepositRatio P d - 1) *
          sourceQuantityRuleTarget P d) =
      localReducedRemainingResidual P d (10 : Fin 11) +
        (1 / localPrefixReserveDepositRatio P d - 1) *
          sourceQuantityRuleTarget P d *
          (Real.exp (localReducedRemainingResidual P d (7 : Fin 11)) - 1) := by
  have hrow : localReducedRemainingResidual P d (10 : Fin 11) =
      localPrefixReducedBankLoans P d -
        (d.currentBankFace / d.controls.inflation +
          (1 / localPrefixReserveDepositRatio P d - 1) *
            d.currentReservesPre) := by
    rfl
  rw [hrow, ← sourceActualReserves_target_gap P d hM]
  ring

#print axioms sourceBankBalance_quantityTarget_substitution


/-- The source deposit-pricing banking row is NOT literally equal to
the Python-style target-rate equation OFF ROOT. Holding the genuine
SOURCE OTC slope at the realized-rate evaluation, its difference
is an EXACT policy-rule cross-row term, including the nonlinear
xi := depositRate / realizedReserveRate correction.

This result uses no approximation, but does not establish the
separate OTC slope correspondence to Python's auxiliary, nor
the full SOURCE/Python Jacobian bridge. -/
theorem sourceDepositPricing_rateTarget_substitution
    (P : Primitives S) (d : LocalPrefixDateData)
    (hr : 0 < d.currentReserveRate) :
    sourceRateRuleTarget P d +
      (1 - d.reserveRequirement) *
        (localPrefixBankDeficitSlope P d +
          localPrefixBankSurplusSlope P d) / 2 -
      (d.controls.depositRate / sourceRateRuleTarget P d -
        d.reserveRequirement) *
        localPrefixMeanAbsolutePaymentShock P *
          (localPrefixBankDeficitSlope P d -
            localPrefixBankSurplusSlope P d) / 2 -
      d.controls.depositRate =
    localReducedRemainingResidual P d (9 : Fin 11) -
      sourceRateRuleTarget P d *
        (Real.exp (localReducedRemainingResidual P d (6 : Fin 11)) - 1) *
        (1 +
          d.controls.depositRate *
            localPrefixMeanAbsolutePaymentShock P *
              (localPrefixBankDeficitSlope P d -
                localPrefixBankSurplusSlope P d) /
                (2 * d.currentReserveRate *
                  sourceRateRuleTarget P d)) := by
  have hrow : localReducedRemainingResidual P d (9 : Fin 11) =
      d.currentReserveRate +
        (1 - d.reserveRequirement) *
          (localPrefixBankDeficitSlope P d +
            localPrefixBankSurplusSlope P d) / 2 -
        (d.controls.depositRate / d.currentReserveRate -
          d.reserveRequirement) *
          localPrefixMeanAbsolutePaymentShock P *
            (localPrefixBankDeficitSlope P d -
              localPrefixBankSurplusSlope P d) / 2 -
        d.controls.depositRate := by
    rfl
  rw [hrow, ← sourceActualReserveRate_target_gap P d hr]
  have hRne : d.currentReserveRate ≠ 0 := ne_of_gt hr
  have hTne : sourceRateRuleTarget P d ≠ 0 := ne_of_gt (Real.exp_pos _)
  field_simp [hRne, hTne] <;> ring

#print axioms sourceDepositPricing_rateTarget_substitution

end Ventura26LiquidityAllocation

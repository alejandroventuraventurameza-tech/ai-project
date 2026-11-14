import Ventura26LiquidityAllocation.SourceConcreteBankRenewalCalibrationCandidate

/-!
# Actual SOURCE reserve-rate and reserve-quantity rules as log ratios

Original SOURCE localReducedRemainingResidual rows 6 and 7 are
logarithmic deviations from the respective policy-rule LOG TARGETS:

  log R_t - [rho_R*log R_{t-1}
    + (1-rho_R)*(log Rbar + phi_pi*log pi_t
    + phi_y*log(Y_t/Ybar)) + v_R,t],

  log M_t - [rho_M*log M_{t-1}
    + (1-rho_M)*log Mbar + v_M,t].

Original Python remaining_residuals rows 6 and 7 use log
(next_state[5]/aux["rr"]) and log
(next_state[6]/aux["money"]) respectively.

This SOURCE theorem proves the exact SOURCE row value equals
log(currentReserveRate/exp(actual SOURCE rule log target)), and
analogously for reserve quantity. It is an OFF-ROOT identity for
all date data with strictly positive policy-rule outcomes, and is
not a claim that original Python aux["rr"] and aux["money"] have
already been formally identified with the SOURCE real targets.

No root existence, full SOURCE/Python operator parity or
infinite-horizon equilibrium is concluded.
-/

namespace Ventura26LiquidityAllocation

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Generic exact real identity for a positive policy quantity
relative to a log-scale policy-rule target; not merely zero-set
equivalence. -/
theorem sourceLogPolicyDeviation_eq_logRatio
    (a targetLog : ℝ) (ha : 0 < a) :
    Real.log a - targetLog =
      Real.log (a / Real.exp targetLog) := by
  rw [Real.log_div (ne_of_gt ha) (ne_of_gt (Real.exp_pos targetLog))]
  simp

#print axioms sourceLogPolicyDeviation_eq_logRatio

/-- Original SOURCE reserve remuneration rule, OFF ROOT, written
as a ratio to the exact positive exponential policy target. -/
theorem sourceReserveRateRule_actual_logRatio
    (P : Primitives S) (d : LocalPrefixDateData)
    (hR : 0 < d.currentReserveRate) :
    localReducedRemainingResidual P d (6 : Fin 11) =
      Real.log (d.currentReserveRate /
        Real.exp (
          P.reserveRatePersistence * Real.log d.lagReserveRate +
            (1 - P.reserveRatePersistence) *
              (Real.log P.reserveRateSteady +
                P.inflationResponse * Real.log d.controls.inflation +
                P.outputResponse *
                  Real.log (localPrefixAggregateOutput P d /
                    P.outputReference)) +
            d.reserveRateInnovation)) := by
  change
    Real.log d.currentReserveRate -
      (P.reserveRatePersistence * Real.log d.lagReserveRate +
        (1 - P.reserveRatePersistence) *
          (Real.log P.reserveRateSteady +
            P.inflationResponse * Real.log d.controls.inflation +
            P.outputResponse * Real.log
              (localPrefixAggregateOutput P d / P.outputReference)) +
        d.reserveRateInnovation) = _
  exact sourceLogPolicyDeviation_eq_logRatio _ _ hR

#print axioms sourceReserveRateRule_actual_logRatio

/-- Original SOURCE reserve QUANTITY rule, OFF ROOT, is also
an exact log ratio when its current quantity is strictly positive. -/
theorem sourceReserveQuantityRule_actual_logRatio
    (P : Primitives S) (d : LocalPrefixDateData)
    (hM : 0 < d.currentReservesPre) :
    localReducedRemainingResidual P d (7 : Fin 11) =
      Real.log (d.currentReservesPre /
        Real.exp (
          P.reserveQuantityPersistence * Real.log d.lagReservesPre +
            (1 - P.reserveQuantityPersistence) *
              Real.log P.reserveQuantitySteady +
            d.reserveQuantityInnovation)) := by
  change
    Real.log d.currentReservesPre -
      (P.reserveQuantityPersistence * Real.log d.lagReservesPre +
        (1 - P.reserveQuantityPersistence) *
          Real.log P.reserveQuantitySteady +
        d.reserveQuantityInnovation) = _
  exact sourceLogPolicyDeviation_eq_logRatio _ _ hM

#print axioms sourceReserveQuantityRule_actual_logRatio

end Ventura26LiquidityAllocation

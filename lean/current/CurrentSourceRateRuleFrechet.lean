import Ventura26LiquidityAllocation.CurrentPinnedLogCoordinateFrechet
import Ventura26LiquidityAllocation.CurrentPinnedMonetaryRoots
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# SOURCE original monetary rate row: Frechet derivative from economic atoms

The original reduced SOURCE rate-policy residual is
  log(R_real) - [rho * log(R_lag)
                + (1-rho)*(log(R_steady) + phi_pi*log(pi)
                                  + phi_Y*log(Y/Ybar)) + eps_R].
This module differentiates that original expression exactly, without
assuming that the full 33-row F is differentiable.

The sole non-coordinate analytic premise in the pinned SOURCE chart
is HasFDerivAt of log(Y/Ybar) at the real stationary origin.
The production/output derivative is not falsely claimed here: it
requires its own real-firm proof (Cobb-Douglas with endogenous labor).
This is neither an infinite equilibrium nor a source/Python identity.
-/

namespace Ventura26LiquidityAllocation
namespace CurrentSourceRateRuleFrechet

open CurrentSourceFullFDeriv
open CurrentPinnedBankDomain
open CurrentPinnedLogCoordinateFrechet
open scoped Topology

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Derivative of the ORIGINAL SOURCE rate-rule residual, with the
innovation constant along the 33-dimensional endogenous chart. -/
theorem original_rate_rule_hasFDerivAt_of_atoms
    (P : Primitives S) (d : Row33 → LocalPrefixDateData)
    (x : Row33) (jReal jLag jInfl jOutput : Row33 →L[ℝ] ℝ)
    (hReal : HasFDerivAt
      (fun z : Row33 => Real.log (d z).currentReserveRate) jReal x)
    (hLag : HasFDerivAt
      (fun z : Row33 => Real.log (d z).lagReserveRate) jLag x)
    (hInfl : HasFDerivAt
      (fun z : Row33 => Real.log (d z).controls.inflation) jInfl x)
    (hOutput : HasFDerivAt
      (fun z : Row33 => Real.log
        (localPrefixAggregateOutput P (d z) / P.outputReference))
        jOutput x)
    (hInnovation : ∀ z : Row33,
      (d z).reserveRateInnovation = (d x).reserveRateInnovation) :
    HasFDerivAt
      (fun z : Row33 => localReducedRemainingResidual P (d z) 6)
      (jReal -
        (P.reserveRatePersistence • jLag +
          (1-P.reserveRatePersistence) •
            (P.inflationResponse • jInfl +
              P.outputResponse • jOutput))) x := by
  have hInner : HasFDerivAt
      (fun z : Row33 =>
        Real.log P.reserveRateSteady +
          P.inflationResponse * Real.log (d z).controls.inflation +
          P.outputResponse * Real.log
            (localPrefixAggregateOutput P (d z) / P.outputReference))
      (P.inflationResponse • jInfl +
        P.outputResponse • jOutput) x := by
    simpa only [zero_add] using
      ((hasFDerivAt_const (Real.log P.reserveRateSteady) x).add
        (hInfl.const_mul P.inflationResponse)).add
        (hOutput.const_mul P.outputResponse)
  have hInn : HasFDerivAt
      (fun z : Row33 => (d z).reserveRateInnovation)
      (0 : Row33 →L[ℝ] ℝ) x := by
    have heq :
        (fun z : Row33 => (d z).reserveRateInnovation) =
        (fun _ : Row33 => (d x).reserveRateInnovation) := by
      funext z
      exact hInnovation z
    rw [heq]
    exact hasFDerivAt_const _ _
  have hPolicy : HasFDerivAt
      (fun z : Row33 =>
        P.reserveRatePersistence * Real.log (d z).lagReserveRate +
          (1-P.reserveRatePersistence) *
            (Real.log P.reserveRateSteady +
              P.inflationResponse * Real.log (d z).controls.inflation +
              P.outputResponse * Real.log
                (localPrefixAggregateOutput P (d z) /
                  P.outputReference)) +
          (d z).reserveRateInnovation)
      (P.reserveRatePersistence • jLag +
        (1-P.reserveRatePersistence) •
          (P.inflationResponse • jInfl +
            P.outputResponse • jOutput)) x := by
    simpa only [add_zero] using
      ((hLag.const_mul P.reserveRatePersistence).add
        (hInner.const_mul (1-P.reserveRatePersistence))).add hInn
  have hDeriv := hReal.sub hPolicy
  change HasFDerivAt
      (fun z : Row33 => localReducedRemainingResidual P (d z) 6)
      (jReal -
        (P.reserveRatePersistence • jLag +
          (1-P.reserveRatePersistence) •
            (P.inflationResponse • jInfl +
              P.outputResponse • jOutput))) x at hDeriv
  exact hDeriv

#print axioms original_rate_rule_hasFDerivAt_of_atoms

/-- Both SOURCE inflation log-levels are genuine coordinates of the
33-log chart. Their Fréchet derivatives are the projections 12/28. -/
theorem pinned_two_inflation_logs_hasFDerivAt (G : ℝ) :
    HasFDerivAt
      (fun z : Row33 => Real.log (pinnedDateZero G z).controls.inflation)
      (rowCoord 12) (0 : Row33) ∧
    HasFDerivAt
      (fun z : Row33 => Real.log (pinnedDateOne G z).controls.inflation)
      (rowCoord 28) (0 : Row33) := by
  constructor
  · change HasFDerivAt
      (fun z : Row33 => Real.log
        (localPrefixCoordinatesVector fullyPinnedStationarySOURCEZ0 12 *
          Real.exp (z 12))) (rowCoord 12) (0 : Row33)
    exact pinned_log_level_hasFDerivAt 12 0
  · change HasFDerivAt
      (fun z : Row33 => Real.log
        (localPrefixCoordinatesVector fullyPinnedStationarySOURCEZ0 28 *
          Real.exp (z 28))) (rowCoord 28) (0 : Row33)
    exact pinned_log_level_hasFDerivAt 28 0

#print axioms pinned_two_inflation_logs_hasFDerivAt

/-- Date-zero lag reserves are inherited (derivative zero); date-one
lag reserve rate equals the date-zero endogenous log coordinate 5. -/
theorem pinned_two_lag_reserve_rate_logs_hasFDerivAt (G : ℝ) :
    HasFDerivAt
      (fun z : Row33 => Real.log (pinnedDateZero G z).lagReserveRate)
      (0 : Row33 →L[ℝ] ℝ) (0 : Row33) ∧
    HasFDerivAt
      (fun z : Row33 => Real.log (pinnedDateOne G z).lagReserveRate)
      (rowCoord 5) (0 : Row33) := by
  constructor
  · change HasFDerivAt
      (fun _ : Row33 => Real.log
        (ProposedStationaryInheritedState.inheritedState G).reserveRateLag)
      (0 : Row33 →L[ℝ] ℝ) (0 : Row33)
    exact hasFDerivAt_const _ _
  · change HasFDerivAt
      (fun z : Row33 => Real.log
        (localPrefixCoordinatesVector fullyPinnedStationarySOURCEZ0 5 *
          Real.exp (z 5))) (rowCoord 5) (0 : Row33)
    exact pinned_log_level_hasFDerivAt 5 0

#print axioms pinned_two_lag_reserve_rate_logs_hasFDerivAt

/-- The actual two SOURCE policy-rate donor rows have Fréchet
derivatives conditional ONLY on their TWO original product log
derivatives. Current/lag reserve rates and inflation derivatives
are proved directly using the exact SOURCE log chart. -/
theorem pinned_two_rate_rule_rows_hasFDerivAt_of_output
    (G : ℝ) (jOutput0 jOutput1 : Row33 →L[ℝ] ℝ)
    (hOutput0 : HasFDerivAt
      (fun z : Row33 =>
        Real.log (localPrefixAggregateOutput
          (ProposedStationaryPrimitives.primitives G)
          (pinnedDateZero G z) /
          (ProposedStationaryPrimitives.primitives G).outputReference))
      jOutput0 (0 : Row33))
    (hOutput1 : HasFDerivAt
      (fun z : Row33 =>
        Real.log (localPrefixAggregateOutput
          (ProposedStationaryPrimitives.primitives G)
          (pinnedDateOne G z) /
          (ProposedStationaryPrimitives.primitives G).outputReference))
      jOutput1 (0 : Row33)) :
    HasFDerivAt
      (fun z : Row33 => localReducedRemainingResidual
        (ProposedStationaryPrimitives.primitives G)
        (pinnedDateZero G z) 6)
      (rowCoord 5 -
        (1/2 : ℝ) • (0 : Row33 →L[ℝ] ℝ) -
        ((1/2 : ℝ) •
          ((3/2 : ℝ) • rowCoord 12 + (1/8 : ℝ) • jOutput0)))
      (0 : Row33) ∧
    HasFDerivAt
      (fun z : Row33 => localReducedRemainingResidual
        (ProposedStationaryPrimitives.primitives G)
        (pinnedDateOne G z) 6)
      (rowCoord 21 -
        ((1/2 : ℝ) • rowCoord 5 +
          (1/2 : ℝ) •
            ((3/2 : ℝ) • rowCoord 28 +
              (1/8 : ℝ) • jOutput1)))
      (0 : Row33) := by
  let P := ProposedStationaryPrimitives.primitives G
  obtain ⟨⟨hReal0, _⟩, ⟨hReal1, _⟩⟩ :=
    pinned_four_realized_monetary_log_hasFDerivAt G
  obtain ⟨hLag0, hLag1⟩ :=
    pinned_two_lag_reserve_rate_logs_hasFDerivAt G
  obtain ⟨hInfl0, hInfl1⟩ :=
    pinned_two_inflation_logs_hasFDerivAt G
  have hInnov0 (z : Row33) :
      (pinnedDateZero G z).reserveRateInnovation =
        (pinnedDateZero G (0 : Row33)).reserveRateInnovation := by
    rfl
  have hInnov1 (z : Row33) :
      (pinnedDateOne G z).reserveRateInnovation =
        (pinnedDateOne G (0 : Row33)).reserveRateInnovation := by
    rfl
  have h0 :=
    original_rate_rule_hasFDerivAt_of_atoms
      P (pinnedDateZero G) (0 : Row33)
      (rowCoord 5) 0 (rowCoord 12) jOutput0
      hReal0 hLag0 hInfl0 hOutput0 hInnov0
  have h1 :=
    original_rate_rule_hasFDerivAt_of_atoms
      P (pinnedDateOne G) (0 : Row33)
      (rowCoord 21) (rowCoord 5) (rowCoord 28) jOutput1
      hReal1 hLag1 hInfl1 hOutput1 hInnov1
  constructor
  · convert h0 using 1
    change (rowCoord 5 -
      (1/2 : ℝ) • (0 : Row33 →L[ℝ] ℝ) -
      (1/2 : ℝ) •
        ((3/2 : ℝ) • rowCoord 12 + (1/8 : ℝ) • jOutput0)) =
      (rowCoord 5 -
        ((1/2 : ℝ) • (0 : Row33 →L[ℝ] ℝ) +
          (1/2 : ℝ) •
            ((3/2 : ℝ) • rowCoord 12 + (1/8 : ℝ) • jOutput0)))
    abel
  · convert h1 using 1
    rfl

#print axioms pinned_two_rate_rule_rows_hasFDerivAt_of_output

end CurrentSourceRateRuleFrechet
end Ventura26LiquidityAllocation

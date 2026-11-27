import Ventura26LiquidityAllocation.CurrentPinnedMonetaryRoots
import Ventura26LiquidityAllocation.CurrentSourceCrossContinuity

/-!
# Actual SOURCE monetary rate-target continuity at the pinned 33-log origin

The original SOURCE rate policy target is the exponential of a sum of
lag-rate, inflation, aggregate-output and innovation terms.

In this module we discharge the lag-rate and inflation logarithm
continuity and monetary-innovation continuity for both genuine SOURCE
dates from their exact positive log coordinates and frozen histories.

The only remaining policy-target regularity premises are continuity
of the two aggregate-output LOG RATIO functions. These are explicitly
separated, rather than assumed under the label "F is smooth".
No SOURCE--Python identification, 33x33 inverse or dynamic equilibrium.
-/

namespace Ventura26LiquidityAllocation
namespace CurrentSourcePinnedRateTargetContinuity

open CurrentSourceFullFDeriv
open CurrentPinnedBankDomain
open CurrentSourceCrossContinuity
open scoped Topology

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- A genuine policy rate target is continuous whenever its three
logarithmic economic inputs and dated innovation are continuous.
The theorem uses the original SOURCE formula, not an auxiliary
Python equation. -/
theorem sourceRateRuleTarget_continuousAt_of_log_inputs
    {X : Type*} [TopologicalSpace X]
    (P : Primitives S) (d : X → LocalPrefixDateData) (x : X)
    (hLag : ContinuousAt
      (fun y => Real.log (d y).lagReserveRate) x)
    (hInfl : ContinuousAt
      (fun y => Real.log (d y).controls.inflation) x)
    (hOutput : ContinuousAt
      (fun y => Real.log
        (localPrefixAggregateOutput P (d y) / P.outputReference)) x)
    (hInnovation : ContinuousAt
      (fun y => (d y).reserveRateInnovation) x) :
    ContinuousAt (fun y => sourceRateRuleTarget P (d y)) x := by
  have hMiddle : ContinuousAt
      (fun y => Real.log P.reserveRateSteady +
        P.inflationResponse * Real.log (d y).controls.inflation +
        P.outputResponse *
          Real.log (localPrefixAggregateOutput P (d y) /
            P.outputReference)) x :=
    (continuousAt_const.add (continuousAt_const.mul hInfl)).add
      (continuousAt_const.mul hOutput)
  have hExponent : ContinuousAt
      (fun y => P.reserveRatePersistence *
        Real.log (d y).lagReserveRate +
        (1 - P.reserveRatePersistence) *
          (Real.log P.reserveRateSteady +
            P.inflationResponse * Real.log (d y).controls.inflation +
            P.outputResponse *
              Real.log (localPrefixAggregateOutput P (d y) /
                P.outputReference)) +
        (d y).reserveRateInnovation) x :=
    ((continuousAt_const.mul hLag).add
      (continuousAt_const.mul hMiddle)).add hInnovation
  change ContinuousAt
    (fun y => Real.exp
      (P.reserveRatePersistence * Real.log (d y).lagReserveRate +
        (1 - P.reserveRatePersistence) *
          (Real.log P.reserveRateSteady +
            P.inflationResponse * Real.log (d y).controls.inflation +
            P.outputResponse * Real.log
              (localPrefixAggregateOutput P (d y) /
                P.outputReference)) +
        (d y).reserveRateInnovation)) x
  exact Real.continuous_exp.continuousAt.comp hExponent

#print axioms sourceRateRuleTarget_continuousAt_of_log_inputs

/-- The logarithm of any positive SOURCE 33-level coordinate is
continuous at the log origin. -/
theorem pinned_log_coordinate_continuousAt (i : Fin 33) :
    ContinuousAt
      (fun z : Row33 => Real.log
        (localPrefixCoordinatesVector fullyPinnedStationarySOURCEZ0 i *
          Real.exp (z i))) (0 : Row33) := by
  have hbase :
      localPrefixCoordinatesVector fullyPinnedStationarySOURCEZ0 i *
        Real.exp ((0 : Row33) i) ≠ 0 :=
    ne_of_gt (mul_pos (fullyPinnedStationarySOURCEZ0_positive i)
      (Real.exp_pos _))
  have hlevel : ContinuousAt
      (fun z : Row33 =>
        localPrefixCoordinatesVector fullyPinnedStationarySOURCEZ0 i *
          Real.exp (z i)) (0 : Row33) :=
    continuousAt_const.mul
      (Real.continuous_exp.continuousAt.comp
        ((continuous_apply i).continuousAt))
  exact hlevel.log hbase

#print axioms pinned_log_coordinate_continuousAt

/-- Date-zero lag reserves are inherited and constant with respect
to z; date-one lag reserve rate is exactly log coordinate 5. -/
theorem pinned_two_lag_rates_log_continuousAt (G : ℝ) :
    ContinuousAt (fun z : Row33 =>
      Real.log (pinnedDateZero G z).lagReserveRate) (0 : Row33) ∧
    ContinuousAt (fun z : Row33 =>
      Real.log (pinnedDateOne G z).lagReserveRate) (0 : Row33) := by
  constructor
  · change ContinuousAt
      (fun _ : Row33 => Real.log
        (ProposedStationaryInheritedState.inheritedState G).reserveRateLag)
        (0 : Row33)
    exact continuousAt_const
  · change ContinuousAt
      (fun z : Row33 => Real.log
        (localPrefixCoordinatesVector fullyPinnedStationarySOURCEZ0 5 *
          Real.exp (z 5))) (0 : Row33)
    exact pinned_log_coordinate_continuousAt 5

#print axioms pinned_two_lag_rates_log_continuousAt

/-- Inflation belongs to log coordinates 12 and 28 on the genuine
SOURCE 33 chart in dates zero and one. -/
theorem pinned_two_inflations_log_continuousAt (G : ℝ) :
    ContinuousAt (fun z : Row33 =>
      Real.log (pinnedDateZero G z).controls.inflation) (0 : Row33) ∧
    ContinuousAt (fun z : Row33 =>
      Real.log (pinnedDateOne G z).controls.inflation) (0 : Row33) := by
  constructor
  · change ContinuousAt
      (fun z : Row33 => Real.log
        (localPrefixCoordinatesVector fullyPinnedStationarySOURCEZ0 12 *
          Real.exp (z 12))) (0 : Row33)
    exact pinned_log_coordinate_continuousAt 12
  · change ContinuousAt
      (fun z : Row33 => Real.log
        (localPrefixCoordinatesVector fullyPinnedStationarySOURCEZ0 28 *
          Real.exp (z 28))) (0 : Row33)
    exact pinned_log_coordinate_continuousAt 28

#print axioms pinned_two_inflations_log_continuousAt

/-- Both rate innovations are frozen primitive inputs with respect
to z, so they are continuous without a differentiability assumption. -/
theorem pinned_two_rate_innovations_continuousAt (G : ℝ) :
    ContinuousAt (fun z : Row33 =>
      (pinnedDateZero G z).reserveRateInnovation) (0 : Row33) ∧
    ContinuousAt (fun z : Row33 =>
      (pinnedDateOne G z).reserveRateInnovation) (0 : Row33) := by
  constructor
  · change ContinuousAt
      (fun _ : Row33 =>
        (ProposedStationaryPrimitives.primitives G).reserveRateInnovation
          (ProposedStationaryPrimitives.primitives G).tree.initial)
      (0 : Row33)
    exact continuousAt_const
  · change ContinuousAt
      (fun _ : Row33 =>
        (ProposedStationaryPrimitives.primitives G).reserveRateInnovation
          .dateOne) (0 : Row33)
    exact continuousAt_const

#print axioms pinned_two_rate_innovations_continuousAt

/-- In the actual stationary-SOURCE 33-log chart, the continuity
of both genuine monetary rate targets reduces to precisely TWO
log-output functions, not the complete SOURCE Jacobian. -/
theorem pinned_two_rate_targets_continuousAt_of_log_output
    (G : ℝ)
    (hOutput0 : ContinuousAt (fun z : Row33 =>
      Real.log (localPrefixAggregateOutput
        (ProposedStationaryPrimitives.primitives G)
        (pinnedDateZero G z) /
        (ProposedStationaryPrimitives.primitives G).outputReference))
      (0 : Row33))
    (hOutput1 : ContinuousAt (fun z : Row33 =>
      Real.log (localPrefixAggregateOutput
        (ProposedStationaryPrimitives.primitives G)
        (pinnedDateOne G z) /
        (ProposedStationaryPrimitives.primitives G).outputReference))
      (0 : Row33)) :
    ContinuousAt (fun z : Row33 =>
      sourceRateRuleTarget
        (ProposedStationaryPrimitives.primitives G)
        (pinnedDateZero G z)) (0 : Row33) ∧
    ContinuousAt (fun z : Row33 =>
      sourceRateRuleTarget
        (ProposedStationaryPrimitives.primitives G)
        (pinnedDateOne G z)) (0 : Row33) := by
  obtain ⟨hLag0, hLag1⟩ :=
    pinned_two_lag_rates_log_continuousAt G
  obtain ⟨hInfl0, hInfl1⟩ :=
    pinned_two_inflations_log_continuousAt G
  obtain ⟨hInnov0, hInnov1⟩ :=
    pinned_two_rate_innovations_continuousAt G
  constructor
  · exact sourceRateRuleTarget_continuousAt_of_log_inputs
      (ProposedStationaryPrimitives.primitives G)
      (pinnedDateZero G) (0 : Row33)
      hLag0 hInfl0 hOutput0 hInnov0
  · exact sourceRateRuleTarget_continuousAt_of_log_inputs
      (ProposedStationaryPrimitives.primitives G)
      (pinnedDateOne G) (0 : Row33)
      hLag1 hInfl1 hOutput1 hInnov1

#print axioms pinned_two_rate_targets_continuousAt_of_log_output

end CurrentSourcePinnedRateTargetContinuity
end Ventura26LiquidityAllocation

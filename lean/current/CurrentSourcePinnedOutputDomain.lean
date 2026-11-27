import Ventura26LiquidityAllocation.CurrentPinnedMonetaryRoots
import Ventura26LiquidityAllocation.CurrentSourceCrossContinuity

/-!
# Actual pinned SOURCE aggregate-output log domain

At the exact stationary SOURCE 33-log origin, the ORIGINAL aggregate
output function equals the strictly positive stationary output
witness in BOTH dates. This is not a numerical evaluation.

Consequently the two log output/references equal log 1 = 0.
When a date-wise aggregate-output function is continuous at the
pinned origin, its SOURCE log-output/reference is also continuous.
This discharges positivity and the reference-denominator conditions
without assuming anything about a Jacobian or full equilibrium.
Continuity of the aggregate output functions themselves is a separate
genuine economic regularity obligation.
-/

namespace Ventura26LiquidityAllocation
namespace CurrentSourcePinnedOutputDomain

open CurrentSourceFullFDeriv
open CurrentPinnedBankDomain
open CurrentPinnedMonetaryRoots
open scoped Topology

/-- The two genuine SOURCE dates have exactly the stationary
aggregate output, not a surrogate from Python. -/
theorem pinned_two_actual_outputs_eq_stationary (G : ℝ) :
    localPrefixAggregateOutput
      (ProposedStationaryPrimitives.primitives G)
      (pinnedDateZero G (0 : Row33)) =
        ProposedStationaryRealScale.aggregateOutput ∧
    localPrefixAggregateOutput
      (ProposedStationaryPrimitives.primitives G)
      (pinnedDateOne G (0 : Row33)) =
        ProposedStationaryRealScale.aggregateOutput := by
  have hOutput :=
    ProposedStationaryProductionBridge.localPrefixAggregateOutput_eq
      (ProposedStationaryPrimitives.primitives G)
      (ProposedStationaryPrimitives.stationary_parameters G).toStationaryRealParameters
  constructor
  · rw [pinned_actual_dateZero_eq_stationary]
    exact hOutput
  · rw [pinned_actual_dateOne_eq_stationary]
    exact hOutput

#print axioms pinned_two_actual_outputs_eq_stationary

/-- Strict positivity of both actual SOURCE output values, proved
through the same exact stationary production witness. -/
theorem pinned_two_actual_outputs_pos (G : ℝ) :
    0 < localPrefixAggregateOutput
      (ProposedStationaryPrimitives.primitives G)
      (pinnedDateZero G (0 : Row33)) ∧
    0 < localPrefixAggregateOutput
      (ProposedStationaryPrimitives.primitives G)
      (pinnedDateOne G (0 : Row33)) := by
  obtain ⟨h0, h1⟩ := pinned_two_actual_outputs_eq_stationary G
  constructor
  · rw [h0]
    exact ProposedStationaryRealScale.aggregates_pos.2.1
  · rw [h1]
    exact ProposedStationaryRealScale.aggregates_pos.2.1

#print axioms pinned_two_actual_outputs_pos

/-- The stationary SOURCE policy-output ratio equals one at both
dates, hence the actual log-output arguments equal zero. -/
theorem pinned_two_output_log_ratios_zero (G : ℝ) :
    Real.log (localPrefixAggregateOutput
      (ProposedStationaryPrimitives.primitives G)
      (pinnedDateZero G (0 : Row33)) /
      (ProposedStationaryPrimitives.primitives G).outputReference) = 0 ∧
    Real.log (localPrefixAggregateOutput
      (ProposedStationaryPrimitives.primitives G)
      (pinnedDateOne G (0 : Row33)) /
      (ProposedStationaryPrimitives.primitives G).outputReference) = 0 := by
  obtain ⟨h0, h1⟩ := pinned_two_actual_outputs_eq_stationary G
  have hpositive : ProposedStationaryRealScale.aggregateOutput ≠ 0 :=
    ne_of_gt ProposedStationaryRealScale.aggregates_pos.2.1
  constructor
  · rw [h0]
    change Real.log (ProposedStationaryRealScale.aggregateOutput /
      ProposedStationaryRealScale.aggregateOutput) = 0
    rw [div_self hpositive, Real.log_one]
  · rw [h1]
    change Real.log (ProposedStationaryRealScale.aggregateOutput /
      ProposedStationaryRealScale.aggregateOutput) = 0
    rw [div_self hpositive, Real.log_one]

#print axioms pinned_two_output_log_ratios_zero

/-- Pure SOURCE output-log continuity once output continuity is
available: denominator nonvanishing is derived from the actual
stationary primitives rather than supplied as a generic hypothesis. -/
theorem pinned_output_log_continuousAt_of_aggregate_output
    (G : ℝ) (d : Row33 → LocalPrefixDateData)
    (hDate : d (0 : Row33) = ProposedStationaryRealScale.dateData)
    (hOutput : ContinuousAt (fun z : Row33 =>
      localPrefixAggregateOutput
        (ProposedStationaryPrimitives.primitives G) (d z)) (0 : Row33)) :
    ContinuousAt (fun z : Row33 =>
      Real.log (localPrefixAggregateOutput
        (ProposedStationaryPrimitives.primitives G) (d z) /
        (ProposedStationaryPrimitives.primitives G).outputReference))
      (0 : Row33) := by
  let P := ProposedStationaryPrimitives.primitives G
  have hRef : P.outputReference ≠ 0 := by
    change ProposedStationaryRealScale.aggregateOutput ≠ 0
    exact ne_of_gt ProposedStationaryRealScale.aggregates_pos.2.1
  have hOutAt : localPrefixAggregateOutput P (d (0 : Row33)) ≠ 0 := by
    rw [hDate]
    rw [ProposedStationaryProductionBridge.localPrefixAggregateOutput_eq
      P (ProposedStationaryPrimitives.stationary_parameters G).toStationaryRealParameters]
    exact ne_of_gt ProposedStationaryRealScale.aggregates_pos.2.1
  have hRatio : ContinuousAt
      (fun z : Row33 => localPrefixAggregateOutput P (d z) /
        P.outputReference) (0 : Row33) :=
    hOutput.div continuousAt_const hRef
  have hRatioNe :
      localPrefixAggregateOutput P (d (0 : Row33)) / P.outputReference ≠ 0 :=
    div_ne_zero hOutAt hRef
  exact (Real.continuousAt_log hRatioNe).comp hRatio

#print axioms pinned_output_log_continuousAt_of_aggregate_output

/-- At the genuine two-date pinned SOURCE root, the remaining two
log-output continuity premises needed by the policy-target bridge
reduce solely to continuity of the two real aggregate-output maps. -/
theorem pinned_two_output_logs_continuousAt_of_aggregate_outputs
    (G : ℝ)
    (hOutput0 : ContinuousAt (fun z : Row33 =>
      localPrefixAggregateOutput
        (ProposedStationaryPrimitives.primitives G) (pinnedDateZero G z))
      (0 : Row33))
    (hOutput1 : ContinuousAt (fun z : Row33 =>
      localPrefixAggregateOutput
        (ProposedStationaryPrimitives.primitives G) (pinnedDateOne G z))
      (0 : Row33)) :
    ContinuousAt (fun z : Row33 =>
      Real.log (localPrefixAggregateOutput
        (ProposedStationaryPrimitives.primitives G)
        (pinnedDateZero G z) /
        (ProposedStationaryPrimitives.primitives G).outputReference))
      (0 : Row33) ∧
    ContinuousAt (fun z : Row33 =>
      Real.log (localPrefixAggregateOutput
        (ProposedStationaryPrimitives.primitives G)
        (pinnedDateOne G z) /
        (ProposedStationaryPrimitives.primitives G).outputReference))
      (0 : Row33) := by
  constructor
  · exact pinned_output_log_continuousAt_of_aggregate_output
      G (pinnedDateZero G) (pinned_actual_dateZero_eq_stationary G) hOutput0
  · exact pinned_output_log_continuousAt_of_aggregate_output
      G (pinnedDateOne G) (pinned_actual_dateOne_eq_stationary G) hOutput1

#print axioms pinned_two_output_logs_continuousAt_of_aggregate_outputs

end CurrentSourcePinnedOutputDomain
end Ventura26LiquidityAllocation

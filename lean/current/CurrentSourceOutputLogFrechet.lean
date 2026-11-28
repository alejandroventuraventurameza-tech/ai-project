import Ventura26LiquidityAllocation.CurrentSourceOutputFrechetAggregation
import Ventura26LiquidityAllocation.CurrentSourcePinnedOutputDomain
import Ventura26LiquidityAllocation.CurrentSourceRateRuleFrechet

/-!
# SOURCE output-log derivative from genuine firm derivatives

The stationary output is the same positive source object in both dates.
This bridge proves the calculus step from original SOURCE firm derivatives
to the log-output rate-rule arguments; firm derivatives remain premises.
No assumption of aggregate/log-output derivatives is introduced.
-/

namespace Ventura26LiquidityAllocation
namespace CurrentSourceOutputLogFrechet

open CurrentSourceFullFDeriv
open CurrentPinnedBankDomain
open CurrentSourceOutputFrechetAggregation
open CurrentSourcePinnedOutputDomain
open CurrentPinnedMonetaryRoots
open CurrentSourceRateRuleFrechet
open scoped Topology

/-- Taking a log of the actual SOURCE aggregate output divided by the
positive stationary reference preserves Fréchet differentiability.
The only derivative premise concerns aggregate output itself. -/
theorem pinned_output_log_differentiableAt_of_aggregate
    (G : ℝ) (d : Row33 → LocalPrefixDateData)
    (hAt : d (0 : Row33) = ProposedStationaryRealScale.dateData)
    (hY : DifferentiableAt ℝ
      (fun z : Row33 => localPrefixAggregateOutput
        (ProposedStationaryPrimitives.primitives G) (d z))
      (0 : Row33)) :
    DifferentiableAt ℝ
      (fun z : Row33 => Real.log
        (localPrefixAggregateOutput
          (ProposedStationaryPrimitives.primitives G) (d z) /
          (ProposedStationaryPrimitives.primitives G).outputReference))
      (0 : Row33) := by
  let P := ProposedStationaryPrimitives.primitives G
  have hRef : P.outputReference ≠ 0 := by
    change ProposedStationaryRealScale.aggregateOutput ≠ 0
    exact ne_of_gt ProposedStationaryRealScale.aggregates_pos.2.1
  have hYAt : localPrefixAggregateOutput P (d (0 : Row33)) ≠ 0 := by
    rw [hAt]
    rw [ProposedStationaryProductionBridge.localPrefixAggregateOutput_eq
      P (ProposedStationaryPrimitives.stationary_parameters G).toStationaryRealParameters]
    exact ne_of_gt ProposedStationaryRealScale.aggregates_pos.2.1
  have hRatio : DifferentiableAt ℝ
      (fun z : Row33 => localPrefixAggregateOutput P (d z) / P.outputReference)
      (0 : Row33) := hY.div (differentiableAt_const _) hRef
  have hRatioNe :
      localPrefixAggregateOutput P (d (0 : Row33)) / P.outputReference ≠ 0 :=
    div_ne_zero hYAt hRef
  exact hRatio.log hRatioNe

#print axioms pinned_output_log_differentiableAt_of_aggregate

/-- Both output-log functions are differentiable at the genuine SOURCE
origin whenever the four SOURCE firm outputs are differentiable. -/
theorem pinned_two_output_logs_differentiableAt_of_firms
    (G : ℝ) (jH0 jL0 jH1 jL1 : Row33 →L[ℝ] ℝ)
    (hH0 : HasFDerivAt
      (fun z : Row33 => localPrefixOutput
        (ProposedStationaryPrimitives.primitives G)
        (pinnedDateZero G z) .H) jH0 (0 : Row33))
    (hL0 : HasFDerivAt
      (fun z : Row33 => localPrefixOutput
        (ProposedStationaryPrimitives.primitives G)
        (pinnedDateZero G z) .L) jL0 (0 : Row33))
    (hH1 : HasFDerivAt
      (fun z : Row33 => localPrefixOutput
        (ProposedStationaryPrimitives.primitives G)
        (pinnedDateOne G z) .H) jH1 (0 : Row33))
    (hL1 : HasFDerivAt
      (fun z : Row33 => localPrefixOutput
        (ProposedStationaryPrimitives.primitives G)
        (pinnedDateOne G z) .L) jL1 (0 : Row33)) :
    DifferentiableAt ℝ
      (fun z : Row33 => Real.log
        (localPrefixAggregateOutput
          (ProposedStationaryPrimitives.primitives G)
          (pinnedDateZero G z) /
          (ProposedStationaryPrimitives.primitives G).outputReference))
      (0 : Row33) ∧
    DifferentiableAt ℝ
      (fun z : Row33 => Real.log
        (localPrefixAggregateOutput
          (ProposedStationaryPrimitives.primitives G)
          (pinnedDateOne G z) /
          (ProposedStationaryPrimitives.primitives G).outputReference))
      (0 : Row33) := by
  obtain ⟨hY0, hY1⟩ :=
    pinned_two_aggregate_outputs_hasFDerivAt_of_firms
      G jH0 jL0 jH1 jL1 hH0 hL0 hH1 hL1
  constructor
  · exact pinned_output_log_differentiableAt_of_aggregate G
      (pinnedDateZero G) (pinned_actual_dateZero_eq_stationary G)
      hY0.differentiableAt
  · exact pinned_output_log_differentiableAt_of_aggregate G
      (pinnedDateOne G) (pinned_actual_dateOne_eq_stationary G)
      hY1.differentiableAt

#print axioms pinned_two_output_logs_differentiableAt_of_firms

end CurrentSourceOutputLogFrechet
end Ventura26LiquidityAllocation

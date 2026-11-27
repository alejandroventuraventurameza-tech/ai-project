import Ventura26LiquidityAllocation.CurrentSourcePinnedAggregateOutputContinuity
import Ventura26LiquidityAllocation.CurrentSourcePinnedOutputDomain
import Ventura26LiquidityAllocation.CurrentSourcePinnedRateTargetContinuity
import Ventura26LiquidityAllocation.CurrentSourcePinnedQuantityTargetContinuity
import Ventura26LiquidityAllocation.CurrentSourceDepositPreSecantRegularity

/-!
# Four genuine SOURCE monetary policy donor rows: continuity without F'

The original SOURCE monetary-rate and monetary-quantity residuals
are exact logarithms of realized/target ratios whenever realized
rates and quantities are positive. That positivity is already proved
for ALL log-coordinate displacements of the pinned stationary chart.

Combine:
* genuine two-date aggregate-output continuity (Cobb-Douglas);
* positive stationary output and continuous log-output ratios;
* original reserve-rate rule target continuity;
* unconditional quantity policy targets;
* positive log-coordinate realized rate and reserves continuity.

This proves all FOUR actual monetary donor residuals continuous in
the pinned 33-dimensional SOURCE chart, with NO assumption that the
full 33-row economic map F is differentiable. The existing exact
zero values of donors follow from CurrentPinnedMonetaryRoots.

No Python surrogate, no 33x33 inverse, no infinite equilibrium.
-/

namespace Ventura26LiquidityAllocation
namespace CurrentPinnedMonetaryDonorContinuity

open CurrentSourceFullFDeriv
open CurrentPinnedBankDomain
open CurrentSourceDepositPreSecantRegularity
open scoped Topology

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Original SOURCE reserve-rate POLICY residual continuity:
the true equation is log(realized/target), not target minus realized.
Assume positive realized reserve rates for all economic inputs so
the off-root identity holds as a function equality. -/
theorem source_rate_rule_residual_continuousAt_of_atoms
    {X : Type*} [TopologicalSpace X]
    (P : Primitives S) (d : X → LocalPrefixDateData) (x : X)
    (hReal : ContinuousAt (fun y => (d y).currentReserveRate) x)
    (hTarget : ContinuousAt
      (fun y => sourceRateRuleTarget P (d y)) x)
    (hPositiveAll : ∀ y : X, 0 < (d y).currentReserveRate) :
    ContinuousAt
      (fun y => localReducedRemainingResidual P (d y) 6) x := by
  have hRatio : ContinuousAt (fun y =>
      (d y).currentReserveRate / sourceRateRuleTarget P (d y)) x :=
    hReal.div hTarget (ne_of_gt (Real.exp_pos _))
  have hRatioNe :
      (d x).currentReserveRate / sourceRateRuleTarget P (d x) ≠ 0 :=
    div_ne_zero (ne_of_gt (hPositiveAll x))
      (ne_of_gt (Real.exp_pos _))
  have hLog : ContinuousAt (fun y =>
      Real.log ((d y).currentReserveRate /
        sourceRateRuleTarget P (d y))) x := hRatio.log hRatioNe
  have hEq :
      (fun y : X => localReducedRemainingResidual P (d y) 6) =
      (fun y : X => Real.log
        ((d y).currentReserveRate / sourceRateRuleTarget P (d y))) := by
    funext y
    simpa only [sourceRateRuleTarget] using
      sourceReserveRateRule_actual_logRatio P (d y) (hPositiveAll y)
  rw [hEq]
  exact hLog

#print axioms source_rate_rule_residual_continuousAt_of_atoms

/-- Original SOURCE RESERVE QUANTITY residual continuity from the
genuine log(realized quantity / policy target) equation. No full
33-row differentiability premise is needed. -/
theorem source_quantity_rule_residual_continuousAt_of_atoms
    {X : Type*} [TopologicalSpace X]
    (P : Primitives S) (d : X → LocalPrefixDateData) (x : X)
    (hReal : ContinuousAt (fun y => (d y).currentReservesPre) x)
    (hTarget : ContinuousAt
      (fun y => sourceQuantityRuleTarget P (d y)) x)
    (hPositiveAll : ∀ y : X, 0 < (d y).currentReservesPre) :
    ContinuousAt
      (fun y => localReducedRemainingResidual P (d y) 7) x := by
  have hRatio : ContinuousAt (fun y =>
      (d y).currentReservesPre / sourceQuantityRuleTarget P (d y)) x :=
    hReal.div hTarget (ne_of_gt (Real.exp_pos _))
  have hRatioNe :
      (d x).currentReservesPre / sourceQuantityRuleTarget P (d x) ≠ 0 :=
    div_ne_zero (ne_of_gt (hPositiveAll x))
      (ne_of_gt (Real.exp_pos _))
  have hLog : ContinuousAt (fun y =>
      Real.log ((d y).currentReservesPre /
        sourceQuantityRuleTarget P (d y))) x := hRatio.log hRatioNe
  have hEq :
      (fun y : X => localReducedRemainingResidual P (d y) 7) =
      (fun y : X => Real.log
        ((d y).currentReservesPre / sourceQuantityRuleTarget P (d y))) := by
    funext y
    simpa only [sourceQuantityRuleTarget] using
      sourceReserveQuantityRule_actual_logRatio P (d y) (hPositiveAll y)
  rw [hEq]
  exact hLog

#print axioms source_quantity_rule_residual_continuousAt_of_atoms

/-- The two original SOURCE realized reserve quantities are
continuous in the logarithmic chart, coordinates 6 and 22. -/
theorem pinned_two_realized_quantities_continuousAt (G : ℝ) :
    ContinuousAt (fun z : Row33 =>
      (pinnedDateZero G z).currentReservesPre) (0 : Row33) ∧
    ContinuousAt (fun z : Row33 =>
      (pinnedDateOne G z).currentReservesPre) (0 : Row33) := by
  have hCoord (i : Fin 33) :
      ContinuousAt (fun z : Row33 =>
        localPrefixCoordinatesVector fullyPinnedStationarySOURCEZ0 i *
          Real.exp (z i)) (0 : Row33) :=
    continuousAt_const.mul
      (Real.continuous_exp.continuousAt.comp
        ((continuous_apply i).continuousAt))
  constructor
  · change ContinuousAt (fun z : Row33 =>
      localPrefixCoordinatesVector fullyPinnedStationarySOURCEZ0 6 *
        Real.exp (z 6)) (0 : Row33)
    exact hCoord 6
  · change ContinuousAt (fun z : Row33 =>
      localPrefixCoordinatesVector fullyPinnedStationarySOURCEZ0 22 *
        Real.exp (z 22)) (0 : Row33)
    exact hCoord 22

#print axioms pinned_two_realized_quantities_continuousAt

/-- Four original SOURCE monetary donor residuals are continuous
AT THE SAME ROOT, for any government bond G, without HasFDerivAt F.
The independent exact zeros at this root come from PR #52. -/
theorem pinned_four_actual_monetary_donors_continuousAt (G : ℝ) :
    (ContinuousAt (fun z : Row33 =>
      localReducedRemainingResidual
        (ProposedStationaryPrimitives.primitives G)
        (pinnedDateZero G z) 6) (0 : Row33) ∧
     ContinuousAt (fun z : Row33 =>
      localReducedRemainingResidual
        (ProposedStationaryPrimitives.primitives G)
        (pinnedDateZero G z) 7) (0 : Row33)) ∧
    (ContinuousAt (fun z : Row33 =>
      localReducedRemainingResidual
        (ProposedStationaryPrimitives.primitives G)
        (pinnedDateOne G z) 6) (0 : Row33) ∧
     ContinuousAt (fun z : Row33 =>
      localReducedRemainingResidual
        (ProposedStationaryPrimitives.primitives G)
        (pinnedDateOne G z) 7) (0 : Row33)) := by
  let P := ProposedStationaryPrimitives.primitives G
  obtain ⟨hOutput0, hOutput1⟩ :=
    CurrentSourcePinnedAggregateOutputContinuity.
      pinned_two_actual_aggregate_outputs_continuousAt G
  obtain ⟨hLog0, hLog1⟩ :=
    CurrentSourcePinnedOutputDomain.
      pinned_two_output_logs_continuousAt_of_aggregate_outputs
        G hOutput0 hOutput1
  obtain ⟨hRateTarget0, hRateTarget1⟩ :=
    CurrentSourcePinnedRateTargetContinuity.
      pinned_two_rate_targets_continuousAt_of_log_output G hLog0 hLog1
  obtain ⟨hQuantityTarget0, hQuantityTarget1⟩ :=
    CurrentSourcePinnedQuantityTargetContinuity.
      pinned_two_quantity_targets_continuousAt G
  obtain ⟨_hDeposit0, hRealRate0, _hDeposit1, hRealRate1⟩ :=
    pinned_deposit_and_reserve_coordinates_continuousAt G
  obtain ⟨hRealQuantity0, hRealQuantity1⟩ :=
    pinned_two_realized_quantities_continuousAt G
  have hRatePos0 (z : Row33) :
      0 < (pinnedDateZero G z).currentReserveRate :=
    (pinned_positive_reserve_states G z).1
  have hRatePos1 (z : Row33) :
      0 < (pinnedDateOne G z).currentReserveRate :=
    (pinned_positive_reserve_states G z).2.2.1
  have hQuantityPos0 (z : Row33) :
      0 < (pinnedDateZero G z).currentReservesPre :=
    (pinned_positive_reserve_states G z).2.1
  have hQuantityPos1 (z : Row33) :
      0 < (pinnedDateOne G z).currentReservesPre :=
    (pinned_positive_reserve_states G z).2.2.2
  exact
    ⟨⟨source_rate_rule_residual_continuousAt_of_atoms
        P (pinnedDateZero G) (0 : Row33)
        hRealRate0 hRateTarget0 hRatePos0,
       source_quantity_rule_residual_continuousAt_of_atoms
        P (pinnedDateZero G) (0 : Row33)
        hRealQuantity0 hQuantityTarget0 hQuantityPos0⟩,
     ⟨source_rate_rule_residual_continuousAt_of_atoms
        P (pinnedDateOne G) (0 : Row33)
        hRealRate1 hRateTarget1 hRatePos1,
       source_quantity_rule_residual_continuousAt_of_atoms
        P (pinnedDateOne G) (0 : Row33)
        hRealQuantity1 hQuantityTarget1 hQuantityPos1⟩⟩

#print axioms pinned_four_actual_monetary_donors_continuousAt

end CurrentPinnedMonetaryDonorContinuity
end Ventura26LiquidityAllocation

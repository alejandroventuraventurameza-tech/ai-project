import Ventura26LiquidityAllocation.CurrentPinnedMonetaryRoots
import Ventura26LiquidityAllocation.CurrentSourceCrossContinuity

/-!
# Genuine SOURCE quantity-rule target: unconditional two-date continuity

The original reserve-quantity target uses the exponential of a lagged
reserve-quantity logarithm, a stationary log target, and a frozen
dated innovation. Date-zero lagged reserve quantity is inherited,
hence constant in z. Date-one lagged reserve quantity is exactly
the state-one log chart coordinate 6, with positive basepoint.

Both actual SOURCE quantity policy targets are therefore continuous
at the pinned 33-dimensional log-chart origin, without assuming
aggregate output regularity or differentiability of the full F.
No Python or augmented-34 equivalence is claimed.
-/

namespace Ventura26LiquidityAllocation
namespace CurrentSourcePinnedQuantityTargetContinuity

open CurrentSourceFullFDeriv
open CurrentPinnedBankDomain
open scoped Topology

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The exact economic SOURCE reserve-quantity target is continuous
whenever the log lag reserves and policy innovation are continuous. -/
theorem sourceQuantityRuleTarget_continuousAt_of_log_inputs
    {X : Type*} [TopologicalSpace X]
    (P : Primitives S) (d : X → LocalPrefixDateData) (x : X)
    (hLag : ContinuousAt (fun y => Real.log (d y).lagReservesPre) x)
    (hInnov : ContinuousAt (fun y => (d y).reserveQuantityInnovation) x) :
    ContinuousAt (fun y => sourceQuantityRuleTarget P (d y)) x := by
  have hExponent : ContinuousAt
      (fun y =>
        P.reserveQuantityPersistence * Real.log (d y).lagReservesPre +
        (1 - P.reserveQuantityPersistence) *
          Real.log P.reserveQuantitySteady +
        (d y).reserveQuantityInnovation) x :=
    ((continuousAt_const.mul hLag).add continuousAt_const).add hInnov
  change ContinuousAt
    (fun y => Real.exp
      (P.reserveQuantityPersistence * Real.log (d y).lagReservesPre +
        (1 - P.reserveQuantityPersistence) *
          Real.log P.reserveQuantitySteady +
        (d y).reserveQuantityInnovation)) x
  exact Real.continuous_exp.continuousAt.comp hExponent

#print axioms sourceQuantityRuleTarget_continuousAt_of_log_inputs

/-- Exact positive SOURCE quantity target for all primitive inputs. -/
theorem sourceQuantityRuleTarget_pos (P : Primitives S)
    (d : LocalPrefixDateData) :
    0 < sourceQuantityRuleTarget P d := Real.exp_pos _

#print axioms sourceQuantityRuleTarget_pos

/-- Both log lag quantities are continuous: inherited at date zero,
positive state-one coordinate 6 at date one. -/
theorem pinned_two_lag_quantities_log_continuousAt (G : ℝ) :
    ContinuousAt (fun z : Row33 =>
      Real.log (pinnedDateZero G z).lagReservesPre) (0 : Row33) ∧
    ContinuousAt (fun z : Row33 =>
      Real.log (pinnedDateOne G z).lagReservesPre) (0 : Row33) := by
  constructor
  · change ContinuousAt (fun _ : Row33 => Real.log
      (ProposedStationaryInheritedState.inheritedState G).reservesPreLag)
      (0 : Row33)
    exact continuousAt_const
  · change ContinuousAt
      (fun z : Row33 => Real.log
        (localPrefixCoordinatesVector fullyPinnedStationarySOURCEZ0 6 *
          Real.exp (z 6))) (0 : Row33)
    have hLevel : ContinuousAt (fun z : Row33 =>
        localPrefixCoordinatesVector fullyPinnedStationarySOURCEZ0 6 *
          Real.exp (z 6)) (0 : Row33) :=
      continuousAt_const.mul
        (Real.continuous_exp.continuousAt.comp
          ((continuous_apply (6 : Fin 33)).continuousAt))
    have hNonzero :
        localPrefixCoordinatesVector fullyPinnedStationarySOURCEZ0 6 *
          Real.exp ((0 : Row33) 6) ≠ 0 :=
      ne_of_gt (mul_pos (fullyPinnedStationarySOURCEZ0_positive 6)
        (Real.exp_pos _))
    exact (Real.continuousAt_log hNonzero).comp hLevel

#print axioms pinned_two_lag_quantities_log_continuousAt

/-- The two actual monetary-quantity innovations are frozen
source primitives, not 33-dimensional endogenous coordinates. -/
theorem pinned_two_quantity_innovations_continuousAt (G : ℝ) :
    ContinuousAt (fun z : Row33 =>
      (pinnedDateZero G z).reserveQuantityInnovation) (0 : Row33) ∧
    ContinuousAt (fun z : Row33 =>
      (pinnedDateOne G z).reserveQuantityInnovation) (0 : Row33) := by
  constructor
  · change ContinuousAt
      (fun _ : Row33 =>
        (ProposedStationaryPrimitives.primitives G).reserveQuantityInnovation
          (ProposedStationaryPrimitives.primitives G).tree.initial)
      (0 : Row33)
    exact continuousAt_const
  · change ContinuousAt
      (fun _ : Row33 =>
        (ProposedStationaryPrimitives.primitives G).reserveQuantityInnovation
          .dateOne) (0 : Row33)
    exact continuousAt_const

#print axioms pinned_two_quantity_innovations_continuousAt

/-- Unconditional continuity of both original SOURCE quantity targets
at the pinned stationary log origin, for every fiscal fiber G. -/
theorem pinned_two_quantity_targets_continuousAt (G : ℝ) :
    ContinuousAt (fun z : Row33 =>
      sourceQuantityRuleTarget
        (ProposedStationaryPrimitives.primitives G)
        (pinnedDateZero G z)) (0 : Row33) ∧
    ContinuousAt (fun z : Row33 =>
      sourceQuantityRuleTarget
        (ProposedStationaryPrimitives.primitives G)
        (pinnedDateOne G z)) (0 : Row33) := by
  obtain ⟨hLag0, hLag1⟩ :=
    pinned_two_lag_quantities_log_continuousAt G
  obtain ⟨hInnov0, hInnov1⟩ :=
    pinned_two_quantity_innovations_continuousAt G
  constructor
  · exact sourceQuantityRuleTarget_continuousAt_of_log_inputs
      (ProposedStationaryPrimitives.primitives G)
      (pinnedDateZero G) (0 : Row33) hLag0 hInnov0
  · exact sourceQuantityRuleTarget_continuousAt_of_log_inputs
      (ProposedStationaryPrimitives.primitives G)
      (pinnedDateOne G) (0 : Row33) hLag1 hInnov1

#print axioms pinned_two_quantity_targets_continuousAt

end CurrentSourcePinnedQuantityTargetContinuity
end Ventura26LiquidityAllocation

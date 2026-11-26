import Ventura26LiquidityAllocation.CurrentPinnedStationaryFundingDual
import Ventura26LiquidityAllocation.SourceFundingDualPositiveLogRegularityCandidate

/-!
# Strict binding neighborhood around the exact stationary SOURCE root

PR #32 certifies that the binding branch of the finite 33-equation
SOURCE prefix vanishes at the pinned stationary origin.
PR #34 certifies that the SAME origin has firm-L normalized funding
dual strictly positive, hence it is not an augmented 34-row zero.

This module strengthens the second fact from a single coordinate
point to an entire (not quantitatively sized) neighborhood. It uses
the existing kernel-proven differentiability of the literal SOURCE
funding-dual function on positive log coordinates.

No fixed-policy SOURCE 34-root is ruled out outside this neighborhood,
no distinct slack equilibrium is constructed, and no local inverse
function theorem or dynamic equilibrium is asserted.
-/

namespace Ventura26LiquidityAllocation
namespace CurrentPinnedStrictBindingNeighborhood

open CurrentPinnedStationaryDual
open ProposedLocalScalarAugmented34Source
open Filter
open scoped Topology

/-- The true SOURCE normalized L funding dual remains strictly
positive for all nearby log-coordinate vectors, independently of
the government bond parameter G in the pinned construction. -/
theorem pinned_stationary_funding_dual_eventually_pos (G : ℝ) :
    ∀ᶠ z : Fin 33 → ℝ in 𝓝 (0 : Fin 33 → ℝ),
      0 < localNormalizedCollateralDualL
        (ProposedStationaryPrimitives.primitives G)
        (localPrefixLogChart fullyPinnedStationarySOURCEZ0 z) := by
  have hZ0 : LocalPrefixCoordinatesPositive
      fullyPinnedStationarySOURCEZ0 :=
    fullyPinnedStationarySOURCEZ0_positive
  have hdiff : DifferentiableAt ℝ
      (fun z : Fin 33 → ℝ =>
        localNormalizedCollateralDualL
          (ProposedStationaryPrimitives.primitives G)
          (localPrefixLogChart fullyPinnedStationarySOURCEZ0 z))
      (0 : Fin 33 → ℝ) :=
    sourceFundingDual_differentiableAt_positive_log
      (ProposedStationaryPrimitives.primitives G)
      fullyPinnedStationarySOURCEZ0 hZ0 (0 : Fin 33 → ℝ)
  have hpos :
      0 < localNormalizedCollateralDualL
        (ProposedStationaryPrimitives.primitives G)
        (localPrefixLogChart fullyPinnedStationarySOURCEZ0
          (0 : Fin 33 → ℝ)) :=
    pinned_stationary_funding_dual_pos G
  exact hdiff.continuousAt.eventually_mem
    (isOpen_Ioi.mem_nhds hpos)

#print axioms pinned_stationary_funding_dual_eventually_pos

/-- There is an entire stationary log-coordinate neighborhood
without any 34-row dual-zero SOURCE boundary root, for ANY
reserve-remuneration innovation h at fixed z in that neighborhood.
The neighborhood need not be valid for large endogenous movements. -/
theorem pinned_stationary_SOURCE34_not_root_eventually (G : ℝ) :
    ∀ᶠ z : Fin 33 → ℝ in 𝓝 (0 : Fin 33 → ℝ),
      ∀ h : ℝ, fullyPinnedStationaryP0SOURCE34 G z h ≠ (0, 0) := by
  filter_upwards [pinned_stationary_funding_dual_eventually_pos G] with z hz
  intro h
  change augmentedBoundaryZeroResidual
    (ProposedStationaryPrimitives.primitives G)
    (ProposedStationaryInheritedState.inheritedState G)
    fullyPinnedStationarySOURCEZ0
    .dateOne .recurrent
    (sourceLogLinearContinuation
      ProposedStationaryRealScale.stateSix
      ProposedStationaryRealScale.controls
      sourceFrozenP0TenControls)
    z h ≠ (0, 0)
  exact augmentedBoundary_not_root_of_source_funding_dual_pos
    (ProposedStationaryPrimitives.primitives G)
    (ProposedStationaryInheritedState.inheritedState G)
    fullyPinnedStationarySOURCEZ0 .dateOne .recurrent
    (sourceLogLinearContinuation
      ProposedStationaryRealScale.stateSix
      ProposedStationaryRealScale.controls
      sourceFrozenP0TenControls)
    z h hz

#print axioms pinned_stationary_SOURCE34_not_root_eventually

end CurrentPinnedStrictBindingNeighborhood
end Ventura26LiquidityAllocation

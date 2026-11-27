import Ventura26LiquidityAllocation.CurrentPinnedJointQuantitativeBall
import Ventura26LiquidityAllocation.CurrentPinnedFiscalFiberWitness

/-!
# A nonzero lower bound on the distance to any SOURCE 34-row boundary root

This module puts two prior kernel-checked SOURCE certificates at the
SAME stationary fiscal witness:
* exact 33-row binding root at z=0, with G=2*Mpre and accounting closure;
* explicit joint SOURCE banking/strict-funding-dual radius r_joint > 0.

Every possible 34-row dual-zero root (z,h) for the selected fiscal
witness must lie OUTSIDE the open ball ‖z‖ < r_joint. The policy shock
h is unrestricted. This is a necessary displacement condition only,
not existence or uniqueness of such a switching root, not a causal
bound on a policy shock, and not an infinite-horizon equilibrium.
-/

namespace Ventura26LiquidityAllocation
namespace CurrentPinnedBoundaryDistance

open CurrentPinnedJointQuantitativeBall
open CurrentPinnedFiscalFiber
open CurrentPinnedQuantitativeBank
open CurrentPinnedOpenBankDomain
open CurrentPinnedBankDomain
open CurrentSourceFullFDeriv
open CurrentSourceTwoDateBank

/-- Any SOURCE 34-row switching boundary at the concrete fiscal
witness must move the endogenous 33-log-vector by at least r_joint.
The result holds for EVERY policy innovation h in the same residual. -/
theorem pinnedFiscal_boundary_root_log_distance (z : Row33) (h : ℝ)
    (hroot : fullyPinnedStationaryP0SOURCE34 pinnedFiscalG z h = (0, 0)) :
    pinnedJointRadius ≤ ‖z‖ := by
  by_contra hnot
  have hnear : ‖z‖ < pinnedJointRadius := lt_of_not_ge hnot
  exact (pinned_SOURCE34_not_root_in_joint_ball
    pinnedFiscalG z hnear h) hroot

#print axioms pinnedFiscal_boundary_root_log_distance

/-- On the explicit common ball the ACTUAL SOURCE date-zero and date-one
banking domain holds and the original normalized L funding dual is positive.
This does not identify the bank-row Jacobian, nor assert optimality. -/
theorem pinnedFiscal_joint_ball_domain (z : Row33)
    (hz : ‖z‖ < pinnedJointRadius) :
    TargetBankAdmissible
        (ProposedStationaryPrimitives.primitives pinnedFiscalG)
        (pinnedDateZero pinnedFiscalG z) ∧
      TargetBankAdmissible
        (ProposedStationaryPrimitives.primitives pinnedFiscalG)
        (pinnedDateOne pinnedFiscalG z) ∧
      0 < localNormalizedCollateralDualL
        (ProposedStationaryPrimitives.primitives pinnedFiscalG)
        (localPrefixLogChart fullyPinnedStationarySOURCEZ0 z) := by
  have hhalf : ‖z‖ < Real.log 2 / 2 :=
    lt_of_lt_of_le hz (min_le_left _ _)
  have hreg : z ∈ pinnedBankLogRegion :=
    pinned_half_log_ball_subset_bank_region z hhalf
  have hadm := pinned_both_dates_bank_admissible
    pinnedFiscalG z hreg.1 hreg.2
  exact ⟨hadm.1, hadm.2,
    pinned_funding_dual_pos_in_joint_ball pinnedFiscalG z hz⟩

#print axioms pinnedFiscal_joint_ball_domain

/-- One bundled finite-SOURCE certificate at a FIXED fiscal witness:
a root of the binding 33 rows, primitive monetary admissibility,
accounting fiscal closure, and a strictly positive exclusion radius
for all augmented 34-row switching roots. This is deliberately NOT
an Equilibrium existence theorem. -/
theorem pinnedFiscal_finite_local_separation :
    (localReducedPrefixLogResidualVector .binding
      (ProposedStationaryPrimitives.primitives pinnedFiscalG)
      (ProposedStationaryInheritedState.inheritedState pinnedFiscalG)
      fullyPinnedStationarySOURCEZ0 .dateOne .recurrent
      (sourceLogLinearContinuation
        ProposedStationaryRealScale.stateSix
        ProposedStationaryRealScale.controls
        sourceFrozenP0TenControls)
      (0 : Fin 33 → ℝ) = 0) ∧
    MonetaryPolicyPrimitiveDomain
      (ProposedStationaryPrimitives.primitives pinnedFiscalG)
      (ProposedStationaryInheritedState.inheritedState pinnedFiscalG) ∧
    FiscalClosure
      (ProposedStationaryPrimitives.primitives pinnedFiscalG)
      (ProposedStationaryInheritedState.inheritedState pinnedFiscalG)
      (ProposedStationaryInheritedState.parentAllocation pinnedFiscalG) ∧
    (0 < pinnedJointRadius) ∧
    (∀ (z : Row33) (h : ℝ),
      fullyPinnedStationaryP0SOURCE34 pinnedFiscalG z h = (0, 0) →
        pinnedJointRadius ≤ ‖z‖) := by
  exact ⟨pinnedFiscalG_binding_prefix33_root,
    pinnedFiscalG_monetary_domain,
    pinnedFiscalG_carrier_fiscal_closure,
    pinnedJointRadius_pos,
    fun z h hz => pinnedFiscal_boundary_root_log_distance z h hz⟩

#print axioms pinnedFiscal_finite_local_separation

end CurrentPinnedBoundaryDistance
end Ventura26LiquidityAllocation

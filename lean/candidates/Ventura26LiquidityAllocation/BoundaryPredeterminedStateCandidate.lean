import Ventura26LiquidityAllocation.BoundaryInheritedFaceMechanismCandidate

/-!
# Predetermined inherited positions: a formal counterfactual gate

The stationary predecessor has a consistent inherited nominal-face identity.
An intervention in date-zero policy primitives preserves this exact *inherited
accounting gap* when the inherited state is held fixed.

By contrast the old SOURCE boundary constructor differs from the stationary
predecessor at the bank-face field, already for the certified source root.
Thus its candidate date-zero state cannot be identified with the frozen
stationary predecessor. This is a rigorous negative audit, not a proof that
any new full infinite-horizon equilibrium exists.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedBoundaryPredeterminedState

open ProposedStationaryBank
open ProposedStationaryPrimitives
open ProposedStationaryInheritedState
open ProposedStationaryRealScale
open ProposedBoundaryNormalizationBridge
open ProposedBoundaryFullPrefix
open ProposedBoundaryInheritedFaceGate
open ProposedBoundaryInheritedFaceDecomposition
open ProposedBoundaryInheritedFaceMechanism

/-- The stationary predecessor has zero inherited nominal-face residual.
The equality is inherited directly from the original consistency theorem. -/
theorem stationary_inherited_gap_zero (G : ℝ) :
    inheritedNominalFaceGap (primitives G) (inheritedState G) = 0 := by
  exact
    (inheritedNominalFaceConsistency_iff_gap_zero
      (primitives G) (inheritedState G)
      (inherited_nominalFaceConsistency G).1).mp
      (inherited_nominalFaceConsistency G)

/-- The exact inherited-face accounting gap remains zero under an initial
policy innovation when the stationary predecessor is frozen. It is only
this inherited identity, not a complete set of equilibrium conditions. -/
theorem frozen_stationary_gap_zero_after_intervention
    (G : ℝ) (v : InitialPolicyIntervention) :
    inheritedNominalFaceGap
      (initialIntervenedPrimitives (primitives G) v)
      (inheritedState G) = 0 := by
  rw [inheritedNominalFaceGap_initialIntervention_invariant]
  exact stationary_inherited_gap_zero G

/-- Any two date-zero monetary interventions have exactly the same
inherited nominal-face residual when the predecessor state is identical.
No equilibrium, optimality or endogenous trajectory is asserted. -/
theorem same_inherited_state_gap_independent_of_policy
    (P : Primitives LocalBridgePhase) (I : InheritedState)
    (v₁ v₂ : InitialPolicyIntervention) :
    inheritedNominalFaceGap (initialIntervenedPrimitives P v₁) I =
      inheritedNominalFaceGap (initialIntervenedPrimitives P v₂) I := by
  calc
    inheritedNominalFaceGap (initialIntervenedPrimitives P v₁) I =
        inheritedNominalFaceGap P I :=
      inheritedNominalFaceGap_initialIntervention_invariant P I v₁
    _ = inheritedNominalFaceGap (initialIntervenedPrimitives P v₂) I :=
      (inheritedNominalFaceGap_initialIntervention_invariant P I v₂).symm

/-- Likewise, inherited nominal-face consistency is identical across two
policy innovations with a fixed predecessor. This concerns one necessary
equilibrium accounting condition, not complete equilibria. -/
theorem same_inherited_state_consistency_iff
    (P : Primitives LocalBridgePhase) (I : InheritedState)
    (v₁ v₂ : InitialPolicyIntervention) :
    InheritedNominalFaceConsistency (initialIntervenedPrimitives P v₁) I ↔
      InheritedNominalFaceConsistency (initialIntervenedPrimitives P v₂) I := by
  exact
    (ProposedBoundaryFrozenInheritance.initialIntervention_inheritedNominalFaceConsistency_iff P I v₁).trans
      (ProposedBoundaryFrozenInheritance.initialIntervention_inheritedNominalFaceConsistency_iff P I v₂).symm

/-- The old SOURCE inherited-state constructor fails to preserve the
stationary predecessor throughout the ENTIRE certified boundary rate
interval, rather than only at the named SOURCE root. The discrepancy is
in the bank-face field, independently of the fiscal parameter. -/
theorem boundary_initial_state_ne_stationary_for_all_boundary_rates
    (G R : ℝ)
    (hR : R ∈ ProposedBoundaryResourceRoot.boundaryInterval) :
    boundaryInitialState G R ≠ inheritedState G := by
  intro hstate
  have hface := congrArg InheritedState.bankFace hstate
  change boundaryBankEquity R = bankEquity at hface
  have hlt : boundaryBankEquity R < bankEquity :=
    boundaryBankFace_lt_stationary R hR
  exact (ne_of_lt hlt) hface

/-- The old SOURCE constructor changes at least the bank face of the
inherited state: its boundary loan rate exceeds the stationary rate.
This disqualifies identification of that constructor with a common
predetermined stationary state in the unanticipated-shock comparison. -/
theorem source_boundary_initial_state_ne_stationary_predecessor (G : ℝ) :
    boundaryInitialState G boundarySourceRate ≠ inheritedState G := by
  intro hstate
  have hface := congrArg InheritedState.bankFace hstate
  change boundaryBankEquity boundarySourceRate = bankEquity at hface
  have hlt : boundaryBankEquity boundarySourceRate < bankEquity :=
    boundaryBankFace_lt_stationary boundarySourceRate
      ⟨boundarySourceRate_spec.1, boundarySourceRate_spec.2.1⟩
  exact (ne_of_lt hlt) hface

#print axioms stationary_inherited_gap_zero
#print axioms frozen_stationary_gap_zero_after_intervention
#print axioms same_inherited_state_gap_independent_of_policy
#print axioms same_inherited_state_consistency_iff
#print axioms boundary_initial_state_ne_stationary_for_all_boundary_rates
#print axioms source_boundary_initial_state_ne_stationary_predecessor

end ProposedBoundaryPredeterminedState
end Ventura26LiquidityAllocation

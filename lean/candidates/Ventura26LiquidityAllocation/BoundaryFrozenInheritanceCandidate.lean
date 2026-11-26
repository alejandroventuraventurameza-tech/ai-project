import Ventura26LiquidityAllocation.BoundaryInheritedFaceIntervalBridgeCandidate

/-!
# Fixed inherited financial state under the four-instrument policy intervention

The source intervention vector modifies only date-zero reserve-remuneration
innovation, reserve-quantity innovation, reserve requirement and corridor
width. It does NOT modify the predetermined installed capital or nominal
faces. These facts below are source-level definitional invariants.

This establishes a valid inherited-data starting point for a *new*
reduced-to-literal equilibrium construction; it does not claim that the
previous boundary rate solves the new system or establishes optimality.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedBoundaryFrozenInheritance

open ProposedStationaryPrimitives
open ProposedStationaryInheritedState

/-- A genuine four-instrument intervention leaves the bank retention /
renewal factor unchanged. It modifies current and announced policy
variables, not the bank's inherited equity-return contract. -/
theorem initialIntervention_bankRenewalFactor_eq
    (P : Primitives LocalBridgePhase) (v : InitialPolicyIntervention) :
    bankRenewalFactor (initialIntervenedPrimitives P v) =
      bankRenewalFactor P := by
  rfl

/-- The literal source initial nominal-face consistency is exactly
invariant when the same inherited state I is held fixed.
This is not an appeal to Walras law or to the reduced 33 rows. -/
theorem initialIntervention_inheritedNominalFaceConsistency_iff
    (P : Primitives LocalBridgePhase) (I : InheritedState)
    (v : InitialPolicyIntervention) :
    InheritedNominalFaceConsistency (initialIntervenedPrimitives P v) I ↔
      InheritedNominalFaceConsistency P I := by
  rfl

/-- The primitive domain of monetary references and inherited quantities
is unchanged by shocks to the *date-zero* instruments. It does not
assert positivity of endogenous reserve rates after an intervention. -/
theorem initialIntervention_monetaryPrimitiveDomain_iff
    (P : Primitives LocalBridgePhase) (I : InheritedState)
    (v : InitialPolicyIntervention) :
    MonetaryPolicyPrimitiveDomain (initialIntervenedPrimitives P v) I ↔
      MonetaryPolicyPrimitiveDomain P I := by
  rfl

/-- By contrast, the old SOURCE boundary constructor makes inherited
capital STRICTLY rate-dependent. Thus different boundary loan-rate
candidates cannot represent surprises applied to a common predetermined
capital state. This is an economic interpretation of the original code,
not an impossibility claim about a different fixed-inheritance model. -/
theorem boundaryInitialState_capital_strictMono
    (G R₁ R₂ : ℝ) (i : FirmType)
    (h₁ : R₁ ∈ ProposedBoundaryResourceRoot.boundaryInterval)
    (h₂ : R₂ ∈ ProposedBoundaryResourceRoot.boundaryInterval)
    (hRate : R₁ < R₂) :
    (ProposedBoundaryFullPrefix.boundaryInitialState G R₁).capital i <
      (ProposedBoundaryFullPrefix.boundaryInitialState G R₂).capital i := by
  change ProposedBoundaryResourceRoot.boundaryCapital R₁ i <
    ProposedBoundaryResourceRoot.boundaryCapital R₂ i
  unfold ProposedBoundaryResourceRoot.boundaryCapital
  exact mul_lt_mul_of_pos_right
    (ProposedBoundaryAnalyticPackage.capitalScale_strictMonoOn h₁ h₂ hRate)
    (ProposedStationaryRealScale.capital_pos i)

/-- For the already certified stationary inherited balance sheet,
all four source policy instruments preserve exact date-zero nominal
compatibility without adjusting deposits, inherited firm faces, capital,
or government bonds as endogenous residuals. -/
theorem stationaryInheritedState_consistent_under_initialIntervention
    (G : ℝ) (v : InitialPolicyIntervention) :
    InheritedNominalFaceConsistency
      (initialIntervenedPrimitives
        (ProposedStationaryPrimitives.primitives G) v)
      (ProposedStationaryInheritedState.inheritedState G) := by
  exact
    (initialIntervention_inheritedNominalFaceConsistency_iff
      (ProposedStationaryPrimitives.primitives G)
      (ProposedStationaryInheritedState.inheritedState G) v).2
      (ProposedStationaryInheritedState.inherited_nominalFaceConsistency G)

#print axioms initialIntervention_bankRenewalFactor_eq
#print axioms initialIntervention_inheritedNominalFaceConsistency_iff
#print axioms initialIntervention_monetaryPrimitiveDomain_iff
#print axioms boundaryInitialState_capital_strictMono
#print axioms stationaryInheritedState_consistent_under_initialIntervention

end ProposedBoundaryFrozenInheritance
end Ventura26LiquidityAllocation

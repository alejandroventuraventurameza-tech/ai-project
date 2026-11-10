import Ventura26LiquidityAllocation.FirmFaceUniformGapCandidate
import Ventura26LiquidityAllocation.BoundaryPredeterminedStateCandidate

/-!
# Predetermined-state monetary impact: literal 4-tool source interface

The previous SOURCE boundary constructor changed the inherited capital,
inherited entrepreneurial promises, and bank face with R. Its conditional
reduced prefix is not an unanticipated monetary experiment. This module
sets the initial state to the exact stationary predecessor `inheritedState G`
and applies only `initialIntervenedPrimitives` to the existing source
primitives. Date-zero controls and all 33 reduced-prefix coordinates remain
endogenous: the theorems here DO NOT solve the new equilibrium.

The first results specify the correct date-zero *data*, separately for
all four instruments, and certify that there is no automatic date-one
counter-shock. A further inequality exposes the strict inherited-capital
discrepancy in the previously constructed SOURCE root bracket.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedFrozenInheritanceImpactPrefix

open ProposedStationaryPrimitives
open ProposedStationaryInheritedState
open ProposedStationaryRealScale
open ProposedBoundaryResourceRoot
open ProposedBoundaryFullPrefix
open ProposedBoundaryAnalyticPackage
open ProposedBoundaryNarrowRightCore
open ProposedBoundaryPredeterminedState
open ProposedBoundaryFrozenInheritance

/-- A literal zero-date intervention in four instruments. This does
NOT replace the source `boundaryPrimitives`, which also specified
date-one innovations to return to stationarity. -/
noncomputable def impactPrimitives (G : ℝ)
    (v : InitialPolicyIntervention) : Primitives LocalBridgePhase :=
  initialIntervenedPrimitives (primitives G) v

/-- The 33-coordinate finite prefix, with the *unchanged* initial
capital and nominal promises of the stationary predecessor. -/
noncomputable def impactDateZero (G : ℝ)
    (v : InitialPolicyIntervention)
    (Z : LocalPrefixCoordinates) : LocalPrefixDateData :=
  localPrefixDateZeroData (impactPrimitives G v)
    (inheritedState G) Z .dateOne

noncomputable def impactDateOne (G : ℝ)
    (v : InitialPolicyIntervention)
    (Z : LocalPrefixCoordinates)
    (tail : LocalPrefixContinuationRule) : LocalPrefixDateData :=
  localPrefixDateOneData (impactPrimitives G v)
    Z .dateOne .recurrent tail

/-- All five predetermined carrier fields enter the literal date-zero
reduced data without updating them in response to the shock. -/
theorem dateZero_predetermined_fields_exact
    (G : ℝ) (v : InitialPolicyIntervention)
    (Z : LocalPrefixCoordinates) :
    (impactDateZero G v Z).currentCapital = capital ∧
    (impactDateZero G v Z).inheritedFace = firmFace ∧
    (impactDateZero G v Z).currentBankFace = bankEquity ∧
    (impactDateZero G v Z).lagReserveRate =
      ProposedStationaryBank.reserveRate ∧
    (impactDateZero G v Z).lagReservesPre = reservesPre := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The four level changes enter precisely their original date-zero
source fields, not inherited capital, nominal promises, or prices. -/
theorem dateZero_four_instruments_exact
    (G : ℝ) (v : InitialPolicyIntervention)
    (Z : LocalPrefixCoordinates) :
    (impactDateZero G v Z).reserveRateInnovation =
        v.reserveRateInnovation ∧
    (impactDateZero G v Z).reserveQuantityInnovation =
        v.reserveQuantityInnovation ∧
    (impactDateZero G v Z).reserveRequirement =
        (1 / 10 : ℝ) + v.reserveRequirement ∧
    (impactDateZero G v Z).corridorWidth =
        (1 / 50 : ℝ) + v.corridorWidth := by
  simp [impactDateZero, impactPrimitives, localPrefixDateZeroData,
    initialIntervenedPrimitives, primitives, localBridgeTree,
    bridgeDateZeroHistory]

/-- The source InitialPolicyIntervention is *transitory* in the literal
calendar. No extra date-one announcement is chosen to force the
old boundary path's return to stationarity. -/
theorem dateOne_four_instruments_unperturbed
    (G : ℝ) (v : InitialPolicyIntervention)
    (Z : LocalPrefixCoordinates)
    (tail : LocalPrefixContinuationRule) :
    (impactDateOne G v Z tail).reserveRateInnovation = 0 ∧
    (impactDateOne G v Z tail).reserveQuantityInnovation = 0 ∧
    (impactDateOne G v Z tail).reserveRequirement =
        (1 / 10 : ℝ) ∧
    (impactDateOne G v Z tail).corridorWidth =
        (1 / 50 : ℝ) := by
  simp [impactDateOne, impactPrimitives, localPrefixDateOneData,
    initialIntervenedPrimitives, primitives, localBridgeTree,
    bridgeDateOneHistory]

/-- The inherited nominal-face accounting identity is unchanged by
any four-instrument date-zero surprise, independent of any assumed
equilibrium path or rate response. -/
theorem inherited_nominal_faces_consistent_for_every_intervention
    (G : ℝ) (v : InitialPolicyIntervention) :
    InheritedNominalFaceConsistency
      (impactPrimitives G v) (inheritedState G) :=
  stationaryInheritedState_consistent_under_initialIntervention G v

/-- A dedicated monetary-vector interface for comparing the old
boundary construction with a *pure date-zero* experiment. The
date-one source policy rules are not copied from the old construction. -/
noncomputable def sourceLikeDateZeroShock (R : ℝ) :
    InitialPolicyIntervention where
  reserveRateInnovation := boundaryReserveRateInnovationZero R
  reserveQuantityInnovation := boundaryReserveQuantityInnovationZero R
  reserveRequirement := 0
  corridorWidth := 0

theorem sourceLike_dateZero_innovation_fields
    (G R : ℝ) (Z : LocalPrefixCoordinates) :
    (impactDateZero G (sourceLikeDateZeroShock R) Z).reserveRateInnovation =
      boundaryReserveRateInnovationZero R ∧
    (impactDateZero G (sourceLikeDateZeroShock R) Z).reserveQuantityInnovation =
      boundaryReserveQuantityInnovationZero R := by
  simpa [sourceLikeDateZeroShock] using
    (dateZero_four_instruments_exact G (sourceLikeDateZeroShock R) Z).1
      |>.and
        (dateZero_four_instruments_exact G (sourceLikeDateZeroShock R) Z).2.1

/-- The old SOURCE root bracket has impact-installed capital
STRICTLY BELOW the stationary predecessor's inherited capital.
This disproves the interpretation that the old SOURCE state was
held fixed before a surprise; the inequality is uniform and
independent of fiscal G and of firm type. -/
theorem moving_SOURCE_capital_below_frozen_predecessor
    (G R : ℝ) (i : FirmType)
    (hlo : (1029135 / 1000000 : ℝ) ≤ R)
    (hhi : R ≤ (1029136 / 1000000 : ℝ)) :
    (boundaryInitialState G R).capital i <
      (inheritedState G).capital i := by
  have hRmem : R ∈ boundaryInterval := by
    change boundaryLo ≤ R ∧ R ≤ boundaryHi
    constructor
    · exact le_trans (by norm_num [boundaryLo]) hlo
    · exact le_trans hhi (by norm_num [boundaryHi])
  have hRight :
      (1029136 / 1000000 : ℝ) ∈ boundaryInterval := by
    change boundaryLo ≤ (1029136 / 1000000 : ℝ) ∧
      (1029136 / 1000000 : ℝ) ≤ boundaryHi
    norm_num [boundaryLo, boundaryHi]
  have hScaleLe :
      boundaryCapitalScale R ≤
        boundaryCapitalScale (1029136 / 1000000 : ℝ) := by
    rcases lt_or_eq_of_le hhi with hlt | heq
    · exact (capitalScale_strictMonoOn hRmem hRight hlt).le
    · rw [heq]
  have hScaleLt : boundaryCapitalScale R < (1 : ℝ) :=
    lt_trans
      (lt_of_le_of_lt hScaleLe source_narrow_right_capital_scale_box.2)
      (by norm_num)
  change boundaryCapitalScale R * capital i < capital i
  simpa only [one_mul] using
    (mul_lt_mul_of_pos_right hScaleLt (capital_pos i))

/-- The distinction is visible directly in the original literal
date-zero data, not only in a notional inherited-state comparison:
the old SOURCE constructor initializes with a strictly smaller
capital stock than the genuinely frozen impact problem. -/
theorem boundary_versus_frozen_dateZero_capital
    (G R : ℝ) (i : FirmType)
    (hlo : (1029135 / 1000000 : ℝ) ≤ R)
    (hhi : R ≤ (1029136 / 1000000 : ℝ)) :
    (boundaryZeroData G R).currentCapital i <
      (impactDateZero G
        (sourceLikeDateZeroShock R) (boundaryCoordinates R)).currentCapital i := by
  have h := moving_SOURCE_capital_below_frozen_predecessor G R i hlo hhi
  change boundaryCapital R i < capital i
  exact h

#print axioms dateZero_predetermined_fields_exact
#print axioms dateZero_four_instruments_exact
#print axioms dateOne_four_instruments_unperturbed
#print axioms inherited_nominal_faces_consistent_for_every_intervention
#print axioms sourceLike_dateZero_innovation_fields
#print axioms moving_SOURCE_capital_below_frozen_predecessor
#print axioms boundary_versus_frozen_dateZero_capital

end ProposedFrozenInheritanceImpactPrefix
end Ventura26LiquidityAllocation

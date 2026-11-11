import Ventura26LiquidityAllocation.StationaryPrimitivesCandidate
import Ventura26LiquidityAllocation.StationaryInheritedStateCandidate
import Ventura26LiquidityAllocation.HandStencilPledgeRowEquivalenceCandidate

/-!
# Policy intervention on the genuine SOURCE stationary primitives

This is NOT a new stationary primitive witness.  It applies the SOURCE
date-zero intervention to the already-constructed \`Primitives LocalBridgePhase\`
in StationaryPrimitivesCandidate, retaining the *same* binary payment law
and core bank/technology parameters.  It then proves exact SOURCE-level
finite-row identities corresponding to the Python illustration.

Scope: algebraic payment moments, reserve/deposit ratio, bank renewal
factor and the low-tightness OTC functions at fixed positive dates.
No Python execution occurs in Lean, no 33-row operator equivalence,
bank optimization, TVC or infinite equilibrium is inferred.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedStationaryInterventionSourceBridge

open ProposedStationaryPrimitives

/-- Apply all four SOURCE policy instruments to the actual stationary
Primitives instance without making a new payment distribution. -/
noncomputable def intervenedPrimitives
    (G : ℝ) (v : InitialPolicyIntervention) :
    Primitives LocalBridgePhase :=
  initialIntervenedPrimitives (primitives G) v

/-- The binary shock law is independent of all four date-zero policy
announcements.  The proof uses the literal original record update. -/
theorem intervened_binary_payment_law
    (G : ℝ) (v : InitialPolicyIntervention) :
    BinarySymmetricPaymentLaw (intervenedPrimitives G v)
      0 1 (1 / 5) := by
  change BinarySymmetricPaymentLaw (primitives G) 0 1 (1 / 5)
  exact binary_payment_law G

/-- The SOURCE mean absolute payment innovation is one fifth, including
in the intervened policy economy; this is the Python zeta=.2 case. -/
theorem intervened_mean_absolute_payment
    (G : ℝ) (v : InitialPolicyIntervention) :
    localPrefixMeanAbsolutePaymentShock (intervenedPrimitives G v) =
      (1 / 5 : ℝ) := by
  exact localPrefixMeanAbsolutePaymentShock_eq_of_binarySymmetric
    (intervenedPrimitives G v) 0 1 (1 / 5)
    (intervened_binary_payment_law G v)

/-- The SOURCE bank renewal factor is unchanged by policy innovations and
equals the reciprocal of the stationary candidate gross loan rate. -/
theorem intervened_bank_renewal_matches_stationary
    (G : ℝ) (v : InitialPolicyIntervention) :
    bankRenewalFactor (intervenedPrimitives G v) =
      1 / ProposedStationaryBank.loanRate := by
  change bankRenewalFactor (primitives G) =
    1 / ProposedStationaryBank.loanRate
  exact ProposedStationaryReducedSystem.bankRenewalFactor_eq
    (primitives G) (stationary_parameters G)

/-- Exact reserve/deposit ratio formula at ANY fixed SOURCE date record.
The nonlinear direct policy effects remain encoded in the record d. -/
theorem intervened_reserve_deposit_ratio
    (G : ℝ) (v : InitialPolicyIntervention)
    (d : LocalPrefixDateData) :
    localPrefixReserveDepositRatio (intervenedPrimitives G v) d =
      d.reserveRequirement +
        (d.controls.depositRate / d.currentReserveRate -
          d.reserveRequirement) * (1 / 5 : ℝ) *
          (1 - d.controls.tightness) / (1 + d.controls.tightness) := by
  unfold localPrefixReserveDepositRatio
  rw [intervened_mean_absolute_payment G v]

/-- Literal OTC deficit slope in the intervened SOURCE Primitives:
the Python half-matching formula is exact for tightness <= 1. -/
theorem intervened_otc_deficit_slope_low_tightness
    (G : ℝ) (v : InitialPolicyIntervention)
    (d : LocalPrefixDateData)
    (htau : d.controls.tightness ≤ 1) :
    localPrefixBankDeficitSlope (intervenedPrimitives G v) d =
      d.corridorWidth * (1 - (1 / 2 : ℝ) +
        (1 / 2 : ℝ) * (1 /
          (1 + Real.sqrt (2 - d.controls.tightness)))) := by
  change otcDeficitSlope d.currentReserveRate
    (otcNegotiatedRate d.currentReserveRate
      (d.currentReserveRate + d.corridorWidth)
      (Real.log (2 : ℝ)) d.controls.tightness)
    (d.currentReserveRate + d.corridorWidth)
    (Real.log (2 : ℝ)) d.controls.tightness = _
  exact ProposedHandStencilPledgeRowEquivalence.source_otc_deficit_slope_matches_python_low_tightness
      d.currentReserveRate d.corridorWidth d.controls.tightness htau

/-- Literal OTC surplus slope in the intervened SOURCE Primitives.
There is deliberately NO claim for tightness > 1. -/
theorem intervened_otc_surplus_slope_low_tightness
    (G : ℝ) (v : InitialPolicyIntervention)
    (d : LocalPrefixDateData)
    (htau : d.controls.tightness ≤ 1) :
    localPrefixBankSurplusSlope (intervenedPrimitives G v) d =
      d.corridorWidth * d.controls.tightness * (1 / 2 : ℝ) *
        (1 / (1 + Real.sqrt (2 - d.controls.tightness))) := by
  change otcSurplusSlope d.currentReserveRate
    (otcNegotiatedRate d.currentReserveRate
      (d.currentReserveRate + d.corridorWidth)
      (Real.log (2 : ℝ)) d.controls.tightness)
    (Real.log (2 : ℝ)) d.controls.tightness = _
  exact ProposedHandStencilPledgeRowEquivalence.source_otc_surplus_slope_matches_python_low_tightness
      d.currentReserveRate d.corridorWidth d.controls.tightness htau

#print axioms intervened_binary_payment_law
#print axioms intervened_mean_absolute_payment
#print axioms intervened_bank_renewal_matches_stationary
#print axioms intervened_reserve_deposit_ratio
#print axioms intervened_otc_deficit_slope_low_tightness
#print axioms intervened_otc_surplus_slope_low_tightness


/-! ## Literal inherited nominal faces under an initial announcement

The stationary inherited state is an independent, already compiled
SOURCE object. Date-zero innovations change neither its inherited
financial positions nor the primitive fields used in the original
nominal consistency and monetary-domain predicates.
These are NOT claims of optimality or equality to Python's frozen
same-predecessor S/B roots. -/

/-- The exact SOURCE inherited household/firm/bank/government nominal
face consistency survives arbitrary initial policy interventions. -/
theorem intervened_inherited_nominal_consistency
    (G : ℝ) (v : InitialPolicyIntervention) :
    InheritedNominalFaceConsistency (intervenedPrimitives G v)
      (ProposedStationaryInheritedState.inheritedState G) := by
  change InheritedNominalFaceConsistency
    (ProposedStationaryPrimitives.primitives G)
    (ProposedStationaryInheritedState.inheritedState G)
  exact ProposedStationaryInheritedState.inherited_nominalFaceConsistency G

/-- If the stationary bond supply covers pre-settlement reserves,
the monetary primitive domain remains satisfied after all four shocks.
This does not enforce a strict interiority margin for date-zero policies. -/
theorem intervened_inherited_monetary_domain
    (G : ℝ) (v : InitialPolicyIntervention)
    (hG : ProposedStationaryRealScale.reservesPre ≤ G) :
    MonetaryPolicyPrimitiveDomain (intervenedPrimitives G v)
      (ProposedStationaryInheritedState.inheritedState G) := by
  change MonetaryPolicyPrimitiveDomain
    (ProposedStationaryPrimitives.primitives G)
    (ProposedStationaryInheritedState.inheritedState G)
  exact ProposedStationaryInheritedState.inherited_monetary_domain G hG

#print axioms intervened_inherited_nominal_consistency
#print axioms intervened_inherited_monetary_domain


/-! ## Literal SOURCE date-zero data-chart witness

This is an exact projection of the original LocalPrefixDateZeroData
applied to the ACTUAL stationary Primitives and InheritedState.
Date-zero innovations are logarithmic offsets, while reserve
requirement and corridor interventions are changes in LEVELS.
Nothing here asserts that an unrestricted shock preserves positive
price or bank-feasibility domains.
-/

noncomputable def sourceStationaryDateZeroData
    (G : ℝ) (v : InitialPolicyIntervention)
    (Z : LocalPrefixCoordinates) : LocalPrefixDateData :=
  localPrefixDateZeroData (intervenedPrimitives G v)
    (ProposedStationaryInheritedState.inheritedState G) Z .dateOne

/-- The four primitive policy innovations appear in the original
date-zero SOURCE data in the literal order (R, M, rho, Delta). -/
theorem source_stationary_datezero_four_policy_fields
    (G : ℝ) (v : InitialPolicyIntervention)
    (Z : LocalPrefixCoordinates) :
    (sourceStationaryDateZeroData G v Z).reserveRateInnovation =
        v.reserveRateInnovation ∧
    (sourceStationaryDateZeroData G v Z).reserveQuantityInnovation =
        v.reserveQuantityInnovation ∧
    (sourceStationaryDateZeroData G v Z).reserveRequirement =
        (1 / 10 : ℝ) + v.reserveRequirement ∧
    (sourceStationaryDateZeroData G v Z).corridorWidth =
        (1 / 50 : ℝ) + v.corridorWidth := by
  simp [sourceStationaryDateZeroData, localPrefixDateZeroData,
    intervenedPrimitives, initialIntervenedPrimitives,
    ProposedStationaryPrimitives.primitives, localBridgeTree]

/-- The original SOURCE calendar keeps aggregate productivity at one
across both initial and next dates. This does not establish a growth
mechanism, or an allocation of the nonlinear prefix. -/
theorem source_stationary_datezero_productivity_fields
    (G : ℝ) (v : InitialPolicyIntervention)
    (Z : LocalPrefixCoordinates) :
    (sourceStationaryDateZeroData G v Z).currentAggregateProductivity = 1 ∧
      (sourceStationaryDateZeroData G v Z).nextAggregateProductivity = 1 := by
  constructor <;> rfl

/-- The literal date-one SOURCE data are fixed-coordinate invariant
under an initial four-tool announcement in the concrete calendar. -/
theorem source_stationary_dateone_data_invariant_fixed_coordinates
    (G : ℝ) (v : InitialPolicyIntervention)
    (Z : LocalPrefixCoordinates) (tail : LocalPrefixContinuationRule) :
    localPrefixDateOneData (intervenedPrimitives G v)
      Z .dateOne .recurrent tail =
    localPrefixDateOneData (primitives G)
      Z .dateOne .recurrent tail := by
  have hdate : LocalBridgePhase.dateOne ≠ (primitives G).tree.initial := by
    change LocalBridgePhase.dateOne ≠ LocalBridgePhase.dateZero
    decide
  exact ProposedHandStencilPledgeRowEquivalence.source_dateone_prefix_data_fixed_coordinates_unaffected
      (primitives G) v Z .dateOne .recurrent tail hdate

#print axioms source_stationary_datezero_four_policy_fields
#print axioms source_stationary_datezero_productivity_fields
#print axioms source_stationary_dateone_data_invariant_fixed_coordinates

end ProposedStationaryInterventionSourceBridge
end Ventura26LiquidityAllocation

import Ventura26LiquidityAllocation.LocalScalarEconomicConeRowsCandidate

/-!
# One exact original source KKT block from the scalar root and row 5

The full 33-row auxiliary system REPLACES the L regime equation
with normalized collateral slack minus the prescribed scalar s.
A scalar root in the source marginal guarantees the omitted dual
complementarity. Combining the two conditions recovers the literal
LocalScalarComplementarityL source predicate at the recovered log
coordinates, for the actual intervened primitives.

The source intervention only changes four policy innovation paths;
it does not change pledgeability, discount factors, or consumption
risk aversion. This invariance is proved explicitly below.

This module proves one firm L collateral KKT block, not the
other source KKT conditions, global firm optimum, or equilibrium.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarOriginalCollateralKktBridge

open ProposedLocalScalarEconomicSlice
open ProposedScalarComplementarityMultiplicity

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The intervention modifies monetary instruments, NOT the
normalized firm funding dual formula evaluated at fixed
economic coordinates. -/
theorem normalizedCollateralDual_invariant_under_initial_intervention
    (P : Primitives S) (v : InitialPolicyIntervention)
    (Z : LocalPrefixCoordinates) :
    localNormalizedCollateralDualL (initialIntervenedPrimitives P v) Z =
      localNormalizedCollateralDualL P Z := by
  rfl

/-- Same observation for the pledge-based normalized slack. -/
theorem normalizedCollateralSlack_invariant_under_initial_intervention
    (P : Primitives S) (v : InitialPolicyIntervention)
    (Z : LocalPrefixCoordinates) :
    localNormalizedSlackL (initialIntervenedPrimitives P v) Z =
      localNormalizedSlackL P Z := by
  rfl

/-- Exact extraction of the prescribed collateral slack from
the fifth source row (index 5, firmRegimeZeroL). -/
theorem source_row_five_recovers_normalized_slack
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (solutionLog : (Fin 5 → ℝ) → (Fin 33 → ℝ))
    (s h : ℝ)
    (hrow : localBindingResidualWithSlack P I Z0 dateOne recurrent tail
      (reserveRemunerationSlice s h)
      (solutionLog (reserveRemunerationSlice s h))
      (5 : Fin 33) = 0) :
    let y := reserveRemunerationSlice s h
    let Pv := initialIntervenedPrimitives P (localScalarParameterIntervention y)
    let Z := localPrefixLogChart Z0 (solutionLog y)
    localNormalizedSlackL Pv Z = s := by
  change localNormalizedSlackL
    (initialIntervenedPrimitives P
      (localScalarParameterIntervention (reserveRemunerationSlice s h)))
    (localPrefixLogChart Z0
      (solutionLog (reserveRemunerationSlice s h))) -
      (reserveRemunerationSlice s h) 0 = 0 at hrow
  rw [reserveRemunerationSlice_slack] at hrow
  exact sub_eq_zero.mp hrow

/-- One certified original local KKT block: the actual normalized
collateral slack of L is nonnegative, its funding dual is nonnegative,
and their product is zero. The logic uses both the literal source row
and the literal source marginal. -/
theorem source_scalar_complementarity_recovers_original_L_KKT
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (solutionLog : (Fin 5 → ℝ) → (Fin 33 → ℝ))
    (s h : ℝ)
    (hrow : localBindingResidualWithSlack P I Z0 dateOne recurrent tail
      (reserveRemunerationSlice s h)
      (solutionLog (reserveRemunerationSlice s h))
      (5 : Fin 33) = 0)
    (hscalar : ScalarComplementarity
      (fun x => economicReserveRemunerationMarginal P Z0 solutionLog x h) s) :
    let y := reserveRemunerationSlice s h
    let Pv := initialIntervenedPrimitives P (localScalarParameterIntervention y)
    let Z := localPrefixLogChart Z0 (solutionLog y)
    LocalScalarComplementarityL Pv Z := by
  let y := reserveRemunerationSlice s h
  let Pv := initialIntervenedPrimitives P (localScalarParameterIntervention y)
  let Z := localPrefixLogChart Z0 (solutionLog y)
  have hslack : localNormalizedSlackL Pv Z = s :=
    source_row_five_recovers_normalized_slack
      P I Z0 dateOne recurrent tail solutionLog s h hrow
  have hdual : localNormalizedCollateralDualL Pv Z =
      economicReserveRemunerationMarginal P Z0 solutionLog s h := by
    change localNormalizedCollateralDualL Pv Z =
      localNormalizedCollateralDualL P Z
    exact normalizedCollateralDual_invariant_under_initial_intervention
      P (localScalarParameterIntervention y) Z
  rcases hscalar with ⟨hsnonneg, hmnonneg, hprod⟩
  change 0 ≤ localNormalizedSlackL Pv Z ∧
    0 ≤ localNormalizedCollateralDualL Pv Z ∧
    localNormalizedSlackL Pv Z * localNormalizedCollateralDualL Pv Z = 0
  rw [hslack, hdual]
  exact ⟨hsnonneg, hmnonneg, hprod⟩

#print axioms normalizedCollateralDual_invariant_under_initial_intervention
#print axioms normalizedCollateralSlack_invariant_under_initial_intervention
#print axioms source_row_five_recovers_normalized_slack
#print axioms source_scalar_complementarity_recovers_original_L_KKT

end ProposedLocalScalarOriginalCollateralKktBridge
end Ventura26LiquidityAllocation

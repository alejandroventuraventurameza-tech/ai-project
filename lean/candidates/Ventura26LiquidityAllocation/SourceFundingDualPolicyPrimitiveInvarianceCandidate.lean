import Ventura26LiquidityAllocation.LocalScalarAugmented34SourceCandidate

/-!
# Funding-dual primitive invariance under the genuine SOURCE monetary intervention

The 34th residual in the augmented remuneration experiment is written
with the baseline Primitives P, whereas the first 33 rows use the
intervened primitives Pv = initialIntervenedPrimitives P (...).

This is economically legitimate for the normalized L funding dual
because its literal SOURCE definition uses only entrepreneurDiscount
and entrepreneurRiskAversion, neither modified by
initialIntervenedPrimitives. The identity below proves that fact on
the actual SOURCE definitions, without a numerical proxy.
It does not assert that the funding dual is unaffected through the
endogenous equilibrium log coordinates (which respond to the shock).
-/

namespace Ventura26LiquidityAllocation

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The literal SOURCE normalized L funding dual is unchanged
when the four supported monetary instruments are perturbed at
the primitive level while holding all coordinates fixed. -/
theorem sourceFundingDual_invariant_under_initialPolicyIntervention
    (P : Primitives S) (v : InitialPolicyIntervention)
    (Z : LocalPrefixCoordinates) :
    localNormalizedCollateralDualL (initialIntervenedPrimitives P v) Z =
      localNormalizedCollateralDualL P Z := by
  rfl

#print axioms sourceFundingDual_invariant_under_initialPolicyIntervention

/-- In the actual 34-equation reserve-remuneration slice, using P
instead of intervened Pv in the 34th residual is definitionally
equivalent. Endogenous effects through z are not eliminated. -/
theorem sourceFundingDual_reserveRemunerationSlice_policy_neutral
    (P : Primitives S) (Z0 : LocalPrefixCoordinates)
    (z : Fin 33 → ℝ) (h : ℝ) :
    localNormalizedCollateralDualL
      (initialIntervenedPrimitives P
        (localScalarParameterIntervention
          (ProposedLocalScalarEconomicSlice.reserveRemunerationSlice 0 h)))
      (localPrefixLogChart Z0 z) =
    localNormalizedCollateralDualL P (localPrefixLogChart Z0 z) := by
  exact sourceFundingDual_invariant_under_initialPolicyIntervention
    P _ (localPrefixLogChart Z0 z)

#print axioms sourceFundingDual_reserveRemunerationSlice_policy_neutral

end Ventura26LiquidityAllocation

import Ventura26LiquidityAllocation.FirmFaceAccountingCandidate

/-!
# Exact wage^5 normalization of the SOURCE inherited entrepreneurial face gap

No numerical root, SOURCE gap value, or paper equation is assumed. Both
sides of this identity refer to the original SOURCE date-zero firm faces;
the wage normalization is inherited from the stationary model and is
strictly positive.

This is a candidate to be checked after FirmFaceAccountingCandidate. The
remaining inequality is a uniform *lower* bound for its right-hand side.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedFirmFaceNormalization

open ProposedStationaryBank
open ProposedStationaryPrimitives
open ProposedStationaryInheritedState
open ProposedStationaryRealScale
open ProposedBoundaryBridge
open ProposedBoundaryResourceRoot
open ProposedBoundaryFullPrefix
open ProposedBoundaryNormalizationBridge
open ProposedBoundaryEndpointBoxes
open ProposedFirmFaceAccounting

/-- The exact original face decline becomes a function of five
wage-unit economic terms. In particular, the inherited nominal
firm promises are not redefined by choosing a new policy rate. -/
theorem source_firm_face_decline_normalized_exact
    (G R : ℝ) (hR : R ∈ boundaryInterval) :
    wage ^ (5 : ℕ) *
      (∑ i, (primitives G).mass i *
        ((inheritedState G).firmFace i -
          boundaryInheritedFace G R (boundaryZeroSeed G R) i)) =
      (1 - 1 / R) * ProposedStationaryBank.loanRate * creditScale -
        (5 / 12 : ℝ) * normalizedOutput R +
        average (normalizedFirmConsumption R) +
        boundaryCapitalPrice R * average capitalScale *
          (1 - (39 / 40 : ℝ) * boundaryCapitalScale R) := by
  have hRaw := source_firm_face_decline_exact G R hR
  have hY := normalized_output_eq_from_source R hR
  have hRH := normalized_firm_eq R (boundary_rate_domain hR).1 .H
  have hRL := normalized_firm_eq R (boundary_rate_domain hR).1 .L
  have hC :
      wage ^ (5 : ℕ) * average (boundaryConsumption R) =
        average (normalizedFirmConsumption R) := by
    unfold average
    calc
      wage ^ (5 : ℕ) *
          ((boundaryConsumption R .H + boundaryConsumption R .L) / 2) =
        (wage ^ (5 : ℕ) * boundaryConsumption R .H +
          wage ^ (5 : ℕ) * boundaryConsumption R .L) / 2 := by ring
      _ = (normalizedFirmConsumption R .H +
          normalizedFirmConsumption R .L) / 2 := by rw [hRH, hRL]
  have hCredit : wage ^ (5 : ℕ) * aggregateCredit = creditScale := by
    rw [aggregateCredit_scale]
    field_simp [ne_of_gt (pow_pos wage_pos (5 : ℕ))] <;> ring
  have hCapital :
      wage ^ (5 : ℕ) * aggregateCapital = average capitalScale := by
    rw [aggregateCapital_scale]
    field_simp [ne_of_gt (pow_pos wage_pos (5 : ℕ))] <;> ring
  calc
    wage ^ (5 : ℕ) *
        (∑ i, (primitives G).mass i *
          ((inheritedState G).firmFace i -
            boundaryInheritedFace G R (boundaryZeroSeed G R) i)) =
      wage ^ (5 : ℕ) *
        ((1 - 1 / R) * ProposedStationaryBank.loanRate * aggregateCredit -
          (5 / 12 : ℝ) * boundaryAggregateOutput R +
          average (boundaryConsumption R) +
          boundaryCapitalPrice R * aggregateCapital *
            (1 - (39 / 40 : ℝ) * boundaryCapitalScale R)) :=
      congrArg (fun x : ℝ => wage ^ (5 : ℕ) * x) hRaw
    _ = _ := by
      rw [← hY, ← hC, ← hCredit, ← hCapital]
      ring

#print axioms source_firm_face_decline_normalized_exact

end ProposedFirmFaceNormalization
end Ventura26LiquidityAllocation

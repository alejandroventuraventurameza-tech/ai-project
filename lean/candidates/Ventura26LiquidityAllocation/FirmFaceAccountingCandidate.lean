import Ventura26LiquidityAllocation.BoundaryBankFaceUniformLowerCandidate

/-!
# Exact accounting formula for the ORIGINAL SOURCE inherited firm-face change

The operating-profit identity follows from firm-level labor demand:
impact wage times hired labor is (5/12) of impact output, under the
original gross-markup/technology conventions. It is NOT an extra
household or firm optimality assumption.

The aggregate face difference then reduces exactly to the incumbent
gross loan rate, the impact rate, incumbent credit, impact aggregate
output and consumption, and the surviving-capital revaluation term.

The identities are source-level candidates. No numerical box, root
residual, independent Python audit or new axiom is assumed.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedFirmFaceAccounting

open ProposedStationaryBank
open ProposedStationaryPrimitives
open ProposedStationaryInheritedState
open ProposedStationaryRealScale
open ProposedBoundaryBridge
open ProposedBoundaryResourceRoot
open ProposedBoundaryFullPrefix
open ProposedBoundaryWorkerLabor
open ProposedBoundaryAnalyticPackage
open ProposedBoundaryNormalizationBridge
open ProposedBoundaryInheritedFaceDecomposition

/-- Firm-specific first-order labor accounting on the ORIGINAL SOURCE
boundary construction. -/
theorem boundary_wage_labor_eq_profit_share
    (R : ℝ) (hR : R ∈ boundaryInterval) (i : FirmType) :
    boundaryWage R * boundaryLabor R i =
      (5 / 12 : ℝ) * boundaryOutput R i := by
  rw [boundaryLabor_eq_parent_mul_factor hR i,
    output_scaling hR i]
  unfold boundaryLaborFactor
  have hw : 0 < boundaryWage R := boundaryWage_pos hR
  have hparent : wage * labor i = (5 / 12 : ℝ) * output i := by
    unfold labor output
    field_simp [ne_of_gt wage_pos] <;> ring
  calc
    boundaryWage R *
        (labor i *
          (boundaryCapitalScale R ^ (4 / 5 : ℝ) *
            (wage / boundaryWage R) ^ (2 : ℕ))) =
      (wage * labor i) * boundaryCapitalScale R ^ (4 / 5 : ℝ) *
        (wage / boundaryWage R) := by
          field_simp [ne_of_gt hw] <;> ring
    _ = (5 / 12 : ℝ) *
          (output i * boundaryCapitalScale R ^ (4 / 5 : ℝ) *
            (wage / boundaryWage R)) := by
          rw [hparent]
          ring

/-- Under SOURCE controls, the original local operating-profit function
equals five-twelfths of each firm's original impact output. -/
theorem boundary_source_operating_profit_eq_output_share
    (G R : ℝ) (hR : R ∈ boundaryInterval) (i : FirmType) :
    localPrefixOperatingProfit (primitives G)
        (boundaryFirmDateSeed R (boundaryZeroSeed G R)) i =
      (5 / 12 : ℝ) * boundaryOutput R i := by
  have hlabor :
      localPrefixLabor (primitives G)
        (boundaryFirmDateSeed R (boundaryZeroSeed G R)) i =
          boundaryLabor R i := by
    change
      ((1 / 2 : ℝ) * (5 / 6) * 1 * technology i *
        boundaryCapital R i ^ (2 / 5 : ℝ) / boundaryWage R) ^
        (1 / (1 - (1 / 2 : ℝ)) : ℝ) = boundaryLabor R i
    unfold boundaryLabor
    congr 1 <;> ring
  have houtput :
      localPrefixOutput (primitives G)
        (boundaryFirmDateSeed R (boundaryZeroSeed G R)) i =
          boundaryOutput R i := by
    unfold localPrefixOutput boundaryOutput
    rw [hlabor]
    change operatingOutput (1 * technology i) (boundaryCapital R i)
        (boundaryLabor R i) (2 / 5) (1 / 2) =
      operatingOutput (technology i) (boundaryCapital R i)
        (boundaryLabor R i) (2 / 5) (1 / 2)
    simp only [one_mul]
  change (5 / 6 : ℝ) * localPrefixOutput (primitives G)
      (boundaryFirmDateSeed R (boundaryZeroSeed G R)) i -
    boundaryWage R * localPrefixLabor (primitives G)
      (boundaryFirmDateSeed R (boundaryZeroSeed G R)) i =
    (5 / 12 : ℝ) * boundaryOutput R i
  rw [houtput, hlabor]
  have h := boundary_wage_labor_eq_profit_share R hR i
  linarith only [h]

/-- Direct original SOURCE firm-face decomposition. This equality
eliminates individually reconstructed profit terms, but by itself
does not supply any strict interval inequality. -/
theorem source_firm_face_decline_exact
    (G R : ℝ) (hR : R ∈ boundaryInterval) :
    (∑ i, (primitives G).mass i *
      ((inheritedState G).firmFace i -
        boundaryInheritedFace G R (boundaryZeroSeed G R) i)) =
      (1 - 1 / R) * ProposedStationaryBank.loanRate * aggregateCredit -
        (5 / 12 : ℝ) * boundaryAggregateOutput R +
        average (boundaryConsumption R) +
        boundaryCapitalPrice R * aggregateCapital *
          (1 - (39 / 40 : ℝ) * boundaryCapitalScale R) := by
  have hRpos : 0 < R := (boundary_rate_domain hR).1
  have hH :=
    boundary_source_operating_profit_eq_output_share G R hR .H
  have hL :=
    boundary_source_operating_profit_eq_output_share G R hR .L
  simp only [sum_firmType_eq_H_add_L]
  change (1 / 2 : ℝ) *
      (firmFace .H -
        boundaryInheritedFace G R (boundaryZeroSeed G R) .H) +
      (1 / 2 : ℝ) *
      (firmFace .L -
        boundaryInheritedFace G R (boundaryZeroSeed G R) .L) = _
  unfold boundaryInheritedFace
  rw [hH, hL]
  dsimp only [boundaryZeroSeed]
  unfold boundaryAggregateOutput aggregateCredit aggregateCapital average
    boundaryCapital boundaryEffectivePrice loan firmFace
  field_simp [ne_of_gt hRpos, ne_of_gt loanRate_pos] <;> ring

#print axioms boundary_wage_labor_eq_profit_share
#print axioms boundary_source_operating_profit_eq_output_share
#print axioms source_firm_face_decline_exact

end ProposedFirmFaceAccounting
end Ventura26LiquidityAllocation

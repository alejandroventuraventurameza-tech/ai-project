import Ventura26LiquidityAllocation.BoundaryEndpointBoxesCandidate

/-!
# Source normalization, four elementary identities from existing parent data

UNCOMPILED candidate; pinned branch work/chat-continuity, commit
16e24fe828a5a0002ef13bb82bae9e295f190f86.

Mathematical conclusion: after multiplying all quantities by stationary
wage^5, no 12th root is needed. These four proofs use original parent
scaling lemmas and the previously established capital-cost identity.
The OUTPUT identity remains a distinct root-of-degree-15 obligation;
it is NOT assumed to hold as a theorem by this file.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedBoundaryNormalizationBridge

open ProposedStationaryBank
open ProposedStationaryRealScale
open ProposedStationaryProductionBridge
open ProposedBoundaryBridge
open ProposedBoundaryResourceRoot
open ProposedBoundaryEndpointBoxes
open ProposedBoundaryWorkerLabor
open ProposedBoundaryAnalyticPackage
open ProposedBoundaryFullPrefix

/-- Express entrepreneur consumption in terms of unit-wage capital scale. -/
theorem firm_coefficient_scaled (i : FirmType) :
    wage ^ (5 : ℕ) * firmConsumption i = firmCoefficient i := by
  unfold firmCoefficient firmConsumption profit output loan firmFace capital
  field_simp [ne_of_gt wage_pos,
    ne_of_gt loanRate_pos] <;> ring

/-- Worker consumption: direct consequence of the stationary scale lemma. -/
theorem normalized_worker_eq (R : ℝ) :
    wage ^ (5 : ℕ) * boundaryWorkerConsumption R =
      normalizedWorkerConsumption R := by
  unfold boundaryWorkerConsumption normalizedWorkerConsumption
  rw [workerConsumption_scale]
  field_simp [ne_of_gt wage_pos, ne_of_gt (pow_pos wage_pos (5 : ℕ))] <;> ring

/-- The entrepreneur coefficients scale with wage^-5, while their
    initial-date consumption response is a rational function of R. -/
theorem normalized_firm_eq (R : ℝ) (hR : 0 < R) (i : FirmType) :
    wage ^ (5 : ℕ) * boundaryConsumption R i =
      normalizedFirmConsumption R i := by
  cases i with
  | H =>
      unfold normalizedFirmConsumption boundaryConsumption
      rw [boundaryEffectivePrice_eq]
      rw [← firm_coefficient_scaled .H]
      field_simp [ne_of_gt hR,
        ne_of_gt (parentEffectivePrice_pos .H)] <;> ring
  | L =>
      unfold normalizedFirmConsumption boundaryConsumption
      rw [← firm_coefficient_scaled .L]
      field_simp [ne_of_gt hR] <;> ring

/-- Investment adjustment costs are linear in aggregate capital, and the
    stationary aggregate capital equals the unit-wage coefficient / wage^5. -/
theorem normalized_capitalCost_eq (R : ℝ)
    (hscale : 0 < boundaryCapitalScale R) :
    wage ^ (5 : ℕ) * boundaryCapitalCost R =
      normalizedCapitalCost R := by
  rw [boundaryCapitalCost_scale_formula hscale, aggregateCapital_scale]
  unfold normalizedCapitalCost
  field_simp [ne_of_gt wage_pos, ne_of_gt (pow_pos wage_pos (5 : ℕ)),
    ne_of_gt hscale] <;> ring

/-- The original SOURCE production scaling proves the exact fifteenth
root expression, rather than postulating it at the two bracket endpoints.
This depends on output_ratio_fifteenth_power in the analytic module. -/
theorem normalized_output_eq_from_source (R : ℝ)
    (hR : R ∈ boundaryInterval) :
    wage ^ (5 : ℕ) * boundaryAggregateOutput R =
      normalizedOutput R := by
  have hY : 0 < boundaryAggregateOutput R := by
    rw [aggregateOutput_scaling hR]
    exact mul_pos
      (mul_pos aggregates_pos.2.1
        (Real.rpow_pos_of_pos
          (boundary_scale_and_investment_domain hR).1 _))
      (div_pos wage_pos (boundaryWage_pos hR))
  have hratio0 :
      0 ≤ boundaryAggregateOutput R / aggregateOutput :=
    (div_pos hY aggregates_pos.2.1).le
  have hpow := output_ratio_fifteenth_power hR
  have hroot :
      boundaryAggregateOutput R / aggregateOutput =
        (boundaryCapitalScale R ^ (8 : ℕ) *
          ((99 / 100 : ℝ) * boundaryDepositRate R) ^ (5 : ℕ)) ^
            (1 / 15 : ℝ) := by
    calc
      boundaryAggregateOutput R / aggregateOutput =
          ((boundaryAggregateOutput R / aggregateOutput) ^
              (15 : ℕ)) ^ (1 / 15 : ℝ) := by
            simpa only [one_div] using
              (Real.pow_rpow_inv_natCast hratio0
                (by norm_num : (15 : ℕ) ≠ 0)).symm
      _ = _ := by rw [hpow]
  have hscale :
      outputScale = wage ^ (5 : ℕ) * aggregateOutput := by
    rw [aggregateOutput_scale]
    field_simp [ne_of_gt wage_pos, ne_of_gt (pow_pos wage_pos (5 : ℕ))] <;> ring
  change wage ^ (5 : ℕ) * boundaryAggregateOutput R =
    outputScale * (boundaryCapitalScale R ^ (8 : ℕ) *
      ((99 / 100 : ℝ) * boundaryDepositRate R) ^ (5 : ℕ)) ^
        (1 / 15 : ℝ)
  rw [← hroot, hscale]
  field_simp [ne_of_gt aggregates_pos.2.1] <;> ring

/-- All five source-normalization fields follow once the one remaining
    output-root identity has been proved. The parent scales are NOT taken
    as hypotheses; the four non-output fields above construct their proofs. -/
theorem scaleIdentities_of_output_root (R : ℝ) (hR : R ∈ boundaryInterval)
    (houtput : wage ^ (5 : ℕ) * boundaryAggregateOutput R =
      normalizedOutput R) :
    BoundaryScaleIdentities R := by
  refine ⟨houtput, normalized_worker_eq R, ?_, ?_, ?_⟩
  · exact normalized_firm_eq R (boundary_rate_domain hR).1 .H
  · exact normalized_firm_eq R (boundary_rate_domain hR).1 .L
  · exact normalized_capitalCost_eq R
      (boundary_scale_and_investment_domain hR).1

/-- The remaining root identity is deliberately isolated in this predicate;
    its exact polynomial content is z^15=s^8*(betaW RD)^5 with z>0.
    A proof may use `Real.rpow_mul` or the root-uniqueness argument. -/
def OutputRootIdentityAt (R : ℝ) : Prop :=
  wage ^ (5 : ℕ) * boundaryAggregateOutput R = normalizedOutput R

/-- The final sign interface after eliminating four normalization obligations:
    only two output-root identities and ten rational boxes remain exposed. -/
theorem endpointSigns_of_boxes_and_output_roots
    (houtputLo : OutputRootIdentityAt boundaryLo)
    (houtputHi : OutputRootIdentityAt boundaryHi)
    (hboxes : BoundaryComponentBoxes) : BoundaryEndpointSigns := by
  apply endpointSigns_of_verified_components
    (scaleIdentities_of_output_root boundaryLo
      (by
        exact ⟨le_refl _, le_of_lt boundaryLo_lt_boundaryHi⟩) houtputLo)
    (scaleIdentities_of_output_root boundaryHi
      (by
        exact ⟨le_of_lt boundaryLo_lt_boundaryHi, le_refl _⟩) houtputHi)
    hboxes

/-- Both exact endpoint production roots are now consequences of
source production and positivity, not independent hypotheses. Ten
rational interval boxes remain an explicit proof obligation. -/
theorem endpointSigns_of_boxes
    (hboxes : BoundaryComponentBoxes) : BoundaryEndpointSigns := by
  exact endpointSigns_of_verified_components
    (scaleIdentities_of_output_root boundaryLo
      ⟨le_refl _, le_of_lt boundaryLo_lt_boundaryHi⟩
      (normalized_output_eq_from_source boundaryLo
        ⟨le_refl _, le_of_lt boundaryLo_lt_boundaryHi⟩))
    (scaleIdentities_of_output_root boundaryHi
      ⟨le_of_lt boundaryLo_lt_boundaryHi, le_refl _⟩
      (normalized_output_eq_from_source boundaryHi
        ⟨le_of_lt boundaryLo_lt_boundaryHi, le_refl _⟩))
    hboxes

/-- The boundary reduced prefix is closed conditionally on only the
ten endpoint boxes: neither the worker-labor FOC nor source monotonicity
nor the fifteenth output root is supplied as an extra assumption. The
full competitive equilibrium and terminal conditions remain separate. -/
theorem boundary_reduced_prefix_from_endpoint_boxes
    (G : ℝ) (hboxes : BoundaryComponentBoxes)
    (branch : LocalPrefixBranch) :
    LocalReducedPrefixEquationsHold branch
      (boundaryPrimitives G
        (boundaryRoot boundary_analyticPackage (endpointSigns_of_boxes hboxes)))
      (boundaryInitialState G
        (boundaryRoot boundary_analyticPackage (endpointSigns_of_boxes hboxes)))
      (boundaryCoordinates
        (boundaryRoot boundary_analyticPackage (endpointSigns_of_boxes hboxes)))
      .dateOne .recurrent boundaryTail := by
  exact boundary_full_prefix_equations_from_root G
    boundary_analyticPackage (endpointSigns_of_boxes hboxes) branch

/-- Conditional uniqueness for the SOURCE *scalar* frontier rate plus
the literal 33-row reduced prefix in every named reduced-system branch.
Uniqueness is of R on the resource bracket, not uniqueness of the
allocation or of an infinite-horizon competitive equilibrium.
The ten rational endpoint boxes are still explicit hypotheses. -/
theorem boundary_unique_reduced_prefix_rate_of_boxes
    (G : ℝ) (hboxes : BoundaryComponentBoxes) :
    ∃! R : ℝ,
      boundaryLo ≤ R ∧ R ≤ boundaryHi ∧
      boundaryResourceResidual R = 0 ∧
      ∀ branch : LocalPrefixBranch,
        LocalReducedPrefixEquationsHold branch
          (boundaryPrimitives G R)
          (boundaryInitialState G R)
          (boundaryCoordinates R) .dateOne .recurrent boundaryTail := by
  let R := boundaryRoot boundary_analyticPackage (endpointSigns_of_boxes hboxes)
  have hspec := boundaryRoot_spec
    boundary_analyticPackage (endpointSigns_of_boxes hboxes)
  have huniq :=
    (Classical.choose_spec
      (boundary_exactRootOn boundary_analyticPackage
        (endpointSigns_of_boxes hboxes))).2
  refine ⟨R, ⟨hspec.1, hspec.2.1, hspec.2.2, ?_⟩, ?_⟩
  · intro branch
    exact boundary_reduced_prefix_from_endpoint_boxes G hboxes branch
  · intro y hy
    exact huniq y ⟨hy.1, hy.2.1, hy.2.2.1⟩


/-- A tight, fully rational enclosure of the literal OTC matching weight.
Every inequality is reduced to exact rational square comparisons with
sqrt(3/2), never to a floating-point evaluation. -/
theorem boundary_weight_rational_micro_box :
    (44948974278 / 100000000000 : ℝ) <
      ProposedStationaryBank.weight ∧
    ProposedStationaryBank.weight <
      (44948974279 / 100000000000 : ℝ) := by
  have hs0 : 0 ≤ Real.sqrt (3 / 2 : ℝ) := Real.sqrt_nonneg _
  have hsq : Real.sqrt (3 / 2 : ℝ) ^ (2 : ℕ) = 3 / 2 :=
    Real.sq_sqrt (by norm_num)
  have hslo :
      (122474487139 / 100000000000 : ℝ) <
        Real.sqrt (3 / 2 : ℝ) := by
    have hsqlo :
        (122474487139 / 100000000000 : ℝ) ^ (2 : ℕ) <
          3 / 2 := by norm_num
    by_contra hn
    have hle :
        Real.sqrt (3 / 2 : ℝ) ≤
          (122474487139 / 100000000000 : ℝ) :=
      le_of_not_gt hn
    have hp : 0 ≤
        ((122474487139 / 100000000000 : ℝ) -
          Real.sqrt (3 / 2 : ℝ)) *
        ((122474487139 / 100000000000 : ℝ) +
          Real.sqrt (3 / 2 : ℝ)) :=
      mul_nonneg (sub_nonneg.mpr hle)
        (add_nonneg (by norm_num) hs0)
    nlinarith only [hsqlo, hsq, hp]
  have hshi :
      Real.sqrt (3 / 2 : ℝ) <
        (122474487140 / 100000000000 : ℝ) := by
    have hsqhi :
        (3 / 2 : ℝ) <
          (122474487140 / 100000000000 : ℝ) ^ (2 : ℕ) := by
      norm_num
    by_contra hn
    have hge :
        (122474487140 / 100000000000 : ℝ) ≤
          Real.sqrt (3 / 2 : ℝ) :=
      le_of_not_gt hn
    have hp : 0 ≤
        (Real.sqrt (3 / 2 : ℝ) -
          (122474487140 / 100000000000 : ℝ)) *
        (Real.sqrt (3 / 2 : ℝ) +
          (122474487140 / 100000000000 : ℝ)) :=
      mul_nonneg (sub_nonneg.mpr hge)
        (add_nonneg hs0 (by norm_num))
    nlinarith only [hsqhi, hsq, hp]
  have hd : 0 < 1 + Real.sqrt (3 / 2 : ℝ) := by linarith
  constructor
  · unfold ProposedStationaryBank.weight
    apply (lt_div_iff₀ hd).2
    nlinarith only [hshi]
  · unfold ProposedStationaryBank.weight
    apply (div_lt_iff₀ hd).2
    nlinarith only [hslo]

/-- The SOURCE OTC mean and differential slopes inherit rational
micro-intervals from the exact matching-weight enclosure. -/
theorem boundary_source_slope_rational_micro_boxes :
    ((8371173070 / 1000000000000 : ℝ) <
      ProposedStationaryBank.meanSlope ∧
      ProposedStationaryBank.meanSlope <
        (8371173072 / 1000000000000 : ℝ)) ∧
    ((12247448713 / 1000000000000 : ℝ) <
      ProposedStationaryBank.slopeGap ∧
      ProposedStationaryBank.slopeGap <
        (12247448715 / 1000000000000 : ℝ)) := by
  rcases boundary_weight_rational_micro_box with ⟨hlo, hhi⟩
  unfold ProposedStationaryBank.meanSlope ProposedStationaryBank.slopeGap
  constructor
  · constructor <;> linarith
  · constructor <;> linarith

#print axioms boundary_weight_rational_micro_box
#print axioms boundary_source_slope_rational_micro_boxes

#print axioms boundary_unique_reduced_prefix_rate_of_boxes

#print axioms normalized_output_eq_from_source
#print axioms endpointSigns_of_boxes
#print axioms boundary_reduced_prefix_from_endpoint_boxes

end ProposedBoundaryNormalizationBridge
end Ventura26LiquidityAllocation

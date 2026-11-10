import Ventura26LiquidityAllocation.BoundaryFaceGapFiscalReductionCandidate

/-!
# Exact normalized SOURCE residual, at every rate in the certified interval

This is an unconditional algebraic identity on the ORIGINAL SOURCE resource
residual. It is not a numerical sign proof. The positive stationary wage^5
factor means source-side sign certificates can be constructed on the
simpler normalized function, using existing source-derived scaling lemmas.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedBoundaryNarrowSourceResidualBridge

open ProposedStationaryRealScale
open ProposedBoundaryResourceRoot
open ProposedBoundaryEndpointBoxes
open ProposedBoundaryNormalizationBridge

/-- The original resource residual equals the normalized residual
divided by stationary wage^5, for every point on the SOURCE interval.
No numerical bounding premise is used: all five normalization identities
follow from the original SOURCE production and accounting functions. -/
theorem normalized_source_resource_residual_exact
    (R : ℝ) (hR : R ∈ boundaryInterval) :
    normalizedResourceResidual R =
      wage ^ (5 : ℕ) * boundaryResourceResidual R := by
  exact normalizedResidual_eq_wage_pow_mul R
    (scaleIdentities_of_output_root R hR
      (normalized_output_eq_from_source R hR))

/-- The normalization factor is strictly positive, including at both
narrow rational endpoints. -/
theorem source_normalization_factor_pos :
    0 < wage ^ (5 : ℕ) := by
  exact pow_pos wage_pos _

/-- Both narrow rational endpoints lie in the original SOURCE interval,
so the preceding exact algebraic normalization applies at each one. -/
theorem narrow_endpoints_source_normalization_exact :
    normalizedResourceResidual (1029135 / 1000000 : ℝ) =
      wage ^ (5 : ℕ) *
        boundaryResourceResidual (1029135 / 1000000 : ℝ) ∧
    normalizedResourceResidual (1029136 / 1000000 : ℝ) =
      wage ^ (5 : ℕ) *
        boundaryResourceResidual (1029136 / 1000000 : ℝ) := by
  have hlo : (1029135 / 1000000 : ℝ) ∈ boundaryInterval := by
    change boundaryLo ≤ (1029135 / 1000000 : ℝ) ∧
      (1029135 / 1000000 : ℝ) ≤ boundaryHi
    norm_num [boundaryLo, boundaryHi]
  have hhi : (1029136 / 1000000 : ℝ) ∈ boundaryInterval := by
    change boundaryLo ≤ (1029136 / 1000000 : ℝ) ∧
      (1029136 / 1000000 : ℝ) ≤ boundaryHi
    norm_num [boundaryLo, boundaryHi]
  exact ⟨normalized_source_resource_residual_exact _ hlo,
    normalized_source_resource_residual_exact _ hhi⟩

/-- An unconditional two-way bridge for the exact SOURCE lower endpoint:
the original sign obligation is equivalent to a normalized sign obligation.
No sign is assumed or certified here. -/
theorem narrow_left_negative_iff_normalized_negative :
    boundaryResourceResidual (1029135 / 1000000 : ℝ) < 0 ↔
      normalizedResourceResidual (1029135 / 1000000 : ℝ) < 0 := by
  rw [narrow_endpoints_source_normalization_exact.1]
  constructor
  · intro h
    exact mul_neg_of_pos_of_neg source_normalization_factor_pos h
  · intro h
    by_contra hn
    have hnonneg :
        0 ≤ boundaryResourceResidual (1029135 / 1000000 : ℝ) :=
      le_of_not_gt hn
    have hprod := mul_nonneg source_normalization_factor_pos.le hnonneg
    linarith

/-- Similarly, positivity at the upper endpoint is exactly equivalent to
positivity of its normalized SOURCE residual. -/
theorem narrow_right_positive_iff_normalized_positive :
    0 < boundaryResourceResidual (1029136 / 1000000 : ℝ) ↔
      0 < normalizedResourceResidual (1029136 / 1000000 : ℝ) := by
  rw [narrow_endpoints_source_normalization_exact.2]
  constructor
  · intro h
    exact mul_pos source_normalization_factor_pos h
  · intro h
    by_contra hn
    have hnonpos :
        boundaryResourceResidual (1029136 / 1000000 : ℝ) ≤ 0 :=
      le_of_not_gt hn
    have hprod :=
      mul_nonpos_of_nonneg_of_nonpos source_normalization_factor_pos.le hnonpos
    linarith

#print axioms normalized_source_resource_residual_exact
#print axioms source_normalization_factor_pos
#print axioms narrow_endpoints_source_normalization_exact
#print axioms narrow_left_negative_iff_normalized_negative
#print axioms narrow_right_positive_iff_normalized_positive

end ProposedBoundaryNarrowSourceResidualBridge
end Ventura26LiquidityAllocation

import Ventura26LiquidityAllocation.BoundaryNarrowResourceLeftCandidate

/-!
# Exact SOURCE left-endpoint resource sign

The broad-bracket SOURCE firm consumption boxes are transported to the
narrow-left endpoint by the exact inverse-gross-rate identity. The
capital-cost lower bound uses the previously source-derived stationary
capital box and the new narrow-left real-capital box. The complete
normalized residual is then strictly negative by rational linear
arithmetic, and the original SOURCE residual follows by positive-wage
normalization.

This is a source-level Lean candidate. Do not mark the final theorem
kernel-checked before the pinned workflow compiles it and rejects sorryAx.
The right-endpoint and inherited nominal-face uniform-gap signs remain
independent outstanding obligations.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedBoundaryNarrowLeftResidualSign

open ProposedStationaryRealScale
open ProposedBoundaryBridge
open ProposedBoundaryResourceRoot
open ProposedBoundaryEndpointBoxes
open ProposedBoundaryNormalizationBridge
open ProposedBoundaryNarrowSourceResidualBridge
open ProposedBoundaryNarrowDepositBox
open ProposedBoundaryNarrowResourceLeft

/-- Both original SOURCE normalized firm consumptions scale exactly as
the reciprocal of the contemporaneous gross loan rate. The predecessor
effective price and numerator remain fixed. -/
private theorem narrow_firm_consumption_rate_identity
    (R : ℝ) (hR : 0 < R) (i : FirmType) :
    R * normalizedFirmConsumption R i =
      boundaryLo * normalizedFirmConsumption boundaryLo i := by
  have hLo : 0 < boundaryLo := by norm_num [boundaryLo]
  cases i with
  | H =>
      dsimp [normalizedFirmConsumption]
      field_simp [ne_of_gt hR, ne_of_gt hLo,
        ne_of_gt (parentEffectivePrice_pos .H)] <;> ring
  | L =>
      dsimp [normalizedFirmConsumption]
      field_simp [ne_of_gt hR, ne_of_gt hLo] <;> ring

/-- Narrow-left H consumption bound follows by transporting the
original broad-left SOURCE component bound, with no new firm pricing
assumption or surrogate function. -/
theorem source_narrow_left_firm_H_lower :
    (295738 / 100000 : ℝ) <
      normalizedFirmConsumption (1029135 / 1000000 : ℝ) .H := by
  let R : ℝ := 1029135 / 1000000
  have hR : 0 < R := by norm_num [R]
  have hbase :
      (296932 / 100000 : ℝ) <
        normalizedFirmConsumption boundaryLo .H :=
    boundary_firm_H_endpoint_boxes_from_source.1
  have hscaled :
      boundaryLo * (296932 / 100000 : ℝ) <
        boundaryLo * normalizedFirmConsumption boundaryLo .H :=
    mul_lt_mul_of_pos_left hbase (by norm_num [boundaryLo])
  have hrat :
      R * (295738 / 100000 : ℝ) <
        boundaryLo * (296932 / 100000 : ℝ) := by
    norm_num [R, boundaryLo]
  have hidentity := narrow_firm_consumption_rate_identity R hR .H
  have hproduct :
      R * (295738 / 100000 : ℝ) <
        R * normalizedFirmConsumption R .H := by
    calc
      _ < boundaryLo * (296932 / 100000 : ℝ) := hrat
      _ < boundaryLo * normalizedFirmConsumption boundaryLo .H := hscaled
      _ = R * normalizedFirmConsumption R .H := hidentity.symm
  dsimp [R] at hproduct
  nlinarith only [hproduct]

/-- Same rate-transport argument for the lower-productivity L firm. -/
theorem source_narrow_left_firm_L_lower :
    (381054 / 100000 : ℝ) <
      normalizedFirmConsumption (1029135 / 1000000 : ℝ) .L := by
  let R : ℝ := 1029135 / 1000000
  have hR : 0 < R := by norm_num [R]
  have hbase :
      (382592 / 100000 : ℝ) <
        normalizedFirmConsumption boundaryLo .L :=
    boundary_firm_L_endpoint_boxes_from_source.1
  have hscaled :
      boundaryLo * (382592 / 100000 : ℝ) <
        boundaryLo * normalizedFirmConsumption boundaryLo .L :=
    mul_lt_mul_of_pos_left hbase (by norm_num [boundaryLo])
  have hrat :
      R * (381054 / 100000 : ℝ) <
        boundaryLo * (382592 / 100000 : ℝ) := by
    norm_num [R, boundaryLo]
  have hidentity := narrow_firm_consumption_rate_identity R hR .L
  have hproduct :
      R * (381054 / 100000 : ℝ) <
        R * normalizedFirmConsumption R .L := by
    calc
      _ < boundaryLo * (382592 / 100000 : ℝ) := hrat
      _ < boundaryLo * normalizedFirmConsumption boundaryLo .L := hscaled
      _ = R * normalizedFirmConsumption R .L := hidentity.symm
  dsimp [R] at hproduct
  nlinarith only [hproduct]

/-- Exact rational SOURCE lower bound for the investment-adjustment
cost. It uses both heterogeneous stationary capital scales and the
narrow-left bound for the original date-zero capital installation. -/
theorem source_narrow_left_capital_cost_lower :
    (206418 / 100000 : ℝ) <
      normalizedCapitalCost (1029135 / 1000000 : ℝ) := by
  let R : ℝ := 1029135 / 1000000
  have hspos : 0 < boundaryCapitalScale R :=
    lt_trans (by norm_num : (0 : ℝ) < 99780498 / 100000000)
      source_narrow_left_capital_scale_box.1
  have hsup :
      boundaryCapitalScale R <
        (99780499 / 100000000 : ℝ) :=
    source_narrow_left_capital_scale_box.2
  have hmul :
      4 * boundaryCapitalScale R <
        4 * (99780499 / 100000000 : ℝ) :=
    mul_lt_mul_of_pos_left hsup (by norm_num)
  have hrecip :
      1 / (4 * (99780499 / 100000000 : ℝ)) <
        1 / (4 * boundaryCapitalScale R) :=
    one_div_lt_one_div_of_lt
      (mul_pos (by norm_num) hspos) hmul
  have hlinear :
      (4719 / 6400 : ℝ) * boundaryCapitalScale R <
        (4719 / 6400 : ℝ) * (99780499 / 100000000 : ℝ) :=
    mul_lt_mul_of_pos_left hsup (by norm_num)
  have hnumeric :
      (273246 / 10000000 : ℝ) <
        (41 / 80 : ℝ) +
          1 / (4 * (99780499 / 100000000 : ℝ)) -
          (4719 / 6400 : ℝ) * (99780499 / 100000000 : ℝ) := by
    norm_num
  have hfactor :
      (273246 / 10000000 : ℝ) <
        (41 / 80 : ℝ) + 1 / (4 * boundaryCapitalScale R) -
          (4719 / 6400 : ℝ) * boundaryCapitalScale R := by
    linarith only [hrecip, hlinear, hnumeric]
  have hKlo :
      (7554294 / 100000 : ℝ) <
        ProposedStationaryRealScale.average
          ProposedStationaryRealScale.capitalScale := by
    rcases boundary_source_capital_scales_sharp_boxes with
      ⟨⟨hHlo, _⟩, ⟨hLlo, _⟩⟩
    unfold ProposedStationaryRealScale.average
    linarith only [hHlo, hLlo]
  have hKpos : 0 <
      ProposedStationaryRealScale.average
        ProposedStationaryRealScale.capitalScale :=
    ProposedStationaryRealScale.aggregate_scales_pos.1
  change (206418 / 100000 : ℝ) < normalizedCapitalCost R
  unfold normalizedCapitalCost
  calc
    (206418 / 100000 : ℝ) <
        (7554294 / 100000 : ℝ) * (273246 / 10000000 : ℝ) := by
      norm_num
    _ < ProposedStationaryRealScale.average
          ProposedStationaryRealScale.capitalScale *
            (273246 / 10000000 : ℝ) :=
      mul_lt_mul_of_pos_right hKlo (by norm_num)
    _ < _ := mul_lt_mul_of_pos_left hfactor hKpos

/-- FIRST strict narrow resource sign on the literal SOURCE expression:
the normalized production upper bound is below the aggregate strictly
bounded absorption, so the source residual is strictly negative.
There are NO endpoint-sign hypotheses or externally imported axioms. -/
theorem source_narrow_left_resource_residual_negative :
    boundaryResourceResidual (1029135 / 1000000 : ℝ) < 0 := by
  have hY := source_narrow_left_normalized_output_upper
  have hW := source_narrow_left_worker_consumption_lower
  have hH := source_narrow_left_firm_H_lower
  have hL := source_narrow_left_firm_L_lower
  have hGamma := source_narrow_left_capital_cost_lower
  have hnorm :
      normalizedResourceResidual (1029135 / 1000000 : ℝ) < 0 := by
    unfold normalizedResourceResidual
    linarith only [hY, hW, hH, hL, hGamma]
  exact narrow_left_negative_iff_normalized_negative.mpr hnorm

#print axioms source_narrow_left_firm_H_lower
#print axioms source_narrow_left_firm_L_lower
#print axioms source_narrow_left_capital_cost_lower
#print axioms source_narrow_left_resource_residual_negative

end ProposedBoundaryNarrowLeftResidualSign
end Ventura26LiquidityAllocation

import Ventura26LiquidityAllocation.FirmFaceUniformBoundsCandidate

/-!
# Uniform inherited financial-face incompatibility, original SOURCE model

The intended theorem is: for any fiscal G and every gross rate in the
narrow SOURCE root bracket, inheritedNominalFaceGap > 0.08.

The original entrepreneur face-decline identity, exact stationary wage
normalization, date-zero production/consumption and investment-price
relations all remain source-level expressions. No fitted rate, Python
audit result, axiom, or floating point computation is a proof hypothesis.

This module is a CANDIDATE, not a verified result, until pinned Lean CI
builds it and audits the transitive dependencies for sorryAx.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedFirmFaceUniformGap

open ProposedStationaryBank
open ProposedStationaryPrimitives
open ProposedStationaryInheritedState
open ProposedStationaryRealScale
open ProposedBoundaryBridge
open ProposedBoundaryResourceRoot
open ProposedBoundaryFullPrefix
open ProposedBoundaryEndpointBoxes
open ProposedBoundaryAnalyticPackage
open ProposedBoundaryNormalizationBridge
open ProposedBoundaryNarrowSourceResidualBridge
open ProposedBoundaryNarrowRightCore
open ProposedBoundaryNarrowLeftResidualSign
open ProposedBoundaryNarrowRightResidualSign
open ProposedBoundaryInheritedFaceDecomposition
open ProposedBoundaryInheritedFaceIntervalBridge
open ProposedBoundaryBankFaceUniformLower
open ProposedFirmFaceAccounting
open ProposedFirmFaceNormalization
open ProposedFirmFaceUniformBounds

/-- A sharp upper bound on the ORIGINAL normalized SOURCE output at
the narrow right endpoint, proved by exact 15th-power comparison. -/
theorem source_right_output_lt_1335242 :
    normalizedOutput (1029136 / 1000000 : ℝ) <
      (1335242 / 100000 : ℝ) := by
  let R : ℝ := 1029136 / 1000000
  have hRmem : R ∈ boundaryInterval := by
    change boundaryLo ≤ R ∧ R ≤ boundaryHi
    dsimp [R]
    norm_num [boundaryLo, boundaryHi]
  have hspos : 0 < boundaryCapitalScale R :=
    (boundary_scale_and_investment_domain hRmem).1
  have hrdpos : 0 < boundaryDepositRate R :=
    lt_trans (by norm_num : (0 : ℝ) < 10271889 / 10000000)
      source_narrow_right_deposit_rate_box.1
  have hsUpper := source_narrow_right_capital_scale_box.2
  have hrdUpper := source_narrow_right_deposit_rate_box.2
  have hspow :
      boundaryCapitalScale R ^ (8 : ℕ) <
        (99780695 / 100000000 : ℝ) ^ (8 : ℕ) := by
    gcongr
  have hdpow :
      ((99 / 100 : ℝ) * boundaryDepositRate R) ^ (5 : ℕ) <
        ((99 / 100 : ℝ) * (10271890 / 10000000 : ℝ)) ^ (5 : ℕ) := by
    gcongr
  let x : ℝ :=
    boundaryCapitalScale R ^ (8 : ℕ) *
      ((99 / 100 : ℝ) * boundaryDepositRate R) ^ (5 : ℕ)
  have hx : 0 ≤ x := by
    dsimp [x]
    exact mul_nonneg (pow_nonneg hspos.le _)
      (pow_nonneg (mul_nonneg (by norm_num) hrdpos.le) _)
  have hm1 :
      boundaryCapitalScale R ^ (8 : ℕ) *
          ((99 / 100 : ℝ) * boundaryDepositRate R) ^ (5 : ℕ) <
        (99780695 / 100000000 : ℝ) ^ (8 : ℕ) *
          ((99 / 100 : ℝ) * boundaryDepositRate R) ^ (5 : ℕ) :=
    mul_lt_mul_of_pos_right hspow
      (pow_pos (mul_pos (by norm_num) hrdpos) _)
  have hm2 :
      (99780695 / 100000000 : ℝ) ^ (8 : ℕ) *
          ((99 / 100 : ℝ) * boundaryDepositRate R) ^ (5 : ℕ) <
        (99780695 / 100000000 : ℝ) ^ (8 : ℕ) *
          ((99 / 100 : ℝ) * (10271890 / 10000000 : ℝ)) ^ (5 : ℕ) :=
    mul_lt_mul_of_pos_left hdpow (by norm_num)
  have hpoly : x ≤ (1004431 / 1000000 : ℝ) ^ (15 : ℕ) := by
    apply le_of_lt
    calc
      x <
        (99780695 / 100000000 : ℝ) ^ (8 : ℕ) *
          ((99 / 100 : ℝ) * (10271890 / 10000000 : ℝ)) ^ (5 : ℕ) :=
        lt_trans hm1 hm2
      _ < (1004431 / 1000000 : ℝ) ^ (15 : ℕ) := by norm_num
  have hroot :
      x ^ (1 / 15 : ℝ) ≤ (1004431 / 1000000 : ℝ) :=
    (fifteenth_root_between 0 (1004431 / 1000000 : ℝ) x
      (by norm_num) (by norm_num) hx
      (by simpa using hx) hpoly).2
  have hYpos : 0 < outputScale := aggregate_scales_pos.2.1
  have hYhi := boundary_source_output_scale_sharp_box.2
  change outputScale * x ^ (1 / 15 : ℝ) <
    (1335242 / 100000 : ℝ)
  calc
    _ ≤ outputScale * (1004431 / 1000000 : ℝ) :=
      mul_le_mul_of_nonneg_left hroot hYpos.le
    _ < (13293504 / 1000000 : ℝ) *
          (1004431 / 1000000 : ℝ) :=
      mul_lt_mul_of_pos_right hYhi (by norm_num)
    _ < (1335242 / 100000 : ℝ) := by norm_num

/-- The normalized output bound is UNIFORM, not merely a sample at the
right endpoint. This transfers the already proved strict monotonicity
of original SOURCE output through the exact positive-wage scaling. -/
theorem source_uniform_normalized_output_lt_1335242
    (R : ℝ)
    (hlo : (1029135 / 1000000 : ℝ) ≤ R)
    (hhi : R ≤ (1029136 / 1000000 : ℝ)) :
    normalizedOutput R < (1335242 / 100000 : ℝ) := by
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
  have hYle :
      boundaryAggregateOutput R ≤
        boundaryAggregateOutput (1029136 / 1000000 : ℝ) := by
    rcases lt_or_eq_of_le hhi with hlt | heq
    · exact (aggregateOutput_strictMonoOn hRmem hRight hlt).le
    · rw [heq]
  calc
    normalizedOutput R =
        wage ^ (5 : ℕ) * boundaryAggregateOutput R :=
      (normalized_output_eq_from_source R hRmem).symm
    _ ≤ wage ^ (5 : ℕ) *
        boundaryAggregateOutput (1029136 / 1000000 : ℝ) :=
      mul_le_mul_of_nonneg_left hYle (pow_nonneg wage_pos.le _)
    _ = normalizedOutput (1029136 / 1000000 : ℝ) :=
      normalized_output_eq_from_source _ hRight
    _ < (1335242 / 100000 : ℝ) :=
      source_right_output_lt_1335242

/-- Exact SOURCE normalized entrepreneur consumption has a rate-invariant
numerator: changing the current gross policy rate changes it by 1/R. -/
private theorem source_normalized_firm_rate_identity
    (R : ℝ) (hR : 0 < R) (i : FirmType) :
    R * normalizedFirmConsumption R i =
      (1029135 / 1000000 : ℝ) *
        normalizedFirmConsumption (1029135 / 1000000 : ℝ) i := by
  have hLeft : (0 : ℝ) < 1029135 / 1000000 := by norm_num
  cases i with
  | H =>
      dsimp [normalizedFirmConsumption]
      field_simp [ne_of_gt hR, ne_of_gt hLeft,
        ne_of_gt (parentEffectivePrice_pos .H)] <;> ring
  | L =>
      dsimp [normalizedFirmConsumption]
      field_simp [ne_of_gt hR, ne_of_gt hLeft] <;> ring

/-- Uniform firm H lower box, transported exactly from the SOURCE
left-endpoint original coefficient. -/
theorem source_uniform_firm_H_gt_2957375
    (R : ℝ)
    (hlo : (1029135 / 1000000 : ℝ) ≤ R)
    (hhi : R ≤ (1029136 / 1000000 : ℝ)) :
    (2957375 / 1000000 : ℝ) < normalizedFirmConsumption R .H := by
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num) hlo
  have hbase := source_narrow_left_firm_H_lower
  have hscaled :
      (1029135 / 1000000 : ℝ) * (295738 / 100000 : ℝ) <
        (1029135 / 1000000 : ℝ) *
          normalizedFirmConsumption (1029135 / 1000000 : ℝ) .H :=
    mul_lt_mul_of_pos_left hbase (by norm_num)
  have hrat :
      (1029136 / 1000000 : ℝ) * (2957375 / 1000000 : ℝ) <
        (1029135 / 1000000 : ℝ) * (295738 / 100000 : ℝ) := by
    norm_num
  have hrbound :
      R * (2957375 / 1000000 : ℝ) ≤
        (1029136 / 1000000 : ℝ) * (2957375 / 1000000 : ℝ) :=
    mul_le_mul_of_nonneg_right hhi (by norm_num)
  have hprod :
      R * (2957375 / 1000000 : ℝ) <
        R * normalizedFirmConsumption R .H := by
    calc
      _ ≤ (1029136 / 1000000 : ℝ) *
          (2957375 / 1000000 : ℝ) := hrbound
      _ < (1029135 / 1000000 : ℝ) *
          (295738 / 100000 : ℝ) := hrat
      _ < (1029135 / 1000000 : ℝ) *
          normalizedFirmConsumption (1029135 / 1000000 : ℝ) .H := hscaled
      _ = R * normalizedFirmConsumption R .H :=
        (source_normalized_firm_rate_identity R hRpos .H).symm
  by_contra hn
  have hle : normalizedFirmConsumption R .H ≤ (2957375 / 1000000 : ℝ) :=
    le_of_not_gt hn
  have hm := mul_le_mul_of_nonneg_left hle hRpos.le
  linarith only [hprod, hm]

/-- Uniform firm L lower box with its own exact SOURCE consumption
coefficient (not the H-firm price or pledgeability). -/
theorem source_uniform_firm_L_gt_3810535
    (R : ℝ)
    (hlo : (1029135 / 1000000 : ℝ) ≤ R)
    (hhi : R ≤ (1029136 / 1000000 : ℝ)) :
    (3810535 / 1000000 : ℝ) < normalizedFirmConsumption R .L := by
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num) hlo
  have hbase := source_narrow_left_firm_L_lower
  have hscaled :
      (1029135 / 1000000 : ℝ) * (381054 / 100000 : ℝ) <
        (1029135 / 1000000 : ℝ) *
          normalizedFirmConsumption (1029135 / 1000000 : ℝ) .L :=
    mul_lt_mul_of_pos_left hbase (by norm_num)
  have hrat :
      (1029136 / 1000000 : ℝ) * (3810535 / 1000000 : ℝ) <
        (1029135 / 1000000 : ℝ) * (381054 / 100000 : ℝ) := by
    norm_num
  have hrbound :
      R * (3810535 / 1000000 : ℝ) ≤
        (1029136 / 1000000 : ℝ) * (3810535 / 1000000 : ℝ) :=
    mul_le_mul_of_nonneg_right hhi (by norm_num)
  have hprod :
      R * (3810535 / 1000000 : ℝ) <
        R * normalizedFirmConsumption R .L := by
    calc
      _ ≤ (1029136 / 1000000 : ℝ) *
          (3810535 / 1000000 : ℝ) := hrbound
      _ < (1029135 / 1000000 : ℝ) *
          (381054 / 100000 : ℝ) := hrat
      _ < (1029135 / 1000000 : ℝ) *
          normalizedFirmConsumption (1029135 / 1000000 : ℝ) .L := hscaled
      _ = R * normalizedFirmConsumption R .L :=
        (source_normalized_firm_rate_identity R hRpos .L).symm
  by_contra hn
  have hle : normalizedFirmConsumption R .L ≤ (3810535 / 1000000 : ℝ) :=
    le_of_not_gt hn
  have hm := mul_le_mul_of_nonneg_left hle hRpos.le
  linarith only [hprod, hm]

/-- Uniformly positive SOURCE loan/credit compensation for the
inherited entrepreneurs at any rate in the six-decimal root bracket. -/
theorem source_uniform_credit_term_gt_64616
    (R : ℝ)
    (hlo : (1029135 / 1000000 : ℝ) ≤ R) :
    (64616 / 100000 : ℝ) <
      (1 - 1 / R) * ProposedStationaryBank.loanRate * creditScale := by
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num) hlo
  have hfracLo : (2831 / 100000 : ℝ) < 1 - 1 / R := by
    have haux :
        (1 : ℝ) / R < 1 - (2831 / 100000 : ℝ) := by
      apply (div_lt_iff₀ hRpos).2
      nlinarith only [hlo]
    linarith only [haux]
  have hfracPos : 0 < 1 - 1 / R :=
    lt_trans (by norm_num) hfracLo
  have hLoanLo := boundary_source_loan_rate_sharp_box.1
  have hCredLo := source_stationary_credit_scale_gt_225529
  have hFirst :
      (2831 / 100000 : ℝ) *
        (101204823607 / 100000000000 : ℝ) *
        (225529 / 10000 : ℝ) <
      (1 - 1 / R) *
        (101204823607 / 100000000000 : ℝ) *
        (225529 / 10000 : ℝ) := by
    have h := mul_lt_mul_of_pos_right hfracLo
      (by norm_num :
        (0 : ℝ) <
          (101204823607 / 100000000000 : ℝ) *
            (225529 / 10000 : ℝ))
    simpa only [mul_assoc] using h
  have hSecond :
      (1 - 1 / R) *
          (101204823607 / 100000000000 : ℝ) *
          (225529 / 10000 : ℝ) <
      (1 - 1 / R) * ProposedStationaryBank.loanRate *
          (225529 / 10000 : ℝ) := by
    have h := mul_lt_mul_of_pos_left hLoanLo hfracPos
    exact mul_lt_mul_of_pos_right h (by norm_num)
  have hThird :
      (1 - 1 / R) * ProposedStationaryBank.loanRate *
          (225529 / 10000 : ℝ) <
      (1 - 1 / R) * ProposedStationaryBank.loanRate * creditScale :=
    mul_lt_mul_of_pos_left hCredLo
      (mul_pos hfracPos ProposedStationaryRealScale.loanRate_pos)
  calc
    (64616 / 100000 : ℝ) <
        (2831 / 100000 : ℝ) *
          (101204823607 / 100000000000 : ℝ) *
          (225529 / 10000 : ℝ) := by norm_num
    _ < _ := hFirst
    _ < _ := hSecond
    _ < _ := hThird

/-- Minimum SOURCE capital revaluation term on the narrow interval,
including the ORIGINAL date-zero capital-price formula. -/
theorem source_uniform_capital_revaluation_gt_207794
    (R : ℝ)
    (hlo : (1029135 / 1000000 : ℝ) ≤ R)
    (hhi : R ≤ (1029136 / 1000000 : ℝ)) :
    (207794 / 100000 : ℝ) <
      boundaryCapitalPrice R * average capitalScale *
        (1 - (39 / 40 : ℝ) * boundaryCapitalScale R) := by
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num) hlo
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
  have hSle :
      boundaryCapitalScale R ≤
        boundaryCapitalScale (1029136 / 1000000 : ℝ) := by
    rcases lt_or_eq_of_le hhi with hlt | heq
    · exact (capitalScale_strictMonoOn hRmem hRight hlt).le
    · rw [heq]
  have hSUpper :
      boundaryCapitalScale R < (99780695 / 100000000 : ℝ) :=
    lt_of_le_of_lt hSle source_narrow_right_capital_scale_box.2
  have hFactor :
      (27138 / 1000000 : ℝ) <
        1 - (39 / 40 : ℝ) * boundaryCapitalScale R := by
    linarith only [hSUpper]
  have hPrice :
      (101359 / 100000 : ℝ) < boundaryCapitalPrice R := by
    unfold boundaryCapitalPrice continuationReturn
    apply (lt_div_iff₀ hRpos).2
    have huLlo := (boundary_source_user_cost_sharp_boxes).2.1
    dsimp [liquidationValue, capitalPrice]
    linarith only [huLlo, hhi]
  have hPricePos : 0 < boundaryCapitalPrice R :=
    lt_trans (by norm_num) hPrice
  have hKlo :
      (7554294 / 100000 : ℝ) < average capitalScale := by
    rcases boundary_source_capital_scales_sharp_boxes with
      ⟨⟨hkHlo, _⟩, ⟨hkLlo, _⟩⟩
    unfold average
    linarith only [hkHlo, hkLlo]
  have hKpos : 0 < average capitalScale := aggregate_scales_pos.1
  have hFirst :
      (101359 / 100000 : ℝ) *
        (7554294 / 100000 : ℝ) *
        (27138 / 1000000 : ℝ) <
      boundaryCapitalPrice R *
        (7554294 / 100000 : ℝ) *
        (27138 / 1000000 : ℝ) := by
    have h := mul_lt_mul_of_pos_right hPrice
      (by norm_num : (0 : ℝ) <
        (7554294 / 100000 : ℝ) *
        (27138 / 1000000 : ℝ))
    simpa only [mul_assoc] using h
  have hSecond :
      boundaryCapitalPrice R *
        (7554294 / 100000 : ℝ) *
        (27138 / 1000000 : ℝ) <
      boundaryCapitalPrice R * average capitalScale *
        (27138 / 1000000 : ℝ) := by
    have h := mul_lt_mul_of_pos_left hKlo hPricePos
    exact mul_lt_mul_of_pos_right h (by norm_num)
  have hThird :
      boundaryCapitalPrice R * average capitalScale *
        (27138 / 1000000 : ℝ) <
      boundaryCapitalPrice R * average capitalScale *
        (1 - (39 / 40 : ℝ) * boundaryCapitalScale R) :=
    mul_lt_mul_of_pos_left hFactor (mul_pos hPricePos hKpos)
  calc
    (207794 / 100000 : ℝ) <
        (101359 / 100000 : ℝ) *
          (7554294 / 100000 : ℝ) *
          (27138 / 1000000 : ℝ) := by norm_num
    _ < _ := hFirst
    _ < _ := hSecond
    _ < _ := hThird

/-- Final entrepreneur obligation reduction. Five independently
SOURCE-derived, uniform boxes imply the exact normalized decline is
larger than 0.5445, while the stationary wage scaling guarantees
0.11*w^5 < 0.540638. Thus the ORIGINAL unscaled decline exceeds 0.11. -/
theorem source_uniform_firm_face_decline_gt_11_percent
    (G R : ℝ)
    (hlo : (1029135 / 1000000 : ℝ) ≤ R)
    (hhi : R ≤ (1029136 / 1000000 : ℝ)) :
    (11 / 100 : ℝ) <
      (∑ i, (primitives G).mass i *
        ((inheritedState G).firmFace i -
          boundaryInheritedFace G R (boundaryZeroSeed G R) i)) := by
  have hRmem : R ∈ boundaryInterval := by
    change boundaryLo ≤ R ∧ R ≤ boundaryHi
    constructor
    · exact le_trans (by norm_num [boundaryLo]) hlo
    · exact le_trans hhi (by norm_num [boundaryHi])
  have hY := source_uniform_normalized_output_lt_1335242 R hlo hhi
  have hH := source_uniform_firm_H_gt_2957375 R hlo hhi
  have hL := source_uniform_firm_L_gt_3810535 R hlo hhi
  have hCredit := source_uniform_credit_term_gt_64616 R hlo
  have hValuation := source_uniform_capital_revaluation_gt_207794 R hlo hhi
  have hAvg :
      (3383955 / 1000000 : ℝ) <
        average (normalizedFirmConsumption R) := by
    unfold average
    linarith only [hH, hL]
  have hNorm :
      (5445 / 10000 : ℝ) <
        (1 - 1 / R) * ProposedStationaryBank.loanRate * creditScale -
          (5 / 12 : ℝ) * normalizedOutput R +
          average (normalizedFirmConsumption R) +
          boundaryCapitalPrice R * average capitalScale *
            (1 - (39 / 40 : ℝ) * boundaryCapitalScale R) := by
    linarith only [hY, hAvg, hCredit, hValuation]
  have hWage5 :
      wage ^ (5 : ℕ) < (11 / 8 : ℝ) ^ (5 : ℕ) := by
    gcongr
    exact source_stationary_wage_lt_11_8
  have hWage5pos : 0 < wage ^ (5 : ℕ) := pow_pos wage_pos _
  have hThreshold :
      (11 / 100 : ℝ) * wage ^ (5 : ℕ) <
        (5445 / 10000 : ℝ) := by
    calc
      _ < (11 / 100 : ℝ) * (11 / 8 : ℝ) ^ (5 : ℕ) :=
        mul_lt_mul_of_pos_left hWage5 (by norm_num)
      _ < (5445 / 10000 : ℝ) := by norm_num
  by_contra hn
  have hFirmLe :
      (∑ i, (primitives G).mass i *
        ((inheritedState G).firmFace i -
          boundaryInheritedFace G R (boundaryZeroSeed G R) i)) ≤
        (11 / 100 : ℝ) := le_of_not_gt hn
  have hScaled :=
    mul_le_mul_of_nonneg_left hFirmLe hWage5pos.le
  rw [source_firm_face_decline_normalized_exact G R hRmem] at hScaled
  linarith only [hNorm, hThreshold, hScaled]

/-- The last of the three SOURCE sign obligations:
the original inherited nominal-face inconsistency exceeds eight percent
UNIFORMLY for every fiscal G and every candidate rate in the narrow
bracket. Both the positive firm and negative bank components are kept. -/
theorem source_uniform_inherited_nominal_face_gap_gt_eight_percent
    (G R : ℝ)
    (hlo : (1029135 / 1000000 : ℝ) ≤ R)
    (hhi : R ≤ (1029136 / 1000000 : ℝ)) :
    (8 / 100 : ℝ) <
      inheritedNominalFaceGap
        (boundaryPrimitives G R) (boundaryInitialState G R) := by
  have hFirm := source_uniform_firm_face_decline_gt_11_percent G R hlo hhi
  have hBank :=
    source_narrow_bank_face_contribution_gt_neg_three_percent G R hlo hhi
  rw [boundaryInheritedGap_eq_face_shifts G R]
  linarith only [hFirm, hBank]

/-- The previously conditional no-competitive-equilibrium theorem now
has NO numerical sign assumptions. This excludes the specific
SOURCE reduced-prefix boundary candidate with its endogenous
policy-dependent inherited state, not every alternative equilibrium. -/
theorem source_boundary_candidate_not_competitive_equilibrium
    (G : ℝ) (X : Allocation LocalBridgePhase) :
    ¬ CompetitiveEquilibrium
      (boundaryPrimitives G boundarySourceRate)
      (boundaryInitialState G boundarySourceRate) X := by
  exact noCompetitiveEquilibrium_of_exact_interval_inequalities
    G X
    source_narrow_left_resource_residual_negative
    source_narrow_right_resource_residual_positive
    (fun R hlo hhi =>
      source_uniform_inherited_nominal_face_gap_gt_eight_percent
        G R hlo hhi)

#print axioms source_right_output_lt_1335242
#print axioms source_uniform_normalized_output_lt_1335242
#print axioms source_uniform_firm_H_gt_2957375
#print axioms source_uniform_firm_L_gt_3810535
#print axioms source_uniform_credit_term_gt_64616
#print axioms source_uniform_capital_revaluation_gt_207794
#print axioms source_uniform_firm_face_decline_gt_11_percent
#print axioms source_uniform_inherited_nominal_face_gap_gt_eight_percent
#print axioms source_boundary_candidate_not_competitive_equilibrium

end ProposedFirmFaceUniformGap
end Ventura26LiquidityAllocation

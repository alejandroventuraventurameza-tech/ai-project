import Ventura26LiquidityAllocation.BoundaryNarrowLeftResidualSignCandidate

/-!
# Original SOURCE narrow-right pricing, capital, and production certificates

Unconditional exact rational micro-boxes at the ORIGINAL residual's right
narrow endpoint, R=1029136/1000000. All source coefficients and continuous
power identities are inherited from the pinned kernel-checked normalization
chain. The independent Python interval audit is NOT imported as an axiom.

These three component bounds do not yet establish the full right-endpoint
resource sign. For that result, SOURCE worker consumption, firm consumption
and installation cost need sharp upper enclosures on the same endpoint.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedBoundaryNarrowRightCore

open ProposedStationaryBank
open ProposedStationaryRealScale
open ProposedBoundaryBridge
open ProposedBoundaryResourceRoot
open ProposedBoundaryEndpointBoxes
open ProposedBoundaryNormalizationBridge

/-- Certified date-zero deposit-rate rational box at the narrow right end. -/
theorem source_narrow_right_deposit_rate_box :
    (10271889 / 10000000 : ℝ) <
      boundaryDepositRate (1029136 / 1000000 : ℝ) ∧
    boundaryDepositRate (1029136 / 1000000 : ℝ) <
      (10271890 / 10000000 : ℝ) := by
  let R : ℝ := 1029136 / 1000000
  have hRmem : R ∈ boundaryInterval := by
    change boundaryLo ≤ R ∧ R ≤ boundaryHi
    dsimp [R]
    norm_num [boundaryLo, boundaryHi]
  have hrrpos : 0 < boundaryReserveRate R :=
    (boundary_rate_domain hRmem).2
  rcases boundary_source_slope_rational_micro_boxes with
    ⟨⟨hmlo, hmhi⟩, ⟨hglo, hghi⟩⟩
  have hpaypos : 0 < boundaryPaymentTerm := by
    unfold boundaryPaymentTerm
    linarith only [hglo]
  have hnumLo :
      (1028421357179 / 1000000000000 : ℝ) <
        boundaryReserveRate R +
          (9 / 10 : ℝ) * meanSlope +
          (1 / 10 : ℝ) * boundaryPaymentTerm := by
    dsimp [R]
    unfold boundaryReserveRate boundaryPaymentTerm
    linarith only [hmhi, hglo]
  have hnumHi :
      boundaryReserveRate R +
        (9 / 10 : ℝ) * meanSlope +
        (1 / 10 : ℝ) * boundaryPaymentTerm <
      (1028421357181 / 1000000000000 : ℝ) := by
    dsimp [R]
    unfold boundaryReserveRate boundaryPaymentTerm
    linarith only [hmlo, hghi]
  have hfracLo :
      (1199830596 / 1000000000000 : ℝ) <
        boundaryPaymentTerm / boundaryReserveRate R := by
    apply (lt_div_iff₀ hrrpos).2
    dsimp [R]
    unfold boundaryPaymentTerm boundaryReserveRate
    linarith only [hmlo, hglo]
  have hfracHi :
      boundaryPaymentTerm / boundaryReserveRate R <
        (1199830597 / 1000000000000 : ℝ) := by
    apply (div_lt_iff₀ hrrpos).2
    dsimp [R]
    unfold boundaryPaymentTerm boundaryReserveRate
    linarith only [hmhi, hghi]
  have hdenpos :
      0 < 1 + boundaryPaymentTerm / boundaryReserveRate R := by
    have hp : 0 < boundaryPaymentTerm / boundaryReserveRate R :=
      div_pos hpaypos hrrpos
    linarith only [hp]
  have hdenLo :
      1 + (1199830596 / 1000000000000 : ℝ) <
        1 + boundaryPaymentTerm / boundaryReserveRate R := by
    linarith only [hfracLo]
  have hdenHi :
      1 + boundaryPaymentTerm / boundaryReserveRate R <
        1 + (1199830597 / 1000000000000 : ℝ) := by
    linarith only [hfracHi]
  change (10271889 / 10000000 : ℝ) <
      (boundaryReserveRate (1029136 / 1000000 : ℝ) +
          (9 / 10 : ℝ) * meanSlope +
          (1 / 10 : ℝ) * boundaryPaymentTerm) /
        (1 + boundaryPaymentTerm /
          boundaryReserveRate (1029136 / 1000000 : ℝ)) ∧
    (boundaryReserveRate (1029136 / 1000000 : ℝ) +
          (9 / 10 : ℝ) * meanSlope +
          (1 / 10 : ℝ) * boundaryPaymentTerm) /
        (1 + boundaryPaymentTerm /
          boundaryReserveRate (1029136 / 1000000 : ℝ)) <
      (10271890 / 10000000 : ℝ)
  constructor
  · apply (lt_div_iff₀ hdenpos).2
    calc
      (10271889 / 10000000 : ℝ) *
          (1 + boundaryPaymentTerm /
            boundaryReserveRate (1029136 / 1000000 : ℝ)) <
        (10271889 / 10000000 : ℝ) *
          (1 + (1199830597 / 1000000000000 : ℝ)) :=
          mul_lt_mul_of_pos_left hdenHi (by norm_num)
      _ < (1028421357179 / 1000000000000 : ℝ) := by norm_num
      _ < _ := hnumLo
  · apply (div_lt_iff₀ hdenpos).2
    calc
      boundaryReserveRate (1029136 / 1000000 : ℝ) +
          (9 / 10 : ℝ) * meanSlope +
          (1 / 10 : ℝ) * boundaryPaymentTerm <
        (1028421357181 / 1000000000000 : ℝ) := hnumHi
      _ < (10271890 / 10000000 : ℝ) *
          (1 + (1199830596 / 1000000000000 : ℝ)) := by norm_num
      _ < (10271890 / 10000000 : ℝ) *
          (1 + boundaryPaymentTerm /
            boundaryReserveRate (1029136 / 1000000 : ℝ)) :=
          mul_lt_mul_of_pos_left hdenLo (by norm_num)

/-- Tight capital scaling using the SOURCE stationary L user-cost box. -/
theorem source_narrow_right_capital_scale_box :
    (99780694 / 100000000 : ℝ) <
      boundaryCapitalScale (1029136 / 1000000 : ℝ) ∧
    boundaryCapitalScale (1029136 / 1000000 : ℝ) <
      (99780695 / 100000000 : ℝ) := by
  let R : ℝ := 1029136 / 1000000
  have hRpos : 0 < R := by norm_num [R]
  rcases (boundary_source_user_cost_sharp_boxes).2 with
    ⟨huLlo, huLhi⟩
  have hJ : liquidationValue = (3159 / 3200 : ℝ) := by
    norm_num [liquidationValue, capitalPrice]
  have hV :
      continuationReturn .L =
        userCost .L + (3159 / 3200 : ℝ) := by
    unfold continuationReturn
    rw [hJ]
  have hden :
      0 < 2 * continuationReturn .L - (41 / 40 : ℝ) * R := by
    rw [hV]
    dsimp [R]
    linarith only [huLlo]
  change (99780694 / 100000000 : ℝ) < boundaryCapitalScale R ∧
    boundaryCapitalScale R < (99780695 / 100000000 : ℝ)
  rw [boundaryCapitalScale_rewrite R (ne_of_gt hRpos)]
  constructor
  · apply (lt_div_iff₀ hden).2
    rw [hV]
    dsimp [R]
    linarith only [huLhi]
  · apply (div_lt_iff₀ hden).2
    rw [hV]
    dsimp [R]
    linarith only [huLlo]

/-- Direct SOURCE production lower enclosure on the narrow-right rate,
obtained from a fifteenth-power rational comparison, not a numerical
sampling surrogate or a hypothesis on the residual. -/
theorem source_narrow_right_normalized_output_lower :
    (1335239 / 100000 : ℝ) <
      normalizedOutput (1029136 / 1000000 : ℝ) := by
  let R : ℝ := 1029136 / 1000000
  have hslo :
      (99780694 / 100000000 : ℝ) < boundaryCapitalScale R :=
    source_narrow_right_capital_scale_box.1
  have hrlo :
      (10271889 / 10000000 : ℝ) < boundaryDepositRate R :=
    source_narrow_right_deposit_rate_box.1
  have hspow :
      (99780694 / 100000000 : ℝ) ^ (8 : ℕ) <
        boundaryCapitalScale R ^ (8 : ℕ) := by
    gcongr
  have hdscaled :
      (99 / 100 : ℝ) * (10271889 / 10000000 : ℝ) <
        (99 / 100 : ℝ) * boundaryDepositRate R :=
    mul_lt_mul_of_pos_left hrlo (by norm_num)
  have hdpow :
      ((99 / 100 : ℝ) * (10271889 / 10000000 : ℝ)) ^ (5 : ℕ) <
        ((99 / 100 : ℝ) * boundaryDepositRate R) ^ (5 : ℕ) := by
    gcongr
  let x : ℝ :=
    boundaryCapitalScale R ^ (8 : ℕ) *
      ((99 / 100 : ℝ) * boundaryDepositRate R) ^ (5 : ℕ)
  have hm1 :
      (99780694 / 100000000 : ℝ) ^ (8 : ℕ) *
          ((99 / 100 : ℝ) * (10271889 / 10000000 : ℝ)) ^ (5 : ℕ) <
        boundaryCapitalScale R ^ (8 : ℕ) *
          ((99 / 100 : ℝ) * (10271889 / 10000000 : ℝ)) ^ (5 : ℕ) :=
    mul_lt_mul_of_pos_right hspow (by norm_num)
  have hm2 :
      boundaryCapitalScale R ^ (8 : ℕ) *
          ((99 / 100 : ℝ) * (10271889 / 10000000 : ℝ)) ^ (5 : ℕ) <
        boundaryCapitalScale R ^ (8 : ℕ) *
          ((99 / 100 : ℝ) * boundaryDepositRate R) ^ (5 : ℕ) :=
    mul_lt_mul_of_pos_left hdpow
      (pow_pos (lt_trans (by norm_num) hslo) _)
  have hpoly :
      (10044302 / 10000000 : ℝ) ^ (15 : ℕ) ≤ x := by
    apply le_of_lt
    calc
      (10044302 / 10000000 : ℝ) ^ (15 : ℕ) <
        (99780694 / 100000000 : ℝ) ^ (8 : ℕ) *
          ((99 / 100 : ℝ) * (10271889 / 10000000 : ℝ)) ^ (5 : ℕ) := by
        norm_num
      _ < _ := hm1
      _ < x := hm2
  have hroot :
      (10044302 / 10000000 : ℝ) ≤ x ^ (1 / 15 : ℝ) := by
    have h := Real.rpow_le_rpow
      (pow_nonneg (by norm_num :
        (0 : ℝ) ≤ (10044302 / 10000000 : ℝ)) (15 : ℕ))
      hpoly (by norm_num : (0 : ℝ) ≤ 1 / 15)
    calc
      (10044302 / 10000000 : ℝ) =
          ((10044302 / 10000000 : ℝ) ^ (15 : ℕ)) ^
            (1 / 15 : ℝ) := by
        simpa only [one_div] using
          (Real.pow_rpow_inv_natCast
            (by norm_num :
              (0 : ℝ) ≤ (10044302 / 10000000 : ℝ))
            (by norm_num : (15 : ℕ) ≠ 0)).symm
      _ ≤ x ^ (1 / 15 : ℝ) := h
  have hYlo := boundary_source_output_scale_sharp_box.1
  have hYpos : 0 < outputScale := aggregate_scales_pos.2.1
  change (1335239 / 100000 : ℝ) < outputScale * x ^ (1 / 15 : ℝ)
  calc
    (1335239 / 100000 : ℝ) <
        (13293498 / 1000000 : ℝ) *
          (10044302 / 10000000 : ℝ) := by norm_num
    _ < outputScale * (10044302 / 10000000 : ℝ) :=
      mul_lt_mul_of_pos_right hYlo (by norm_num)
    _ ≤ _ := mul_le_mul_of_nonneg_left hroot hYpos.le

#print axioms source_narrow_right_deposit_rate_box
#print axioms source_narrow_right_capital_scale_box
#print axioms source_narrow_right_normalized_output_lower

end ProposedBoundaryNarrowRightCore
end Ventura26LiquidityAllocation

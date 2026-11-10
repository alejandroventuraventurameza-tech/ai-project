import Ventura26LiquidityAllocation.BoundaryNarrowSourceResidualBridgeCandidate

/-!
# A source-derived narrow-endpoint deposit-price interval

Strict rational enclosures for the original date-zero deposit rate at
R = 1029135 / 1000000. The interval is obtained exclusively from the
already kernel-checked stationary OTC slope micro-boxes and positive
denominators, not from a numerical certificate treated as a premise.

This is one source-side component certificate. It is not a proof of the
sign of the full resource residual or existence of a competitive equilibrium.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedBoundaryNarrowDepositBox

open ProposedStationaryBank
open ProposedBoundaryResourceRoot
open ProposedBoundaryNormalizationBridge
open ProposedBoundaryEndpointBoxes

/-- Original SOURCE deposit remuneration, at the lower narrow rate,
lies in a fully rational interval of width 10^(-7). -/
theorem source_narrow_left_deposit_rate_box :
    (10271879 / 10000000 : ℝ) <
      boundaryDepositRate (1029135 / 1000000 : ℝ) ∧
    boundaryDepositRate (1029135 / 1000000 : ℝ) <
      (10271880 / 10000000 : ℝ) := by
  let R : ℝ := 1029135 / 1000000
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
      (1028420357179 / 1000000000000 : ℝ) <
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
      (1028420357181 / 1000000000000 : ℝ) := by
    dsimp [R]
    unfold boundaryReserveRate boundaryPaymentTerm
    linarith only [hmlo, hghi]
  have hfracLo :
      (1199831771 / 1000000000000 : ℝ) <
        boundaryPaymentTerm / boundaryReserveRate R := by
    apply (lt_div_iff₀ hrrpos).2
    dsimp [R]
    unfold boundaryPaymentTerm boundaryReserveRate
    linarith only [hmlo, hglo]
  have hfracHi :
      boundaryPaymentTerm / boundaryReserveRate R <
        (1199831773 / 1000000000000 : ℝ) := by
    apply (div_lt_iff₀ hrrpos).2
    dsimp [R]
    unfold boundaryPaymentTerm boundaryReserveRate
    linarith only [hmhi, hghi]
  have hdenpos :
      0 < 1 + boundaryPaymentTerm / boundaryReserveRate R := by
    have hpos : 0 < boundaryPaymentTerm / boundaryReserveRate R :=
      div_pos hpaypos hrrpos
    linarith only [hpos]
  have hdenLo :
      1 + (1199831771 / 1000000000000 : ℝ) <
        1 + boundaryPaymentTerm / boundaryReserveRate R := by
    linarith only [hfracLo]
  have hdenHi :
      1 + boundaryPaymentTerm / boundaryReserveRate R <
        1 + (1199831773 / 1000000000000 : ℝ) := by
    linarith only [hfracHi]
  change (10271879 / 10000000 : ℝ) <
      (boundaryReserveRate (1029135 / 1000000 : ℝ) +
        (9 / 10 : ℝ) * meanSlope +
        (1 / 10 : ℝ) * boundaryPaymentTerm) /
        (1 + boundaryPaymentTerm /
          boundaryReserveRate (1029135 / 1000000 : ℝ)) ∧
    (boundaryReserveRate (1029135 / 1000000 : ℝ) +
        (9 / 10 : ℝ) * meanSlope +
        (1 / 10 : ℝ) * boundaryPaymentTerm) /
        (1 + boundaryPaymentTerm /
          boundaryReserveRate (1029135 / 1000000 : ℝ)) <
      (10271880 / 10000000 : ℝ)
  constructor
  · apply (lt_div_iff₀ hdenpos).2
    calc
      (10271879 / 10000000 : ℝ) *
          (1 + boundaryPaymentTerm /
            boundaryReserveRate (1029135 / 1000000 : ℝ)) <
        (10271879 / 10000000 : ℝ) *
          (1 + (1199831773 / 1000000000000 : ℝ)) :=
          mul_lt_mul_of_pos_left hdenHi (by norm_num)
      _ < (1028420357179 / 1000000000000 : ℝ) := by norm_num
      _ < _ := hnumLo
  · apply (div_lt_iff₀ hdenpos).2
    calc
      boundaryReserveRate (1029135 / 1000000 : ℝ) +
          (9 / 10 : ℝ) * meanSlope +
          (1 / 10 : ℝ) * boundaryPaymentTerm <
        (1028420357181 / 1000000000000 : ℝ) := hnumHi
      _ < (10271880 / 10000000 : ℝ) *
          (1 + (1199831771 / 1000000000000 : ℝ)) := by norm_num
      _ < (10271880 / 10000000 : ℝ) *
          (1 + boundaryPaymentTerm /
            boundaryReserveRate (1029135 / 1000000 : ℝ)) :=
          mul_lt_mul_of_pos_left hdenLo (by norm_num)

/-- First directly source-derived component bound at the narrow left
resource endpoint. The proof combines the exact stationary worker
consumption-scale lower box with the original SOURCE deposit-price upper
box; the final product comparison is entirely rational. This is not yet
the sign of the full SOURCE resource residual. -/
theorem source_narrow_left_worker_consumption_lower :
    (790435 / 100000 : ℝ) <
      normalizedWorkerConsumption (1029135 / 1000000 : ℝ) := by
  have hw := boundary_worker_consumption_scale_lower
  have hrd := source_narrow_left_deposit_rate_box.2
  have hRmem :
      (1029135 / 1000000 : ℝ) ∈ boundaryInterval := by
    change boundaryLo ≤ (1029135 / 1000000 : ℝ) ∧
      (1029135 / 1000000 : ℝ) ≤ boundaryHi
    norm_num [boundaryLo, boundaryHi]
  have hden :
      0 < (99 / 100 : ℝ) *
        boundaryDepositRate (1029135 / 1000000 : ℝ) :=
    mul_pos (by norm_num) (boundaryDepositRate_pos hRmem)
  unfold normalizedWorkerConsumption
  apply (lt_div_iff₀ hden).2
  have hrate :
      (99 / 100 : ℝ) *
        boundaryDepositRate (1029135 / 1000000 : ℝ) <
      (99 / 100 : ℝ) * (10271880 / 10000000 : ℝ) :=
    mul_lt_mul_of_pos_left hrd (by norm_num)
  have hprod :
      (790435 / 100000 : ℝ) *
          ((99 / 100 : ℝ) *
            boundaryDepositRate (1029135 / 1000000 : ℝ)) <
      (790435 / 100000 : ℝ) *
          ((99 / 100 : ℝ) * (10271880 / 10000000 : ℝ)) :=
    mul_lt_mul_of_pos_left hrate (by norm_num)
  calc
    _ < (790435 / 100000 : ℝ) *
          ((99 / 100 : ℝ) * (10271880 / 10000000 : ℝ)) := hprod
    _ < (8038062 / 1000000 : ℝ) := by norm_num
    _ < _ := hw

#print axioms source_narrow_left_deposit_rate_box
#print axioms source_narrow_left_worker_consumption_lower

end ProposedBoundaryNarrowDepositBox
end Ventura26LiquidityAllocation

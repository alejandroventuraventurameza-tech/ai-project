import Ventura26LiquidityAllocation.FirmFaceNormalizationCandidate

/-!
# Structural stationary enclosures for the final SOURCE inherited-face gap

Every inequality is derived from SOURCE stationary real-price and capital
micro-boxes and the original banking budget. No fitted wage, numerical
root, or independent interval audit enters as a proof assumption.

These are CANDIDATE Lean proofs until the pinned CI compiles them and
audits the transitive axioms. Firm-face gap uniformity is not concluded
by the bounds in this file alone.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedFirmFaceUniformBounds

open ProposedStationaryBank
open ProposedStationaryRealScale
open ProposedBoundaryNormalizationBridge
open ProposedBoundaryNarrowRightResidualSign

/-- Stationary wage lies below 11/8. Unlike a numerical wage
evaluation, the proof compares its exact twelfth power with the
SOURCE-based stationary labor and consumption coefficient boxes. -/
theorem source_stationary_wage_lt_11_8 :
    wage < (11 / 8 : ℝ) := by
  rcases boundary_source_user_cost_sharp_boxes with
    ⟨⟨_, huHhi⟩, ⟨_, huLhi⟩⟩
  rcases boundary_source_capital_scales_sharp_boxes with
    ⟨⟨_, hkHhi⟩, ⟨_, hkLhi⟩⟩
  have hHpos : 0 < userCost .H := userCost_pos .H
  have hLpos : 0 < userCost .L := userCost_pos .L
  have hkHpos : 0 < capitalScale .H := capitalScale_pos .H
  have hkLpos : 0 < capitalScale .L := capitalScale_pos .L
  have hprodH :
      userCost .H * capitalScale .H <
        (63166372 / 1000000000 : ℝ) *
          (5677037 / 100000 : ℝ) := by
    calc
      _ < (63166372 / 1000000000 : ℝ) * capitalScale .H :=
        mul_lt_mul_of_pos_right huHhi hkHpos
      _ < (63166372 / 1000000000 : ℝ) *
          (5677037 / 100000 : ℝ) :=
        mul_lt_mul_of_pos_left hkHhi (by norm_num)
  have hprodL :
      userCost .L * capitalScale .L <
        (55943657 / 1000000000 : ℝ) *
          (9431556 / 100000 : ℝ) := by
    calc
      _ < (55943657 / 1000000000 : ℝ) * capitalScale .L :=
        mul_lt_mul_of_pos_right huLhi hkLpos
      _ < (55943657 / 1000000000 : ℝ) *
          (9431556 / 100000 : ℝ) :=
        mul_lt_mul_of_pos_left hkLhi (by norm_num)
  have hLabor : laborScale < (277 / 50 : ℝ) := by
    unfold laborScale average
    linarith only [hprodH, hprodL]
  have hC := source_stationary_worker_scale_sharp_upper
  have hLaborPos := aggregate_scales_pos.2.2.1
  have hWorkerPos := aggregate_scales_pos.2.2.2.2
  have hProduct :
      laborScale * workerConsumptionScale <
        (277 / 50 : ℝ) * (8038071 / 1000000 : ℝ) := by
    calc
      _ < (277 / 50 : ℝ) * workerConsumptionScale :=
        mul_lt_mul_of_pos_right hLabor hWorkerPos
      _ < _ := mul_lt_mul_of_pos_left hC (by norm_num)
  have hRational :
      (277 / 50 : ℝ) * (8038071 / 1000000 : ℝ) <
        (11 / 8 : ℝ) ^ (12 : ℕ) := by norm_num
  by_contra hn
  have hwGe : (11 / 8 : ℝ) ≤ wage := le_of_not_gt hn
  have hPow :
      (11 / 8 : ℝ) ^ (12 : ℕ) ≤ wage ^ (12 : ℕ) := by
    gcongr
  rw [wage_pow_twelve] at hPow
  linarith only [hProduct, hRational, hPow]

/-- SOURCE exact loan-face numerator and the sharp stationary capital
boxes imply the strict credit-scale lower bound 22.5529. -/
theorem source_stationary_credit_scale_gt_225529 :
    (225529 / 10000 : ℝ) < creditScale := by
  rcases boundary_source_capital_scales_sharp_boxes with
    ⟨⟨hkHlo, _⟩, ⟨hkLlo, _⟩⟩
  have hLoanPos : 0 < ProposedStationaryBank.loanRate :=
    ProposedStationaryRealScale.loanRate_pos
  have hLoanHi := boundary_source_loan_rate_sharp_box.2
  have hScaled :
      creditScale * ProposedStationaryBank.loanRate =
        ((3 / 20 : ℝ) * (3159 / 3200 : ℝ) * capitalScale .H +
          (2 / 5 : ℝ) * (3159 / 3200 : ℝ) * capitalScale .L) / 2 := by
    unfold creditScale average pledgeability liquidationValue capitalPrice
    field_simp [ne_of_gt hLoanPos] <;> ring
  have hLower :
      (225529 / 10000 : ℝ) *
          (101204823808 / 100000000000 : ℝ) <
        ((3 / 20 : ℝ) * (3159 / 3200 : ℝ) * capitalScale .H +
          (2 / 5 : ℝ) * (3159 / 3200 : ℝ) * capitalScale .L) / 2 := by
    linarith only [hkHlo, hkLlo]
  by_contra hn
  have hCreditLe : creditScale ≤ (225529 / 10000 : ℝ) :=
    le_of_not_gt hn
  have hMul :=
    mul_le_mul_of_nonneg_right hCreditLe hLoanPos.le
  rw [hScaled] at hMul
  have hLoanBound :
      (225529 / 10000 : ℝ) * ProposedStationaryBank.loanRate <
        (225529 / 10000 : ℝ) *
          (101204823808 / 100000000000 : ℝ) :=
    mul_lt_mul_of_pos_left hLoanHi (by norm_num)
  linarith only [hLower, hMul, hLoanBound]

#print axioms source_stationary_wage_lt_11_8
#print axioms source_stationary_credit_scale_gt_225529

end ProposedFirmFaceUniformBounds
end Ventura26LiquidityAllocation

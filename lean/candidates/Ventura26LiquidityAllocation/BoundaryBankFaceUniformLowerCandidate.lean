import Ventura26LiquidityAllocation.BoundaryNarrowRightResidualSignCandidate

/-!
# Unconditional uniform lower bound on the inherited SOURCE bank-face change

This component concerns the ORIGINAL nominal stock of bank equity/face.
On the six-decimal SOURCE root bracket, its renewal-adjusted impact
change lies strictly above -0.03, despite being strictly negative.

The proof uses the original heterogeneous capital and loan primitives,
wage^12 equation, exact bank reserve/deposit denominator, and positive
nominal bank equity. No independent Python interval is a Lean hypothesis.

This is ONE component only; the positive firm-face decline bound is a
separate, remaining obligation. Never infer the total gap from this
negative bank contribution alone.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedBoundaryBankFaceUniformLower

open ProposedStationaryBank
open ProposedStationaryRealScale
open ProposedStationaryPrimitives
open ProposedStationaryInheritedState
open ProposedBoundaryResourceRoot
open ProposedBoundaryFullPrefix
open ProposedBoundaryNormalizationBridge
open ProposedBoundaryInheritedFaceMechanism

/-- Exact stationary real wage exceeds 1.37. The only quantitative
premises are proven SOURCE component micro-box theorems. -/
theorem source_stationary_wage_gt_137 :
    (137 / 100 : ℝ) < wage := by
  rcases boundary_source_user_cost_sharp_boxes with
    ⟨⟨huHlo, _⟩, ⟨huLlo, _⟩⟩
  rcases boundary_source_capital_scales_sharp_boxes with
    ⟨⟨hkHlo, _⟩, ⟨hkLlo, _⟩⟩
  have hHpos := capitalScale_pos .H
  have hLpos := capitalScale_pos .L
  have hpH :
      (63166370 / 1000000000 : ℝ) *
          (5677035 / 100000 : ℝ) <
        userCost .H * capitalScale .H := by
    calc
      _ < (63166370 / 1000000000 : ℝ) *
            capitalScale .H :=
        mul_lt_mul_of_pos_left hkHlo (by norm_num)
      _ < _ := mul_lt_mul_of_pos_right huHlo hHpos
  have hpL :
      (55943655 / 1000000000 : ℝ) *
          (9431553 / 100000 : ℝ) <
        userCost .L * capitalScale .L := by
    calc
      _ < (55943655 / 1000000000 : ℝ) *
            capitalScale .L :=
        mul_lt_mul_of_pos_left hkLlo (by norm_num)
      _ < _ := mul_lt_mul_of_pos_right huLlo hLpos
  have hLabor :
      (5538 / 1000 : ℝ) < laborScale := by
    unfold laborScale average
    linarith only [hpH, hpL]
  have hWorker :
      (8038062 / 1000000 : ℝ) < workerConsumptionScale :=
    boundary_worker_consumption_scale_lower
  have hProduct :
      (137 / 100 : ℝ) ^ (12 : ℕ) <
        laborScale * workerConsumptionScale := by
    have h1 :
        (5538 / 1000 : ℝ) * (8038062 / 1000000 : ℝ) <
          laborScale * (8038062 / 1000000 : ℝ) :=
      mul_lt_mul_of_pos_right hLabor (by norm_num)
    have h2 :
        laborScale * (8038062 / 1000000 : ℝ) <
          laborScale * workerConsumptionScale :=
      mul_lt_mul_of_pos_left hWorker
        (lt_trans (by norm_num) hLabor)
    calc
      (137 / 100 : ℝ) ^ (12 : ℕ) <
        (5538 / 1000 : ℝ) * (8038062 / 1000000 : ℝ) := by norm_num
      _ < _ := h1
      _ < _ := h2
  by_contra hn
  have hWle : wage ≤ (137 / 100 : ℝ) := le_of_not_gt hn
  have hPowLe :
      wage ^ (12 : ℕ) ≤ (137 / 100 : ℝ) ^ (12 : ℕ) := by
    gcongr
  rw [wage_pow_twelve] at hPowLe
  linarith only [hProduct, hPowLe]

/-- Source-derived creditScale < 22.553; its nominal level is normalized
by the already bounded wage^5, not an assumed bank equity midpoint. -/
theorem source_credit_scale_lt_22553 :
    creditScale < (22553 / 1000 : ℝ) := by
  rcases boundary_source_capital_scales_sharp_boxes with
    ⟨⟨_, hkHhi⟩, ⟨_, hkLhi⟩⟩
  have hLoan := boundary_source_loan_rate_sharp_box.1
  have hLoanPos : 0 < ProposedStationaryBank.loanRate :=
    ProposedStationaryRealScale.loanRate_pos
  have hIdentity :
      creditScale * ProposedStationaryBank.loanRate =
        ((3 / 20 : ℝ) * (3159 / 3200 : ℝ) * capitalScale .H +
          (2 / 5 : ℝ) * (3159 / 3200 : ℝ) * capitalScale .L) / 2 := by
    unfold creditScale average pledgeability liquidationValue capitalPrice
    field_simp [ne_of_gt hLoanPos] <;> ring
  have hScaledUpper :
      ((3 / 20 : ℝ) * (3159 / 3200 : ℝ) * capitalScale .H +
          (2 / 5 : ℝ) * (3159 / 3200 : ℝ) * capitalScale .L) / 2 <
        (22553 / 1000 : ℝ) *
          (101204823607 / 100000000000 : ℝ) := by
    linarith only [hkHhi, hkLhi]
  by_contra hn
  have hCreditGe : (22553 / 1000 : ℝ) ≤ creditScale :=
    le_of_not_gt hn
  have hm := mul_le_mul_of_nonneg_right hCreditGe hLoanPos.le
  rw [hIdentity] at hm
  linarith only [hScaledUpper, hm, hLoan]

/-- Original nominal stationary bank equity is below 1.76.
The leverage denominator remains the original OTC reserve/deposit ratio. -/
theorem source_stationary_bank_equity_lt_44_25 :
    bankEquity < (44 / 25 : ℝ) := by
  have hw := source_stationary_wage_gt_137
  have hw5 :
      (137 / 100 : ℝ) ^ (5 : ℕ) < wage ^ (5 : ℕ) := by
    gcongr
  have hden : (8 / 3 : ℝ) <
      3 - 2 * ProposedStationaryBank.reserveDepositRatio :=
    ProposedStationaryBank.normalized_portfolio_bounds.2.2.1
  have hdenpos : 0 < 3 - 2 * ProposedStationaryBank.reserveDepositRatio :=
    lt_trans (by norm_num) hden
  have hwp : 0 < wage ^ (5 : ℕ) := pow_pos wage_pos _
  have hBankpos : 0 < bankEquity := bank_scale_pos.1
  have hId :
      bankEquity *
        (3 - 2 * ProposedStationaryBank.reserveDepositRatio) *
          wage ^ (5 : ℕ) = creditScale := by
    unfold bankEquity
    rw [aggregateCredit_scale]
    field_simp [ne_of_gt hdenpos, ne_of_gt hwp] <;> ring
  have hLower :
      (8 / 3 : ℝ) * (137 / 100 : ℝ) ^ (5 : ℕ) <
        (3 - 2 * ProposedStationaryBank.reserveDepositRatio) *
          wage ^ (5 : ℕ) := by
    calc
      _ < (3 - 2 * ProposedStationaryBank.reserveDepositRatio) *
            (137 / 100 : ℝ) ^ (5 : ℕ) :=
        mul_lt_mul_of_pos_right hden (by norm_num)
      _ < _ :=
        mul_lt_mul_of_pos_left hw5 hdenpos
  have hUpper := source_credit_scale_lt_22553
  by_contra hn
  have hBankGe : (44 / 25 : ℝ) ≤ bankEquity := le_of_not_gt hn
  have hNonnegProd :
      0 ≤ (3 - 2 * ProposedStationaryBank.reserveDepositRatio) *
        wage ^ (5 : ℕ) :=
    mul_nonneg hdenpos.le hwp.le
  have hMul := mul_le_mul_of_nonneg_right hBankGe hNonnegProd
  have hMulLower :
      (44 / 25 : ℝ) *
          ((8 / 3 : ℝ) * (137 / 100 : ℝ) ^ (5 : ℕ)) <
        bankEquity *
          ((3 - 2 * ProposedStationaryBank.reserveDepositRatio) *
            wage ^ (5 : ℕ)) := by
    calc
      _ < (44 / 25 : ℝ) *
            ((3 - 2 * ProposedStationaryBank.reserveDepositRatio) *
              wage ^ (5 : ℕ)) :=
        mul_lt_mul_of_pos_left hLower (by norm_num)
      _ ≤ _ := hMul
  have hNumerical :
      (22553 / 1000 : ℝ) <
        (44 / 25 : ℝ) *
          ((8 / 3 : ℝ) * (137 / 100 : ℝ) ^ (5 : ℕ)) := by
    norm_num
  rw [mul_assoc, hId] at hMulLower
  linarith only [hUpper, hMulLower, hNumerical]

/-- The ORIGINAL bank-face contribution cannot be more negative
than three percentage points anywhere on the narrow SOURCE bracket.
No total nominal-gap sign is assumed. -/
theorem source_narrow_bank_face_contribution_gt_neg_three_percent
    (G R : ℝ)
    (hlo : (1029135 / 1000000 : ℝ) ≤ R)
    (hhi : R ≤ (1029136 / 1000000 : ℝ)) :
    -(3 / 100 : ℝ) <
      (boundaryBankEquity R - bankEquity) /
        bankRenewalFactor (primitives G) := by
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num) hlo
  have hRmem : R ∈ boundaryInterval := by
    change boundaryLo ≤ R ∧ R ≤ boundaryHi
    constructor
    · exact le_trans (by norm_num [boundaryLo]) hlo
    · exact le_trans hhi (by norm_num [boundaryHi])
  have hBankPos : 0 < bankEquity := bank_scale_pos.1
  have hBankUpper := source_stationary_bank_equity_lt_44_25
  have hLoanPos : 0 < ProposedStationaryBank.loanRate := loanRate_pos
  have hLoanLtR := stationaryLoanRate_lt_boundaryRate R hRmem
  have hGapPos : 0 < R - ProposedStationaryBank.loanRate :=
    sub_pos.mpr hLoanLtR
  have hLoanUpper :
      ProposedStationaryBank.loanRate <
        (10120483 / 10000000 : ℝ) :=
    lt_trans boundary_source_loan_rate_sharp_box.2 (by norm_num)
  have hGapUpper :
      R - ProposedStationaryBank.loanRate < (171 / 10000 : ℝ) := by
    have hLoanLower := boundary_source_loan_rate_sharp_box.1
    linarith only [hhi, hLoanLower]
  have hNUpper :
      bankEquity * ProposedStationaryBank.loanRate *
          (R - ProposedStationaryBank.loanRate) <
        (44 / 25 : ℝ) * (10120483 / 10000000 : ℝ) *
          (171 / 10000 : ℝ) := by
    have hB :
        bankEquity * ProposedStationaryBank.loanRate <
          (44 / 25 : ℝ) * ProposedStationaryBank.loanRate :=
      mul_lt_mul_of_pos_right hBankUpper hLoanPos
    have hL :
        (44 / 25 : ℝ) * ProposedStationaryBank.loanRate <
          (44 / 25 : ℝ) * (10120483 / 10000000 : ℝ) :=
      mul_lt_mul_of_pos_left hLoanUpper (by norm_num)
    calc
      _ < ((44 / 25 : ℝ) * ProposedStationaryBank.loanRate) *
          (R - ProposedStationaryBank.loanRate) :=
        mul_lt_mul_of_pos_right hB hGapPos
      _ < ((44 / 25 : ℝ) * (10120483 / 10000000 : ℝ)) *
          (R - ProposedStationaryBank.loanRate) :=
        mul_lt_mul_of_pos_right hL hGapPos
      _ < _ :=
        mul_lt_mul_of_pos_left hGapUpper (by norm_num)
  have hBound :
      bankEquity * ProposedStationaryBank.loanRate *
          (R - ProposedStationaryBank.loanRate) <
        (3 / 100 : ℝ) * R := by
    calc
      _ < (44 / 25 : ℝ) * (10120483 / 10000000 : ℝ) *
          (171 / 10000 : ℝ) := hNUpper
      _ < (3 / 100 : ℝ) * (1029135 / 1000000 : ℝ) := by norm_num
      _ ≤ (3 / 100 : ℝ) * R :=
        mul_le_mul_of_nonneg_left hlo (by norm_num)
  have hDiv :
      bankEquity * ProposedStationaryBank.loanRate *
          (R - ProposedStationaryBank.loanRate) / R <
        (3 / 100 : ℝ) :=
    (div_lt_iff₀ hRpos).2 (by simpa [mul_comm] using hBound)
  have hIdentity :
      (boundaryBankEquity R - bankEquity) /
        bankRenewalFactor (primitives G) =
      - (bankEquity * ProposedStationaryBank.loanRate *
          (R - ProposedStationaryBank.loanRate)) / R := by
    rw [bankRenewalFactor_eq (primitives G) (stationary_parameters G)]
    unfold boundaryBankEquity
    field_simp [ne_of_gt hRpos, ne_of_gt hLoanPos] <;> ring
  rw [hIdentity]
  linarith only [hDiv]

#print axioms source_stationary_wage_gt_137
#print axioms source_credit_scale_lt_22553
#print axioms source_stationary_bank_equity_lt_44_25
#print axioms source_narrow_bank_face_contribution_gt_neg_three_percent

end ProposedBoundaryBankFaceUniformLower
end Ventura26LiquidityAllocation

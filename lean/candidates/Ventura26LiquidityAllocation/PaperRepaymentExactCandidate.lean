import Ventura26LiquidityAllocation.PaperInterface

/-!
# Paper Lemma 3.1: robust repayment coverage, exactly as pinned

The checkpoint's repaymentSpec includes four conclusions:
(i) loan repayment remains covered in every admissible state after
normalization by inflation; (ii) the firm's future net worth dominates
the unpledged liquidation value plus safe deposits and operating profit;
(iii) that lower bound is nonnegative; (iv) capital or deposits make
future net worth strictly positive.

No bankruptcy, global equilibrium, or bank solvency claim follows.
This file targets the exact pinned spec, with no extra hypotheses.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedPaperRepaymentExact

theorem exact_repaymentSpec : repaymentSpec := by
  intro qNext inflationNext theta depreciation loanRate depositRate
    loan deposit capitalNext operatingProfit
    hq hinfl htheta0 htheta1 hdelta0 hdelta1 hprofit0
    hrl hrd hloan0 hdeposit0 hcapital0 hcoverage
  have hthetaGap : 0 < 1 - theta := sub_pos.mpr htheta1
  have hdeltaGap : 0 < 1 - depreciation := sub_pos.mpr hdelta1
  have hrealCover :
      loanRate * loan / inflationNext ≤
        theta * (1 - depreciation) * qNext * capitalNext := by
    apply (div_le_iff₀ hinfl).2
    calc
      loanRate * loan ≤
          theta * (1 - depreciation) *
            (inflationNext * qNext) * capitalNext := hcoverage
      _ = (theta * (1 - depreciation) * qNext * capitalNext) *
          inflationNext := by ring
  have hcapitalNonneg :
      0 ≤ (1 - theta) * (1 - depreciation) * qNext * capitalNext := by
    positivity
  have hdepositNonneg :
      0 ≤ depositRate * deposit / inflationNext := by
    positivity
  have hwealthBound :
      operatingProfit +
          (1 - theta) * (1 - depreciation) * qNext * capitalNext +
          depositRate * deposit / inflationNext ≤
        operatingProfit + (1 - depreciation) * qNext * capitalNext -
          loanRate * loan / inflationNext +
          depositRate * deposit / inflationNext := by
    calc
      operatingProfit +
            (1 - theta) * (1 - depreciation) * qNext * capitalNext +
            depositRate * deposit / inflationNext =
          operatingProfit +
            ((1 - depreciation) * qNext * capitalNext -
              theta * (1 - depreciation) * qNext * capitalNext) +
            depositRate * deposit / inflationNext := by ring
      _ ≤ operatingProfit +
            ((1 - depreciation) * qNext * capitalNext -
              loanRate * loan / inflationNext) +
            depositRate * deposit / inflationNext := by
          have hsub :=
            sub_le_sub_left hrealCover
              ((1 - depreciation) * qNext * capitalNext)
          convert
            (add_le_add_right (add_le_add_left hsub operatingProfit)
              (depositRate * deposit / inflationNext)) using 1 <;> ring
      _ = operatingProfit + (1 - depreciation) * qNext * capitalNext -
            loanRate * loan / inflationNext +
            depositRate * deposit / inflationNext := by ring
  have hlowerNonneg :
      0 ≤ operatingProfit +
        (1 - theta) * (1 - depreciation) * qNext * capitalNext +
        depositRate * deposit / inflationNext := by
    linarith
  refine ⟨hrealCover, hwealthBound, hlowerNonneg, ?_⟩
  intro hpositivePositions
  have hlowerPos :
      0 < operatingProfit +
        (1 - theta) * (1 - depreciation) * qNext * capitalNext +
        depositRate * deposit / inflationNext := by
    rcases hpositivePositions with hcapitalPos | hdepositPos
    · have hpositiveUnpledged :
          0 < (1 - theta) * (1 - depreciation) * qNext *
            capitalNext := by positivity
      linarith
    · have hpositiveSafe :
          0 < depositRate * deposit / inflationNext := by positivity
      linarith
  exact lt_of_lt_of_le hlowerPos hwealthBound

#print axioms exact_repaymentSpec

end ProposedPaperRepaymentExact
end Ventura26LiquidityAllocation

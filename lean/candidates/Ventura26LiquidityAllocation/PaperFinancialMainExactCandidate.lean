import Ventura26LiquidityAllocation.PaperInterface

/-!
# Exact source-facing paper financial results 3.2, 3.3 and 3.5

Unlike auxiliary financial lemmas, these prove the LITERAL propositions
declared in the pinned PaperInterface, with their original quantifiers
and assumptions. No new assumptions are added to the target specs.

- 3.2: both positive gross positions contradict loan/deposit KKT when
  the gross lending rate exceeds the safe deposit rate;
- 3.3: the signed derivative of capacity at fixed funds/prices/collateral;
- 3.5: all three branches of the exact financing superdifferential.

These are isolated financial propositions. They do not prove the
global firm optimality/terminality of Lemma 3.4 or equilibrium multiplicity.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedPaperFinancialMainExact

/-- Exact PaperInterface Lemma 3.2, not merely a separate one-period
example. The normalized discount's positive value follows already
from the strictly positive deposit rate and its interior Euler equation. -/
theorem exact_noSimultaneousSavingBorrowingSpec :
    noSimultaneousSavingBorrowingSpec := by
  intro W hfin probability marginalValueNext inflationNext
    entrepreneurDiscount cashMultiplier discount loanRate depositRate
    collateralDual loanCornerDual depositCornerDual loan deposit
  intro hdiscountSource hdepositRate hspread hcollateralDual
    hloanCorner hdepositCorner hloanNonneg hdepositNonneg
    hloanFOC hloanComp hdepositFOC hdepositComp
  by_cases hloanZero : loan = 0
  · exact Or.inl hloanZero
  · right
    by_contra hdepositZero
    have hloanPos : 0 < loan :=
      lt_of_le_of_ne hloanNonneg (Ne.symm hloanZero)
    have hdepositPos : 0 < deposit :=
      lt_of_le_of_ne hdepositNonneg (Ne.symm hdepositZero)
    have hloanDualZero : loanCornerDual = 0 :=
      (mul_eq_zero.mp hloanComp).resolve_right hloanPos.ne'
    have hdepositDualZero : depositCornerDual = 0 :=
      (mul_eq_zero.mp hdepositComp).resolve_right hdepositPos.ne'
    have hLoan : loanRate * (discount + collateralDual) = 1 := by
      rw [hloanDualZero] at hloanFOC
      linarith
    have hDeposit : depositRate * discount = 1 := by
      rw [hdepositDualZero] at hdepositFOC
      linarith
    have hDiscountPos : 0 < discount := by
      by_contra h
      have hNonpos : discount ≤ 0 := le_of_not_gt h
      have hProdNonpos : depositRate * discount ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hdepositRate.le hNonpos
      linarith
    have hLoanRatePos : 0 < loanRate := lt_trans hdepositRate hspread
    have hDifference :
        depositRate * discount < loanRate * discount :=
      mul_lt_mul_of_pos_right hspread hDiscountPos
    have hNonnegDualTerm : 0 ≤ loanRate * collateralDual :=
      mul_nonneg hLoanRatePos.le hcollateralDual
    nlinarith [hLoan, hDeposit, hDifference, hNonnegDualTerm]

/-- Exact PaperInterface Proposition 3.3: derivative under fixed
positive funds, capital price and pledgeable value. -/
theorem exact_financingCapacityComparativeSpec :
    financingCapacityComparativeSpec := by
  intro ownResources capitalPrice collateral loanRate
    hresources hcollateral hrate hbound
  change
    HasDerivAt
        (fun r => financingCapacity ownResources capitalPrice collateral r)
        (-ownResources * collateral /
          (loanRate ^ 2 * (capitalPrice - collateral / loanRate) ^ 2))
        loanRate ∧
      -ownResources * collateral /
          (loanRate ^ 2 * (capitalPrice - collateral / loanRate) ^ 2) < 0
  exact financingCapacity_hasDerivAt_and_deriv_neg
    hresources hcollateral hrate hbound

/-- Exact PaperInterface Lemma 3.5; in particular, the subgradient
at zero is the ENTIRE interval and not one of the two interior Euler
conditions. -/
theorem exact_fundingSupergradientSpec :
    fundingSupergradientSpec := by
  intro loanRate depositRate face slope hdeposit hspread
  change
    IsFundingSupergradient loanRate depositRate face slope ↔
      FundingSupergradientCases loanRate depositRate face slope
  exact isFundingSupergradient_iff_cases ⟨hdeposit, hspread⟩

#print axioms exact_noSimultaneousSavingBorrowingSpec
#print axioms exact_financingCapacityComparativeSpec
#print axioms exact_fundingSupergradientSpec

end ProposedPaperFinancialMainExact
end Ventura26LiquidityAllocation

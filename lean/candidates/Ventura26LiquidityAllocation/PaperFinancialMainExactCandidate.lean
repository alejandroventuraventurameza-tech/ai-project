import Ventura26LiquidityAllocation.PaperInterface

/-!
# Exact source-facing paper financial results 3.2, 3.3 and corrected 3.5

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

/-- Audit finding: the PINNED PaperInterface definition currently parses
as [(rate assumptions -> supergradient)] iff cases, because its displayed
implication lacks parentheses around the full equivalence.
That unguarded proposition is false: RL = RD = 1, face = 0, slope = 2
makes the left implication vacuously true and the right cases false.

We preserve the upstream source verbatim and refute that malformed
interface instead of silently weakening the original objective. -/
theorem original_fundingSupergradientSpec_false :
    ¬ fundingSupergradientSpec := by
  intro hspec
  have hbad := hspec (1 : ℝ) (1 : ℝ) (0 : ℝ) (2 : ℝ)
  have hleft :
      ((0 : ℝ) < 1 →
        (1 : ℝ) < 1 →
          ∀ g : ℝ,
            fundingCash 1 1 g ≤ fundingCash 1 1 0 + 2 * (g - 0)) := by
    intro _ hlt
    norm_num at hlt
  have hright := hbad.mp hleft
  norm_num at hright

/-- Correct source formula: the rate domain guards the ENTIRE
supergradient equivalence, not just the left implication.
This is the paper's mathematical Lemma 3.5, including its corner. -/
def fundingSupergradientCorrectedSpec : Prop :=
  ∀ (loanRate depositRate face slope : ℝ),
    0 < depositRate →
      depositRate < loanRate →
        ((∀ g : ℝ,
            fundingCash loanRate depositRate g ≤
              fundingCash loanRate depositRate face + slope * (g - face)) ↔
          ((face < 0 ∧ slope = 1 / depositRate) ∨
            (face = 0 ∧ 1 / loanRate ≤ slope ∧ slope ≤ 1 / depositRate) ∨
            (0 < face ∧ slope = 1 / loanRate)))

/-- Corrected, scoped theorem corresponding to the economic manuscript's
superdifferential, under strict RL > RD > 0. -/
theorem corrected_fundingSupergradientSpec :
    fundingSupergradientCorrectedSpec := by
  intro loanRate depositRate face slope hdeposit hspread
  change
    IsFundingSupergradient loanRate depositRate face slope ↔
      FundingSupergradientCases loanRate depositRate face slope
  exact isFundingSupergradient_iff_cases ⟨hdeposit, hspread⟩

#print axioms exact_noSimultaneousSavingBorrowingSpec
#print axioms exact_financingCapacityComparativeSpec
#print axioms original_fundingSupergradientSpec_false
#print axioms corrected_fundingSupergradientSpec

end ProposedPaperFinancialMainExact
end Ventura26LiquidityAllocation

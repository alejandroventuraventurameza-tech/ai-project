import Ventura26LiquidityAllocation.DateZeroCapitalDeviationCandidate

/-!
# One-sided capital deviations at a binding robust-collateral constraint

Capital installed at date zero may be raised while keeping the loan and
nominal face fixed. If the collateral payoff coefficient is nonnegative
in every admissible successor, this change cannot violate an already
feasible robust repayment inequality. Unlike the two-sided slack case,
there is no assertion that a negative capital deviation is feasible.

This is a monotonicity lemma, not a KKT, derivative or equilibrium theorem.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedOneSidedCollateralMonotonicity

variable {S : Type*} [Fintype S]

/-- A nonnegative one-sided capital increase preserves the robust collateral
    inequality for all admissible successors, even when it originally binds. -/
theorem robustCollateral_capital_mono
    (theta delta loanRate loan capital epsilon : ℝ)
    (possible : S → Prop)
    (inflationNext capitalPriceNext : S → ℝ)
    (hcoll : RobustCollateral theta delta loanRate loan capital
      possible inflationNext capitalPriceNext)
    (heps : 0 ≤ epsilon)
    (hcoeff : ∀ s : S, possible s →
      0 ≤ theta * (1 - delta) *
        (inflationNext s * capitalPriceNext s)) :
    RobustCollateral theta delta loanRate loan (capital + epsilon)
      possible inflationNext capitalPriceNext := by
  intro s hs
  have hbase := hcoll s hs
  let a : ℝ := theta * (1 - delta) *
    (inflationNext s * capitalPriceNext s)
  have hpositive : 0 ≤ a * epsilon := mul_nonneg (hcoeff s hs) heps
  change loanRate * loan ≤ a * (capital + epsilon)
  calc
    loanRate * loan ≤ a * capital := hbase
    _ ≤ a * capital + a * epsilon := le_add_of_nonneg_right hpositive
    _ = a * (capital + epsilon) := by ring

/-- Primitive sign restrictions are sufficient for monotonicity. -/
theorem robustCollateral_capital_mono_of_nonneg_prices
    (theta delta loanRate loan capital epsilon : ℝ)
    (possible : S → Prop)
    (inflationNext capitalPriceNext : S → ℝ)
    (hcoll : RobustCollateral theta delta loanRate loan capital
      possible inflationNext capitalPriceNext)
    (heps : 0 ≤ epsilon)
    (htheta : 0 ≤ theta)
    (hdelta : delta ≤ 1)
    (hinfl : ∀ s : S, possible s → 0 ≤ inflationNext s)
    (hprice : ∀ s : S, possible s → 0 ≤ capitalPriceNext s) :
    RobustCollateral theta delta loanRate loan (capital + epsilon)
      possible inflationNext capitalPriceNext := by
  apply robustCollateral_capital_mono theta delta loanRate loan capital
    epsilon possible inflationNext capitalPriceNext hcoll heps
  intro s hs
  exact mul_nonneg
    (mul_nonneg htheta (sub_nonneg.mpr hdelta))
    (mul_nonneg (hinfl s hs) (hprice s hs))

end ProposedOneSidedCollateralMonotonicity
end Ventura26LiquidityAllocation

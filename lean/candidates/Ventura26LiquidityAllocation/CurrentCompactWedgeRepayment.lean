import Mathlib

/-!
# IE project: fuente compacta del 26 de noviembre de 2026

Source version:
  ai-project@bac3c6255da39cd1169a965df35bb5e9a230e6e8

This file targets only:
  - Lemma A.1.1 (`lem:repayment`): net worth under real robust collateral.
  - Proposition 5.3 (`prop:compact_source_collateral_effective_wedge`): effective price wedge.

It deliberately does NOT assert two dynamic equilibria, uniqueness of
an Allocation, KKT sufficiency, numerical source coefficients, or growth.

Both statements are source-specific self-contained `Spec` declarations.
The proof endpoints are separate declarations. This file does not by
itself substitute the official AppliedModelingLib source-to-Lean review.
-/

namespace Ventura26LiquidityAllocation.CurrentCompact

/-- Exact economic statement of Appendix Lemma A.1.1, conditional on the
real robust coverage inequality. Depreciation can equal zero, unlike the
earlier (historical) repaymentSpec requiring `0 < depreciation`.
No condition is added asserting future wealth is already nonnegative. -/
def repaymentCurrentSpec : Prop :=
  ∀ (qNext inflationNext theta depreciation loanRate depositRate loan deposit
      capitalNext operatingProfit : ℝ),
    0 < qNext →
    0 < inflationNext →
    0 ≤ theta → theta < 1 →
    0 ≤ depreciation → depreciation < 1 →
    0 < loanRate → 0 < depositRate →
    0 ≤ loan → 0 ≤ deposit → 0 ≤ capitalNext →
    0 ≤ operatingProfit →
    loanRate * loan / inflationNext ≤
      theta * (1 - depreciation) * qNext * capitalNext →
    let netWorth :=
      operatingProfit + (1 - depreciation) * qNext * capitalNext -
        loanRate * loan / inflationNext + depositRate * deposit / inflationNext
    let lowerBound :=
      operatingProfit + (1 - theta) * (1 - depreciation) * qNext * capitalNext +
        depositRate * deposit / inflationNext
    lowerBound ≤ netWorth ∧
      0 ≤ netWorth ∧
      ((0 < capitalNext ∨ 0 < deposit) → 0 < netWorth)

/-- Separate kernel-checkable proof endpoint for Lemma A.1.1. -/
theorem repaymentCurrent_exact : repaymentCurrentSpec := by
  intro qNext inflationNext theta depreciation loanRate depositRate loan deposit
    capitalNext operatingProfit
    hq hpi htheta0 htheta1 hdelta0 hdelta1 hloanRate hdepositRate
    hloan0 hdeposit0 hcapital0 hprofit0 hcoverage
  have hthetaGap : 0 < 1 - theta := sub_pos.mpr htheta1
  have hdeltaGap : 0 < 1 - depreciation := sub_pos.mpr hdelta1
  have hlowerNonneg :
      0 ≤ operatingProfit +
        (1 - theta) * (1 - depreciation) * qNext * capitalNext +
        depositRate * deposit / inflationNext := by
    positivity
  have hwealthBound :
      operatingProfit +
          (1 - theta) * (1 - depreciation) * qNext * capitalNext +
          depositRate * deposit / inflationNext ≤
        operatingProfit + (1 - depreciation) * qNext * capitalNext -
          loanRate * loan / inflationNext +
          depositRate * deposit / inflationNext := by
    nlinarith [hcoverage]
  dsimp
  refine ⟨hwealthBound, le_trans hlowerNonneg hwealthBound, ?_⟩
  intro hpositive
  rcases hpositive with hcapitalPos | hdepositPos
  · have hpositiveUnpledged :
        0 < (1 - theta) * (1 - depreciation) * qNext * capitalNext := by
      positivity
    linarith
  · have hpositiveSafe :
        0 < depositRate * deposit / inflationNext := by
      positivity
    linarith

/-- Proposition 5.3: effective-price wedge for types H and L.
The current capital price is unrestricted because it cancels.
Only the source's common gross loan rate, strictly positive terminal
inflation/capital price, depreciation below one, and pledge ordering
are assumed. -/
def effectiveWedgeCurrentSpec : Prop :=
  ∀ (loanRate depreciation inflationNext capitalPriceNext thetaH thetaL
      capitalPriceCurrent : ℝ),
    0 < loanRate →
    depreciation < 1 →
    0 < inflationNext →
    0 < capitalPriceNext →
    thetaH < thetaL →
    let collateralValue := (1 - depreciation) * inflationNext * capitalPriceNext
    let effectivePriceH := capitalPriceCurrent - thetaH * collateralValue / loanRate
    let effectivePriceL := capitalPriceCurrent - thetaL * collateralValue / loanRate
    effectivePriceH - effectivePriceL =
        (thetaL - thetaH) * collateralValue / loanRate ∧
      0 < effectivePriceH - effectivePriceL

/-- Separate kernel-checkable proof endpoint for Proposition 5.3. -/
theorem effectiveWedgeCurrent_exact : effectiveWedgeCurrentSpec := by
  intro loanRate depreciation inflationNext capitalPriceNext thetaH thetaL
    capitalPriceCurrent
    hloanRate hdelta hInflation hCapitalPrice htheta
  have hcollateral :
      0 < (1 - depreciation) * inflationNext * capitalPriceNext := by
    have hRemain : 0 < 1 - depreciation := sub_pos.mpr hdelta
    exact mul_pos (mul_pos hRemain hInflation) hCapitalPrice
  have hthetaGap : 0 < thetaL - thetaH := sub_pos.mpr htheta
  have hidentity :
      (capitalPriceCurrent -
           thetaH * ((1 - depreciation) * inflationNext * capitalPriceNext) /
             loanRate) -
          (capitalPriceCurrent -
           thetaL * ((1 - depreciation) * inflationNext * capitalPriceNext) /
             loanRate) =
        (thetaL - thetaH) *
          ((1 - depreciation) * inflationNext * capitalPriceNext) /
            loanRate := by
    ring
  dsimp
  refine ⟨hidentity, ?_⟩
  rw [hidentity]
  exact div_pos (mul_pos hthetaGap hcollateral) hloanRate

#print axioms repaymentCurrent_exact
#print axioms effectiveWedgeCurrent_exact

end Ventura26LiquidityAllocation.CurrentCompact

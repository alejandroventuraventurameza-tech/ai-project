import Ventura26LiquidityAllocation.DateZeroJointCapitalLoanTangentAlgebraCandidate

/-!
# Algebraic conversion of binding joint tangency to two compatible FOCs

At the binding tangent dk=R*epsilon, db=Gamma*epsilon, stationarity of the
genuine joint utility derivative implies
    R * capitalEulerPrimalGap = Gamma * loanEulerPrimalGap
where the second gap is the loan budget/real repayment margin:
    loanGap = 1 - beta*u'(c1)/u'(c0) * R/inflation1.

Both gaps can therefore be represented with one common nonnegative dual if
Gamma>0, R>0, and the one-sided capital gap is nonnegative. This module
proves the scalar real algebra, not the model-specific history sums.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedDateZeroJointTangentGapBalanceAlgebra

/-- Exact normalization of the joint derivative by current marginal utility.
    It is not a separate state-by-state Euler equation. -/
theorem tangentGradient_zero_implies_margin_balance
    (m0 m1 q R Gamma payoff beta inflation : ℝ)
    (hm0 : m0 ≠ 0) (hpi : inflation ≠ 0)
    (hgradient :
      m0 * (Gamma - q * R) +
        beta * m1 * (R * payoff - R * Gamma / inflation) = 0) :
    R * (q - beta * m1 / m0 * payoff) =
      Gamma * (1 - beta * m1 / m0 * (R / inflation)) := by
  field_simp [hm0, hpi] at hgradient ⊢
  nlinarith [hgradient]

/-- Joint stationarity and nonnegative capital investment gap yield a
    single common nonnegative dual satisfying both the capital and loan
    first-order equations, provided R and Gamma are positive. -/
theorem exists_shared_scalarMultiplier_of_tangent_gradient
    (m0 m1 q R Gamma payoff beta inflation : ℝ)
    (hm0 : m0 ≠ 0) (hpi : inflation ≠ 0)
    (hR : 0 < R) (hGamma : 0 < Gamma)
    (hcapital : 0 ≤ q - beta * m1 / m0 * payoff)
    (hgradient :
      m0 * (Gamma - q * R) +
        beta * m1 * (R * payoff - R * Gamma / inflation) = 0) :
    ∃ mu : ℝ, 0 ≤ mu ∧
      q - beta * m1 / m0 * payoff = mu * Gamma ∧
      1 - beta * m1 / m0 * (R / inflation) = mu * R := by
  have hbalance := tangentGradient_zero_implies_margin_balance
    m0 m1 q R Gamma payoff beta inflation hm0 hpi hgradient
  exact exists_shared_scalarMultiplier_of_tangent_balance
    R Gamma (q - beta * m1 / m0 * payoff)
    (1 - beta * m1 / m0 * (R / inflation))
    hR hGamma hcapital hbalance

end ProposedDateZeroJointTangentGapBalanceAlgebra
end Ventura26LiquidityAllocation

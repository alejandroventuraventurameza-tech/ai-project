import Ventura26LiquidityAllocation.DateZeroStatewiseCapitalMultiplierCandidate

/-!
# Joint date-zero capital/loan tangent: the missing KKT interface

At an ACTIVE collateral constraint R*b = Gamma*k, the variation
    dk = R * epsilon, db = Gamma * epsilon
preserves the constraint exactly (for a single active successor).

If the derivative of the SOURCE objective along this true two-control
tangent can later be shown to vanish, its marginal gaps must satisfy
    R * capitalGap = Gamma * loanGap.
For R,Gamma>0, both gaps then share the SAME nonnegative scalar multiplier.

This module proves only the algebraic interface. It does NOT postulate
that the joint full FirmPlan deviation is feasible or that FirmOptimal
already implies the required tangent derivative; those are the next
analytic/economic proof obligations.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedDateZeroJointCapitalLoanTangentAlgebra

/-- The binding robust collateral equality is preserved by the linear
    capital-loan tangent at its active successor. -/
theorem bindingCollateral_joint_tangent
    (R b k Gamma epsilon : ℝ)
    (hbind : R * b = Gamma * k) :
    R * (b + Gamma * epsilon) =
      Gamma * (k + R * epsilon) := by
  calc
    R * (b + Gamma * epsilon) =
      R * b + R * Gamma * epsilon := by ring
    _ = Gamma * k + Gamma * R * epsilon := by
      rw [hbind]
      ring
    _ = Gamma * (k + R * epsilon) := by ring

/-- The *same* scalar shadow price normalizes both marginal gaps if
    differentiability along the binding-capital-loan tangent yields the
    indicated balance. The balance itself is not assumed to follow from
    FirmOptimal in this algebraic lemma. -/
theorem normalized_capital_loan_margins_equal
    (R Gamma capitalGap loanGap : ℝ)
    (hR : R ≠ 0) (hGamma : Gamma ≠ 0)
    (hbalance : R * capitalGap = Gamma * loanGap) :
    capitalGap / Gamma = loanGap / R := by
  field_simp [hR, hGamma] <;> nlinarith [hbalance]

/-- Nonnegative capital gap plus positive collateral coefficient yields
    a shared nonnegative multiplier for both equations once the tangent
    marginal balance has been established. -/
theorem exists_shared_scalarMultiplier_of_tangent_balance
    (R Gamma capitalGap loanGap : ℝ)
    (hR : 0 < R) (hGamma : 0 < Gamma)
    (hgap : 0 ≤ capitalGap)
    (hbalance : R * capitalGap = Gamma * loanGap) :
    ∃ mu : ℝ, 0 ≤ mu ∧
      capitalGap = mu * Gamma ∧ loanGap = mu * R := by
  refine ⟨capitalGap / Gamma, div_nonneg hgap (le_of_lt hGamma), ?_, ?_⟩
  · field_simp [ne_of_gt hGamma] <;> ring
  · field_simp [ne_of_gt hGamma] <;> nlinarith [hbalance]

end ProposedDateZeroJointCapitalLoanTangentAlgebra
end Ventura26LiquidityAllocation

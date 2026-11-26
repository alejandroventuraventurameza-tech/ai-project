import Ventura26LiquidityAllocation.DateZeroOneSidedEulerInequalityCandidate

/-!
# One-sided expected Euler inequality, specialized to a single successor

The SOURCE firm optimality problem implies an expected Euler inequality
under nonnegative collateral coefficients and positive date-zero capital.
When all probability at dates zero and one is concentrated on a single
history, the inequality reduces to the single-successor cost-return row.

The single-history support assumptions remain explicit. This is not a
state-by-state KKT for a general stochastic transition and it does not
identify the existing Allocation.collateralDual field.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedDateZeroOneSidedDeterministicCost

open ProposedDateZeroOneSidedEulerInequality
open ProposedDateZeroCapitalExpectedEuler
open ProposedDateZeroCapitalEulerDerivative

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem firmOptimal_oneSided_singleSuccessor_cost_ge_benefit
    (P : Primitives S) (I : InheritedState)
    (X : Allocation S) (i : FirmType)
    (h0 : History S 0) (h1 : History S 1)
    (hopt : FirmOptimal P I X i)
    (hcapital : ∀ h : History S 0,
      FirmHistoryAdmissible P 0 h → 0 < X.capital i 0 h)
    (hcoeff : ∀ h : History S 0,
      FirmHistoryAdmissible P 0 h → ∀ s : S,
      0 < P.tree.transition (currentState h) s →
      0 ≤ P.pledgeability i * (1 - P.depreciation) *
        (X.inflation 1 (childHistory h s) *
          X.capitalPrice 1 (childHistory h s)))
    (hw0 : P.tree.historyWeight 0 h0 = 1)
    (hz0 : ∀ h : History S 0, h ≠ h0 →
      P.tree.historyWeight 0 h = 0)
    (hw1 : P.tree.historyWeight 1 h1 = 1)
    (hz1 : ∀ h : History S 1, h ≠ h1 →
      P.tree.historyWeight 1 h = 0) :
    P.entrepreneurDiscount *
      (crraMarginal P.entrepreneurRiskAversion (X.firmConsumption i 1 h1) *
        dateOneMarginalCapitalPayoff P X i (firmPlanOfAllocation X i) h1) ≤
      crraMarginal P.entrepreneurRiskAversion (X.firmConsumption i 0 h0) *
        X.capitalPrice 0 h0 := by
  have hgrad := firmOptimal_expectedCapitalEuler_gradient_nonpos
    P I X i hopt hcapital hcoeff
  unfold expectedCapitalEulerGradient dateOneCapitalMarginalBenefit at hgrad
  have hsum0 :
      (∑ h : History S 0, P.tree.historyWeight 0 h *
        (crraMarginal P.entrepreneurRiskAversion
          ((firmPlanOfAllocation X i).consumption 0 h) *
          (-X.capitalPrice 0 h))) =
      -(crraMarginal P.entrepreneurRiskAversion
          ((firmPlanOfAllocation X i).consumption 0 h0) *
          X.capitalPrice 0 h0) := by
    rw [Finset.sum_eq_single h0]
    · rw [hw0]
      ring
    · intro h _ hne
      rw [hz0 h hne]
      ring
    · simp
  have hsum1 :
      (∑ h : History S 1, P.tree.historyWeight 1 h *
        (crraMarginal P.entrepreneurRiskAversion
          ((firmPlanOfAllocation X i).consumption 1 h) *
          dateOneMarginalCapitalPayoff P X i (firmPlanOfAllocation X i) h)) =
      crraMarginal P.entrepreneurRiskAversion
        ((firmPlanOfAllocation X i).consumption 1 h1) *
        dateOneMarginalCapitalPayoff P X i (firmPlanOfAllocation X i) h1 := by
    rw [Finset.sum_eq_single h1]
    · rw [hw1]
      ring
    · intro h _ hne
      rw [hz1 h hne]
      ring
    · simp
  rw [hsum0, hsum1] at hgrad
  change - (crraMarginal P.entrepreneurRiskAversion
      (X.firmConsumption i 0 h0) * X.capitalPrice 0 h0) +
    P.entrepreneurDiscount *
      (crraMarginal P.entrepreneurRiskAversion (X.firmConsumption i 1 h1) *
        dateOneMarginalCapitalPayoff P X i (firmPlanOfAllocation X i) h1) ≤ 0
    at hgrad
  linarith

end ProposedDateZeroOneSidedDeterministicCost
end Ventura26LiquidityAllocation

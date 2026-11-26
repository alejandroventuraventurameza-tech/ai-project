import Ventura26LiquidityAllocation.DateZeroJointBindingFermatCandidate
import Ventura26LiquidityAllocation.DateZeroJointTangentGapBalanceAlgebraCandidate
import Ventura26LiquidityAllocation.DateZeroCalendarEulerBridgeCandidate

/-!
# Two-control binding marginal balance from source firm optimality

We define the date-zero loan primal gap from the literal borrower cash
budget and the next-period real repayment. Under the deterministic source
calendar, the expected gradient of the TRUE joint capital/loan deviation
collapses to the single supported successor, never to an arbitrary
state-by-state stochastic Euler equation.

The joint Fermat theorem plus finite-history probabilities yields:
  loanRate0 * capitalEulerPrimalGap
    = collateralUnit * dateZeroLoanPrimalGap.
This is the missing KKT compatibility condition between the two genuine
control margins, derived under explicitly stated positive consumption and
inflation assumptions.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedDateZeroJointBindingMarginalBalance

open ProposedDateZeroJointBindingFermat
open ProposedDateZeroJointTangentExpectedDerivative
open ProposedDateZeroJointTangentGapBalanceAlgebra
open ProposedDateZeroDeterministicMarkovBridge
open ProposedDateZeroCalendarEulerBridge
open ProposedDateZeroCapitalEulerDerivative
open ProposedProposition42KKTIdentification

variable {S : Type*} [Fintype S] [DecidableEq S]

noncomputable def dateZeroLoanPrimalGap
    (P : Primitives S) (X : Allocation S) (i : FirmType)
    (s : S) : ℝ :=
  let h0 := rootHistory P.tree
  let h1 := childHistory h0 s
  1 - (P.entrepreneurDiscount *
    crraMarginal P.entrepreneurRiskAversion
      (X.firmConsumption i 1 h1) /
    crraMarginal P.entrepreneurRiskAversion
      (X.firmConsumption i 0 h0)) *
    (X.loanRate 0 h0 / X.inflation 1 h1)

/-- Purely source-facing bridge from the expected binding gradient to the
    primal capital/loan gaps, without assuming either Euler FOC. -/
theorem sourceCalendar_jointTangent_gradient_zero_implies_gap_balance
    (P : Primitives S) (X : Allocation S) (i : FirmType)
    (dateOne recurrent : S)
    (hcalendar : DeterministicBridgeCalendar P dateOne recurrent)
    (hc0 : 0 < X.firmConsumption i 0 (rootHistory P.tree))
    (hpi : X.inflation 1
      (childHistory (rootHistory P.tree) dateOne) ≠ 0)
    (hgrad :
      jointTangentExpectedGradient P X i (firmPlanOfAllocation X i)
        (X.loanRate 0 (rootHistory P.tree))
        (capitalEulerCollateralUnit P X i 0
          (rootHistory P.tree) dateOne) = 0) :
    X.loanRate 0 (rootHistory P.tree) *
      capitalEulerPrimalGap P X i 0 (rootHistory P.tree) dateOne =
    capitalEulerCollateralUnit P X i 0 (rootHistory P.tree) dateOne *
      dateZeroLoanPrimalGap P X i dateOne := by
  let h0 : History S 0 := rootHistory P.tree
  let h1 : History S 1 := childHistory h0 dateOne
  let p : FirmPlan S := firmPlanOfAllocation X i
  let R : ℝ := X.loanRate 0 h0
  let Gamma : ℝ := capitalEulerCollateralUnit P X i 0 h0 dateOne
  let m0 : ℝ := crraMarginal P.entrepreneurRiskAversion
    (X.firmConsumption i 0 h0)
  let m1 : ℝ := crraMarginal P.entrepreneurRiskAversion
    (X.firmConsumption i 1 h1)
  have hm0 : m0 ≠ 0 := by
    dsimp [m0, crraMarginal]
    exact ne_of_gt (Real.rpow_pos_of_pos hc0 _)
  have htrans : P.tree.transition P.tree.initial dateOne = 1 :=
    hcalendar.2.2.2.1
  have hothers : ∀ v : S, v ≠ dateOne →
      P.tree.transition P.tree.initial v = 0 :=
    sourceCalendar_other_transitions_zero P dateOne recurrent hcalendar
  obtain ⟨hw0, hz0, hw1, hz1⟩ :=
    deterministic_historyWeight_package P dateOne htrans hothers
  have hprev : previousHistory h1 = h0 := by
    funext j
    rfl
  have hcur : currentState h1 = dateOne := rfl
  have hsum0 :
      (∑ h : History S 0, P.tree.historyWeight 0 h *
        (crraMarginal P.entrepreneurRiskAversion (p.consumption 0 h) *
          (Gamma - X.capitalPrice 0 h * R))) =
      m0 * (Gamma - X.capitalPrice 0 h0 * R) := by
    rw [Finset.sum_eq_single h0]
    · rw [hw0]
      simp [p, m0, firmPlanOfAllocation]
    · intro h _ hne
      rw [hz0 h hne]
      ring
    · simp
  have hsum1 :
      (∑ h : History S 1, P.tree.historyWeight 1 h *
        (crraMarginal P.entrepreneurRiskAversion (p.consumption 1 h) *
          (R * dateOneMarginalCapitalPayoff P X i p h -
            X.loanRate 0 (previousHistory h) * Gamma /
              X.inflation 1 h))) =
      m1 * (R * dateOneMarginalCapitalPayoff P X i p h1 -
        R * Gamma / X.inflation 1 h1) := by
    rw [Finset.sum_eq_single h1]
    · rw [hw1]
      simp [p, m1, R, hprev, firmPlanOfAllocation]
    · intro h _ hne
      rw [hz1 h hne]
      ring
    · simp
  have hgradient :
      m0 * (Gamma - X.capitalPrice 0 h0 * R) +
        P.entrepreneurDiscount *
          (m1 * (R * dateOneMarginalCapitalPayoff P X i p h1 -
            R * Gamma / X.inflation 1 h1)) = 0 := by
    have hg := hgrad
    unfold jointTangentExpectedGradient at hg
    change (∑ h : History S 0, P.tree.historyWeight 0 h *
        (crraMarginal P.entrepreneurRiskAversion (p.consumption 0 h) *
          (Gamma - X.capitalPrice 0 h * R))) +
      P.entrepreneurDiscount * (∑ h : History S 1,
        P.tree.historyWeight 1 h *
          (crraMarginal P.entrepreneurRiskAversion (p.consumption 1 h) *
            (R * dateOneMarginalCapitalPayoff P X i p h -
              X.loanRate 0 (previousHistory h) * Gamma /
                X.inflation 1 h))) = 0 at hg
    rw [hsum0, hsum1] at hg
    exact hg
  have hnormalized :=
    tangentGradient_zero_implies_margin_balance
      m0 m1 (X.capitalPrice 0 h0) R Gamma
      (dateOneMarginalCapitalPayoff P X i p h1)
      P.entrepreneurDiscount (X.inflation 1 h1)
      hm0 hpi (by
        simpa only [mul_assoc] using hgradient)
  have hpay :
      dateOneMarginalCapitalPayoff P X i p h1 =
      X.inputPrice 1 h1 *
        (P.aggregateProductivity dateOne * P.productivity i) *
        P.alpha * (X.capital i 0 h0) ^ (P.alpha - 1) *
          (X.labor i 1 h1) ^ P.beta +
        (1 - P.depreciation) * X.capitalPrice 1 h1 := by
    simp only [dateOneMarginalCapitalPayoff, p,
      firmPlanOfAllocation, hprev, hcur]
  have hcapitalGap :
      capitalEulerPrimalGap P X i 0 h0 dateOne =
      X.capitalPrice 0 h0 -
        P.entrepreneurDiscount * m1 / m0 *
          dateOneMarginalCapitalPayoff P X i p h1 := by
    rw [hpay]
    dsimp [capitalEulerPrimalGap, m0, m1, h0, h1]
  have hloanGap :
      dateZeroLoanPrimalGap P X i dateOne =
        1 - P.entrepreneurDiscount * m1 / m0 *
          (R / X.inflation 1 h1) := by
    rfl
  change R * capitalEulerPrimalGap P X i 0 h0 dateOne =
    Gamma * dateZeroLoanPrimalGap P X i dateOne
  rw [hcapitalGap, hloanGap]
  exact hnormalized

/-- The actual FirmOptimal and binding regime, not an assumed Euler row,
    generate the equality between the source capital and loan primal gaps. -/
theorem firmOptimal_sourceCalendar_binding_capitalLoanGap_balance
    (P : Primitives S) (I : InheritedState)
    (X : Allocation S) (i : FirmType)
    (dateOne recurrent : S)
    (hcalendar : DeterministicBridgeCalendar P dateOne recurrent)
    (hopt : FirmOptimal P I X i)
    (hbinding : DateZeroBindingBorrower P X i)
    (hcapital : ∀ h : History S 0,
      FirmHistoryAdmissible P 0 h → 0 < X.capital i 0 h)
    (hpi : X.inflation 1
      (childHistory (rootHistory P.tree) dateOne) ≠ 0) :
    X.loanRate 0 (rootHistory P.tree) *
      capitalEulerPrimalGap P X i 0 (rootHistory P.tree) dateOne =
    capitalEulerCollateralUnit P X i 0 (rootHistory P.tree) dateOne *
      dateZeroLoanPrimalGap P X i dateOne := by
  have hadm : FirmHistoryAdmissible P 0 (rootHistory P.tree) := by
    simp [FirmHistoryAdmissible, FiniteMarkovTree.historyWeight,
      rootHistory, currentState]
  have hc0 : 0 < X.firmConsumption i 0 (rootHistory P.tree) :=
    (hopt.1.1 0 (rootHistory P.tree) hadm).1
  apply sourceCalendar_jointTangent_gradient_zero_implies_gap_balance
    P X i dateOne recurrent hcalendar hc0 hpi
  exact firmOptimal_sourceCalendar_binding_jointTangent_gradient_zero
    P I X i dateOne recurrent hcalendar hopt hbinding hcapital

end ProposedDateZeroJointBindingMarginalBalance
end Ventura26LiquidityAllocation

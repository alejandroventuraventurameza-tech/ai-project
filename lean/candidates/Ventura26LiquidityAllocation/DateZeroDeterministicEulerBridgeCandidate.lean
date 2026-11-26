import Ventura26LiquidityAllocation.DateZeroCapitalExpectedEulerCandidate

/-!
A conditional reduction of the SOURCE expected Euler equality to a
single history at dates zero and one. It does NOT claim that a stochastic
Markov economy has a state-by-state Euler equation, nor that the structural
collateral-dual field has been identified.

This is a proposed candidate; CI must verify it independently.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedDateZeroDeterministicEulerBridge

open ProposedDateZeroCapitalExpectedEuler
open ProposedDateZeroCapitalEulerDerivative

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Reduction of date-zero and date-one expectations under unit mass at one
    selected history on each date. The concentration assumptions should be
    discharged from deterministic transition primitives in a later theorem. -/
theorem firmOptimal_singleSuccessor_capitalEuler
    (P : Primitives S) (I : InheritedState)
    (X : Allocation S) (i : FirmType)
    (h0 : History S 0) (h1 : History S 1)
    (hopt : FirmOptimal P I X i)
    (hcapital : ∀ h : History S 0,
      FirmHistoryAdmissible P 0 h → 0 < X.capital i 0 h)
    (hslack : DateZeroSlackBorrower P X i)
    (hw0 : P.tree.historyWeight 0 h0 = 1)
    (hz0 : ∀ h : History S 0, h ≠ h0 →
      P.tree.historyWeight 0 h = 0)
    (hw1 : P.tree.historyWeight 1 h1 = 1)
    (hz1 : ∀ h : History S 1, h ≠ h1 →
      P.tree.historyWeight 1 h = 0) :
    crraMarginal P.entrepreneurRiskAversion (X.firmConsumption i 0 h0) *
      X.capitalPrice 0 h0 =
    P.entrepreneurDiscount *
      (crraMarginal P.entrepreneurRiskAversion (X.firmConsumption i 1 h1) *
        dateOneMarginalCapitalPayoff P X i (firmPlanOfAllocation X i) h1) := by
  have heuler := firmOptimal_expectedCapitalEuler P I X i hopt hcapital hslack
  unfold dateZeroCapitalMarginalCost dateOneCapitalMarginalBenefit at heuler
  have hsum0 :
      (∑ h : History S 0, P.tree.historyWeight 0 h *
        (crraMarginal P.entrepreneurRiskAversion
          ((firmPlanOfAllocation X i).consumption 0 h) *
          X.capitalPrice 0 h)) =
      crraMarginal P.entrepreneurRiskAversion
        ((firmPlanOfAllocation X i).consumption 0 h0) *
        X.capitalPrice 0 h0 := by
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
  rw [hsum0, hsum1] at heuler
  simpa [firmPlanOfAllocation] using heuler

end ProposedDateZeroDeterministicEulerBridge
end Ventura26LiquidityAllocation

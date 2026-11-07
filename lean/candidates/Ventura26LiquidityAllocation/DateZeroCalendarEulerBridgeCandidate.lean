import Ventura26LiquidityAllocation.DateZeroDeterministicMarkovBridgeCandidate
import Ventura26LiquidityAllocation.DateZeroPrimalKKTBridgeCandidate

/-!
# Eliminate redundant off-path transition assumptions from source Markov laws

In a nonnegative finite stochastic row whose probabilities sum to one, a
successor with probability one forces every other successor's probability to
zero. Thus the SOURCE DeterministicBridgeCalendar is already sufficient for
the single-successor Euler theorem; no separate hothers is needed.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedDateZeroCalendarEulerBridge

open ProposedDateZeroDeterministicMarkovBridge
open ProposedDateZeroCapitalEulerDerivative

variable {S : Type*} [Fintype S] [DecidableEq S]

private theorem all_other_transitions_zero
    (T : FiniteMarkovTree S) (s : S)
    (htrans : T.transition T.initial s = 1) :
    ∀ v : S, v ≠ s → T.transition T.initial v = 0 := by
  let f : S → ℝ := T.transition T.initial
  have hsum : (Finset.univ : Finset S).sum f = 1 :=
    T.transition_sum_one T.initial
  have hsplit : ((Finset.univ : Finset S).erase s).sum f + f s =
      (Finset.univ : Finset S).sum f :=
    Finset.sum_erase_add (Finset.univ : Finset S) f (Finset.mem_univ s)
  have hrest : ((Finset.univ : Finset S).erase s).sum f = 0 := by
    have hfs : f s = 1 := htrans
    linarith [hsplit, hsum]
  intro v hv
  have hmem : v ∈ (Finset.univ : Finset S).erase s := by
    simp [hv]
  have hsplitv : (((Finset.univ : Finset S).erase s).erase v).sum f + f v =
      ((Finset.univ : Finset S).erase s).sum f :=
    Finset.sum_erase_add ((Finset.univ : Finset S).erase s) f hmem
  have hnonneg : 0 ≤ (((Finset.univ : Finset S).erase s).erase v).sum f :=
    Finset.sum_nonneg (fun w hw => T.transition_nonneg _ _)
  have hv_nonneg : 0 ≤ f v := T.transition_nonneg _ _
  change f v = 0
  linarith [hsplitv, hrest, hnonneg, hv_nonneg]

/-- A probability-one transition is enough for the deterministic Euler
    equality; the other zero weights follow from the Markov axioms. -/
theorem firmOptimal_deterministicTransition_capitalEuler_of_unitTransition
    (P : Primitives S) (I : InheritedState)
    (X : Allocation S) (i : FirmType) (s : S)
    (hopt : FirmOptimal P I X i)
    (hcapital : ∀ h : History S 0,
      FirmHistoryAdmissible P 0 h → 0 < X.capital i 0 h)
    (hslack : DateZeroSlackBorrower P X i)
    (htrans : P.tree.transition P.tree.initial s = 1) :
    crraMarginal P.entrepreneurRiskAversion
        (X.firmConsumption i 0 (rootHistory P.tree)) *
      X.capitalPrice 0 (rootHistory P.tree) =
    P.entrepreneurDiscount *
      (crraMarginal P.entrepreneurRiskAversion
          (X.firmConsumption i 1 (childHistory (rootHistory P.tree) s)) *
        dateOneMarginalCapitalPayoff P X i (firmPlanOfAllocation X i)
          (childHistory (rootHistory P.tree) s)) := by
  exact firmOptimal_deterministicTransition_capitalEuler
    P I X i s hopt hcapital hslack htrans
      (all_other_transitions_zero P.tree s htrans)

/-- Source calendar (date zero -> date one -> recurrent) supplies the
    probability-one transition, requiring no new environment assumption. -/
theorem firmOptimal_sourceCalendar_capitalEuler
    (P : Primitives S) (I : InheritedState)
    (X : Allocation S) (i : FirmType)
    (dateOne recurrent : S)
    (hcalendar : DeterministicBridgeCalendar P dateOne recurrent)
    (hopt : FirmOptimal P I X i)
    (hcapital : ∀ h : History S 0,
      FirmHistoryAdmissible P 0 h → 0 < X.capital i 0 h)
    (hslack : DateZeroSlackBorrower P X i) :
    crraMarginal P.entrepreneurRiskAversion
        (X.firmConsumption i 0 (rootHistory P.tree)) *
      X.capitalPrice 0 (rootHistory P.tree) =
    P.entrepreneurDiscount *
      (crraMarginal P.entrepreneurRiskAversion
          (X.firmConsumption i 1 (childHistory (rootHistory P.tree) dateOne)) *
        dateOneMarginalCapitalPayoff P X i (firmPlanOfAllocation X i)
          (childHistory (rootHistory P.tree) dateOne)) := by
  apply firmOptimal_deterministicTransition_capitalEuler_of_unitTransition
    P I X i dateOne hopt hcapital hslack
  exact hcalendar.2.2.2.1


/-- In the literal source bridge calendar, source optimality plus the
    strict-slack regime entails the ORIGINAL capital Euler residual at date 0.
    The source DateZeroSlackBorrower assumption supplies dual = 0. -/
theorem firmOptimal_sourceCalendar_slackCapitalEulerResidual_zero
    (P : Primitives S) (I : InheritedState)
    (X : Allocation S) (i : FirmType)
    (dateOne recurrent : S)
    (hcalendar : DeterministicBridgeCalendar P dateOne recurrent)
    (hopt : FirmOptimal P I X i)
    (hcapital : ∀ h : History S 0,
      FirmHistoryAdmissible P 0 h → 0 < X.capital i 0 h)
    (hslack : DateZeroSlackBorrower P X i) :
    localFirmCapitalEulerResidual P X i 0 (rootHistory P.tree) dateOne = 0 := by
  have htrans : P.tree.transition P.tree.initial dateOne = 1 :=
    hcalendar.2.2.2.1
  exact ProposedDateZeroPrimalKKTBridge.firmOptimal_deterministic_slack_sourceCapitalEulerResidual_zero
    P I X i dateOne hopt hcapital hslack htrans
      (all_other_transitions_zero P.tree dateOne htrans)

end ProposedDateZeroCalendarEulerBridge
end Ventura26LiquidityAllocation

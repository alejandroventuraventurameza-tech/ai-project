import Ventura26LiquidityAllocation.DateZeroDeterministicEulerBridgeCandidate

/-!
# A deterministic transition law supplies the single-successor Euler hypotheses

This module discharges the support-concentration assumptions of the preceding
candidate directly from the primitive finite Markov tree. It does not impose
a deterministic law on the original stochastic model: the result is explicitly
conditional on a probability-one transition out of the initial state.
The underlying optimality theorem still requires interior capital and strictly
slack collateral for the selected firm. No equilibrium existence is claimed.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedDateZeroDeterministicMarkovBridge

open ProposedDateZeroDeterministicEulerBridge
open ProposedDateZeroCapitalEulerDerivative

variable {S : Type*} [Fintype S] [DecidableEq S]

private theorem root_weight_one (P : Primitives S) :
    P.tree.historyWeight 0 (rootHistory P.tree) = 1 := by
  simp [FiniteMarkovTree.historyWeight, rootHistory, currentState]

private theorem initial_history_eq_root_of_current_eq
    (P : Primitives S) (h : History S 0)
    (heq : currentState h = P.tree.initial) :
    h = rootHistory P.tree := by
  funext j
  have hj : j = 0 := Fin.eq_zero j
  subst j
  simpa [rootHistory, currentState] using heq

private theorem root_weight_zero_other (P : Primitives S)
    (h : History S 0) (hne : h ≠ rootHistory P.tree) :
    P.tree.historyWeight 0 h = 0 := by
  have hc : currentState h ≠ P.tree.initial := by
    intro he
    exact hne (initial_history_eq_root_of_current_eq P h he)
  simp [FiniteMarkovTree.historyWeight, hc]

private theorem child_weight_one (P : Primitives S) (s : S)
    (htrans : P.tree.transition P.tree.initial s = 1) :
    P.tree.historyWeight 1 (childHistory (rootHistory P.tree) s) = 1 := by
  have hp : previousHistory (childHistory (rootHistory P.tree) s) =
      rootHistory P.tree := by
    funext j
    rfl
  have hc : currentState (childHistory (rootHistory P.tree) s) = s := rfl
  change P.tree.historyWeight 0
      (previousHistory (childHistory (rootHistory P.tree) s)) *
    P.tree.transition
      (currentState (previousHistory (childHistory (rootHistory P.tree) s)))
      (currentState (childHistory (rootHistory P.tree) s)) = 1
  rw [hp, hc, root_weight_one P]
  simpa [rootHistory, currentState] using htrans

private theorem child_weight_zero_other (P : Primitives S) (s : S)
    (hothers : ∀ v : S, v ≠ s → P.tree.transition P.tree.initial v = 0) :
    ∀ h : History S 1,
      h ≠ childHistory (rootHistory P.tree) s →
        P.tree.historyWeight 1 h = 0 := by
  intro h hne
  change P.tree.historyWeight 0 (previousHistory h) *
    P.tree.transition (currentState (previousHistory h)) (currentState h) = 0
  by_cases hp : previousHistory h = rootHistory P.tree
  · have hs : currentState h ≠ s := by
      intro he
      apply hne
      have hrec : childHistory (previousHistory h) (currentState h) = h :=
        childHistory_previousHistory_currentState h
      rw [hp, he] at hrec
      exact hrec.symm
    have ht : P.tree.transition (currentState (previousHistory h))
        (currentState h) = 0 := by
      simpa [hp, rootHistory, currentState] using hothers (currentState h) hs
    rw [ht]
    ring
  · have hw : P.tree.historyWeight 0 (previousHistory h) = 0 :=
      root_weight_zero_other P _ hp
    rw [hw]
    ring

/-- The source optimality Euler under a degenerate transition. -/
theorem firmOptimal_deterministicTransition_capitalEuler
    (P : Primitives S) (I : InheritedState)
    (X : Allocation S) (i : FirmType) (s : S)
    (hopt : FirmOptimal P I X i)
    (hcapital : ∀ h : History S 0,
      FirmHistoryAdmissible P 0 h → 0 < X.capital i 0 h)
    (hslack : DateZeroSlackBorrower P X i)
    (htrans : P.tree.transition P.tree.initial s = 1)
    (hothers : ∀ v : S, v ≠ s →
      P.tree.transition P.tree.initial v = 0) :
    crraMarginal P.entrepreneurRiskAversion
        (X.firmConsumption i 0 (rootHistory P.tree)) *
      X.capitalPrice 0 (rootHistory P.tree) =
    P.entrepreneurDiscount *
      (crraMarginal P.entrepreneurRiskAversion
          (X.firmConsumption i 1 (childHistory (rootHistory P.tree) s)) *
        dateOneMarginalCapitalPayoff P X i (firmPlanOfAllocation X i)
          (childHistory (rootHistory P.tree) s)) := by
  exact firmOptimal_singleSuccessor_capitalEuler
    P I X i (rootHistory P.tree) (childHistory (rootHistory P.tree) s)
    hopt hcapital hslack (root_weight_one P) (root_weight_zero_other P)
    (child_weight_one P s htrans) (child_weight_zero_other P s hothers)

end ProposedDateZeroDeterministicMarkovBridge
end Ventura26LiquidityAllocation

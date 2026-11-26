import Ventura26LiquidityAllocation.DateZeroCapitalNeighborhoodCandidate
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Derive continuity of the realized capital gain from source technology

The profit gain of a DATE-ZERO capital deviation is nonlinear due to real
Cobb-Douglas powers. The Real.rpow continuity theorem gives continuity at
epsilon=0 whenever predetermined capital K>0, independently of the value
of alpha. All other terms are continuous algebraic combinations.

A positive-probability date-one history has a positive-probability
predecessor under the source finite Markov tree. Consequently positive
date-zero capital at admissible histories gives continuity at every
relevant successor.

The final theorem DISCHARGES the explicit gain-continuity assumption of
the prior neighborhood theorem: only original firm optimality, positive
capital and strict slack remain.

No new axioms, sorry/admit, source modifications, assumption of an Euler
FOC, or paper equilibrium witness.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedDateZeroCapitalGainContinuity

open ProposedDateZeroCapitalDeviation
open ProposedDateZeroCapitalNeighborhood

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- With a nonnegative Markov transition, an admissible child cannot
    descend from a zero-probability predecessor. -/
theorem admissible_predecessor_of_admissible_child
    (P : Primitives S) (h : History S 1)
    (hchild : FirmHistoryAdmissible P 1 h) :
    FirmHistoryAdmissible P 0 (previousHistory h) := by
  change 0 <
    P.tree.historyWeight 0 (previousHistory h) *
      P.tree.transition (currentState (previousHistory h)) (currentState h)
    at hchild
  change 0 < P.tree.historyWeight 0 (previousHistory h)
  by_contra hnot
  have hw : P.tree.historyWeight 0 (previousHistory h) ≤ 0 :=
    le_of_not_gt hnot
  have ht :
      0 ≤ P.tree.transition (currentState (previousHistory h)) (currentState h) :=
    P.tree.transition_nonneg _ _
  have hp :
      P.tree.historyWeight 0 (previousHistory h) *
        P.tree.transition (currentState (previousHistory h)) (currentState h) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hw ht
  exact (not_le.mpr hchild) hp

/-- The literal nonlinear realized capital gain is continuous at zero for
    every date-one history whose inherited date-zero capital is positive. -/
theorem dateOneCapitalGain_continuousAt_zero
    (P : Primitives S) (X : Allocation S) (i : FirmType)
    (p : FirmPlan S) (h : History S 1)
    (hcapital : 0 < p.capital 0 (previousHistory h)) :
    ContinuousAt (fun epsilon : ℝ =>
      dateOneCapitalGain P X i p epsilon h) 0 := by
  let K : ℝ := p.capital 0 (previousHistory h)
  have hK : ContinuousAt (fun epsilon : ℝ => K + epsilon) 0 := by
    fun_prop
  have hKnonzero : K + (0 : ℝ) ≠ 0 := by
    simpa [K] using ne_of_gt hcapital
  have hrpow : ContinuousAt (fun epsilon : ℝ =>
      (K + epsilon) ^ P.alpha) 0 :=
    hK.rpow_const (Or.inl hKnonzero)
  have hprofit : ContinuousAt (fun epsilon : ℝ =>
      operatingProfit (X.inputPrice 1 h)
        (P.aggregateProductivity (currentState h) * P.productivity i)
        (K + epsilon) (p.labor 1 h) P.alpha P.beta (X.wage 1 h)) 0 := by
    unfold operatingProfit operatingOutput
    exact
      (continuousAt_const.mul
        ((continuousAt_const.mul hrpow).mul continuousAt_const)).sub
          continuousAt_const
  change ContinuousAt (fun epsilon : ℝ =>
    operatingProfit (X.inputPrice 1 h)
      (P.aggregateProductivity (currentState h) * P.productivity i)
      (K + epsilon) (p.labor 1 h) P.alpha P.beta (X.wage 1 h) -
    operatingProfit (X.inputPrice 1 h)
      (P.aggregateProductivity (currentState h) * P.productivity i)
      K (p.labor 1 h) P.alpha P.beta (X.wage 1 h) +
    X.capitalPrice 1 h * (1 - P.depreciation) * epsilon) 0
  exact (hprofit.sub continuousAt_const).add
    (continuousAt_const.mul continuousAt_id)

/-- No extra analytic gain-continuity assumption is needed under positive
    date-zero capital and source strict-slack collateral. -/
theorem exists_twoSided_feasible_optimality_radius_of_interior_slack
    (P : Primitives S) (I : InheritedState)
    (X : Allocation S) (i : FirmType)
    (hopt : FirmOptimal P I X i)
    (hcapital : ∀ h : History S 0,
      FirmHistoryAdmissible P 0 h → 0 < X.capital i 0 h)
    (hslack : DateZeroSlackBorrower P X i) :
    ∃ radius : ℝ, 0 < radius ∧
      ∀ epsilon : ℝ, |epsilon| < radius →
        FirmFeasible P I X i
          (capitalDateZeroVariation P X i (firmPlanOfAllocation X i) epsilon) ∧
        FirmObjectiveWellDefined P
          (capitalDateZeroVariation P X i (firmPlanOfAllocation X i) epsilon) ∧
        discountedFirmUtility P
          (capitalDateZeroVariation P X i (firmPlanOfAllocation X i) epsilon) ≤
          discountedFirmUtility P (firmPlanOfAllocation X i) := by
  have hgainContinuous : ∀ h : History S 1,
      FirmHistoryAdmissible P 1 h →
      ContinuousAt (fun epsilon : ℝ =>
        dateOneCapitalGain P X i (firmPlanOfAllocation X i) epsilon h) 0 := by
    intro h hh
    have hprev := admissible_predecessor_of_admissible_child P h hh
    apply dateOneCapitalGain_continuousAt_zero P X i
      (firmPlanOfAllocation X i) h
    change 0 < X.capital i 0 (previousHistory h)
    exact hcapital _ hprev
  exact exists_twoSided_feasible_optimality_radius P I X i
    hopt hcapital hslack hgainContinuous

end ProposedDateZeroCapitalGainContinuity
end Ventura26LiquidityAllocation

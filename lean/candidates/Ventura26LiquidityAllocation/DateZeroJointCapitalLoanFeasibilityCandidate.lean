import Ventura26LiquidityAllocation.DateZeroJointCapitalLoanDeviationCandidate

/-!
# Full source feasibility of a joint date-zero capital/loan deviation

The preceding module constructs the exact nonlinear plan and proves the
nominal-face, budget, and date-one wealth identities. Here we isolate ONLY
the remaining local sign and robust-collateral inequalities. Under these
explicit bounds, the entire source FirmFeasible predicate follows. No
economic optimality or derivative is assumed and the source model is not
modified.

Next: on a binding deterministic collateral state, produce a two-sided
radius along the binding tangent and differentiate the actual objective.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedDateZeroJointCapitalLoanFeasibility

open ProposedDateZeroJointCapitalLoanDeviation

variable {S : Type*} [Fintype S] [DecidableEq S]

def JointCapitalLoanVariationLocalBounds
    (P : Primitives S) (X : Allocation S) (i : FirmType)
    (p : FirmPlan S) (dk db : ℝ) : Prop :=
  (∀ h : History S 0, FirmHistoryAdmissible P 0 h →
    0 < p.consumption 0 h - X.capitalPrice 0 h * dk + db ∧
    0 ≤ p.capital 0 h + dk ∧
    0 ≤ p.loan 0 h + db ∧
    RobustCollateral (P.pledgeability i) P.depreciation
      (X.loanRate 0 h) (p.loan 0 h + db) (p.capital 0 h + dk)
      (fun s => 0 < P.tree.transition (currentState h) s)
      (fun s => X.inflation 1 (childHistory h s))
      (fun s => X.capitalPrice 1 (childHistory h s))) ∧
  (∀ h : History S 1, FirmHistoryAdmissible P 1 h →
    0 < p.consumption 1 h + dateOneJointGain P X i p dk db h)

/-- Source-wide feasibility is derived from the few explicit local bounds.
    In particular budgets, face identity and nonlinear wealth transitions
    are NOT postulated as additional hypotheses. -/
theorem jointDateZeroVariation_feasible
    (P : Primitives S) (I : InheritedState)
    (X : Allocation S) (i : FirmType)
    (p : FirmPlan S) (dk db : ℝ)
    (hfeas : FirmFeasible P I X i p)
    (hloc : JointCapitalLoanVariationLocalBounds P X i p dk db) :
    FirmFeasible P I X i
      (jointDateZeroVariation P X i p dk db) := by
  rcases hfeas with ⟨hpos, hface, hbudget, hcoll, hwealth0, hwealthNext⟩
  rcases hloc with ⟨hloc0, hloc1⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t h hadm
    by_cases ht0 : t = 0
    · subst t
      obtain ⟨hc, hk, hb, _⟩ := hloc0 h hadm
      obtain ⟨_, _, hl, _, hd⟩ := hpos 0 h hadm
      simpa [jointDateZeroVariation] using
        (show 0 < p.consumption 0 h - X.capitalPrice 0 h * dk + db ∧
          0 ≤ p.capital 0 h + dk ∧ 0 ≤ p.labor 0 h ∧
          0 ≤ p.loan 0 h + db ∧ 0 ≤ p.deposit 0 h from
          ⟨hc, hk, hl, hb, hd⟩)
    · by_cases ht1 : t = 1
      · subst t
        obtain ⟨_, hk, hl, hb, hd⟩ := hpos 1 h hadm
        simpa [jointDateZeroVariation] using
          (show 0 < p.consumption 1 h + dateOneJointGain P X i p dk db h ∧
            0 ≤ p.capital 1 h ∧ 0 ≤ p.labor 1 h ∧
            0 ≤ p.loan 1 h ∧ 0 ≤ p.deposit 1 h from
            ⟨hloc1 h hadm, hk, hl, hb, hd⟩)
      · simpa [jointDateZeroVariation, ht0, ht1] using
          hpos t h hadm
  · intro t h hadm
    by_cases ht0 : t = 0
    · subst t
      exact joint_signed_face_zero P X i p dk db h
        (hface 0 h hadm)
    · simpa [jointDateZeroVariation, ht0] using hface t h hadm
  · intro t h hadm
    by_cases ht0 : t = 0
    · subst t
      exact joint_budget_zero P X i p dk db h (hbudget 0 h hadm)
    · by_cases ht1 : t = 1
      · subst t
        exact joint_budget_one P X i p dk db h (hbudget 1 h hadm)
      · simpa [jointDateZeroVariation, ht0, ht1] using
          hbudget t h hadm
  · intro t h hadm
    by_cases ht0 : t = 0
    · subst t
      simpa [jointDateZeroVariation] using (hloc0 h hadm).2.2.2
    · simpa [jointDateZeroVariation, ht0] using hcoll t h hadm
  · intro h hadm
    exact hwealth0 h hadm
  · intro t h s hadm
    cases t with
    | zero =>
      exact joint_wealth_transition_one P X i p dk db h s
        (hwealthNext 0 h s hadm)
    | succ t =>
      simpa [jointDateZeroVariation] using
        hwealthNext (t + 1) h s hadm

end ProposedDateZeroJointCapitalLoanFeasibility
end Ventura26LiquidityAllocation

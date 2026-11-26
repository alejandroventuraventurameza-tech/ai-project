import Ventura26LiquidityAllocation.DateZeroJointCapitalLoanFeasibilityCandidate
import Ventura26LiquidityAllocation.DateZeroCapitalUtilityCandidate

/-!
# Infinite-horizon objective-domain preservation for joint capital and loan

The source joint deviation changes entrepreneur consumption ONLY at dates
zero and one. Its discounted utility sequence therefore agrees with the
original from date two onward. Summability is equivalent in both directions
without differentiating the infinite series or assuming a new tail bound.

Combining this fact with the full feasibility theorem yields dominance of
the finite joint deviation from the original FirmOptimal plan. This is the
key prerequisite for deriving the binding-capital-loan tangent derivative.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedDateZeroJointCapitalLoanUtility

open ProposedDateZeroJointCapitalLoanDeviation
open ProposedDateZeroJointCapitalLoanFeasibility

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem jointUtilityTerm_later_eq
    (P : Primitives S) (X : Allocation S) (i : FirmType)
    (p : FirmPlan S) (dk db : ℝ) (n : ℕ) :
    firmUtilityTerm P (jointDateZeroVariation P X i p dk db) (n + 2) =
      firmUtilityTerm P p (n + 2) := by
  have hc :
      (jointDateZeroVariation P X i p dk db).consumption (n + 2) =
        p.consumption (n + 2) := by
    funext h
    simp [jointDateZeroVariation]
  unfold firmUtilityTerm
  rw [hc]

theorem jointVariation_objectiveWellDefined_iff
    (P : Primitives S) (X : Allocation S) (i : FirmType)
    (p : FirmPlan S) (dk db : ℝ) :
    FirmObjectiveWellDefined P (jointDateZeroVariation P X i p dk db) ↔
      FirmObjectiveWellDefined P p := by
  let f : ℕ → ℝ := firmUtilityTerm P (jointDateZeroVariation P X i p dk db)
  let g : ℕ → ℝ := firmUtilityTerm P p
  let middle : ℕ → ℝ := fun n => if n = 0 then f n else g n
  have hfirst : Summable f ↔ Summable middle := by
    apply summable_iff_of_eq_off_one f middle 1
    intro n hn
    by_cases hn0 : n = 0
    · subst n
      simp [middle]
    · change f n = if n = 0 then f n else g n
      simp only [if_neg hn0]
      have hnmin : 2 ≤ n := by omega
      have hnidentity : n - 2 + 2 = n := Nat.sub_add_cancel hnmin
      simpa only [hnidentity] using
        (jointUtilityTerm_later_eq P X i p dk db (n - 2))
  have hsecond : Summable middle ↔ Summable g := by
    apply summable_iff_of_eq_off_one middle g 0
    intro n hn
    simp [middle, hn]
  exact hfirst.trans hsecond

/-- Any locally feasible joint capital-and-financing deviation is dominated
    by the source optimum; objective convergence is derived above. -/
theorem firmOptimal_dominates_jointDeviation
    (P : Primitives S) (I : InheritedState)
    (X : Allocation S) (i : FirmType) (dk db : ℝ)
    (hopt : FirmOptimal P I X i)
    (hloc : JointCapitalLoanVariationLocalBounds P X i
      (firmPlanOfAllocation X i) dk db) :
    discountedFirmUtility P
      (jointDateZeroVariation P X i
        (firmPlanOfAllocation X i) dk db) ≤
    discountedFirmUtility P (firmPlanOfAllocation X i) := by
  apply hopt.2.2.2
  · exact jointDateZeroVariation_feasible P I X i
      (firmPlanOfAllocation X i) dk db hopt.1 hloc
  · exact (jointVariation_objectiveWellDefined_iff P X i
      (firmPlanOfAllocation X i) dk db).2 hopt.2.1

end ProposedDateZeroJointCapitalLoanUtility
end Ventura26LiquidityAllocation

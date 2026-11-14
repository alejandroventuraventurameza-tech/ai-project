import Ventura26LiquidityAllocation.DateZeroCapitalDeviationCandidate

/-!
# Finite-date objective closure for the explicit firm capital deviation

The source FirmObjectiveWellDefined is an infinite-horizon Summable statement.
Because DateZeroCapitalDeviationCandidate modifies consumption ONLY in periods
zero and one, its utility-term sequence agrees with the original at ALL t>=2.
We use the already-audited summable_iff_of_eq_off_one twice.

Consequently the perturbed plan belongs to the original objective domain
whenever the original plan does. Combined with the proved global feasibility
bridge, FirmOptimal genuinely dominates the constructed deviation.

No Euler equation, KKT condition, positivity interval, source modification,
new axiom, sorry, or admit is introduced.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedDateZeroCapitalUtility

open ProposedDateZeroCapitalDeviation

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Unchanged consumption at every t>=2 implies an identical discounted
    utility contribution, for all histories and the original Markov law. -/
theorem utilityTerm_later_eq
    (P : Primitives S) (X : Allocation S) (i : FirmType)
    (p : FirmPlan S) (epsilon : ℝ) (n : ℕ) :
    firmUtilityTerm P (capitalDateZeroVariation P X i p epsilon) (n + 2) =
      firmUtilityTerm P p (n + 2) := by
  have hc :
      (capitalDateZeroVariation P X i p epsilon).consumption (n + 2) =
        p.consumption (n + 2) := by
    funext h
    simp [capitalDateZeroVariation]
  unfold firmUtilityTerm
  rw [hc]

/-- Two finite-date modifications cannot change the summability of the
    full original discounted utility series; neither direction needs
    a new tail bound. -/
theorem capitalVariation_objectiveWellDefined_iff
    (P : Primitives S) (X : Allocation S) (i : FirmType)
    (p : FirmPlan S) (epsilon : ℝ) :
    FirmObjectiveWellDefined P (capitalDateZeroVariation P X i p epsilon) ↔
      FirmObjectiveWellDefined P p := by
  let f : ℕ → ℝ := firmUtilityTerm P (capitalDateZeroVariation P X i p epsilon)
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
        (utilityTerm_later_eq P X i p epsilon (n - 2))
  have hsecond : Summable middle ↔ Summable g := by
    apply summable_iff_of_eq_off_one middle g 0
    intro n hn
    simp [middle, hn]
  exact hfirst.trans hsecond

/-- The ACTUAL optimal firm plan dominates the explicit two-date
    capital perturbation, once the three local sign/collateral tests hold.
    The objective-domain premise is proved above, not assumed. -/
theorem firmOptimal_dominates_capitalDeviation
    (P : Primitives S) (I : InheritedState)
    (X : Allocation S) (i : FirmType) (epsilon : ℝ)
    (hopt : FirmOptimal P I X i)
    (hloc : CapitalVariationLocalBounds P X i
      (firmPlanOfAllocation X i) epsilon) :
    discountedFirmUtility P
      (capitalDateZeroVariation P X i (firmPlanOfAllocation X i) epsilon) ≤
    discountedFirmUtility P (firmPlanOfAllocation X i) := by
  apply hopt.2.2.2
  · exact capitalDateZeroVariation_feasible P I X i
      (firmPlanOfAllocation X i) epsilon hopt.1 hloc
  · exact (capitalVariation_objectiveWellDefined_iff P X i
      (firmPlanOfAllocation X i) epsilon).2 hopt.2.1

end ProposedDateZeroCapitalUtility
end Ventura26LiquidityAllocation

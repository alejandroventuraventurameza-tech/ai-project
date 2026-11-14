import Ventura26LiquidityAllocation.DateZeroJointCapitalLoanTangentAlgebraCandidate
import Ventura26LiquidityAllocation.DateZeroCalendarScalarKKTCandidate

/-!
# Robust binding collateral along the exact joint capital/loan tangent

For the deterministic source calendar there is exactly one supported
date-one successor. At a binding date-zero borrower, a perturbation
    dk = loanRate0 * epsilon
    db = collateralUnit0 * epsilon
preserves the SOURCE robust collateral inequality for arbitrary epsilon,
even when epsilon is negative. This is the basis for a two-sided local
feasible radius once capital/loan/consumption signs are checked.

This lemma does not yet assert full FirmFeasible or optimality.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedDateZeroJointBindingCollateral

open ProposedDateZeroJointCapitalLoanTangentAlgebra
open ProposedDateZeroCalendarEulerBridge
open ProposedDateZeroScalarBindingComplementarity
open ProposedProposition42KKTIdentification

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem binding_sourceCalendar_robustCollateral_joint_tangent
    (P : Primitives S) (X : Allocation S) (i : FirmType)
    (dateOne recurrent : S)
    (hcalendar : DeterministicBridgeCalendar P dateOne recurrent)
    (hbinding : DateZeroBindingBorrower P X i)
    (epsilon : ℝ) :
    RobustCollateral (P.pledgeability i) P.depreciation
      (X.loanRate 0 (rootHistory P.tree))
      (X.loan i 0 (rootHistory P.tree) +
        capitalEulerCollateralUnit P X i 0
          (rootHistory P.tree) dateOne * epsilon)
      (X.capital i 0 (rootHistory P.tree) +
        X.loanRate 0 (rootHistory P.tree) * epsilon)
      (fun s => 0 < P.tree.transition P.tree.initial s)
      (fun s => X.inflation 1 (childHistory (rootHistory P.tree) s))
      (fun s => X.capitalPrice 1 (childHistory (rootHistory P.tree) s)) := by
  let h0 : History S 0 := rootHistory P.tree
  let R : ℝ := X.loanRate 0 h0
  let Gamma : ℝ := capitalEulerCollateralUnit P X i 0 h0 dateOne
  have hothers : ∀ s : S, s ≠ dateOne →
      P.tree.transition P.tree.initial s = 0 :=
    sourceCalendar_other_transitions_zero P dateOne recurrent hcalendar
  have hactive : rootCollateralSlack P X i dateOne = 0 :=
    rootCollateralSlack_zero_of_binding_unique_successor
      P X i dateOne hbinding hothers
  have hbind : R * X.loan i 0 h0 =
      Gamma * X.capital i 0 h0 := by
    dsimp [R, Gamma, h0, rootCollateralSlack,
      capitalEulerCollateralUnit] at *
    nlinarith [hactive]
  have heq := bindingCollateral_joint_tangent
    R (X.loan i 0 h0) (X.capital i 0 h0) Gamma epsilon hbind
  intro s hs
  have hstate : s = dateOne := by
    by_contra hne
    have hz := hothers s hne
    rw [hz] at hs
    exact (lt_irrefl (0 : ℝ)) hs
  subst s
  change R * (X.loan i 0 h0 + Gamma * epsilon) ≤
    P.pledgeability i * (1 - P.depreciation) *
      (X.inflation 1 (childHistory h0 dateOne) *
        X.capitalPrice 1 (childHistory h0 dateOne)) *
      (X.capital i 0 h0 + R * epsilon)
  have hrewrite :
      Gamma =
        P.pledgeability i * (1 - P.depreciation) *
          (X.inflation 1 (childHistory h0 dateOne) *
            X.capitalPrice 1 (childHistory h0 dateOne)) := by
    dsimp [Gamma, capitalEulerCollateralUnit]
    ring
  rw [← hrewrite]
  exact le_of_eq heq

end ProposedDateZeroJointBindingCollateral
end Ventura26LiquidityAllocation

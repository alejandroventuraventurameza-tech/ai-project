import Ventura26LiquidityAllocation.DateZeroJointBindingMarginalBalanceCandidate
import Ventura26LiquidityAllocation.DateZeroCalendarScalarKKTCandidate
import Ventura26LiquidityAllocation.DateZeroJointCapitalLoanTangentAlgebraCandidate

/-!
# One common scalar shadow price for capital and borrowing margins

This theorem aims to close the missing TWO-CONTROL binding KKT interface in
the original deterministic Markov calendar. It combines:
  (1) the nonnegative capital gap from the source one-sided optimum,
  (2) the loan-capital marginal balance derived from the genuine feasible
      two-sided joint tangent and original infinite-horizon FirmOptimal,
  (3) the strict positivity of the loan-rate and collateral coefficient,
  (4) the original binding collateral slack.

The common scalar multiplier satisfies BOTH capital and loan Euler equations
as algebraic marginal conditions, along with complementary slackness.
The theorem does NOT identify the free source Allocation.collateralDual
field or assert complete equilibrium existence, policy uniqueness, or
the entire infinite-horizon KKT system.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedDateZeroJointBindingSharedDual

open ProposedDateZeroJointBindingMarginalBalance
open ProposedDateZeroCalendarScalarKKT
open ProposedDateZeroScalarBindingComplementarity
open ProposedDateZeroJointCapitalLoanTangentAlgebra
open ProposedDateZeroCalendarEulerBridge
open ProposedProposition42KKTIdentification
open ProposedContinuationContractAudit

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem firmOptimal_sourceCalendar_binding_exists_shared_capitalLoanMultiplier
    (P : Primitives S) (I : InheritedState)
    (X : Allocation S) (i : FirmType)
    (dateOne recurrent : S)
    (hcalendar : DeterministicBridgeCalendar P dateOne recurrent)
    (hopt : FirmOptimal P I X i)
    (hbinding : DateZeroBindingBorrower P X i)
    (hcapital : ∀ h : History S 0,
      FirmHistoryAdmissible P 0 h → 0 < X.capital i 0 h)
    (hR : 0 < X.loanRate 0 (rootHistory P.tree))
    (hGamma : 0 < capitalEulerCollateralUnit
      P X i 0 (rootHistory P.tree) dateOne)
    (hpi : X.inflation 1
      (childHistory (rootHistory P.tree) dateOne) ≠ 0) :
    ∃ mu : ℝ, 0 ≤ mu ∧
      capitalEulerPrimalGap P X i 0 (rootHistory P.tree) dateOne =
        mu * capitalEulerCollateralUnit P X i 0
          (rootHistory P.tree) dateOne ∧
      dateZeroLoanPrimalGap P X i dateOne =
        mu * X.loanRate 0 (rootHistory P.tree) ∧
      mu * rootCollateralSlack P X i dateOne = 0 := by
  let h0 : History S 0 := rootHistory P.tree
  let R : ℝ := X.loanRate 0 h0
  let Gamma : ℝ := capitalEulerCollateralUnit P X i 0 h0 dateOne
  obtain ⟨mu0, hmu0, hrow, _hslack, _hcomp⟩ :=
    firmOptimal_sourceCalendar_binding_scalarComplementarity_of_posUnit
      P I X i dateOne recurrent hcalendar hopt hbinding hcapital hGamma
  have hgapEq :
      capitalEulerPrimalGap P X i 0 h0 dateOne = mu0 * Gamma := by
    have hr := hrow
    rw [capitalEulerResidual_eq_primalGap_sub_dual,
      capitalEulerPrimalGap_replaceDual,
      capitalEulerCollateralUnit_replaceDual] at hr
    change capitalEulerPrimalGap P X i 0 h0 dateOne -
      mu0 * Gamma = 0 at hr
    linarith
  have hgapNonneg :
      0 ≤ capitalEulerPrimalGap P X i 0 h0 dateOne := by
    rw [hgapEq]
    exact mul_nonneg hmu0 (le_of_lt hGamma)
  have hbalance :
      R * capitalEulerPrimalGap P X i 0 h0 dateOne =
        Gamma * dateZeroLoanPrimalGap P X i dateOne :=
    firmOptimal_sourceCalendar_binding_capitalLoanGap_balance
      P I X i dateOne recurrent hcalendar hopt hbinding hcapital hpi
  obtain ⟨mu, hmu, hcap, hloan⟩ :=
    exists_shared_scalarMultiplier_of_tangent_balance
      R Gamma (capitalEulerPrimalGap P X i 0 h0 dateOne)
        (dateZeroLoanPrimalGap P X i dateOne)
      hR hGamma hgapNonneg hbalance
  have hothers : ∀ v : S, v ≠ dateOne →
      P.tree.transition P.tree.initial v = 0 :=
    sourceCalendar_other_transitions_zero P dateOne recurrent hcalendar
  have hslack :
      rootCollateralSlack P X i dateOne = 0 :=
    rootCollateralSlack_zero_of_binding_unique_successor
      P X i dateOne hbinding hothers
  refine ⟨mu, hmu, hcap, hloan, ?_⟩
  rw [hslack]
  ring

end ProposedDateZeroJointBindingSharedDual
end Ventura26LiquidityAllocation

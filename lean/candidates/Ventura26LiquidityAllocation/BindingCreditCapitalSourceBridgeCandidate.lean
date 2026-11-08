import Ventura26LiquidityAllocation.BindingCreditCapitalTransmissionCandidate

/-!
# Source bridge: from FirmFeasible to the binding-credit capital identity

This lemma connects the algebra of the financing identity to the literal
economic model's firm budget. We fix a firm, an admissible history, a supported
worst-child liquidation value, and an actually binding robust collateral
constraint. Zero firm deposits and a positive net capital cost are explicit.

FirmFeasible supplies the budget, nonnegative choices, and childwise robust
collateral; it DOES NOT by itself assert collateral equality. Binding is an
additional premise and is never inferred from an active-set label alone.

No FirmOptimal, global equilibrium, branch existence, or growth theorem
follows from this necessary identity.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedBindingCreditCapitalSourceBridge

open ProposedBindingCreditCapitalTransmission

variable {S : Type*} [Fintype S]

/-- A binding promise evaluated at a legitimate supported worst child.
This is a regime-specific condition, NOT a consequence of FirmFeasible. -/
def BindingAtSupportedWorstChild
    (P : Primitives S) (X : Allocation S) (i : FirmType)
    (p : FirmPlan S) (t : ℕ) (h : History S t)
    (liquidation : ℝ) : Prop :=
  SupportedWorstChildValue P X t h liquidation ∧
    X.loanRate t h * p.loan t h =
      (P.pledgeability i * (1 - P.depreciation) * liquidation) *
        p.capital t h

/-- The closed-form binding capital formula follows from the ORIGINAL
FirmFeasible budget, after imposing a binding worst-state robust collateral
constraint and the economically stated no-firm-deposit branch. -/
theorem firmFeasible_binding_capital_formula
    (P : Primitives S) (I : InheritedState) (X : Allocation S)
    (i : FirmType) (p : FirmPlan S) (t : ℕ) (h : History S t)
    (liquidation : ℝ)
    (hfeas : FirmFeasible P I X i p)
    (hadmissible : FirmHistoryAdmissible P t h)
    (hzeroDeposits : p.deposit t h = 0)
    (hbinding : BindingAtSupportedWorstChild P X i p t h liquidation)
    (hloanRate : 0 < X.loanRate t h)
    (hnetPrice : 0 < effectivePrice (X.capitalPrice t h)
      (P.pledgeability i * (1 - P.depreciation) * liquidation)
      (X.loanRate t h)) :
    p.capital t h =
      bindingCapital (p.wealth t h - p.consumption t h)
        (X.capitalPrice t h)
        (P.pledgeability i * (1 - P.depreciation) * liquidation)
        (X.loanRate t h) := by
  obtain ⟨_hworst, hrepayment⟩ := hbinding
  have hbudget := hfeas.2.2.1 t h hadmissible
  have hcash : X.capitalPrice t h * p.capital t h =
      (p.wealth t h - p.consumption t h) + p.loan t h := by
    linarith only [hbudget, hzeroDeposits]
  exact capital_from_budget_and_binding
    (ne_of_gt hloanRate) (ne_of_gt hnetPrice) hcash hrepayment

/-- The same SOURCE hypotheses identify the loan principal. Loan volume
is not an independent causal proxy for chosen capital across equilibria. -/
theorem firmFeasible_binding_loan_formula
    (P : Primitives S) (I : InheritedState) (X : Allocation S)
    (i : FirmType) (p : FirmPlan S) (t : ℕ) (h : History S t)
    (liquidation : ℝ)
    (hfeas : FirmFeasible P I X i p)
    (hadmissible : FirmHistoryAdmissible P t h)
    (hzeroDeposits : p.deposit t h = 0)
    (hbinding : BindingAtSupportedWorstChild P X i p t h liquidation)
    (hloanRate : 0 < X.loanRate t h)
    (hnetPrice : 0 < effectivePrice (X.capitalPrice t h)
      (P.pledgeability i * (1 - P.depreciation) * liquidation)
      (X.loanRate t h)) :
    p.loan t h =
      bindingLoan (p.wealth t h - p.consumption t h)
        (X.capitalPrice t h)
        (P.pledgeability i * (1 - P.depreciation) * liquidation)
        (X.loanRate t h) := by
  have hcapital := firmFeasible_binding_capital_formula
    P I X i p t h liquidation
    hfeas hadmissible hzeroDeposits hbinding hloanRate hnetPrice
  obtain ⟨_hworst, hrepayment⟩ := hbinding
  have hloan := loan_from_binding (ne_of_gt hloanRate) hrepayment
  rw [hcapital] at hloan
  simpa only [bindingLoan] using hloan

#print axioms firmFeasible_binding_capital_formula
#print axioms firmFeasible_binding_loan_formula

end ProposedBindingCreditCapitalSourceBridge
end Ventura26LiquidityAllocation

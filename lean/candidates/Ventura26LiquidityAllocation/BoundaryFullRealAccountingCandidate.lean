import Ventura26LiquidityAllocation.BoundaryFullBankBalanceCandidate

/-!
# Exact accounting and remaining compatibility gates for the named SOURCE root

This module takes the *constructed* full Allocation at the certified SOURCE
frontier, not an existentially assumed history-indexed allocation. The real
aggregate accounts are mechanically completed by the original source model.
The fiscal, household-budget and resource closures are kept separate: the
required OTC settlement and compatibility conditions remain visible.

A successful kernel audit here does NOT imply FirmOptimal, HouseholdOptimal,
BankPopulationEquilibrium, RetailOptimal, terminal conditions or full
CompetitiveEquilibrium.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedBoundaryRealAccounting

open ProposedStationaryRealScale
open ProposedBoundaryFullPrefix
open ProposedBoundaryNormalizationBridge
open ProposedBoundaryFullAllocationCarrier
open ProposedBoundaryFullBankBalance

/-- Exact source aggregate production, capital accumulation/clearing and
retailer/price-adjustment accounting at every supported history. These are
identities satisfied by construction, not optimality certificates. -/
theorem sourceBoundary_real_accounting (G : ℝ) :
    AggregateProduction
      (boundaryPrimitives G boundarySourceRate)
      (boundaryInitialState G boundarySourceRate)
      (sourceBoundaryLiteralAllocation G) ∧
    CapitalClears
      (boundaryPrimitives G boundarySourceRate)
      (boundaryInitialState G boundarySourceRate)
      (sourceBoundaryLiteralAllocation G) ∧
    AccountingIdentities
      (boundaryPrimitives G boundarySourceRate)
      (sourceBoundaryLiteralAllocation G) := by
  let P := boundaryPrimitives G boundarySourceRate
  let I := boundaryInitialState G boundarySourceRate
  let B := localSlackSettlementAllocation P (sourceBoundaryDateData G)
  change AggregateProduction P I (withSourceAccountingCompletion P I B) ∧
    CapitalClears P I (withSourceAccountingCompletion P I B) ∧
    AccountingIdentities P (withSourceAccountingCompletion P I B)
  constructor
  · change AggregateProduction P I (withSourceRealAccounts P I B)
    exact withSourceRealAccounts_aggregateProduction P I B
  constructor
  · change CapitalClears P I (withSourceRealAccounts P I B)
    exact withSourceRealAccounts_capitalClears P I B
  · change AccountingIdentities P (withSourceRealAccounts P I B)
    exact withSourceRealAccounts_accountingIdentities P I B

/-- The constructed loan rate is strictly nonzero at every date:
the new frontier loan rate at date zero and the positive stationary loan
rate at dates one and later. -/
theorem sourceBoundary_all_loan_rates_nonzero (G : ℝ) :
    ∀ t, (sourceBoundaryDateData G t).controls.loanRate ≠ 0 := by
  intro t
  cases t with
  | zero =>
      rw [sourceBoundaryDateData_zero]
      change boundarySourceRate ≠ 0
      exact ne_of_gt boundarySourceRate_positiveRealDomain.1
  | succ t =>
      cases t with
      | zero =>
          rw [sourceBoundaryDateData_one]
          change ProposedStationaryBank.loanRate ≠ 0
          exact ne_of_gt loanRate_pos
      | succ n =>
          change (sourceBoundaryDateData G (n + 2)).controls.loanRate ≠ 0
          rw [sourceBoundaryDateData_tail]
          change ProposedStationaryBank.loanRate ≠ 0
          exact ne_of_gt loanRate_pos

/-- The actual source nominal promises agree with originated loans and
deposits at every supported history, rather than merely at the 33-row
reduced surface. -/
theorem sourceBoundary_current_nominal_face_consistency (G : ℝ) :
    CurrentNominalFaceConsistency
      (boundaryPrimitives G boundarySourceRate)
      (sourceBoundaryLiteralAllocation G) := by
  exact localSlackLiteralAllocation_currentNominalFaceConsistency
    (boundaryPrimitives G boundarySourceRate)
    (boundaryInitialState G boundarySourceRate)
    (sourceBoundaryDateData G)
    (sourceBoundary_all_loan_rates_nonzero G)

/-- The full constructed allocation satisfies the exact fiscal closure IF
and only if its source settlement gate has been supplied here in the
sufficient direction. Net OTC clearing is NOT inferred from bank balance. -/
theorem sourceBoundary_fiscalClosure_of_settlement (G : ℝ)
    (hsettlement :
      SettlementClears
        (boundaryPrimitives G boundarySourceRate)
        (localSlackSettlementAllocation
          (boundaryPrimitives G boundarySourceRate)
          (sourceBoundaryDateData G))) :
    FiscalClosure
      (boundaryPrimitives G boundarySourceRate)
      (boundaryInitialState G boundarySourceRate)
      (sourceBoundaryLiteralAllocation G) := by
  exact withSourceAccountingCompletion_fiscalClosure
    (boundaryPrimitives G boundarySourceRate)
    (boundaryInitialState G boundarySourceRate)
    (localSlackSettlementAllocation
      (boundaryPrimitives G boundarySourceRate)
      (sourceBoundaryDateData G)) hsettlement

/-- The exact remaining real resource obligation for the constructed
history-indexed SOURCE Allocation. Do not confuse row 2 of a reduced
date-data surface with this predicate until a bridge is proved. -/
theorem sourceBoundary_resourceClears_iff (G : ℝ) :
    ResourceClears
      (boundaryPrimitives G boundarySourceRate)
      (sourceBoundaryLiteralAllocation G) ↔
    SourceRealResourceCompatibility
      (boundaryPrimitives G boundarySourceRate)
      (boundaryInitialState G boundarySourceRate)
      (localSlackSettlementAllocation
        (boundaryPrimitives G boundarySourceRate)
        (sourceBoundaryDateData G)) := by
  exact resourceClears_withSourceAccountingCompletion_iff
    (boundaryPrimitives G boundarySourceRate)
    (boundaryInitialState G boundarySourceRate)
    (localSlackSettlementAllocation
      (boundaryPrimitives G boundarySourceRate)
      (sourceBoundaryDateData G))

/-- The exact remaining worker nominal-budget obligation. This equivalence
does not itself prove the worker budget or household optimality. -/
theorem sourceBoundary_householdBudget_iff (G : ℝ) :
    HouseholdBudgetFlows
      (boundaryPrimitives G boundarySourceRate)
      (boundaryInitialState G boundarySourceRate)
      (sourceBoundaryLiteralAllocation G) ↔
    SourceFiscalHouseholdCompatibility
      (boundaryPrimitives G boundarySourceRate)
      (boundaryInitialState G boundarySourceRate)
      (withSourceRealAccounts
        (boundaryPrimitives G boundarySourceRate)
        (boundaryInitialState G boundarySourceRate)
        (localSlackSettlementAllocation
          (boundaryPrimitives G boundarySourceRate)
          (sourceBoundaryDateData G))) := by
  exact householdBudgetFlows_withSourceAccountingCompletion_iff
    (boundaryPrimitives G boundarySourceRate)
    (boundaryInitialState G boundarySourceRate)
    (localSlackSettlementAllocation
      (boundaryPrimitives G boundarySourceRate)
      (sourceBoundaryDateData G))

#print axioms sourceBoundary_real_accounting
#print axioms sourceBoundary_all_loan_rates_nonzero
#print axioms sourceBoundary_current_nominal_face_consistency
#print axioms sourceBoundary_fiscalClosure_of_settlement
#print axioms sourceBoundary_resourceClears_iff
#print axioms sourceBoundary_householdBudget_iff

end ProposedBoundaryRealAccounting
end Ventura26LiquidityAllocation

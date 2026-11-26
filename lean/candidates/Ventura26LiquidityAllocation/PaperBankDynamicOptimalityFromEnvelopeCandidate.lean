import Ventura26LiquidityAllocation.PaperBankUnitKKTAllEquityBridgeCandidate

/-!
# Conditional SOURCE bank dynamic optimality from the derived bank envelope

We connect the EXACT source predicate BankContinuationOptimalAt
(feasibility, well-defined infinite payoff, terminal condition,
and dominance of every feasible and well-defined alternative) to:
  1. an all-equity date-zero Bellman upper envelope;
  2. source first-step tail decomposition for each alternative;
  3. an explicit successor-tail value upper bound;
  4. a candidate that actually attains the proposed upper envelope.

The second theorem obtains the all-equity envelope from the literal
five-dual unit static KKT and source supported-state positivity.
Neither theorem creates an attaining candidate, verifies the
candidate's terminal condition, nor proves the successor-tail value
upper bound. Therefore these are CONDITIONAL implications into
BankContinuationOptimalAt, not a BankOptimal model solution.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedBankDynamicOptimalityFromEnvelope

open ProposedBankGlobalDividendBoundFromNormalized
open ProposedBankSourceNextEquityBridge
open ProposedBankUnitKKTAllEquityBridge
variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The complete source infinite-horizon predicate follows from
an all-alternatives Bellman upper envelope IF tail bounds,
summability, candidate attainment, and candidate terminality are
proved separately. Note that only the candidate needs the terminal
condition, not each arbitrary alternative. -/
theorem source_bank_dynamic_optimal_of_all_equity_envelope
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t)
    (equity coefficient : ℝ)
    (bankValue : BankValueProcess S)
    (candidate : BankContinuationPolicy S P.paymentSupport)
    (hcandidateFeasible : BankContinuationFeasibleAt P X t h equity candidate)
    (hcandidateSummable : BankContinuationObjectiveWellDefinedAt P X t h candidate)
    (hcandidateTerminal : BankContinuationTerminalConditionAt P X t h candidate)
    (hcandidateAttains :
      bankContinuationPayoffAt P X t h candidate = coefficient * equity)
    (hcurrent : 0 < X.workerConsumption t h)
    (hchild : ∀ s, 0 < P.tree.transition (currentState h) s →
      0 < X.workerConsumption (t + 1) (childHistory h s))
    (hallEquityEnvelope : ∀ alternative,
      BankContinuationFeasibleAt P X t h equity alternative →
      alternative.dividend 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j) +
        sourceDateZeroBellman P X t h alternative (bankValue (t + 1)) ≤
        coefficient * equity)
    (haltTailsSummable : ∀ alternative,
      BankContinuationFeasibleAt P X t h equity alternative →
      BankContinuationObjectiveWellDefinedAt P X t h alternative →
      ∀ s, 0 < P.tree.transition (currentState h) s →
      ∀ ω : P.paymentSupport,
      Summable (bankContinuationPayoffTermAt P X (t + 1)
        (childHistory h s) (tailBankContinuationPolicy alternative s ω)))
    (haltTailsBounded : ∀ alternative,
      BankContinuationFeasibleAt P X t h equity alternative →
      BankContinuationObjectiveWellDefinedAt P X t h alternative →
      ∀ s, 0 < P.tree.transition (currentState h) s →
      ∀ ω : P.paymentSupport,
      bankContinuationPayoffAt P X (t + 1) (childHistory h s)
        (tailBankContinuationPolicy alternative s ω) ≤
      bankValue (t + 1)
        (alternative.equity 1 (fun _ => s) (fun _ => ω))
        (childHistory h s)) :
    BankContinuationOptimalAt P X t h equity candidate := by
  refine ⟨hcandidateFeasible, hcandidateSummable, hcandidateTerminal, ?_⟩
  intro alternative haltFeasible haltSummable
  have hfirstStep :=
    bankContinuationPayoffAt_le_sourceBellman_of_tailBound
      P X t h equity alternative haltFeasible (bankValue (t + 1))
      hcurrent hchild
      (haltTailsSummable alternative haltFeasible haltSummable)
      (haltTailsBounded alternative haltFeasible haltSummable)
  calc
    bankContinuationPayoffAt P X t h alternative ≤
        alternative.dividend 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j) +
          sourceDateZeroBellman P X t h alternative (bankValue (t + 1)) := by
      unfold sourceDateZeroBellman
      exact hfirstStep
    _ ≤ coefficient * equity :=
      hallEquityEnvelope alternative haltFeasible
    _ = bankContinuationPayoffAt P X t h candidate :=
      hcandidateAttains.symm

/-- Direct bridge from a SOURCE unit-equity five-dual static KKT
certificate to BankContinuationOptimalAt. Unit KKT, positive
consumption/inflation and exit, nonnegative unit future value and
k>=1 derive the one-step upper bound for ALL source-feasible
alternatives. Candidate attainment, terminality and the infinite
successor-tail envelope are STILL explicit premises. -/
theorem source_bank_dynamic_optimal_of_unit_kkt_and_tail_bounds
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t)
    (equity : ℝ)
    (bankValue : BankValueProcess S)
    (unitLoans unitReserves unitDeposits : ℝ)
    (marginal : BankPayment → ℝ)
    (loanCapDual loanZeroDual reserveZeroDual depositCapDual depositZeroDual : ℝ)
    (hKKT : UnitBankKKTCertificateAt P X t h
      unitLoans unitReserves unitDeposits marginal
      loanCapDual loanZeroDual reserveZeroDual depositCapDual depositZeroDual)
    (hhomogeneous : BankValueHomogeneousAt P t h bankValue)
    (hcurrent : 0 < X.workerConsumption t h)
    (hchild : ∀ s, 0 < P.tree.transition (currentState h) s →
      0 < X.workerConsumption (t + 1) (childHistory h s))
    (hinflation : ∀ s, 0 < P.tree.transition (currentState h) s →
      0 < X.inflation (t + 1) (childHistory h s))
    (hexit : 0 < P.bankExit)
    (hunitValue : ∀ s, 0 < P.tree.transition (currentState h) s →
      0 ≤ bankValue (t + 1) 1 (childHistory h s))
    (hcoefficient : 1 ≤ sourceUnitContinuationCoefficient P X t h
      bankValue unitLoans unitReserves unitDeposits)
    (candidate : BankContinuationPolicy S P.paymentSupport)
    (hcandidateFeasible : BankContinuationFeasibleAt P X t h equity candidate)
    (hcandidateSummable : BankContinuationObjectiveWellDefinedAt P X t h candidate)
    (hcandidateTerminal : BankContinuationTerminalConditionAt P X t h candidate)
    (hcandidateAttains :
      bankContinuationPayoffAt P X t h candidate =
        sourceUnitContinuationCoefficient P X t h bankValue
          unitLoans unitReserves unitDeposits * equity)
    (haltTailsSummable : ∀ alternative,
      BankContinuationFeasibleAt P X t h equity alternative →
      BankContinuationObjectiveWellDefinedAt P X t h alternative →
      ∀ s, 0 < P.tree.transition (currentState h) s →
      ∀ ω : P.paymentSupport,
      Summable (bankContinuationPayoffTermAt P X (t + 1)
        (childHistory h s) (tailBankContinuationPolicy alternative s ω)))
    (haltTailsBounded : ∀ alternative,
      BankContinuationFeasibleAt P X t h equity alternative →
      BankContinuationObjectiveWellDefinedAt P X t h alternative →
      ∀ s, 0 < P.tree.transition (currentState h) s →
      ∀ ω : P.paymentSupport,
      bankContinuationPayoffAt P X (t + 1) (childHistory h s)
        (tailBankContinuationPolicy alternative s ω) ≤
      bankValue (t + 1)
        (alternative.equity 1 (fun _ => s) (fun _ => ω))
        (childHistory h s)) :
    BankContinuationOptimalAt P X t h equity candidate := by
  have hEnvelope :=
    source_all_equity_bank_bellman_bound_of_unit_kkt
      P X t h equity bankValue
      unitLoans unitReserves unitDeposits marginal
      loanCapDual loanZeroDual reserveZeroDual depositCapDual depositZeroDual
      hKKT hhomogeneous hcurrent hchild hinflation hexit hunitValue hcoefficient
  exact source_bank_dynamic_optimal_of_all_equity_envelope
    P X t h equity
    (sourceUnitContinuationCoefficient P X t h bankValue
      unitLoans unitReserves unitDeposits)
    bankValue candidate
    hcandidateFeasible hcandidateSummable hcandidateTerminal
    hcandidateAttains hcurrent hchild hEnvelope
    haltTailsSummable haltTailsBounded

#print axioms source_bank_dynamic_optimal_of_all_equity_envelope
#print axioms source_bank_dynamic_optimal_of_unit_kkt_and_tail_bounds

end ProposedBankDynamicOptimalityFromEnvelope
end Ventura26LiquidityAllocation

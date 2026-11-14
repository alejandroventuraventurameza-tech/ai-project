import Ventura26LiquidityAllocation.PaperBankScaledCandidateAttainmentCandidate

/-!
# SOURCE CONCRETE full-retention bank continuation

The chosen candidate is NOT an invented continuation policy: it is the
literal `bankContinuationPolicyFromPlan` built from the source
`fullRetentionCommonBankPlan`, with actual OTC/facility settlement
and payment-history equity.

We prove:
* source feasibility from `BankFeasible`, the matching-rule plan,
  positive reserve rate and positive market tightness;
* exact date-zero Bellman attainment from the scaled unit portfolio;
* a conditional result in the EXACT source `BankContinuationOptimalAt`,
  using the SOURCE geometric envelope theorem to discharge the
  candidate's summability and terminal conditions.

Economic premises NOT proved here: existence of a global BankFeasible
plan at equilibrium prices, the unit KKT certificate, normalized
portfolio alignment, k >= 1, actual geometric envelope constants,
successor candidate-tail equalities and the alternative-tail upper
bounds. In particular, no BankOptimal or general-equilibrium theorem
is claimed by this module.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedBankConcreteFullRetentionOptimality

open ProposedBankGlobalDividendBoundFromNormalized
open ProposedBankSourceNextEquityBridge
open ProposedBankUnitKKTAllEquityBridge
open ProposedBankDynamicOptimalityFromEnvelope
open ProposedBankScaledCandidateAttainment

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Exactly the source's idiosyncratic-payment continuation policy of
its common full-retention plan. -/
noncomputable def sourceFullRetentionCandidate
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t) :
    BankContinuationPolicy S P.paymentSupport :=
  bankContinuationPolicyFromPlan P X (fullRetentionCommonBankPlan P X) t h

/-- Real SOURCE feasibility of the concrete full-retention candidate,
with the bank's balance, solvency and collateral-like caps taken from
the source BankFeasible predicate and actual settlement matching. -/
theorem source_full_retention_candidate_feasible
    (P : Primitives S) (I : InheritedState) (X : Allocation S)
    (t : ℕ) (h : History S t)
    (hh : FirmHistoryAdmissible P t h)
    (hbankFeasible : BankFeasible P I X (fullRetentionCommonBankPlan P X))
    (hreserveRate : ∀ k H, FirmHistoryAdmissible P k H →
      0 < X.reserveRate k H)
    (htightness : ∀ k H, FirmHistoryAdmissible P k H →
      0 < X.bankTightness k H) :
    BankContinuationFeasibleAt P X t h (X.bankEquity t h)
      (sourceFullRetentionCandidate P X t h) := by
  change BankContinuationFeasibleAt P X t h
    ((fullRetentionCommonBankPlan P X).equity t h)
    (bankContinuationPolicyFromPlan P X (fullRetentionCommonBankPlan P X) t h)
  exact bankContinuationPolicyFromPlan_feasible P I X
    (fullRetentionCommonBankPlan P X) t h hh hbankFeasible
    (fun k H _hk => fullRetentionCommonBankPlan_candidateFlows P X k H)
    hreserveRate htightness

/-- Extract source date-zero controls of the LITERAL candidate.
The normalized ratios are economic premises about the aggregate bank
allocation X, not identities of an arbitrary normalized optimum. -/
theorem source_full_retention_candidate_scaled_initial_controls
    (P : Primitives S) (I : InheritedState) (X : Allocation S)
    (t : ℕ) (h : History S t)
    (hh : FirmHistoryAdmissible P t h)
    (hbankFeasible : BankFeasible P I X (fullRetentionCommonBankPlan P X))
    (unitLoans unitReserves unitDeposits : ℝ)
    (hloans : X.bankLoans t h = X.bankEquity t h * unitLoans)
    (hreserves : X.reservesPrePayment t h = X.bankEquity t h * unitReserves)
    (hdeposits : X.bankDeposits t h = X.bankEquity t h * unitDeposits) :
    (sourceFullRetentionCandidate P X t h).dividend 0
        (fun j => Fin.elim0 j) (fun j => Fin.elim0 j) = 0 ∧
    (sourceFullRetentionCandidate P X t h).loans 0
        (fun j => Fin.elim0 j) (fun j => Fin.elim0 j) =
      X.bankEquity t h * unitLoans ∧
    (sourceFullRetentionCandidate P X t h).reserves 0
        (fun j => Fin.elim0 j) (fun j => Fin.elim0 j) =
      X.bankEquity t h * unitReserves ∧
    (sourceFullRetentionCandidate P X t h).deposits 0
        (fun j => Fin.elim0 j) (fun j => Fin.elim0 j) =
      X.bankEquity t h * unitDeposits := by
  have hequity : 0 < X.bankEquity t h :=
    (hbankFeasible.1 t h hh).1
  have hstarts : BankContinuationStartsWithPlanAt
      (fullRetentionCommonBankPlan P X) t h
      (sourceFullRetentionCandidate P X t h) :=
    bankContinuationPolicyFromPlan_startsWithPlanAt
      P X (fullRetentionCommonBankPlan P X) t h hequity.ne'
  rcases hstarts with ⟨_, hdiv, _, hloan, hres, hdep⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [fullRetentionCommonBankPlan] using hdiv
  · calc
      (sourceFullRetentionCandidate P X t h).loans 0
          (fun j => Fin.elim0 j) (fun j => Fin.elim0 j) =
        (fullRetentionCommonBankPlan P X).loans t h := hloan
      _ = X.bankLoans t h := rfl
      _ = X.bankEquity t h * unitLoans := hloans
  · calc
      (sourceFullRetentionCandidate P X t h).reserves 0
          (fun j => Fin.elim0 j) (fun j => Fin.elim0 j) =
        (fullRetentionCommonBankPlan P X).reservesPre t h := hres
      _ = X.reservesPrePayment t h := rfl
      _ = X.bankEquity t h * unitReserves := hreserves
  · calc
      (sourceFullRetentionCandidate P X t h).deposits 0
          (fun j => Fin.elim0 j) (fun j => Fin.elim0 j) =
        (fullRetentionCommonBankPlan P X).deposits t h := hdep
      _ = X.bankDeposits t h := rfl
      _ = X.bankEquity t h * unitDeposits := hdeposits

/-- Attainment of the SOURCE one-period Bellman bound by the concrete
full-retention candidate, assuming its aggregate portfolio agrees
with the unit portfolio scaled by its initial equity. -/
theorem source_full_retention_candidate_attains_bellman
    (P : Primitives S) (I : InheritedState) (X : Allocation S)
    (t : ℕ) (h : History S t)
    (hh : FirmHistoryAdmissible P t h)
    (hbankFeasible : BankFeasible P I X (fullRetentionCommonBankPlan P X))
    (hreserveRate : ∀ k H, FirmHistoryAdmissible P k H →
      0 < X.reserveRate k H)
    (htightness : ∀ k H, FirmHistoryAdmissible P k H →
      0 < X.bankTightness k H)
    (bankValue : BankValueProcess S)
    (hhomogeneous : BankValueHomogeneousAt P t h bankValue)
    (unitLoans unitReserves unitDeposits : ℝ)
    (hloans : X.bankLoans t h = X.bankEquity t h * unitLoans)
    (hreserves : X.reservesPrePayment t h = X.bankEquity t h * unitReserves)
    (hdeposits : X.bankDeposits t h = X.bankEquity t h * unitDeposits) :
    (sourceFullRetentionCandidate P X t h).dividend 0
        (fun j => Fin.elim0 j) (fun j => Fin.elim0 j) +
      sourceDateZeroBellman P X t h
        (sourceFullRetentionCandidate P X t h) (bankValue (t + 1)) =
      sourceUnitContinuationCoefficient P X t h bankValue
        unitLoans unitReserves unitDeposits * X.bankEquity t h := by
  have hequity : 0 < X.bankEquity t h :=
    (hbankFeasible.1 t h hh).1
  have hfeasible :=
    source_full_retention_candidate_feasible
      P I X t h hh hbankFeasible hreserveRate htightness
  obtain ⟨hdiv, hloan, hres, hdep⟩ :=
    source_full_retention_candidate_scaled_initial_controls
      P I X t h hh hbankFeasible unitLoans unitReserves unitDeposits
      hloans hreserves hdeposits
  exact source_scaled_candidate_attains_one_step_bellman
    P X t h (X.bankEquity t h) hequity
    (sourceFullRetentionCandidate P X t h)
    bankValue unitLoans unitReserves unitDeposits
    hfeasible hhomogeneous hdiv hloan hres hdep

/-- Conditional optimality of the ACTUAL source full-retention plan.
The bank plan's all-history feasibility is a source premise;
candidate summability and terminality are DERIVED from explicit
geometric envelopes using a source theorem; candidate attainment of
the infinite payoff follows from its successor-tail equality.
An independent alternative-tail super-solution is still needed
and is NOT deduced from optimality of the candidate. -/
theorem source_full_retention_candidate_optimal_of_kkt_and_growth
    (P : Primitives S) (I : InheritedState) (X : Allocation S)
    (t : ℕ) (h : History S t)
    (hh : FirmHistoryAdmissible P t h)
    (hbankFeasible : BankFeasible P I X (fullRetentionCommonBankPlan P X))
    (hreserveRate : ∀ k H, FirmHistoryAdmissible P k H →
      0 < X.reserveRate k H)
    (htightness : ∀ k H, FirmHistoryAdmissible P k H →
      0 < X.bankTightness k H)
    (bankValue : BankValueProcess S)
    (unitLoans unitReserves unitDeposits : ℝ)
    (marginal : BankPayment → ℝ)
    (loanCapDual loanZeroDual reserveZeroDual depositCapDual depositZeroDual : ℝ)
    (hKKT : UnitBankKKTCertificateAt P X t h
      unitLoans unitReserves unitDeposits marginal
      loanCapDual loanZeroDual reserveZeroDual depositCapDual depositZeroDual)
    (hhomogeneous : BankValueHomogeneousAt P t h bankValue)
    (hloans : X.bankLoans t h = X.bankEquity t h * unitLoans)
    (hreserves : X.reservesPrePayment t h = X.bankEquity t h * unitReserves)
    (hdeposits : X.bankDeposits t h = X.bankEquity t h * unitDeposits)
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
    (payoffBound payoffRate terminalBound terminalRate : ℝ)
    (hpayoffBound : 0 ≤ payoffBound)
    (hpayoffRate0 : 0 ≤ payoffRate) (hpayoffRate1 : payoffRate < 1)
    (hterminalBound : 0 ≤ terminalBound)
    (hterminalRate0 : 0 ≤ terminalRate) (hterminalRate1 : terminalRate < 1)
    (hpayoff : ∀ n,
      |bankContinuationPayoffTermAt P X t h
        (sourceFullRetentionCandidate P X t h) n| ≤
        payoffBound * payoffRate ^ n)
    (hterminal : ∀ T,
      |bankSurvivingValueTermAt P X t h
        (sourceFullRetentionCandidate P X t h) T| ≤
        terminalBound * terminalRate ^ T)
    (hcandidateTailsSummable : ∀ s,
      0 < P.tree.transition (currentState h) s →
      ∀ omega : P.paymentSupport,
      Summable (bankContinuationPayoffTermAt P X (t + 1)
        (childHistory h s)
        (tailBankContinuationPolicy
          (sourceFullRetentionCandidate P X t h) s omega)))
    (hcandidateTailsExact : ∀ s,
      0 < P.tree.transition (currentState h) s →
      ∀ omega : P.paymentSupport,
      bankContinuationPayoffAt P X (t + 1) (childHistory h s)
        (tailBankContinuationPolicy
          (sourceFullRetentionCandidate P X t h) s omega) =
        bankValue (t + 1)
          ((sourceFullRetentionCandidate P X t h).equity 1
            (fun _ => s) (fun _ => omega))
          (childHistory h s))
    (haltTailsSummable : ∀ alternative,
      BankContinuationFeasibleAt P X t h (X.bankEquity t h) alternative →
      BankContinuationObjectiveWellDefinedAt P X t h alternative →
      ∀ s, 0 < P.tree.transition (currentState h) s →
      ∀ omega : P.paymentSupport,
      Summable (bankContinuationPayoffTermAt P X (t + 1)
        (childHistory h s) (tailBankContinuationPolicy alternative s omega)))
    (haltTailsBounded : ∀ alternative,
      BankContinuationFeasibleAt P X t h (X.bankEquity t h) alternative →
      BankContinuationObjectiveWellDefinedAt P X t h alternative →
      ∀ s, 0 < P.tree.transition (currentState h) s →
      ∀ omega : P.paymentSupport,
      bankContinuationPayoffAt P X (t + 1) (childHistory h s)
        (tailBankContinuationPolicy alternative s omega) ≤
      bankValue (t + 1)
        (alternative.equity 1 (fun _ => s) (fun _ => omega))
        (childHistory h s)) :
    BankContinuationOptimalAt P X t h (X.bankEquity t h)
      (sourceFullRetentionCandidate P X t h) := by
  have hfeasible :=
    source_full_retention_candidate_feasible
      P I X t h hh hbankFeasible hreserveRate htightness
  obtain ⟨hsummable, hterminality⟩ :=
    bankContinuationObjectiveAndTerminal_of_weightedEnvelopes
      P X t h (sourceFullRetentionCandidate P X t h)
      payoffBound payoffRate terminalBound terminalRate
      hpayoffBound hpayoffRate0 hpayoffRate1
      hterminalBound hterminalRate0 hterminalRate1
      hpayoff hterminal
  have hactualValue :=
    source_candidate_actual_payoff_eq_one_step_bellman
      P X t h (X.bankEquity t h)
      (sourceFullRetentionCandidate P X t h) bankValue
      hfeasible hcurrent hchild
      hcandidateTailsSummable hcandidateTailsExact
  have honeStepValue :=
    source_full_retention_candidate_attains_bellman
      P I X t h hh hbankFeasible hreserveRate htightness
      bankValue hhomogeneous
      unitLoans unitReserves unitDeposits
      hloans hreserves hdeposits
  have hactualAttains :
      bankContinuationPayoffAt P X t h
          (sourceFullRetentionCandidate P X t h) =
        sourceUnitContinuationCoefficient P X t h bankValue
          unitLoans unitReserves unitDeposits * X.bankEquity t h :=
    hactualValue.trans honeStepValue
  exact source_bank_dynamic_optimal_of_unit_kkt_and_tail_bounds
    P X t h (X.bankEquity t h) bankValue
    unitLoans unitReserves unitDeposits marginal
    loanCapDual loanZeroDual reserveZeroDual depositCapDual depositZeroDual
    hKKT hhomogeneous hcurrent hchild hinflation hexit hunitValue
    hcoefficient (sourceFullRetentionCandidate P X t h)
    hfeasible hsummable hterminality hactualAttains
    haltTailsSummable haltTailsBounded

#print axioms source_full_retention_candidate_feasible
#print axioms source_full_retention_candidate_scaled_initial_controls
#print axioms source_full_retention_candidate_attains_bellman
#print axioms source_full_retention_candidate_optimal_of_kkt_and_growth

end ProposedBankConcreteFullRetentionOptimality
end Ventura26LiquidityAllocation

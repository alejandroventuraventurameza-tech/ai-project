import Ventura26LiquidityAllocation.PaperBankDynamicOptimalityFromEnvelopeCandidate

/-!
# Attainment: scaled unit portfolio vs. ACTUAL infinite bank owner payoff

At a positive equity e, a dynamically feasible bank candidate with
zero current dividend and date-zero portfolio e*(unit optimal portfolio)
achieves the normalized Bellman upper bound at that date. This is an
equality proved from the LITERAL source homogeneity and static-return
scale theorem; it is NOT an assumption of attained infinite payoff.

A second result reduces actual infinite-horizon value attainment to
summability of supported successor tails and an exact successor-tail
value identity. These are visible, independently necessary premises:
neither global bank optimality nor the candidate tail-value identity
is asserted as proved by the portfolio scaling calculation.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedBankScaledCandidateAttainment

open ProposedBankGlobalDividendBoundFromNormalized
open ProposedBankSourceNextEquityBridge
variable {S : Type*} [Fintype S] [DecidableEq S]

/-- A source-feasible zero-dividend candidate operating the unit
portfolio scaled by positive equity ATTAINS its Bellman one-step
coefficient times equity. No KKT certificate is necessary for this
identity; KKT is needed separately to bound all alternative portfolios. -/
theorem source_scaled_candidate_attains_one_step_bellman
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (equity : ℝ) (hequity : 0 < equity)
    (q : BankContinuationPolicy S P.paymentSupport)
    (bankValue : BankValueProcess S)
    (unitLoans unitReserves unitDeposits : ℝ)
    (hfeasible : BankContinuationFeasibleAt P X t h equity q)
    (hhomogeneous : BankValueHomogeneousAt P t h bankValue)
    (hzeroDividend : q.dividend 0 (fun j => Fin.elim0 j)
      (fun j => Fin.elim0 j) = 0)
    (hloans : q.loans 0 (fun j => Fin.elim0 j)
      (fun j => Fin.elim0 j) = equity * unitLoans)
    (hreserves : q.reserves 0 (fun j => Fin.elim0 j)
      (fun j => Fin.elim0 j) = equity * unitReserves)
    (hdeposits : q.deposits 0 (fun j => Fin.elim0 j)
      (fun j => Fin.elim0 j) = equity * unitDeposits) :
    q.dividend 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j) +
      sourceDateZeroBellman P X t h q (bankValue (t + 1)) =
      sourceUnitContinuationCoefficient P X t h bankValue
        unitLoans unitReserves unitDeposits * equity := by
  have hstatic :=
    bankContinuationFeasibleAt_initialStaticPortfolio
      P X t h equity q hfeasible
  have hBellman :
      sourceDateZeroBellman P X t h q (bankValue (t + 1)) =
        bankBellmanContinuationWeightAt P X t h (bankValue (t + 1)) *
          bankStaticPortfolioPayoffAt P X t h
            (bankOTCDeficitSlopeAt P X t h (X.bankTightness t h))
            (bankOTCSurplusSlopeAt P X t h (X.bankTightness t h))
            (q.loans 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j))
            (q.reserves 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j))
            (q.deposits 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j)) := by
    unfold sourceDateZeroBellman
    exact bankBellmanContinuation_eq_weight_mul_payoff P X t h
      (bankOTCDeficitSlopeAt P X t h (X.bankTightness t h))
      (bankOTCSurplusSlopeAt P X t h (X.bankTightness t h))
      (q.retainedEquity 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j))
      (q.loans 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j))
      (q.reserves 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j))
      (q.deposits 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j))
      bankValue hhomogeneous hstatic
  rw [hBellman, hzeroDividend, zero_add, hloans, hreserves, hdeposits]
  have hscale := bankStaticPortfolioPayoff_scale P X t h
    (bankOTCDeficitSlopeAt P X t h (X.bankTightness t h))
    (bankOTCSurplusSlopeAt P X t h (X.bankTightness t h))
    unitLoans unitReserves unitDeposits equity hequity
  rw [hscale]
  unfold sourceUnitContinuationCoefficient
  ring

/-- Actual source owner payoff agrees with its literal one-step
Bellman evaluation when all supported successor tails are summable
and realize the specified future bankValue. No alternative-policy
tail condition is smuggled into candidate attainment. -/
theorem source_candidate_actual_payoff_eq_one_step_bellman
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (equity : ℝ)
    (q : BankContinuationPolicy S P.paymentSupport)
    (bankValue : BankValueProcess S)
    (hfeasible : BankContinuationFeasibleAt P X t h equity q)
    (hcurrent : 0 < X.workerConsumption t h)
    (hchild : ∀ s, 0 < P.tree.transition (currentState h) s →
      0 < X.workerConsumption (t + 1) (childHistory h s))
    (htailSummable : ∀ s, 0 < P.tree.transition (currentState h) s →
      ∀ ω : P.paymentSupport,
        Summable (bankContinuationPayoffTermAt P X (t + 1)
          (childHistory h s) (tailBankContinuationPolicy q s ω)))
    (htailExact : ∀ s, 0 < P.tree.transition (currentState h) s →
      ∀ ω : P.paymentSupport,
        bankContinuationPayoffAt P X (t + 1) (childHistory h s)
          (tailBankContinuationPolicy q s ω) =
        bankValue (t + 1)
          (q.equity 1 (fun _ => s) (fun _ => ω)) (childHistory h s)) :
    bankContinuationPayoffAt P X t h q =
      q.dividend 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j) +
        sourceDateZeroBellman P X t h q (bankValue (t + 1)) := by
  have htailEnvelope :
      bankContinuationPayoffAt P X t h q =
      ProposedBankSourceOneStepEnvelope.bankTailEnvelopeAt
        P X t h q (bankValue (t + 1)) := by
    rw [bankContinuationPayoffAt_first_step
      P X t h q hcurrent hchild htailSummable]
    unfold ProposedBankSourceOneStepEnvelope.bankTailEnvelopeAt
    apply congrArg (fun z : ℝ =>
      q.dividend 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j) + z)
    apply Finset.sum_congr rfl
    intro s _hs
    apply Finset.sum_congr rfl
    intro ω _hω
    by_cases hzero : P.tree.transition (currentState h) s = 0
    · simp [hzero]
    have hpositive : 0 < P.tree.transition (currentState h) s :=
      lt_of_le_of_ne (P.tree.transition_nonneg _ _) (Ne.symm hzero)
    rw [htailExact s hpositive ω]
  calc
    bankContinuationPayoffAt P X t h q =
        ProposedBankSourceOneStepEnvelope.bankTailEnvelopeAt
          P X t h q (bankValue (t + 1)) := htailEnvelope
    _ = q.dividend 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j) +
        sourceDateZeroBellman P X t h q (bankValue (t + 1)) := by
      rw [bankTailEnvelopeAt_eq_dividend_add_sourceBellman
        P X t h equity q hfeasible (bankValue (t + 1))]
      rfl

/-- Full value attainment now reduces to actual successor-tail
realization + the date-zero scaled unit portfolio identity. This
is weaker as an input than directly postulating
J(candidate)=k*equity, but still requires an independently
verified construction of the candidate and its tails. -/
theorem source_scaled_candidate_actual_payoff_attains_unit_value
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (equity : ℝ) (hequity : 0 < equity)
    (q : BankContinuationPolicy S P.paymentSupport)
    (bankValue : BankValueProcess S)
    (unitLoans unitReserves unitDeposits : ℝ)
    (hfeasible : BankContinuationFeasibleAt P X t h equity q)
    (hhomogeneous : BankValueHomogeneousAt P t h bankValue)
    (hzeroDividend : q.dividend 0 (fun j => Fin.elim0 j)
      (fun j => Fin.elim0 j) = 0)
    (hloans : q.loans 0 (fun j => Fin.elim0 j)
      (fun j => Fin.elim0 j) = equity * unitLoans)
    (hreserves : q.reserves 0 (fun j => Fin.elim0 j)
      (fun j => Fin.elim0 j) = equity * unitReserves)
    (hdeposits : q.deposits 0 (fun j => Fin.elim0 j)
      (fun j => Fin.elim0 j) = equity * unitDeposits)
    (hcurrent : 0 < X.workerConsumption t h)
    (hchild : ∀ s, 0 < P.tree.transition (currentState h) s →
      0 < X.workerConsumption (t + 1) (childHistory h s))
    (htailSummable : ∀ s, 0 < P.tree.transition (currentState h) s →
      ∀ ω : P.paymentSupport,
      Summable (bankContinuationPayoffTermAt P X (t + 1)
        (childHistory h s) (tailBankContinuationPolicy q s ω)))
    (htailExact : ∀ s, 0 < P.tree.transition (currentState h) s →
      ∀ ω : P.paymentSupport,
      bankContinuationPayoffAt P X (t + 1) (childHistory h s)
        (tailBankContinuationPolicy q s ω) =
      bankValue (t + 1)
        (q.equity 1 (fun _ => s) (fun _ => ω)) (childHistory h s)) :
    bankContinuationPayoffAt P X t h q =
      sourceUnitContinuationCoefficient P X t h bankValue
        unitLoans unitReserves unitDeposits * equity := by
  calc
    bankContinuationPayoffAt P X t h q =
        q.dividend 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j) +
          sourceDateZeroBellman P X t h q (bankValue (t + 1)) :=
      source_candidate_actual_payoff_eq_one_step_bellman
        P X t h equity q bankValue hfeasible
        hcurrent hchild htailSummable htailExact
    _ = sourceUnitContinuationCoefficient P X t h bankValue
          unitLoans unitReserves unitDeposits * equity :=
      source_scaled_candidate_attains_one_step_bellman
        P X t h equity hequity q bankValue
        unitLoans unitReserves unitDeposits
        hfeasible hhomogeneous hzeroDividend hloans hreserves hdeposits

#print axioms source_scaled_candidate_attains_one_step_bellman
#print axioms source_candidate_actual_payoff_eq_one_step_bellman
#print axioms source_scaled_candidate_actual_payoff_attains_unit_value

end ProposedBankScaledCandidateAttainment
end Ventura26LiquidityAllocation

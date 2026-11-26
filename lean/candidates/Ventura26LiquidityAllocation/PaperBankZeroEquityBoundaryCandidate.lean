import Ventura26LiquidityAllocation.PaperBankGlobalDividendBoundFromNormalizedCandidate

/-!
# Exact SOURCE zero-equity boundary and one-step Bellman ranking

The source bank's dynamic feasibility imposes zero date-zero dividends,
retention, loans, reserves and deposits when initial equity is zero.
The source static expected payoff of a zero portfolio is identically
zero by degree-one homogeneity, independently of any limit argument.

Together with the already positive-equity envelope, this module
covers ALL source-feasible initial equity sizes, conditional on
homogeneous future value, unit static optimality and k>=1.
The infinite-horizon tail comparison and attainment remain separate
obligations; this is not BankContinuationOptimalAt.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedBankZeroEquityBoundary

open ProposedBankGlobalDividendBoundFromNormalized
open ProposedBankSourceNextEquityBridge
variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The original source zero-equity feasibility clause forces every
initial bank control to vanish, with NO division by initial equity. -/
theorem source_zero_initial_equity_controls
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t)
    (q : BankContinuationPolicy S P.paymentSupport)
    (hfeasible : BankContinuationFeasibleAt P X t h 0 q) :
    q.dividend 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j) = 0 ∧
    q.retainedEquity 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j) = 0 ∧
    q.loans 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j) = 0 ∧
    q.reserves 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j) = 0 ∧
    q.deposits 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j) = 0 := by
  let emptyS : Fin 0 → S := fun j => Fin.elim0 j
  let emptyOmega : Fin 0 → P.paymentSupport := fun j => Fin.elim0 j
  have hzero := hfeasible.2 0 emptyS emptyOmega (by trivial)
  rcases hzero with
    ⟨_, _, _, _, _, _, hzeroBoundary, _, _, _, _, _, _, _⟩
  exact hzeroBoundary hfeasible.1

/-- In the SOURCE linear bank problem, the expected reduced payoff
of the zero portfolio vanishes. Use scaling by TWO rather than
assuming a new primitive about the value at zero. -/
theorem source_static_zero_portfolio_payoff
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t)
    (deficitSlope surplusSlope : ℝ) :
    bankStaticPortfolioPayoffAt P X t h
      deficitSlope surplusSlope 0 0 0 = 0 := by
  have hscale := bankStaticPortfolioPayoff_scale
    P X t h deficitSlope surplusSlope 0 0 0 2 (by norm_num)
  simp only [mul_zero] at hscale
  linarith

/-- At zero initial equity all SOURCE-feasible one-step Bellman values
are zero, given homogeneity of the next-period bank value. -/
theorem source_zero_equity_one_step_value
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t)
    (q : BankContinuationPolicy S P.paymentSupport)
    (bankValue : BankValueProcess S)
    (hfeasible : BankContinuationFeasibleAt P X t h 0 q)
    (hhomogeneous : BankValueHomogeneousAt P t h bankValue) :
    q.dividend 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j) +
      sourceDateZeroBellman P X t h q (bankValue (t + 1)) = 0 := by
  obtain ⟨hdividend, hretained, hloans, hreserves, hdeposits⟩ :=
    source_zero_initial_equity_controls P X t h q hfeasible
  have hstatic := bankContinuationFeasibleAt_initialStaticPortfolio
    P X t h 0 q hfeasible
  have hstaticZero : BankStaticPortfolioFeasibleAt P X t h
      (bankOTCDeficitSlopeAt P X t h (X.bankTightness t h))
      (bankOTCSurplusSlopeAt P X t h (X.bankTightness t h))
      0 0 0 0 := by
    simpa only [hretained, hloans, hreserves, hdeposits]
      using hstatic
  have hbellman := bankBellmanContinuation_eq_weight_mul_payoff
    P X t h
      (bankOTCDeficitSlopeAt P X t h (X.bankTightness t h))
      (bankOTCSurplusSlopeAt P X t h (X.bankTightness t h))
      0 0 0 0 bankValue hhomogeneous hstaticZero
  have hpayoffZero := source_static_zero_portfolio_payoff
    P X t h
      (bankOTCDeficitSlopeAt P X t h (X.bankTightness t h))
      (bankOTCSurplusSlopeAt P X t h (X.bankTightness t h))
  rw [hpayoffZero, mul_zero] at hbellman
  unfold sourceDateZeroBellman
  rw [hdividend, hloans, hreserves, hdeposits, zero_add]
  exact hbellman

/-- The POSITIVE-equity theorem plus the SOURCE zero-equity boundary
covers every feasible initial equity. This is still a one-step bound
conditional on the unit optimizer and the marginal k>=1. -/
theorem source_all_equity_dividend_portfolio_upper_bound
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t)
    (equity : ℝ)
    (bankValue : BankValueProcess S)
    (unitLoans unitReserves unitDeposits : ℝ)
    (hhomogeneous : BankValueHomogeneousAt P t h bankValue)
    (hweight : 0 ≤ bankBellmanContinuationWeightAt P X t h
      (bankValue (t + 1)))
    (hunitOptimal : BankStaticPortfolioOptimalAt P X t h
      (bankOTCDeficitSlopeAt P X t h (X.bankTightness t h))
      (bankOTCSurplusSlopeAt P X t h (X.bankTightness t h))
      1 unitLoans unitReserves unitDeposits)
    (hcoefficient : 1 ≤ sourceUnitContinuationCoefficient
      P X t h bankValue unitLoans unitReserves unitDeposits) :
    ∀ q : BankContinuationPolicy S P.paymentSupport,
      BankContinuationFeasibleAt P X t h equity q →
      q.dividend 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j) +
        sourceDateZeroBellman P X t h q (bankValue (t + 1)) ≤
      sourceUnitContinuationCoefficient P X t h bankValue
        unitLoans unitReserves unitDeposits * equity := by
  intro q hfeasible
  by_cases hzero : equity = 0
  · subst equity
    have hvalueZero :=
      source_zero_equity_one_step_value
        P X t h q bankValue hfeasible hhomogeneous
    rw [hvalueZero, mul_zero]
  · let emptyS : Fin 0 → S := fun j => Fin.elim0 j
    let emptyOmega : Fin 0 → P.paymentSupport := fun j => Fin.elim0 j
    have hdateZeroNonneg := (hfeasible.2 0 emptyS emptyOmega (by trivial)).1
    have hstart : q.equity 0 emptyS emptyOmega = equity := hfeasible.1
    rw [hstart] at hdateZeroNonneg
    have hequity : 0 < equity :=
      lt_of_le_of_ne hdateZeroNonneg (Ne.symm hzero)
    exact source_positive_equity_dividend_and_portfolio_bound
      P X t h equity hequity bankValue
        unitLoans unitReserves unitDeposits
        hhomogeneous hweight hunitOptimal hcoefficient
        q hfeasible

#print axioms source_zero_initial_equity_controls
#print axioms source_static_zero_portfolio_payoff
#print axioms source_zero_equity_one_step_value
#print axioms source_all_equity_dividend_portfolio_upper_bound

end ProposedBankZeroEquityBoundary
end Ventura26LiquidityAllocation

import Ventura26LiquidityAllocation.PaperBankNormalizedPortfolioEnvelopeCandidate

/-!
# Source-feasible bank deviations: discharge the positive-equity global bound

The source's BankContinuationFeasibleAt enforces strictly positive
retention at every supported node with positive bank equity. Combining
this with the already proved normalized portfolio envelope gives the
ONE-STEP Bellman bound for EVERY alternative continuation policy with
the same positive starting equity, rather than assuming that bound.

The normalized unit portfolio must still be shown globally optimal
(KKT certificate) and the normalized continuation coefficient must
be at least one. An attaining candidate and the infinite-horizon
terminal/value identity remain separate obligations.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedBankGlobalDividendBoundFromNormalized

open ProposedBankSourceNextEquityBridge
open ProposedBankNormalizedPortfolioEnvelope
open ProposedBankDividendRetentionDominance

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The literal date-zero source Bellman continuation at a policy's
actual date-zero loan, reserve, and deposit positions. -/
noncomputable def sourceDateZeroBellman
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (q : BankContinuationPolicy S P.paymentSupport)
    (V : ℝ → History S (t + 1) → ℝ) : ℝ :=
  bankBellmanContinuationAt P X t h
    (bankOTCDeficitSlopeAt P X t h (X.bankTightness t h))
    (bankOTCSurplusSlopeAt P X t h (X.bankTightness t h))
    (q.loans 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j))
    (q.reserves 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j))
    (q.deposits 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j))
    V

/-- The SOURCE continuation weight multiplied by the normalized static
unit-equity payoff. No sign or economic optimality is built into this
definition. -/
noncomputable def sourceUnitContinuationCoefficient
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (bankValue : BankValueProcess S)
    (unitLoans unitReserves unitDeposits : ℝ) : ℝ :=
  bankBellmanContinuationWeightAt P X t h (bankValue (t + 1)) *
    bankStaticPortfolioPayoffAt P X t h
      (bankOTCDeficitSlopeAt P X t h (X.bankTightness t h))
      (bankOTCSurplusSlopeAt P X t h (X.bankTightness t h))
      unitLoans unitReserves unitDeposits

/-- Source dynamic feasibility forces positive retained equity when
initial equity is strictly positive. This uses the SOURCE constraint
and does not postulate positivity for a generic static portfolio. -/
theorem source_feasible_positive_initial_retention
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (equity : ℝ) (q : BankContinuationPolicy S P.paymentSupport)
    (hequity : 0 < equity)
    (hfeasible : BankContinuationFeasibleAt P X t h equity q) :
    0 < q.retainedEquity 0
      (fun j => Fin.elim0 j) (fun j => Fin.elim0 j) := by
  let emptyS : Fin 0 → S := fun j => Fin.elim0 j
  let emptyOmega : Fin 0 → P.paymentSupport := fun j => Fin.elim0 j
  have hzero := hfeasible.2 0 emptyS emptyOmega (by trivial)
  rcases hzero with
    ⟨_, _, _, _, _, _, _, hretainedPositive, _, _, _, _, _, _⟩
  have hstart : 0 < q.equity 0 emptyS emptyOmega := by
    rw [hfeasible.1]
    exact hequity
  exact hretainedPositive hstart

/-- A normalized static optimum yields a linear Bellman upper bound
for EVERY source-feasible bank continuation with positive equity.
The all-alternatives Bellman envelope is now DERIVED from the source
scale theorem, not a separate premise. -/
theorem source_positive_equity_global_portfolio_bound
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (equity : ℝ) (hequity : 0 < equity)
    (bankValue : BankValueProcess S)
    (unitLoans unitReserves unitDeposits : ℝ)
    (hhomogeneous : BankValueHomogeneousAt P t h bankValue)
    (hweight : 0 ≤ bankBellmanContinuationWeightAt P X t h
      (bankValue (t + 1)))
    (hunitOptimal : BankStaticPortfolioOptimalAt P X t h
      (bankOTCDeficitSlopeAt P X t h (X.bankTightness t h))
      (bankOTCSurplusSlopeAt P X t h (X.bankTightness t h))
      1 unitLoans unitReserves unitDeposits) :
    ∀ q : BankContinuationPolicy S P.paymentSupport,
      BankContinuationFeasibleAt P X t h equity q →
      sourceDateZeroBellman P X t h q (bankValue (t + 1)) ≤
        sourceUnitContinuationCoefficient P X t h bankValue
          unitLoans unitReserves unitDeposits *
            q.retainedEquity 0
              (fun j => Fin.elim0 j) (fun j => Fin.elim0 j) := by
  intro q hfeasible
  have hretained :=
    source_feasible_positive_initial_retention
      P X t h equity q hequity hfeasible
  have hstatic :=
    bankContinuationFeasibleAt_initialStaticPortfolio
      P X t h equity q hfeasible
  unfold sourceDateZeroBellman sourceUnitContinuationCoefficient
  exact source_bellman_le_retained_mul_unit_value
    P X t h
      (bankOTCDeficitSlopeAt P X t h (X.bankTightness t h))
      (bankOTCSurplusSlopeAt P X t h (X.bankTightness t h))
      (q.retainedEquity 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j))
      (q.loans 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j))
      (q.reserves 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j))
      (q.deposits 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j))
      unitLoans unitReserves unitDeposits
      bankValue hretained hstatic hhomogeneous hweight hunitOptimal

/-- Combining the derived portfolio bound with the SOURCE dividend
identity gives a universal one-step bound among ALL dynamically
feasible bank policies with the same positive starting equity. -/
theorem source_positive_equity_dividend_and_portfolio_bound
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (equity : ℝ) (hequity : 0 < equity)
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
  have hbound := source_positive_equity_global_portfolio_bound
    P X t h equity hequity bankValue
      unitLoans unitReserves unitDeposits
      hhomogeneous hweight hunitOptimal q hfeasible
  unfold sourceDateZeroBellman sourceUnitContinuationCoefficient at *
  exact source_bank_dividend_portfolio_upper_bound
    P X t h equity
    (bankBellmanContinuationWeightAt P X t h (bankValue (t + 1)) *
      bankStaticPortfolioPayoffAt P X t h
        (bankOTCDeficitSlopeAt P X t h (X.bankTightness t h))
        (bankOTCSurplusSlopeAt P X t h (X.bankTightness t h))
        unitLoans unitReserves unitDeposits)
    q (bankValue (t + 1)) hfeasible hcoefficient hbound

#print axioms source_feasible_positive_initial_retention
#print axioms source_positive_equity_global_portfolio_bound
#print axioms source_positive_equity_dividend_and_portfolio_bound

end ProposedBankGlobalDividendBoundFromNormalized
end Ventura26LiquidityAllocation

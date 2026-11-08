import Ventura26LiquidityAllocation.PaperBankStaticSupergradientSufficiencyCandidate

/-!
# A genuine one-period Bellman portfolio comparison from GLOBAL static optimality

The literal source already proves that, for ANY feasible local bank
portfolio, the continuation expression equals a common (state-history
dependent) weight times its static expected gross return, provided the
future bank value is homogeneous in equity.

The new bridge below applies that source equality to BOTH the
candidate and EVERY feasible alternative. With a strictly positive
common continuation weight, the global static portfolio ordering
implies a Bellman continuation ordering without any appeal to FOCs.

What this does not prove: current dividends vs retention, construction
of a globally optimal bank continuation policy over all histories,
infinite-horizon value attainment, terminal/transversality conditions,
or competitive-equilibrium branch existence/selection.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedPaperBankBellmanStaticSufficiency

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The missing reverse bridge from source static dominance to the
source's literal discounted one-period Bellman continuation ranking.
It is NOT the converse of a global infinite-horizon optimality claim. -/
theorem source_bellman_portfolio_ranking_of_static_global_optimality
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t)
    (deficitSlope surplusSlope retainedEquity : ℝ)
    (candidateLoans candidateReserves candidateDeposits : ℝ)
    (bankValue : BankValueProcess S)
    (hhomogeneous : BankValueHomogeneousAt P t h bankValue)
    (hpositiveWeight :
      0 < bankBellmanContinuationWeightAt P X t h (bankValue (t + 1)))
    (hcandidateFeasible : BankStaticPortfolioFeasibleAt P X t h
      deficitSlope surplusSlope retainedEquity
      candidateLoans candidateReserves candidateDeposits)
    (hstaticOptimal : BankStaticPortfolioOptimalAt P X t h
      deficitSlope surplusSlope retainedEquity
      candidateLoans candidateReserves candidateDeposits) :
    ∀ loans reserves deposits,
      BankStaticPortfolioFeasibleAt P X t h
        deficitSlope surplusSlope retainedEquity
        loans reserves deposits →
      bankBellmanContinuationAt P X t h deficitSlope surplusSlope
        loans reserves deposits (bankValue (t + 1)) ≤
      bankBellmanContinuationAt P X t h deficitSlope surplusSlope
        candidateLoans candidateReserves candidateDeposits
        (bankValue (t + 1)) := by
  intro loans reserves deposits hfeasible
  rw [bankBellmanContinuation_eq_weight_mul_payoff P X t h
      deficitSlope surplusSlope retainedEquity
      loans reserves deposits bankValue hhomogeneous hfeasible]
  rw [bankBellmanContinuation_eq_weight_mul_payoff P X t h
      deficitSlope surplusSlope retainedEquity
      candidateLoans candidateReserves candidateDeposits
      bankValue hhomogeneous hcandidateFeasible]
  exact mul_le_mul_of_nonneg_left
    (hstaticOptimal loans reserves deposits hfeasible)
    hpositiveWeight.le

#print axioms source_bellman_portfolio_ranking_of_static_global_optimality

end ProposedPaperBankBellmanStaticSufficiency
end Ventura26LiquidityAllocation

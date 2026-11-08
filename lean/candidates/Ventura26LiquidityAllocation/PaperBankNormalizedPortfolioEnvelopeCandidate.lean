import Ventura26LiquidityAllocation.PaperBankDividendRetentionDominanceCandidate

/-!
# SOURCE normalized bank portfolio envelope under positive retained equity

A degree-one static banking problem converts global optimality at
ONE unit of retained equity to a uniform linear upper bound for
every feasible positive retained equity. This removes the need to
assume a separate bound for each positive size, provided that the
normalized static optimizer and positive continuation weight are
established in the source economy.

The unit optimizer, value-process homogeneity and nonnegative
continuation weight are explicit hypotheses. This file does not
establish BankContinuationOptimalAt or BankOptimal and does not
cover the zero-equity branch.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedBankNormalizedPortfolioEnvelope

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- A SOURCE static optimum at retained equity one dominates
any feasible portfolio with retained equity r>0, up to scale r. -/
theorem source_static_payoff_le_retained_mul_unit_optimum
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t)
    (deficitSlope surplusSlope retained loans reserves deposits : ℝ)
    (unitLoans unitReserves unitDeposits : ℝ)
    (hretained : 0 < retained)
    (hfeasible : BankStaticPortfolioFeasibleAt P X t h
      deficitSlope surplusSlope retained loans reserves deposits)
    (hunitOptimal : BankStaticPortfolioOptimalAt P X t h
      deficitSlope surplusSlope 1 unitLoans unitReserves unitDeposits) :
    bankStaticPortfolioPayoffAt P X t h deficitSlope surplusSlope
      loans reserves deposits ≤
    retained * bankStaticPortfolioPayoffAt P X t h
      deficitSlope surplusSlope unitLoans unitReserves unitDeposits := by
  have hunit : (1 / retained : ℝ) * retained = 1 := by
    field_simp [ne_of_gt hretained]
  have hnormalized := bankStaticPortfolioFeasible_scale
    P X t h deficitSlope surplusSlope
      retained loans reserves deposits
      (1 / retained) (one_div_pos.mpr hretained) hfeasible
  rw [hunit] at hnormalized
  have hunitBound := hunitOptimal
    ((1 / retained) * loans)
    ((1 / retained) * reserves)
    ((1 / retained) * deposits) hnormalized
  have hrecover (z : ℝ) : retained * ((1 / retained) * z) = z := by
    calc
      retained * ((1 / retained) * z) =
        ((1 / retained) * retained) * z := by ring
      _ = z := by rw [hunit]; ring
  have hscaled := bankStaticPortfolioPayoff_scale
    P X t h deficitSlope surplusSlope
      ((1 / retained) * loans)
      ((1 / retained) * reserves)
      ((1 / retained) * deposits)
      retained hretained
  rw [hrecover loans, hrecover reserves, hrecover deposits] at hscaled
  calc
    bankStaticPortfolioPayoffAt P X t h deficitSlope surplusSlope
        loans reserves deposits =
      retained * bankStaticPortfolioPayoffAt P X t h deficitSlope surplusSlope
        ((1 / retained) * loans)
        ((1 / retained) * reserves)
        ((1 / retained) * deposits) := hscaled
    _ ≤ retained * bankStaticPortfolioPayoffAt P X t h deficitSlope
        surplusSlope unitLoans unitReserves unitDeposits :=
      mul_le_mul_of_nonneg_left hunitBound hretained.le

/-- SOURCE Bellman continuation bound from source homogeneity and a
globally optimal one-equity static portfolio. Exactly the model's
original Bellman and discount weight appear on both sides. -/
theorem source_bellman_le_retained_mul_unit_value
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t)
    (deficitSlope surplusSlope retained loans reserves deposits : ℝ)
    (unitLoans unitReserves unitDeposits : ℝ)
    (bankValue : BankValueProcess S)
    (hretained : 0 < retained)
    (hfeasible : BankStaticPortfolioFeasibleAt P X t h
      deficitSlope surplusSlope retained loans reserves deposits)
    (hhomogeneous : BankValueHomogeneousAt P t h bankValue)
    (hweight : 0 ≤ bankBellmanContinuationWeightAt P X t h
      (bankValue (t + 1)))
    (hunitOptimal : BankStaticPortfolioOptimalAt P X t h
      deficitSlope surplusSlope 1 unitLoans unitReserves unitDeposits) :
    bankBellmanContinuationAt P X t h
        deficitSlope surplusSlope loans reserves deposits
        (bankValue (t + 1)) ≤
      (bankBellmanContinuationWeightAt P X t h (bankValue (t + 1)) *
        bankStaticPortfolioPayoffAt P X t h deficitSlope surplusSlope
          unitLoans unitReserves unitDeposits) * retained := by
  rw [bankBellmanContinuation_eq_weight_mul_payoff
    P X t h deficitSlope surplusSlope retained loans reserves deposits
    bankValue hhomogeneous hfeasible]
  have hpayoff := source_static_payoff_le_retained_mul_unit_optimum
    P X t h deficitSlope surplusSlope retained
      loans reserves deposits unitLoans unitReserves unitDeposits
      hretained hfeasible hunitOptimal
  have hweighted := mul_le_mul_of_nonneg_left hpayoff hweight
  calc
    bankBellmanContinuationWeightAt P X t h (bankValue (t + 1)) *
        bankStaticPortfolioPayoffAt P X t h deficitSlope surplusSlope
          loans reserves deposits ≤
      bankBellmanContinuationWeightAt P X t h (bankValue (t + 1)) *
        (retained * bankStaticPortfolioPayoffAt P X t h
          deficitSlope surplusSlope unitLoans unitReserves unitDeposits) :=
      hweighted
    _ = (bankBellmanContinuationWeightAt P X t h
        (bankValue (t + 1)) *
        bankStaticPortfolioPayoffAt P X t h deficitSlope surplusSlope
          unitLoans unitReserves unitDeposits) * retained := by ring

#print axioms source_static_payoff_le_retained_mul_unit_optimum
#print axioms source_bellman_le_retained_mul_unit_value

end ProposedBankNormalizedPortfolioEnvelope
end Ventura26LiquidityAllocation

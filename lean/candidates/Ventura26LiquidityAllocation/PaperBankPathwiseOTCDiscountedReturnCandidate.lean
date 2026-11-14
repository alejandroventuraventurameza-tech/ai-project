import Ventura26LiquidityAllocation.PaperBankSurvivingContractionCandidate

/-!
# Source OTC portfolio: exact pathwise discounted equity multiplier

The verified source theorem `fullRetentionContinuation_cumulative_joint_child`
rewrites the next-period individual bank equity times cumulative household
SDF as current discounted equity times a LITERAL multiplier. That multiplier
retains the source matching-generated OTC balance-sheet return and next
period inflation. Nothing is replaced by an exogenous reduced-form return.

The first proof gives a PATHWISE discounted-equity upper bound from a
bound on that literal multiplier. The second dissects a sufficient
bound into a household SDF/consumption factor and a real bank portfolio
return/aggregate-equity factor.

Neither proof has yet summed over Markov transitions and payment
probabilities. Therefore it does NOT certify the expected surviving
equity contraction, which remains a separate aggregation obligation.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedBankPathwiseOTCDiscountedReturn

open ProposedBankConcreteFullRetentionOptimality

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The *actual* one-step real SDF times gross equity-return factor:
household discount/consumption ratio times the detailed OTC bank
portfolio return, scaled by aggregate bank equity and inflation.
For the source exact identity we use log worker utility (risk aversion 1).
This definition itself does not enforce signs or a bound. -/
noncomputable def sourceDiscountedEquityGrowthFactor
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t) (n : ℕ)
    (future : Fin n → S) (s : S) (omega : P.paymentSupport) : ℝ :=
  (P.workerDiscount *
      X.workerConsumption (t + n) (continuationHistory h future) /
        X.workerConsumption (t + n + 1)
          (childHistory (continuationHistory h future) s)) *
    (bankDetailedPortfolioReturnAt P X (t + n)
        (continuationHistory h future)
        (X.bankTightness (t + n) (continuationHistory h future))
        (X.bankLoans (t + n) (continuationHistory h future))
        (X.reservesPrePayment (t + n) (continuationHistory h future))
        (X.bankDeposits (t + n) (continuationHistory h future)) omega /
      X.bankEquity (t + n) (continuationHistory h future) /
      X.inflation (t + n + 1)
        (childHistory (continuationHistory h future) s))

/-- At each individual aggregate/payment history, the SOURCE
SDF-discounted equity at the child is bounded by a gross factor times
current SDF-discounted equity. The bridge uses the source's exact
matching and payment-dependent bank return, with no Bellman or
global-equilibrium optimality assumption. -/
theorem source_full_retention_discounted_equity_pathwise_le
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t) (n : ℕ)
    (future : Fin n → S) (payments : Fin n → P.paymentSupport)
    (s : S) (omega : P.paymentSupport)
    (grossBound : ℝ)
    (hrisk : P.workerRiskAversion = 1)
    (hinitialConsumption : 0 < X.workerConsumption t h)
    (hcurrentConsumption : 0 <
      X.workerConsumption (t + n) (continuationHistory h future))
    (hchildConsumption : 0 <
      X.workerConsumption (t + n + 1)
        (childHistory (continuationHistory h future) s))
    (hindividual : 0 <
      (sourceFullRetentionCandidate P X t h).equity n future payments)
    (haggregate : 0 <
      X.bankEquity (t + n) (continuationHistory h future))
    (hfactor : sourceDiscountedEquityGrowthFactor
      P X t h n future s omega ≤ grossBound) :
    bankCumulativeSDFAt P X t h (childFutureHistory future s) *
        (sourceFullRetentionCandidate P X t h).equity (n + 1)
          (childFutureHistory future s) (childPaymentHistory payments omega) ≤
      (bankCumulativeSDFAt P X t h future *
        (sourceFullRetentionCandidate P X t h).equity n future payments) *
          grossBound := by
  have hbeta : 0 < P.workerDiscount :=
    lt_trans P.discount_order.1 P.discount_order.2.1
  have hsdf : 0 < bankCumulativeSDFAt P X t h future := by
    unfold bankCumulativeSDFAt
    exact div_pos
      (mul_pos (pow_pos hbeta n)
        (Real.rpow_pos_of_pos hcurrentConsumption (-P.workerRiskAversion)))
      (Real.rpow_pos_of_pos hinitialConsumption (-P.workerRiskAversion))
  have hnonneg : 0 ≤
      bankCumulativeSDFAt P X t h future *
        (sourceFullRetentionCandidate P X t h).equity n future payments :=
    (mul_pos hsdf hindividual).le
  have hsource := fullRetentionContinuation_cumulative_joint_child
    P X t h n future payments s omega
    hrisk hcurrentConsumption hchildConsumption.ne'
    hindividual haggregate
  calc
    bankCumulativeSDFAt P X t h (childFutureHistory future s) *
        (sourceFullRetentionCandidate P X t h).equity (n + 1)
          (childFutureHistory future s) (childPaymentHistory payments omega) =
      (bankCumulativeSDFAt P X t h future *
        (sourceFullRetentionCandidate P X t h).equity n future payments) *
          sourceDiscountedEquityGrowthFactor
            P X t h n future s omega := by
      simpa only [sourceFullRetentionCandidate,
        sourceDiscountedEquityGrowthFactor] using hsource
    _ ≤ (bankCumulativeSDFAt P X t h future *
        (sourceFullRetentionCandidate P X t h).equity n future payments) *
          grossBound :=
      mul_le_mul_of_nonneg_left hfactor hnonneg

/-- The literal source one-step factor is controlled by TWO
economically interpretable multipliers: the discounted marginal-
utility/consumption ratio and the detailed real bank return per
unit of aggregate equity. Each bound must be established from the
candidate equilibrium (or a numerical enclosure), not assumed as
a generally valid property of OTC market clearing. -/
theorem source_discounted_equity_growth_factor_le_two_bounds
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t) (n : ℕ)
    (future : Fin n → S) (s : S) (omega : P.paymentSupport)
    (sdfBound realReturnBound : ℝ)
    (hsdfLower : 0 ≤
      P.workerDiscount *
        X.workerConsumption (t + n) (continuationHistory h future) /
          X.workerConsumption (t + n + 1)
            (childHistory (continuationHistory h future) s))
    (hsdfUpper :
      P.workerDiscount *
        X.workerConsumption (t + n) (continuationHistory h future) /
          X.workerConsumption (t + n + 1)
            (childHistory (continuationHistory h future) s) ≤ sdfBound)
    (hreturnLower : 0 ≤
      bankDetailedPortfolioReturnAt P X (t + n)
        (continuationHistory h future)
        (X.bankTightness (t + n) (continuationHistory h future))
        (X.bankLoans (t + n) (continuationHistory h future))
        (X.reservesPrePayment (t + n) (continuationHistory h future))
        (X.bankDeposits (t + n) (continuationHistory h future)) omega /
      X.bankEquity (t + n) (continuationHistory h future) /
      X.inflation (t + n + 1)
        (childHistory (continuationHistory h future) s))
    (hreturnUpper :
      bankDetailedPortfolioReturnAt P X (t + n)
        (continuationHistory h future)
        (X.bankTightness (t + n) (continuationHistory h future))
        (X.bankLoans (t + n) (continuationHistory h future))
        (X.reservesPrePayment (t + n) (continuationHistory h future))
        (X.bankDeposits (t + n) (continuationHistory h future)) omega /
      X.bankEquity (t + n) (continuationHistory h future) /
      X.inflation (t + n + 1)
        (childHistory (continuationHistory h future) s) ≤ realReturnBound) :
    sourceDiscountedEquityGrowthFactor P X t h n future s omega ≤
      sdfBound * realReturnBound := by
  unfold sourceDiscountedEquityGrowthFactor
  have hnonnegSdfBound : 0 ≤ sdfBound := le_trans hsdfLower hsdfUpper
  exact mul_le_mul hsdfUpper hreturnUpper hreturnLower hnonnegSdfBound

#print axioms source_full_retention_discounted_equity_pathwise_le
#print axioms source_discounted_equity_growth_factor_le_two_bounds

end ProposedBankPathwiseOTCDiscountedReturn
end Ventura26LiquidityAllocation

import Ventura26LiquidityAllocation.PaperBankExpectedSurvivorEnvelopeCandidate

/-!
# From the SOURCE one-step OTC bank return to all-history pathwise growth

The previous bridge proved that exact Markov and payment path weights
sum to one. Here we complete the other missing direction: a uniform
bound on the LITERAL discounted OTC bank-equity growth factor at every
supported child implies a uniform bound on discounted equity along
EVERY finite individual payment history.

The proof uses the source recursive equity plan rather than substituting
an aggregate bank balance for each individual's history.

The economic cost is explicit: log worker utility, strictly positive
individual and aggregate equity at all relevant histories, positive
worker consumption, and a uniform upper bound on the detailed
source OTC discounted return. These are not asserted to be automatic
properties of a computed equilibrium.

Combining the induction with primitive probability normalization gives
the concrete full-retention candidate's summability and TVC, whenever
(1-bankExit)*grossBound < 1.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedBankPathwiseGrowthInduction

open ProposedBankConcreteFullRetentionOptimality
open ProposedBankPathwiseOTCDiscountedReturn
open ProposedBankExpectedSurvivorEnvelope

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Positive household consumption and the primitive discount ordering
ensure strict positivity of the source cumulative stochastic discount
factor along every supported or unsupported aggregate history. -/
theorem source_bank_cumulative_sdf_pos
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t) (n : ℕ) (future : Fin n → S)
    (hinitial : 0 < X.workerConsumption t h)
    (hfuture : 0 <
      X.workerConsumption (t + n) (continuationHistory h future)) :
    0 < bankCumulativeSDFAt P X t h future := by
  have hbeta : 0 < P.workerDiscount :=
    lt_trans P.discount_order.1 P.discount_order.2.1
  unfold bankCumulativeSDFAt
  exact div_pos
    (mul_pos (pow_pos hbeta n)
      (Real.rpow_pos_of_pos hfuture (-P.workerRiskAversion)))
    (Real.rpow_pos_of_pos hinitial (-P.workerRiskAversion))

/-- The LITERAL source full-retention bank continuation starts at
the aggregate bank equity, but thereafter individual equity remains
specific to the realized sequence of payment shocks. -/
theorem source_full_retention_initial_discounted_equity
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t)
    (future : Fin 0 → S) (payments : Fin 0 → P.paymentSupport)
    (hinitial : 0 < X.workerConsumption t h) :
    bankCumulativeSDFAt P X t h future *
      (sourceFullRetentionCandidate P X t h).equity 0 future payments =
      X.bankEquity t h := by
  have hconsumptionPow :
      X.workerConsumption t h ^ (-P.workerRiskAversion) ≠ 0 :=
    (Real.rpow_pos_of_pos hinitial (-P.workerRiskAversion)).ne'
  have hsdf : bankCumulativeSDFAt P X t h future = 1 := by
    unfold bankCumulativeSDFAt
    rw [continuationHistory_zero h future]
    simp [hconsumptionPow]
  have hequity :
      (sourceFullRetentionCandidate P X t h).equity 0 future payments =
      X.bankEquity t h := rfl
  rw [hsdf, hequity, one_mul]

/-- Inductively multiply the detailed source one-step upper bound.
No control or equilibrium price is silently replaced by an exogenous
loan return, and no stationary banking distribution is assumed.

`grossBound` may be >1. What matters for terminality is the
discounted survival-adjusted factor. -/
theorem source_full_retention_pathwise_discounted_equity_power_bound
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t)
    (C grossBound : ℝ)
    (hinitial : 0 < X.workerConsumption t h)
    (hC : X.bankEquity t h ≤ C)
    (hgross : 0 ≤ grossBound)
    (hrisk : P.workerRiskAversion = 1)
    (hconsumption : ∀ n (future : Fin n → S),
      0 < X.workerConsumption (t + n) (continuationHistory h future))
    (hchildConsumption : ∀ n (future : Fin n → S) s,
      0 < X.workerConsumption (t + n + 1)
        (childHistory (continuationHistory h future) s))
    (hindividual : ∀ n (future : Fin n → S)
      (payments : Fin n → P.paymentSupport),
      0 < (sourceFullRetentionCandidate P X t h).equity n future payments)
    (haggregate : ∀ n (future : Fin n → S),
      0 < X.bankEquity (t + n) (continuationHistory h future))
    (hfactor : ∀ n (future : Fin n → S) s
      (omega : P.paymentSupport),
      sourceDiscountedEquityGrowthFactor P X t h n future s omega ≤
        grossBound) :
    ∀ n (future : Fin n → S) (payments : Fin n → P.paymentSupport),
      bankCumulativeSDFAt P X t h future *
        (sourceFullRetentionCandidate P X t h).equity n future payments ≤
          C * grossBound ^ n := by
  intro n
  induction n with
  | zero =>
    intro future payments
    have hstart := source_full_retention_initial_discounted_equity
      P X t h future payments hinitial
    rw [hstart, pow_zero, mul_one]
    exact hC
  | succ n ih =>
    intro future payments
    let previousFuture : Fin n → S := fun j => future j.succ
    let previousPayments : Fin n → P.paymentSupport :=
      fun j => payments j.succ
    have hfuture :
        childFutureHistory previousFuture (future 0) = future := by
      funext j
      refine Fin.cases ?_ (fun k => ?_) j <;> rfl
    have hpayments :
        childPaymentHistory previousPayments (payments 0) = payments := by
      funext j
      refine Fin.cases ?_ (fun k => ?_) j <;> rfl
    have hstep :=
      source_full_retention_discounted_equity_pathwise_le
        P X t h n previousFuture previousPayments (future 0)
        (payments 0) grossBound hrisk hinitial
        (hconsumption n previousFuture)
        (hchildConsumption n previousFuture (future 0))
        (hindividual n previousFuture previousPayments)
        (haggregate n previousFuture)
        (hfactor n previousFuture (future 0) (payments 0))
    rw [hfuture, hpayments] at hstep
    calc
      bankCumulativeSDFAt P X t h future *
          (sourceFullRetentionCandidate P X t h).equity (n + 1)
            future payments ≤
        (bankCumulativeSDFAt P X t h previousFuture *
          (sourceFullRetentionCandidate P X t h).equity n
            previousFuture previousPayments) * grossBound := hstep
      _ ≤ (C * grossBound ^ n) * grossBound :=
        mul_le_mul_of_nonneg_right
          (ih previousFuture previousPayments) hgross
      _ = C * grossBound ^ (n + 1) := by
        rw [pow_succ]
        ring

/-- A concrete bridge from a per-step bound on the SOURCE discounted
OTC portfolio return to owner-payoff summability and terminality of
the exact full-retention candidate. Markov and payment paths are
aggregated using source-normalized probability weights. -/
theorem source_full_retention_analytic_conditions_of_otc_pathwise_factor
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t)
    (C grossBound : ℝ)
    (hinitial : 0 < X.workerConsumption t h)
    (hC : 0 ≤ C)
    (hbase : X.bankEquity t h ≤ C)
    (hgross : 0 ≤ grossBound)
    (hrisk : P.workerRiskAversion = 1)
    (hexit : P.bankExit < 1)
    (hcontract : (1 - P.bankExit) * grossBound < 1)
    (hconsumption : ∀ n (future : Fin n → S),
      0 < X.workerConsumption (t + n) (continuationHistory h future))
    (hchildConsumption : ∀ n (future : Fin n → S) s,
      0 < X.workerConsumption (t + n + 1)
        (childHistory (continuationHistory h future) s))
    (hindividual : ∀ n (future : Fin n → S)
      (payments : Fin n → P.paymentSupport),
      0 < (sourceFullRetentionCandidate P X t h).equity n future payments)
    (haggregate : ∀ n (future : Fin n → S),
      0 < X.bankEquity (t + n) (continuationHistory h future))
    (hfactor : ∀ n (future : Fin n → S) s
      (omega : P.paymentSupport),
      sourceDiscountedEquityGrowthFactor P X t h n future s omega ≤
        grossBound) :
    BankContinuationObjectiveWellDefinedAt P X t h
      (sourceFullRetentionCandidate P X t h) ∧
    BankContinuationTerminalConditionAt P X t h
      (sourceFullRetentionCandidate P X t h) := by
  have hpathUpper :=
    source_full_retention_pathwise_discounted_equity_power_bound
      P X t h C grossBound hinitial hbase hgross hrisk
      hconsumption hchildConsumption hindividual haggregate hfactor
  have hpathNonneg : ∀ n (future : Fin n → S)
      (payments : Fin n → P.paymentSupport),
      0 ≤ bankCumulativeSDFAt P X t h future *
        (sourceFullRetentionCandidate P X t h).equity n future payments := by
    intro n future payments
    exact (mul_pos
      (source_bank_cumulative_sdf_pos P X t h n future
        hinitial (hconsumption n future))
      (hindividual n future payments)).le
  exact source_full_retention_analytic_conditions_of_pathwise_growth
    P X t h C grossBound hC hgross
    (sub_nonneg.mpr P.bank_exit_mem.2) hexit hcontract
    hpathNonneg hpathUpper

#print axioms source_bank_cumulative_sdf_pos
#print axioms source_full_retention_initial_discounted_equity
#print axioms source_full_retention_pathwise_discounted_equity_power_bound
#print axioms source_full_retention_analytic_conditions_of_otc_pathwise_factor

end ProposedBankPathwiseGrowthInduction
end Ventura26LiquidityAllocation

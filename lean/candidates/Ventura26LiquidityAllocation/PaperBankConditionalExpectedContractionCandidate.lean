import Ventura26LiquidityAllocation.PaperBankConditionalOTCMeanCandidate

/-!
# Conditional OTC growth: from bank-wealth-weighted return to survivor TVC

The SOURCE terminal term is the survival probability (1-exit)^n
times a finite Markov/payment expectation of discounted individual
bank equity. The finite conditional growth inequality was already
kernel-checked in PaperBankConditionalOTCMeanCandidate.

Here we prove that a ONE-STEP exact mass identity (separately stated)
turns that inequality into a survivor-equity contraction, hence both
summability and the terminal condition of the literal full-retention
source bank. The bridge is valid even with correlation between
individual bank equity and the historical OTC return.

The exact mass identity is STILL AN EXPLICIT HYPOTHESIS:
    Mass_(n+1) = sum_{hist_n} probability(hist_n) *
                 discountedEquity(hist_n) * conditionalOTCGrowth(hist_n).
Proving it requires reindexing the SOURCE Fin histories and applying
fullRetentionContinuation_cumulative_joint_child, and is the next
kernel obligation. This module makes that boundary impossible to hide.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedBankConditionalExpectedContraction

open ProposedBankConcreteFullRetentionOptimality
open ProposedBankConditionalOTCMean
open ProposedBankContinuationPathProbabilityMass
open ProposedBankExpectedSurvivorEnvelope
open ProposedBankFullRetentionTerminalEnvelope
open ProposedBankSurvivingContraction

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- SOURCE discounted expected equity before applying the survival
probability. Both finite law factors are the original primitives. -/
noncomputable def sourceDiscountedBankEquityMassAt
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (n : ℕ) : ℝ :=
  ∑ future : Fin n → S, ∑ payments : Fin n → P.paymentSupport,
    (continuationTransitionWeight P.tree (currentState h) n future *
      continuationPaymentWeight P payments) *
      (bankCumulativeSDFAt P X t h future *
        (sourceFullRetentionCandidate P X t h).equity n future payments)

/-- The original source survival-weighted equity term equals
survival probability to the n times the SOURCE discounted equity mass.
This is an exact finite-sum identity, not a moment approximation. -/
theorem source_surviving_value_eq_survival_pow_mul_mass
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t) (n : ℕ) :
    bankSurvivingValueTermAt P X t h
      (sourceFullRetentionCandidate P X t h) n =
      (1 - P.bankExit) ^ n *
        sourceDiscountedBankEquityMassAt P X t h n := by
  classical
  unfold bankSurvivingValueTermAt sourceDiscountedBankEquityMassAt
  calc
    (∑ future : Fin n → S, ∑ payments : Fin n → P.paymentSupport,
      continuationTransitionWeight P.tree (currentState h) n future *
        continuationPaymentWeight P payments *
        bankCumulativeSDFAt P X t h future *
        (1 - P.bankExit) ^ n *
        (sourceFullRetentionCandidate P X t h).equity n future payments) =
      ∑ future : Fin n → S, ∑ payments : Fin n → P.paymentSupport,
        (1 - P.bankExit) ^ n *
          ((continuationTransitionWeight P.tree (currentState h) n future *
            continuationPaymentWeight P payments) *
            (bankCumulativeSDFAt P X t h future *
              (sourceFullRetentionCandidate P X t h).equity n future payments)) := by
        apply Finset.sum_congr rfl
        intro future _hf
        apply Finset.sum_congr rfl
        intro payments _hp
        ring
    _ = (1 - P.bankExit) ^ n *
      (∑ future : Fin n → S, ∑ payments : Fin n → P.paymentSupport,
        (continuationTransitionWeight P.tree (currentState h) n future *
          continuationPaymentWeight P payments) *
          (bankCumulativeSDFAt P X t h future *
            (sourceFullRetentionCandidate P X t h).equity n future payments)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro future _hf
        rw [Finset.mul_sum]

/-- Conditional mean bounds yield the exact SOURCE mass contraction,
provided the source's ONE-STEP mass-aggregation identity has been
proved independently. No unconditional independence assumption. -/
theorem source_discounted_bank_mass_contracts_of_conditional_otc_bound
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t) (grossBound : ℝ)
    (hnonneg : ∀ n (future : Fin n → S)
      (payments : Fin n → P.paymentSupport),
      0 ≤ bankCumulativeSDFAt P X t h future *
        (sourceFullRetentionCandidate P X t h).equity n future payments)
    (hconditional : ∀ n (future : Fin n → S),
      sourceConditionalOTCGrowthFactor P X t h n future ≤ grossBound)
    (hnext : ∀ n,
      sourceDiscountedBankEquityMassAt P X t h (n + 1) =
      ∑ future : Fin n → S, ∑ payments : Fin n → P.paymentSupport,
        ((continuationTransitionWeight P.tree (currentState h) n future *
          continuationPaymentWeight P payments) *
          (bankCumulativeSDFAt P X t h future *
            (sourceFullRetentionCandidate P X t h).equity n future payments)) *
          sourceConditionalOTCGrowthFactor P X t h n future) :
    ∀ n, sourceDiscountedBankEquityMassAt P X t h (n + 1) ≤
      grossBound * sourceDiscountedBankEquityMassAt P X t h n := by
  intro n
  calc
    sourceDiscountedBankEquityMassAt P X t h (n + 1) =
      ∑ future : Fin n → S, ∑ payments : Fin n → P.paymentSupport,
        ((continuationTransitionWeight P.tree (currentState h) n future *
          continuationPaymentWeight P payments) *
          (bankCumulativeSDFAt P X t h future *
            (sourceFullRetentionCandidate P X t h).equity n future payments)) *
          sourceConditionalOTCGrowthFactor P X t h n future := hnext n
    _ ≤ grossBound * sourceDiscountedBankEquityMassAt P X t h n := by
      unfold sourceDiscountedBankEquityMassAt
      exact source_conditional_otc_mean_weighted_bound
        P X t h n grossBound (hnonneg n) (hconditional n)

/-- The conditional expected OTC return induces a nonnegative
survivor-equity contraction of ratio (1-exit)*grossBound, without
a worst-case bound on each shock. -/
theorem source_surviving_equity_contracts_of_conditional_otc_bound
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t) (grossBound : ℝ)
    (hsurvive : 0 ≤ 1 - P.bankExit)
    (hnonneg : ∀ n (future : Fin n → S)
      (payments : Fin n → P.paymentSupport),
      0 ≤ bankCumulativeSDFAt P X t h future *
        (sourceFullRetentionCandidate P X t h).equity n future payments)
    (hconditional : ∀ n (future : Fin n → S),
      sourceConditionalOTCGrowthFactor P X t h n future ≤ grossBound)
    (hnext : ∀ n,
      sourceDiscountedBankEquityMassAt P X t h (n + 1) =
      ∑ future : Fin n → S, ∑ payments : Fin n → P.paymentSupport,
        ((continuationTransitionWeight P.tree (currentState h) n future *
          continuationPaymentWeight P payments) *
          (bankCumulativeSDFAt P X t h future *
            (sourceFullRetentionCandidate P X t h).equity n future payments)) *
          sourceConditionalOTCGrowthFactor P X t h n future) :
    ∀ n, bankSurvivingValueTermAt P X t h
        (sourceFullRetentionCandidate P X t h) (n + 1) ≤
      ((1 - P.bankExit) * grossBound) *
        bankSurvivingValueTermAt P X t h
          (sourceFullRetentionCandidate P X t h) n := by
  have hmass := source_discounted_bank_mass_contracts_of_conditional_otc_bound
    P X t h grossBound hnonneg hconditional hnext
  intro n
  calc
    bankSurvivingValueTermAt P X t h
        (sourceFullRetentionCandidate P X t h) (n + 1) =
      (1 - P.bankExit) ^ (n + 1) *
        sourceDiscountedBankEquityMassAt P X t h (n + 1) :=
      source_surviving_value_eq_survival_pow_mul_mass P X t h (n + 1)
    _ ≤ (1 - P.bankExit) ^ (n + 1) *
        (grossBound * sourceDiscountedBankEquityMassAt P X t h n) :=
      mul_le_mul_of_nonneg_left (hmass n) (pow_nonneg hsurvive _)
    _ = ((1 - P.bankExit) * grossBound) *
        bankSurvivingValueTermAt P X t h
          (sourceFullRetentionCandidate P X t h) n := by
      rw [source_surviving_value_eq_survival_pow_mul_mass P X t h n]
      rw [pow_succ]
      ring

/-- SOURCE terminal condition and owner-payoff summability from a
CONDITIONAL, wealth-weighted OTC growth bound. The only remaining
technical input in this theorem is the explicit one-step mass identity,
not an unexplained black-box expectation or BankOptimal assumption. -/
theorem source_full_retention_tvc_of_conditional_otc_return
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t)
    (C grossBound : ℝ)
    (hC : 0 ≤ C)
    (hgross : 0 ≤ grossBound)
    (hsurvive : 0 ≤ 1 - P.bankExit)
    (hexit : P.bankExit < 1)
    (hcontraction : (1 - P.bankExit) * grossBound < 1)
    (hbase : bankSurvivingValueTermAt P X t h
        (sourceFullRetentionCandidate P X t h) 0 ≤ C)
    (hnonneg : ∀ n (future : Fin n → S)
      (payments : Fin n → P.paymentSupport),
      0 ≤ bankCumulativeSDFAt P X t h future *
        (sourceFullRetentionCandidate P X t h).equity n future payments)
    (hconditional : ∀ n (future : Fin n → S),
      sourceConditionalOTCGrowthFactor P X t h n future ≤ grossBound)
    (hnext : ∀ n,
      sourceDiscountedBankEquityMassAt P X t h (n + 1) =
      ∑ future : Fin n → S, ∑ payments : Fin n → P.paymentSupport,
        ((continuationTransitionWeight P.tree (currentState h) n future *
          continuationPaymentWeight P payments) *
          (bankCumulativeSDFAt P X t h future *
            (sourceFullRetentionCandidate P X t h).equity n future payments)) *
          sourceConditionalOTCGrowthFactor P X t h n future) :
    BankContinuationObjectiveWellDefinedAt P X t h
      (sourceFullRetentionCandidate P X t h) ∧
    BankContinuationTerminalConditionAt P X t h
      (sourceFullRetentionCandidate P X t h) := by
  have hnonnegSurvive := source_surviving_value_nonneg_of_pathwise_nonneg
    P X t h hsurvive hnonneg
  have hstep := source_surviving_equity_contracts_of_conditional_otc_bound
    P X t h grossBound hsurvive hnonneg hconditional hnext
  exact full_retention_analytic_conditions_of_survivor_contraction
    P X t h C ((1 - P.bankExit) * grossBound)
    hC (mul_nonneg hsurvive hgross) hcontraction
    hexit hnonnegSurvive hbase hstep

#print axioms source_surviving_value_eq_survival_pow_mul_mass
#print axioms source_discounted_bank_mass_contracts_of_conditional_otc_bound
#print axioms source_surviving_equity_contracts_of_conditional_otc_bound
#print axioms source_full_retention_tvc_of_conditional_otc_return

end ProposedBankConditionalExpectedContraction
end Ventura26LiquidityAllocation

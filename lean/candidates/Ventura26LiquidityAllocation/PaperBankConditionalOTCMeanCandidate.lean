import Ventura26LiquidityAllocation.PaperBankZeroEquityAbsorptionCandidate

/-!
# Finite conditional OTC-return bound with individual bank wealth weights

The literal full-retention discounted return multiplier is determined
by the aggregate history and the NEXT aggregate/payment shock.
Individual bank equity still depends on its entire prior sequence of
idiosyncratic payment shocks.

A conditional mean bound on that multiplier can be applied to the
current bank-equity-weighted probability distribution WITHOUT assuming
independence of bank wealth and future returns. It is not valid to
substitute an unconditional mean bound without an additional argument.

This module proves the weighted finite-sum inequality in the SOURCE
Markov and payment carrier. An independent time-extension identity is
still required to identify its left side with next-date surviving equity.
It does not yet prove BankOptimal, an actual conditional return
enclosure, or an equilibrium trajectory.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedBankConditionalOTCMean

open ProposedBankConcreteFullRetentionOptimality
open ProposedBankPathwiseOTCDiscountedReturn
open ProposedBankContinuationPathProbabilityMass

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The conditional expected real discounted OTC equity multiplier
at a given aggregate future path. It does not depend on the bank's
past payment path because the SOURCE bank portfolio scales linearly
with each individual bank's own equity. -/
noncomputable def sourceConditionalOTCGrowthFactor
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t) (n : ℕ)
    (future : Fin n → S) : ℝ :=
  ∑ s : S, ∑ omega : P.paymentSupport,
    P.tree.transition (currentState (continuationHistory h future)) s *
      P.paymentProbability omega *
      sourceDiscountedEquityGrowthFactor P X t h n future s omega

/-- For SOURCE probabilities, a bounded CONDITIONAL expected OTC
growth factor yields an upper bound for the equity-weighted
conditional future return. Past individual equity and the factor
are allowed to be correlated through the aggregate history. -/
theorem source_conditional_otc_mean_weighted_bound
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t) (n : ℕ) (grossBound : ℝ)
    (hnonneg : ∀ (future : Fin n → S)
      (payments : Fin n → P.paymentSupport),
      0 ≤ bankCumulativeSDFAt P X t h future *
        (sourceFullRetentionCandidate P X t h).equity n future payments)
    (hconditional : ∀ (future : Fin n → S),
      sourceConditionalOTCGrowthFactor P X t h n future ≤ grossBound) :
    (∑ future : Fin n → S, ∑ payments : Fin n → P.paymentSupport,
      ((continuationTransitionWeight P.tree (currentState h) n future *
          continuationPaymentWeight P payments) *
        (bankCumulativeSDFAt P X t h future *
          (sourceFullRetentionCandidate P X t h).equity n future payments)) *
        sourceConditionalOTCGrowthFactor P X t h n future) ≤
    grossBound *
      (∑ future : Fin n → S, ∑ payments : Fin n → P.paymentSupport,
        (continuationTransitionWeight P.tree (currentState h) n future *
          continuationPaymentWeight P payments) *
        (bankCumulativeSDFAt P X t h future *
          (sourceFullRetentionCandidate P X t h).equity n future payments)) := by
  classical
  have hweight : ∀ (future : Fin n → S)
      (payments : Fin n → P.paymentSupport),
      0 ≤ (continuationTransitionWeight P.tree (currentState h) n future *
          continuationPaymentWeight P payments) *
        (bankCumulativeSDFAt P X t h future *
          (sourceFullRetentionCandidate P X t h).equity n future payments) := by
    intro future payments
    exact mul_nonneg
      (source_joint_future_path_weight_nonneg
        P n (currentState h) future payments)
      (hnonneg future payments)
  calc
    (∑ future : Fin n → S, ∑ payments : Fin n → P.paymentSupport,
      ((continuationTransitionWeight P.tree (currentState h) n future *
          continuationPaymentWeight P payments) *
        (bankCumulativeSDFAt P X t h future *
          (sourceFullRetentionCandidate P X t h).equity n future payments)) *
        sourceConditionalOTCGrowthFactor P X t h n future) ≤
      ∑ future : Fin n → S, ∑ payments : Fin n → P.paymentSupport,
        ((continuationTransitionWeight P.tree (currentState h) n future *
            continuationPaymentWeight P payments) *
          (bankCumulativeSDFAt P X t h future *
            (sourceFullRetentionCandidate P X t h).equity n future payments)) *
          grossBound := by
      apply Finset.sum_le_sum
      intro future _hf
      apply Finset.sum_le_sum
      intro payments _hp
      exact mul_le_mul_of_nonneg_left
        (hconditional future) (hweight future payments)
    _ = (∑ future : Fin n → S, ∑ payments : Fin n → P.paymentSupport,
        (continuationTransitionWeight P.tree (currentState h) n future *
          continuationPaymentWeight P payments) *
        (bankCumulativeSDFAt P X t h future *
          (sourceFullRetentionCandidate P X t h).equity n future payments)) *
        grossBound := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro future _hf
      rw [Finset.sum_mul]
    _ = grossBound *
      (∑ future : Fin n → S, ∑ payments : Fin n → P.paymentSupport,
        (continuationTransitionWeight P.tree (currentState h) n future *
          continuationPaymentWeight P payments) *
        (bankCumulativeSDFAt P X t h future *
          (sourceFullRetentionCandidate P X t h).equity n future payments)) := by
      ring

#print axioms source_conditional_otc_mean_weighted_bound

end ProposedBankConditionalOTCMean
end Ventura26LiquidityAllocation

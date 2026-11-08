import Ventura26LiquidityAllocation.PaperBankContinuationPathProbabilityMassCandidate

/-!
# From SOURCE pathwise discounted bank equity to the EXPECTED survivor TVC

The exact source bank surviving-value term is not a single-path value:
it integrates over the primitive Markov path and idiosyncratic payment
support and multiplies by the bank survival probability.

Using the proven finite-path probability normalization and
nonnegative weights, this file derives the geometric surviving-value
upper bound from a UNIFORM pathwise discounted bank-equity bound.
It then derives the source bank candidate's objective summability
and terminal condition from a single factor (1-bankExit)*gross < 1.

The uniform pathwise discounted-return bound still must be proved
from the OTC source return and household SDF. The next gate is to
derive it by induction from the exact SOURCE child-equity identity.
The result below does not construct a competitive equilibrium,
BankOptimal or a numerical IRF.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedBankExpectedSurvivorEnvelope

open ProposedBankContinuationPathProbabilityMass
open ProposedBankConcreteFullRetentionOptimality
open ProposedBankFullRetentionTerminalEnvelope

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Nonnegative pathwise SDF times bank equity imply nonnegative
discounted expected surviving equity, using SOURCE probabilities. -/
theorem source_surviving_value_nonneg_of_pathwise_nonneg
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (hsurvive : 0 ≤ 1 - P.bankExit)
    (hpathNonneg : ∀ n (future : Fin n → S)
      (payments : Fin n → P.paymentSupport),
      0 ≤ bankCumulativeSDFAt P X t h future *
        (sourceFullRetentionCandidate P X t h).equity n future payments) :
    ∀ n, 0 ≤ bankSurvivingValueTermAt P X t h
      (sourceFullRetentionCandidate P X t h) n := by
  classical
  intro n
  unfold bankSurvivingValueTermAt
  apply Finset.sum_nonneg
  intro future _hf
  apply Finset.sum_nonneg
  intro payments _hp
  have hweight := source_joint_future_path_weight_nonneg
    P n (currentState h) future payments
  have hterm := mul_nonneg
    (pow_nonneg hsurvive n) (hpathNonneg n future payments)
  calc
    0 ≤ (continuationTransitionWeight P.tree (currentState h) n future *
        continuationPaymentWeight P payments) *
      ((1 - P.bankExit) ^ n *
        (bankCumulativeSDFAt P X t h future *
          (sourceFullRetentionCandidate P X t h).equity n future payments)) :=
      mul_nonneg hweight hterm
    _ = continuationTransitionWeight P.tree (currentState h) n future *
        continuationPaymentWeight P payments *
        bankCumulativeSDFAt P X t h future *
        (1 - P.bankExit) ^ n *
        (sourceFullRetentionCandidate P X t h).equity n future payments := by
      ring

/-- A uniform *pathwise* discounted-equity bound plus the exact
probability-one mass of the SOURCE Markov/payment carrier gives the
survival-weighted expected equity upper bound. The normalization
is not a hypothesis: see the imported primitive path lemmas. -/
theorem source_expected_surviving_equity_geometric_upper_bound
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (C gross : ℝ)
    (hsurvive : 0 ≤ 1 - P.bankExit)
    (hpathUpper : ∀ n (future : Fin n → S)
      (payments : Fin n → P.paymentSupport),
      bankCumulativeSDFAt P X t h future *
        (sourceFullRetentionCandidate P X t h).equity n future payments ≤
          C * gross ^ n) :
    ∀ n, bankSurvivingValueTermAt P X t h
      (sourceFullRetentionCandidate P X t h) n ≤
        C * ((1 - P.bankExit) * gross) ^ n := by
  classical
  intro n
  have hsurvivePower : 0 ≤ (1 - P.bankExit) ^ n :=
    pow_nonneg hsurvive n
  have hpower : (1 - P.bankExit) ^ n * (C * gross ^ n) =
      C * ((1 - P.bankExit) * gross) ^ n := by
    rw [mul_pow]
    ring
  unfold bankSurvivingValueTermAt
  calc
    (∑ future : Fin n → S, ∑ payments : Fin n → P.paymentSupport,
      continuationTransitionWeight P.tree (currentState h) n future *
        continuationPaymentWeight P payments *
        bankCumulativeSDFAt P X t h future *
        (1 - P.bankExit) ^ n *
        (sourceFullRetentionCandidate P X t h).equity n future payments) =
      (∑ future : Fin n → S, ∑ payments : Fin n → P.paymentSupport,
        (continuationTransitionWeight P.tree (currentState h) n future *
          continuationPaymentWeight P payments) *
          ((1 - P.bankExit) ^ n *
            (bankCumulativeSDFAt P X t h future *
              (sourceFullRetentionCandidate P X t h).equity n future payments))) := by
      apply Finset.sum_congr rfl
      intro future _hf
      apply Finset.sum_congr rfl
      intro payments _hp
      ring
    _ ≤ ∑ future : Fin n → S, ∑ payments : Fin n → P.paymentSupport,
        (continuationTransitionWeight P.tree (currentState h) n future *
          continuationPaymentWeight P payments) *
          (C * ((1 - P.bankExit) * gross) ^ n) := by
      apply Finset.sum_le_sum
      intro future _hf
      apply Finset.sum_le_sum
      intro payments _hp
      have hbound := mul_le_mul_of_nonneg_left
        (hpathUpper n future payments) hsurvivePower
      rw [hpower] at hbound
      exact mul_le_mul_of_nonneg_left hbound
        (source_joint_future_path_weight_nonneg
          P n (currentState h) future payments)
    _ = (∑ future : Fin n → S, ∑ payments : Fin n → P.paymentSupport,
          continuationTransitionWeight P.tree (currentState h) n future *
            continuationPaymentWeight P payments) *
          (C * ((1 - P.bankExit) * gross) ^ n) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro future _hf
      rw [Finset.sum_mul]
    _ = C * ((1 - P.bankExit) * gross) ^ n := by
      rw [source_joint_future_path_mass_one]
      ring

/-- The SOURCE full-retention bank's objective summability and TVC
follow from a uniform pathwise equity growth estimate and the
economically interpretable survival-adjusted factor strictly below
one. No separate assumption on the normalization of Markov/payment
probabilities is used. -/
theorem source_full_retention_analytic_conditions_of_pathwise_growth
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (C gross : ℝ)
    (hC : 0 ≤ C) (hgross : 0 ≤ gross)
    (hsurvive : 0 ≤ 1 - P.bankExit)
    (hexit : P.bankExit < 1)
    (hcontract : (1 - P.bankExit) * gross < 1)
    (hpathNonneg : ∀ n (future : Fin n → S)
      (payments : Fin n → P.paymentSupport),
      0 ≤ bankCumulativeSDFAt P X t h future *
        (sourceFullRetentionCandidate P X t h).equity n future payments)
    (hpathUpper : ∀ n (future : Fin n → S)
      (payments : Fin n → P.paymentSupport),
      bankCumulativeSDFAt P X t h future *
        (sourceFullRetentionCandidate P X t h).equity n future payments ≤
          C * gross ^ n) :
    BankContinuationObjectiveWellDefinedAt P X t h
      (sourceFullRetentionCandidate P X t h) ∧
    BankContinuationTerminalConditionAt P X t h
      (sourceFullRetentionCandidate P X t h) := by
  have hnonneg := source_surviving_value_nonneg_of_pathwise_nonneg
    P X t h hsurvive hpathNonneg
  have hupper := source_expected_surviving_equity_geometric_upper_bound
    P X t h C gross hsurvive hpathUpper
  have habs : ∀ n,
      |bankSurvivingValueTermAt P X t h
        (sourceFullRetentionCandidate P X t h) n| ≤
          C * ((1 - P.bankExit) * gross) ^ n := by
    intro n
    simpa only [abs_of_nonneg (hnonneg n)] using hupper n
  exact source_full_retention_objective_and_terminal_of_surviving_envelope
    P X t h C ((1 - P.bankExit) * gross)
    hC (mul_nonneg hsurvive hgross) hcontract hexit habs

#print axioms source_surviving_value_nonneg_of_pathwise_nonneg
#print axioms source_expected_surviving_equity_geometric_upper_bound
#print axioms source_full_retention_analytic_conditions_of_pathwise_growth

end ProposedBankExpectedSurvivorEnvelope
end Ventura26LiquidityAllocation

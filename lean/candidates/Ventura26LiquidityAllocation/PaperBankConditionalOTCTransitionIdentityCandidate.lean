import Ventura26LiquidityAllocation.PaperBankConditionalExpectedContractionCandidate

/-!
# EXACT SOURCE conditional OTC mass transition

The mathematical obstacle is the chronology of finite histories:
Fin (n+1) -> S and Fin (n+1) -> paymentSupport index paths with
the *newest* state/payment at index zero. Reindex those finite sums
by Fin.cons, use the source one-step cumulative SDF/equity identity,
and factor the conditional Markov/payment expectation.

The source detailed OTC return and household consumption ratio remain
inside sourceDiscountedEquityGrowthFactor. No stochastic independence
between historical bank equity and OTC returns is assumed.

The derived mass equation closes the earlier explicit hnext premise.
The accompanying TVC implication remains conditional on:
- log household utility (risk aversion one);
- strictly positive individual and aggregate equity, consumption on
  all histories quantified here (stronger than supported-only);
- the SOURCE conditional OTC return upper bound and
  survival-adjusted contraction ratio below one.

These positivity and return enclosures must be established for a
specific economy; this module does NOT establish BankOptimal,
general-equilibrium existence, nor policy IRFs.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedBankConditionalOTCTransitionIdentity

open ProposedBankConditionalExpectedContraction
open ProposedBankConditionalOTCMean
open ProposedBankPathwiseOTCDiscountedReturn
open ProposedBankPathwiseGrowthInduction
open ProposedBankConcreteFullRetentionOptimality

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Reindex finite function histories by their newest element.
This is the chronological complement of SOURCE sum_pi_snoc. -/
theorem sum_pi_cons
    {A : Type*} [Fintype A] {n : ℕ}
    (f : (Fin (n + 1) → A) → ℝ) :
    (∑ q, f q) = ∑ a : A, ∑ q : Fin n → A, f (Fin.cons a q) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) ↦ A)).sum_comp f,
    Fintype.sum_prod_type]
  rfl

/-- Literal source Markov path weight when appending the newest
aggregate state, expressed with the SOURCE continued history. -/
theorem source_transition_weight_child
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t)
    (n : ℕ) (future : Fin n → S) (s : S) :
    continuationTransitionWeight P.tree (currentState h) (n + 1)
        (childFutureHistory future s) =
      continuationTransitionWeight P.tree (currentState h) n future *
        P.tree.transition
          (currentState (continuationHistory h future)) s := by
  rw [currentState_continuationHistory h future]
  rfl

/-- A newly realized supported payment shock enters the source
payment history with its primitive probability. -/
theorem source_payment_weight_child
    (P : Primitives S) {n : ℕ}
    (payments : Fin n → P.paymentSupport)
    (omega : P.paymentSupport) :
    continuationPaymentWeight P (childPaymentHistory payments omega) =
      continuationPaymentWeight P payments * P.paymentProbability omega := by
  unfold continuationPaymentWeight
  rw [Fin.prod_univ_succ]
  change P.paymentProbability omega *
      (∏ j : Fin n, P.paymentProbability (payments j)) =
    (∏ j : Fin n, P.paymentProbability (payments j)) *
      P.paymentProbability omega
  ring

/-- Pure finite-sum law of conditional expectation. No probability
independence is used: W can be correlated arbitrarily with the
conditioning variable A, while K depends on that history A. -/
theorem weighted_finite_conditional_factorization
    {A B C D : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (W : A → B → ℝ) (K : A → C → D → ℝ) :
    (∑ c : C, ∑ a : A, ∑ d : D, ∑ b : B,
      W a b * K a c d) =
      ∑ a : A, ∑ b : B, W a b *
        (∑ c : C, ∑ d : D, K a c d) := by
  classical
  calc
    (∑ c : C, ∑ a : A, ∑ d : D, ∑ b : B,
        W a b * K a c d) =
      ∑ a : A, ∑ c : C, ∑ d : D, ∑ b : B,
        W a b * K a c d := Finset.sum_comm
    _ = ∑ a : A, ∑ c : C, ∑ b : B, ∑ d : D,
        W a b * K a c d := by
      apply Finset.sum_congr rfl
      intro a _ha
      apply Finset.sum_congr rfl
      intro c _hc
      exact Finset.sum_comm
    _ = ∑ a : A, ∑ b : B, ∑ c : C, ∑ d : D,
        W a b * K a c d := by
      apply Finset.sum_congr rfl
      intro a _ha
      exact Finset.sum_comm
    _ = ∑ a : A, ∑ b : B, W a b *
        (∑ c : C, ∑ d : D, K a c d) := by
      apply Finset.sum_congr rfl
      intro a _ha
      apply Finset.sum_congr rfl
      intro b _hb
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _hc
      rw [Finset.mul_sum]

/-- The EXACT SOURCE mass transition equals past discounted bank
equity weighted by the conditional Markov/payment OTC growth factor.
This discharges the entire earlier hnext obligation using source
primitives and the already certified individual wealth evolution. -/
theorem source_discounted_bank_mass_next_eq_conditional_growth
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t)
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
      0 < X.bankEquity (t + n) (continuationHistory h future)) :
    ∀ n,
      sourceDiscountedBankEquityMassAt P X t h (n + 1) =
        ∑ future : Fin n → S, ∑ payments : Fin n → P.paymentSupport,
          ((continuationTransitionWeight P.tree (currentState h) n future *
            continuationPaymentWeight P payments) *
            (bankCumulativeSDFAt P X t h future *
              (sourceFullRetentionCandidate P X t h).equity n future payments)) *
              sourceConditionalOTCGrowthFactor P X t h n future := by
  classical
  intro n
  let W : (Fin n → S) → (Fin n → P.paymentSupport) → ℝ :=
    fun future payments =>
      (continuationTransitionWeight P.tree (currentState h) n future *
        continuationPaymentWeight P payments) *
        (bankCumulativeSDFAt P X t h future *
          (sourceFullRetentionCandidate P X t h).equity n future payments)
  let K : (Fin n → S) → S → P.paymentSupport → ℝ :=
    fun future s omega =>
      (P.tree.transition (currentState (continuationHistory h future)) s *
        P.paymentProbability omega) *
        sourceDiscountedEquityGrowthFactor P X t h n future s omega
  unfold sourceDiscountedBankEquityMassAt
  calc
    (∑ newFuture : Fin (n + 1) → S,
      ∑ newPayments : Fin (n + 1) → P.paymentSupport,
        (continuationTransitionWeight P.tree (currentState h) (n + 1)
            newFuture * continuationPaymentWeight P newPayments) *
          (bankCumulativeSDFAt P X t h newFuture *
            (sourceFullRetentionCandidate P X t h).equity
              (n + 1) newFuture newPayments)) =
      ∑ s : S, ∑ future : Fin n → S,
        ∑ omega : P.paymentSupport,
        ∑ payments : Fin n → P.paymentSupport,
          W future payments * K future s omega := by
      rw [sum_pi_cons]
      apply Finset.sum_congr rfl
      intro s _hs
      apply Finset.sum_congr rfl
      intro future _hf
      rw [sum_pi_cons]
      apply Finset.sum_congr rfl
      intro omega _ho
      apply Finset.sum_congr rfl
      intro payments _hp
      have hsource := fullRetentionContinuation_cumulative_joint_child
        P X t h n future payments s omega hrisk
        (hconsumption n future)
        (hchildConsumption n future s).ne'
        (hindividual n future payments)
        (haggregate n future)
      rw [source_transition_weight_child P X t h n future s]
      rw [source_payment_weight_child P payments omega]
      rw [show
        bankCumulativeSDFAt P X t h (childFutureHistory future s) *
          (sourceFullRetentionCandidate P X t h).equity (n + 1)
            (childFutureHistory future s)
            (childPaymentHistory payments omega) =
        (bankCumulativeSDFAt P X t h future *
          (sourceFullRetentionCandidate P X t h).equity n future payments) *
          sourceDiscountedEquityGrowthFactor P X t h n future s omega by
        simpa only [sourceFullRetentionCandidate,
          sourceDiscountedEquityGrowthFactor] using hsource]
      dsimp [W, K]
      ring
    _ = ∑ future : Fin n → S,
          ∑ payments : Fin n → P.paymentSupport,
          W future payments * (∑ s : S,
            ∑ omega : P.paymentSupport, K future s omega) :=
      weighted_finite_conditional_factorization W K
    _ = ∑ future : Fin n → S,
        ∑ payments : Fin n → P.paymentSupport,
          ((continuationTransitionWeight P.tree (currentState h) n future *
            continuationPaymentWeight P payments) *
            (bankCumulativeSDFAt P X t h future *
              (sourceFullRetentionCandidate P X t h).equity n future payments)) *
            sourceConditionalOTCGrowthFactor P X t h n future := by
      dsimp [W, K, sourceConditionalOTCGrowthFactor]
      rfl

/-- SOURCE owner-payoff summability and TVC under a bounded conditional
expected OTC return, with the exact mass transition now DERIVED
rather than accepted as a hypothesis. No independence or identical
past equity across banks is needed. -/
theorem source_full_retention_tvc_of_source_conditional_otc_growth
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
    (hrisk : P.workerRiskAversion = 1)
    (hinitial : 0 < X.workerConsumption t h)
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
    (hconditional : ∀ n (future : Fin n → S),
      sourceConditionalOTCGrowthFactor P X t h n future ≤ grossBound) :
    BankContinuationObjectiveWellDefinedAt P X t h
      (sourceFullRetentionCandidate P X t h) ∧
    BankContinuationTerminalConditionAt P X t h
      (sourceFullRetentionCandidate P X t h) := by
  have hnonneg : ∀ n (future : Fin n → S)
      (payments : Fin n → P.paymentSupport),
      0 ≤ bankCumulativeSDFAt P X t h future *
        (sourceFullRetentionCandidate P X t h).equity n future payments := by
    intro n future payments
    exact (mul_pos
      (source_bank_cumulative_sdf_pos P X t h n future
        hinitial (hconsumption n future))
      (hindividual n future payments)).le
  have hnext := source_discounted_bank_mass_next_eq_conditional_growth
    P X t h hrisk hconsumption hchildConsumption hindividual haggregate
  exact source_full_retention_tvc_of_conditional_otc_return
    P X t h C grossBound hC hgross hsurvive hexit
    hcontraction hbase hnonneg hconditional hnext

#print axioms sum_pi_cons
#print axioms source_transition_weight_child
#print axioms source_payment_weight_child
#print axioms weighted_finite_conditional_factorization
#print axioms source_discounted_bank_mass_next_eq_conditional_growth
#print axioms source_full_retention_tvc_of_source_conditional_otc_growth

end ProposedBankConditionalOTCTransitionIdentity
end Ventura26LiquidityAllocation

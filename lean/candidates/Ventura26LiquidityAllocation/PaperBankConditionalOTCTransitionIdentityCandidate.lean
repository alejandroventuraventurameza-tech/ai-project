import Ventura26LiquidityAllocation.PaperBankConditionalExpectedContractionCandidate
import Ventura26LiquidityAllocation.PaperBankZeroEquityAbsorptionCandidate

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
      have htrans := source_transition_weight_child P X t h n future s
      change continuationTransitionWeight P.tree (currentState h) (n + 1)
        (Fin.cons s future) =
        continuationTransitionWeight P.tree (currentState h) n future *
          P.tree.transition
            (currentState (continuationHistory h future)) s at htrans
      rw [htrans]
      have hpayment := source_payment_weight_child P payments omega
      change continuationPaymentWeight P (Fin.cons omega payments) =
        continuationPaymentWeight P payments * P.paymentProbability omega
        at hpayment
      rw [hpayment]
      have hsource' :
        bankCumulativeSDFAt P X t h (Fin.cons s future) *
          (sourceFullRetentionCandidate P X t h).equity (n + 1)
            (Fin.cons s future) (Fin.cons omega payments) =
        (bankCumulativeSDFAt P X t h future *
          (sourceFullRetentionCandidate P X t h).equity n future payments) *
          sourceDiscountedEquityGrowthFactor P X t h n future s omega := by
        simpa only [sourceFullRetentionCandidate,
          sourceDiscountedEquityGrowthFactor,
          childFutureHistory, childPaymentHistory] using hsource
      rw [hsource']
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


/-!
## Finite support reduction (new proof obligation toward zero-equity boundary)

The next two purely finite-sum results do NOT remove source positivity
assumptions from the exact OTC transition. They show that zero-probability
or zero-equity parent nodes contribute no mass and that a conditional
growth enclosure is only needed at active nodes. To apply them to the
source transition, a zero-equity absorption result for source full
retention, and a child-mass identity on active nodes, are still needed.
-/

/-- Histories with zero probability or zero bank equity have exactly
zero contribution to a finite discounted mass. This is an algebraic
support reduction, not a new economic assumption. -/
theorem weighted_sum_eq_active_support
    {A : Type*} [Fintype A]
    (p equity sdf : A → ℝ) :
    (∑ a : A, p a * (equity a * sdf a)) =
      (Finset.univ.filter (fun a => p a ≠ 0 ∧ equity a ≠ 0)).sum
        (fun a => p a * (equity a * sdf a)) := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _ha
  by_cases hp : p a = 0
  · simp [hp]
  by_cases he : equity a = 0
  · simp [he]
  · simp [hp, he]

/-- A conditional bound on *active* histories suffices for a weighted
expectation inequality. No return bound is required at zero-mass nodes. -/
theorem weighted_conditional_bound_on_active_support
    {A : Type*} [Fintype A]
    (p equity growth : A → ℝ) (grossBound : ℝ)
    (hp : ∀ a, 0 ≤ p a)
    (he : ∀ a, 0 ≤ equity a)
    (hg : ∀ a, p a ≠ 0 → equity a ≠ 0 →
      growth a ≤ grossBound) :
    (∑ a : A, (p a * equity a) * growth a) ≤
      grossBound * (∑ a : A, p a * equity a) := by
  classical
  calc
    (∑ a : A, (p a * equity a) * growth a) ≤
        ∑ a : A, (p a * equity a) * grossBound := by
      apply Finset.sum_le_sum
      intro a _ha
      by_cases hzeroP : p a = 0
      · simp [hzeroP]
      by_cases hzeroE : equity a = 0
      · simp [hzeroE]
      · exact mul_le_mul_of_nonneg_left
          (hg a hzeroP hzeroE) (mul_nonneg (hp a) (he a))
    _ = grossBound * (∑ a : A, p a * equity a) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _ha
      ring

#print axioms weighted_sum_eq_active_support
#print axioms weighted_conditional_bound_on_active_support


/-!
## Conditional zero-equity boundary

This algebraic lemma is intended to be instantiated using the literal
`zeroBoundary` clause of `BankContinuationFeasibleAt`, *after*
showing that that clause provides the stated upper bound for supported
children. It is NOT itself a proof of that source instantiation.
-/

/-- If source feasibility bounds next equity by a finite multiple of
current equity, and next equity is nonnegative, zero current equity
is absorbing. The economic upper bound is an explicit premise. -/
theorem zero_equity_absorbing_of_scaled_upper_bound
    (parent child factor : ℝ)
    (hparent : parent = 0)
    (hchild : 0 ≤ child)
    (hupper : child ≤ factor * parent) :
    child = 0 := by
  apply le_antisymm
  · simpa [hparent] using hupper
  · exact hchild

/-- A supported child of zero equity has zero weighted discounted
contribution, provided its own nonnegative-equity absorbing condition
has been established. No assumption about the child SDF is needed. -/
theorem zero_parent_child_discounted_contribution
    (parent child factor pathProbability childSDF : ℝ)
    (hparent : parent = 0)
    (hchild : 0 ≤ child)
    (hupper : child ≤ factor * parent) :
    pathProbability * (childSDF * child) = 0 := by
  have heq := zero_equity_absorbing_of_scaled_upper_bound
    parent child factor hparent hchild hupper
  simp [heq]

#print axioms zero_equity_absorbing_of_scaled_upper_bound
#print axioms zero_parent_child_discounted_contribution


/-- Once the source-equity transition has a supported-child scaled
upper bound, zero equity is absorbing at every subsequent step along
that supported path. This is an induction theorem for a nonnegative
sequence; source instantiation remains a separate obligation. -/
theorem zero_equity_absorbing_along_supported_path
    (equity factor : ℕ → ℝ)
    (hinitial : equity 0 = 0)
    (hnonneg : ∀ n, 0 ≤ equity (n + 1))
    (hupper : ∀ n, equity (n + 1) ≤ factor n * equity n) :
    ∀ n, equity n = 0 := by
  intro n
  induction n with
  | zero => exact hinitial
  | succ n ih =>
      exact zero_equity_absorbing_of_scaled_upper_bound
        (equity n) (equity (n + 1)) (factor n)
        ih (hnonneg n) (hupper n)

#print axioms zero_equity_absorbing_along_supported_path


/-!
## Direct source boundary: no artificial scaled-upper-bound premise

The source already proves `source_feasible_zero_equity_is_absorbing`
using the literal `zeroBoundary` feasibility clause and detailed OTC
portfolio homogeneity. The following theorem specializes that source
result to the named full-retention policy. Its sole feasibility premise
still has to be obtained for the candidate and economic allocation.
-/

/-- For the literal source full-retention candidate, zero individual
bank equity remains zero at each supported successor, assuming the
named candidate is SOURCE-feasible. No positive-equity ratio or
additional multiplicative growth enclosure is used here. -/
theorem source_full_retention_supported_zero_equity_absorbing
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t)
    (hfeasible : BankContinuationFeasibleAt P X t h
      (X.bankEquity t h) (sourceFullRetentionCandidate P X t h))
    (n : ℕ) (future : Fin n → S)
    (payments : Fin n → P.paymentSupport)
    (hpath : FuturePathSupported P.tree (currentState h) n future)
    (hzero : (sourceFullRetentionCandidate P X t h).equity
      n future payments = 0)
    (s : S) (omega : P.paymentSupport)
    (htrans : 0 < P.tree.transition
      (currentState (continuationHistory h future)) s) :
    (sourceFullRetentionCandidate P X t h).equity (n + 1)
      (childFutureHistory future s)
      (childPaymentHistory payments omega) = 0 := by
  exact ProposedBankZeroEquityAbsorption.source_feasible_zero_equity_is_absorbing
    P X t h (X.bankEquity t h)
    (sourceFullRetentionCandidate P X t h) hfeasible
    n future payments hpath hzero s omega htrans

#print axioms source_full_retention_supported_zero_equity_absorbing


/-- The preceding source-boundary absorption is obtained directly from
the ORIGINAL equilibrium bank-feasibility and positivity premises.
This removes the separately assumed continuation-feasibility witness,
but it does not prove that an equilibrium satisfying these premises
exists. -/
theorem source_full_retention_zero_equity_absorbing_of_bank_feasible
    (P : Primitives S) (I : InheritedState) (X : Allocation S)
    (t : ℕ) (h : History S t)
    (hh : FirmHistoryAdmissible P t h)
    (hbankFeasible : BankFeasible P I X (fullRetentionCommonBankPlan P X))
    (hreserveRate : ∀ k H, FirmHistoryAdmissible P k H →
      0 < X.reserveRate k H)
    (htightness : ∀ k H, FirmHistoryAdmissible P k H →
      0 < X.bankTightness k H)
    (n : ℕ) (future : Fin n → S)
    (payments : Fin n → P.paymentSupport)
    (hpath : FuturePathSupported P.tree (currentState h) n future)
    (hzero : (sourceFullRetentionCandidate P X t h).equity
      n future payments = 0)
    (s : S) (omega : P.paymentSupport)
    (htrans : 0 < P.tree.transition
      (currentState (continuationHistory h future)) s) :
    (sourceFullRetentionCandidate P X t h).equity (n + 1)
      (childFutureHistory future s)
      (childPaymentHistory payments omega) = 0 := by
  have hfeasible := source_full_retention_candidate_feasible
    P I X t h hh hbankFeasible hreserveRate htightness
  exact source_full_retention_supported_zero_equity_absorbing
    P X t h hfeasible n future payments hpath hzero s omega htrans

#print axioms source_full_retention_zero_equity_absorbing_of_bank_feasible


/-!
## Finite parent-child mass bridge on active support

These two statements isolate the remaining aggregation obligation.
In particular, a zero parent only needs a zero *weighted* child
contribution; it need not have a well-defined return ratio.
To instantiate them for SOURCE OTC, the child identity must be
derived using supported transitions and the source zero-equity
absorption theorem. No economic result is promoted here.
-/

/-- A parent-child mass identity only needs to be checked separately
at active and zero-equity parents. This is a finite-sum statement,
not an assertion that source equilibrium supplies the premises. -/
theorem parent_child_mass_eq_of_active_and_zero
    {A B : Type*} [Fintype A] [Fintype B]
    (weight equity growth : A → ℝ) (childMass : A → B → ℝ)
    (hactive : ∀ a, equity a ≠ 0 →
      (∑ b : B, childMass a b) =
        (weight a * equity a) * growth a)
    (hzero : ∀ a, equity a = 0 →
      ∀ b : B, childMass a b = 0) :
    (∑ a : A, ∑ b : B, childMass a b) =
      ∑ a : A, (weight a * equity a) * growth a := by
  classical
  apply Finset.sum_congr rfl
  intro a _ha
  by_cases he : equity a = 0
  · simp [hzero a he, he]
  · exact hactive a he

/-- Under nonnegative parent mass and an active-only bound on
conditional growth, the full child mass is bounded by the parent mass.
This avoids any return-ratio hypothesis at the zero-equity boundary. -/
theorem parent_child_mass_le_of_supported_growth
    {A B : Type*} [Fintype A] [Fintype B]
    (weight equity growth : A → ℝ) (childMass : A → B → ℝ)
    (grossBound : ℝ)
    (hw : ∀ a, 0 ≤ weight a)
    (he : ∀ a, 0 ≤ equity a)
    (hactive : ∀ a, equity a ≠ 0 →
      (∑ b : B, childMass a b) =
        (weight a * equity a) * growth a)
    (hzero : ∀ a, equity a = 0 →
      ∀ b : B, childMass a b = 0)
    (hbound : ∀ a, weight a ≠ 0 → equity a ≠ 0 →
      growth a ≤ grossBound) :
    (∑ a : A, ∑ b : B, childMass a b) ≤
      grossBound * (∑ a : A, weight a * equity a) := by
  rw [parent_child_mass_eq_of_active_and_zero
    weight equity growth childMass hactive hzero]
  exact weighted_conditional_bound_on_active_support
    weight equity growth grossBound hw he hbound

#print axioms parent_child_mass_eq_of_active_and_zero
#print axioms parent_child_mass_le_of_supported_growth


/-!
## Exact source weighted child contribution at a zero-equity parent

The Markov transition is allowed to vanish. On a zero-probability edge,
the weighted term vanishes algebraically; on a positive edge, the
SOURCE absorption theorem forces child equity to zero. This avoids
assuming positivity on unsupported successors or dividing by equity.
-/

/-- Every probability-weighted one-step child contribution vanishes
when its parent has zero equity and the source candidate is feasible.
No assumption about the payment probability or child SDF is needed. -/
theorem source_full_retention_zero_parent_weighted_child_eq_zero
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t)
    (hfeasible : BankContinuationFeasibleAt P X t h
      (X.bankEquity t h) (sourceFullRetentionCandidate P X t h))
    (n : ℕ) (future : Fin n → S)
    (payments : Fin n → P.paymentSupport)
    (hpath : FuturePathSupported P.tree (currentState h) n future)
    (hzero : (sourceFullRetentionCandidate P X t h).equity
      n future payments = 0)
    (s : S) (omega : P.paymentSupport) :
    (P.tree.transition
      (currentState (continuationHistory h future)) s *
        P.paymentProbability omega) *
      (bankCumulativeSDFAt P X t h (childFutureHistory future s) *
        (sourceFullRetentionCandidate P X t h).equity (n + 1)
          (childFutureHistory future s)
          (childPaymentHistory payments omega)) = 0 := by
  by_cases ht : P.tree.transition
      (currentState (continuationHistory h future)) s = 0
  · simp [ht]
  · have hpositive : 0 < P.tree.transition
        (currentState (continuationHistory h future)) s :=
      lt_of_le_of_ne (P.tree.transition_nonneg _ _) (Ne.symm ht)
    have heq := source_full_retention_supported_zero_equity_absorbing
      P X t h hfeasible n future payments hpath hzero s omega hpositive
    simp [heq]

/-- The sum of all one-step weighted child contributions from a
supported parent with zero source bank equity is exactly zero. -/
theorem source_full_retention_zero_parent_weighted_children_sum_eq_zero
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t)
    (hfeasible : BankContinuationFeasibleAt P X t h
      (X.bankEquity t h) (sourceFullRetentionCandidate P X t h))
    (n : ℕ) (future : Fin n → S)
    (payments : Fin n → P.paymentSupport)
    (hpath : FuturePathSupported P.tree (currentState h) n future)
    (hzero : (sourceFullRetentionCandidate P X t h).equity
      n future payments = 0) :
    (∑ s : S, ∑ omega : P.paymentSupport,
      (P.tree.transition
        (currentState (continuationHistory h future)) s *
          P.paymentProbability omega) *
        (bankCumulativeSDFAt P X t h (childFutureHistory future s) *
          (sourceFullRetentionCandidate P X t h).equity (n + 1)
            (childFutureHistory future s)
            (childPaymentHistory payments omega))) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro s _hs
  apply Finset.sum_eq_zero
  intro omega _ho
  exact source_full_retention_zero_parent_weighted_child_eq_zero
    P X t h hfeasible n future payments hpath hzero s omega

#print axioms source_full_retention_zero_parent_weighted_child_eq_zero
#print axioms source_full_retention_zero_parent_weighted_children_sum_eq_zero


/-!
## Source active-parent OTC child identity, before stochastic aggregation

This is a literal one-child identity for positive individual and
aggregate bank equity. The zero-parent theorem immediately above
handles the complementary solvency boundary. Both pieces still need
a full supported-history sum and a bound on actual OTC conditional
returns before an unrestricted terminal result can be claimed.
-/

/-- At a bank history with positive individual and aggregate equity,
the source discounted successor equity equals its parent's
discounted equity times the exact OTC growth factor. -/
theorem source_full_retention_active_parent_child_identity
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t)
    (n : ℕ) (future : Fin n → S)
    (payments : Fin n → P.paymentSupport)
    (s : S) (omega : P.paymentSupport)
    (hrisk : P.workerRiskAversion = 1)
    (hconsumption : 0 <
      X.workerConsumption (t + n) (continuationHistory h future))
    (hchildConsumption : 0 <
      X.workerConsumption (t + n + 1)
        (childHistory (continuationHistory h future) s))
    (hindividual : 0 <
      (sourceFullRetentionCandidate P X t h).equity n future payments)
    (haggregate : 0 <
      X.bankEquity (t + n) (continuationHistory h future)) :
    (P.tree.transition
      (currentState (continuationHistory h future)) s *
        P.paymentProbability omega) *
      (bankCumulativeSDFAt P X t h (childFutureHistory future s) *
        (sourceFullRetentionCandidate P X t h).equity (n + 1)
          (childFutureHistory future s)
          (childPaymentHistory payments omega)) =
      (P.tree.transition
        (currentState (continuationHistory h future)) s *
          P.paymentProbability omega) *
        ((bankCumulativeSDFAt P X t h future *
          (sourceFullRetentionCandidate P X t h).equity
            n future payments) *
          sourceDiscountedEquityGrowthFactor P X t h n future s omega) := by
  have hsource := fullRetentionContinuation_cumulative_joint_child
    P X t h n future payments s omega hrisk
    hconsumption hchildConsumption.ne' hindividual haggregate
  have hsource' :
      bankCumulativeSDFAt P X t h (childFutureHistory future s) *
        (sourceFullRetentionCandidate P X t h).equity (n + 1)
          (childFutureHistory future s)
          (childPaymentHistory payments omega) =
      (bankCumulativeSDFAt P X t h future *
        (sourceFullRetentionCandidate P X t h).equity
          n future payments) *
        sourceDiscountedEquityGrowthFactor P X t h n future s omega := by
    simpa only [sourceFullRetentionCandidate,
      sourceDiscountedEquityGrowthFactor] using hsource
  rw [hsource']

#print axioms source_full_retention_active_parent_child_identity


/-- Unified SOURCE one-child identity with only NONNEGATIVE
individual bank equity. A supported zero-equity parent is absorbing;
an active parent uses the literal source OTC discounted-return lemma.
The aggregate bank equity is required positive only at active parents.
This is not yet the full path-summed stochastic mass identity. -/
theorem source_full_retention_nonnegative_parent_child_identity
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t)
    (hfeasible : BankContinuationFeasibleAt P X t h
      (X.bankEquity t h) (sourceFullRetentionCandidate P X t h))
    (n : ℕ) (future : Fin n → S)
    (payments : Fin n → P.paymentSupport)
    (hpath : FuturePathSupported P.tree (currentState h) n future)
    (s : S) (omega : P.paymentSupport)
    (hrisk : P.workerRiskAversion = 1)
    (hconsumption : 0 <
      X.workerConsumption (t + n) (continuationHistory h future))
    (hchildConsumption : 0 <
      X.workerConsumption (t + n + 1)
        (childHistory (continuationHistory h future) s))
    (hnonneg : 0 ≤
      (sourceFullRetentionCandidate P X t h).equity n future payments)
    (haggregate : 0 <
      X.bankEquity (t + n) (continuationHistory h future)) :
    (P.tree.transition
      (currentState (continuationHistory h future)) s *
        P.paymentProbability omega) *
      (bankCumulativeSDFAt P X t h (childFutureHistory future s) *
        (sourceFullRetentionCandidate P X t h).equity (n + 1)
          (childFutureHistory future s)
          (childPaymentHistory payments omega)) =
      (P.tree.transition
        (currentState (continuationHistory h future)) s *
          P.paymentProbability omega) *
        ((bankCumulativeSDFAt P X t h future *
          (sourceFullRetentionCandidate P X t h).equity
            n future payments) *
          sourceDiscountedEquityGrowthFactor P X t h n future s omega) := by
  by_cases hzero :
      (sourceFullRetentionCandidate P X t h).equity n future payments = 0
  · have hleft := source_full_retention_zero_parent_weighted_child_eq_zero
      P X t h hfeasible n future payments hpath hzero s omega
    rw [hleft, hzero]
    simp
  · exact source_full_retention_active_parent_child_identity
      P X t h n future payments s omega
      hrisk hconsumption hchildConsumption
      (lt_of_le_of_ne hnonneg (Ne.symm hzero)) haggregate

#print axioms source_full_retention_nonnegative_parent_child_identity


/-- Exact SOURCE conditional aggregation of all one-step children at
a SUPPORTED parent, allowing individual equity to equal zero.
The only growth factor is the source's literal OTC conditional mean;
this is a local identity and does not yet sum over all parent paths. -/
theorem source_full_retention_nonnegative_parent_conditional_child_sum
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t)
    (hfeasible : BankContinuationFeasibleAt P X t h
      (X.bankEquity t h) (sourceFullRetentionCandidate P X t h))
    (n : ℕ) (future : Fin n → S)
    (payments : Fin n → P.paymentSupport)
    (hpath : FuturePathSupported P.tree (currentState h) n future)
    (hrisk : P.workerRiskAversion = 1)
    (hconsumption : 0 <
      X.workerConsumption (t + n) (continuationHistory h future))
    (hchildConsumption : ∀ s, 0 <
      X.workerConsumption (t + n + 1)
        (childHistory (continuationHistory h future) s))
    (haggregate : 0 <
      X.bankEquity (t + n) (continuationHistory h future)) :
    (∑ s : S, ∑ omega : P.paymentSupport,
      (P.tree.transition
        (currentState (continuationHistory h future)) s *
          P.paymentProbability omega) *
        (bankCumulativeSDFAt P X t h (childFutureHistory future s) *
          (sourceFullRetentionCandidate P X t h).equity (n + 1)
            (childFutureHistory future s)
            (childPaymentHistory payments omega))) =
      (bankCumulativeSDFAt P X t h future *
        (sourceFullRetentionCandidate P X t h).equity n future payments) *
          sourceConditionalOTCGrowthFactor P X t h n future := by
  classical
  have hn := (hfeasible.2 n future payments hpath).1
  have hterm : ∀ s : S, ∀ omega : P.paymentSupport,
      (P.tree.transition
        (currentState (continuationHistory h future)) s *
          P.paymentProbability omega) *
        (bankCumulativeSDFAt P X t h (childFutureHistory future s) *
          (sourceFullRetentionCandidate P X t h).equity (n + 1)
            (childFutureHistory future s)
            (childPaymentHistory payments omega)) =
      (bankCumulativeSDFAt P X t h future *
        (sourceFullRetentionCandidate P X t h).equity n future payments) *
          (P.tree.transition
            (currentState (continuationHistory h future)) s *
              P.paymentProbability omega *
              sourceDiscountedEquityGrowthFactor P X t h n future s omega) := by
    intro s omega
    have hidentity := source_full_retention_nonnegative_parent_child_identity
      P X t h hfeasible n future payments hpath s omega
      hrisk hconsumption (hchildConsumption s) hn haggregate
    calc
      _ = (P.tree.transition
          (currentState (continuationHistory h future)) s *
            P.paymentProbability omega) *
          ((bankCumulativeSDFAt P X t h future *
            (sourceFullRetentionCandidate P X t h).equity n future payments) *
            sourceDiscountedEquityGrowthFactor P X t h n future s omega) :=
        hidentity
      _ = _ := by ring
  calc
    (∑ s : S, ∑ omega : P.paymentSupport,
      (P.tree.transition
        (currentState (continuationHistory h future)) s *
          P.paymentProbability omega) *
        (bankCumulativeSDFAt P X t h (childFutureHistory future s) *
          (sourceFullRetentionCandidate P X t h).equity (n + 1)
            (childFutureHistory future s)
            (childPaymentHistory payments omega))) =
      ∑ s : S, ∑ omega : P.paymentSupport,
        (bankCumulativeSDFAt P X t h future *
          (sourceFullRetentionCandidate P X t h).equity n future payments) *
          (P.tree.transition
            (currentState (continuationHistory h future)) s *
              P.paymentProbability omega *
              sourceDiscountedEquityGrowthFactor P X t h n future s omega) := by
        apply Finset.sum_congr rfl
        intro s _hs
        apply Finset.sum_congr rfl
        intro omega _ho
        exact hterm s omega
    _ = (bankCumulativeSDFAt P X t h future *
          (sourceFullRetentionCandidate P X t h).equity n future payments) *
          sourceConditionalOTCGrowthFactor P X t h n future := by
        unfold sourceConditionalOTCGrowthFactor
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _hs
        rw [Finset.mul_sum]

#print axioms source_full_retention_nonnegative_parent_conditional_child_sum


/-- A strictly positive SOURCE Markov path probability implies the
SOURCE feasibility support predicate. Hence a zero-probability path
can be discarded before invoking supported-path bank feasibility. -/
theorem positive_transition_weight_implies_supported
    (T : FiniteMarkovTree S) (start : S) :
    ∀ n (future : Fin n → S),
      0 < continuationTransitionWeight T start n future →
        FuturePathSupported T start n future := by
  intro n
  induction n with
  | zero =>
      intro future _hweight
      trivial
  | succ n ih =>
      intro future hweight
      let previous : Fin n → S := fun j => future j.succ
      let prior : S := if hn : n = 0 then start
        else previous ⟨0, Nat.pos_of_ne_zero hn⟩
      have hprod :
          0 < continuationTransitionWeight T start n previous *
            T.transition prior (future 0) := by
        simpa only [continuationTransitionWeight, previous, prior]
          using hweight
      have hpreviousNonzero :
          continuationTransitionWeight T start n previous ≠ 0 := by
        intro hzero
        simp [hzero] at hprod
      have htransitionNonzero :
          T.transition prior (future 0) ≠ 0 := by
        intro hzero
        simp [hzero] at hprod
      have hpreviousPos :
          0 < continuationTransitionWeight T start n previous :=
        lt_of_le_of_ne
          (ProposedBankContinuationPathProbabilityMass.source_aggregate_future_path_weight_nonneg
            T n start previous) (Ne.symm hpreviousNonzero)
      have htransitionPos : 0 < T.transition prior (future 0) :=
        lt_of_le_of_ne (T.transition_nonneg _ _) (Ne.symm htransitionNonzero)
      change FuturePathSupported T start n previous ∧
        0 < T.transition prior (future 0)
      exact ⟨ih previous hpreviousPos, htransitionPos⟩

#print axioms positive_transition_weight_implies_supported


/-- A SOURCE Markov parent with zero probability contributes nothing
to any weighted child-equity expression. This step never invokes
off-support banking feasibility or assumes positive consumption. -/
theorem source_zero_probability_parent_weighted_child
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t)
    (n : ℕ) (future : Fin n → S)
    (payments : Fin n → P.paymentSupport)
    (s : S) (omega : P.paymentSupport)
    (hzero : continuationTransitionWeight P.tree (currentState h)
      n future = 0) :
    (continuationTransitionWeight P.tree (currentState h) n future *
      continuationPaymentWeight P payments) *
        ((P.tree.transition
          (currentState (continuationHistory h future)) s *
            P.paymentProbability omega) *
          (bankCumulativeSDFAt P X t h (childFutureHistory future s) *
            (sourceFullRetentionCandidate P X t h).equity (n + 1)
              (childFutureHistory future s)
              (childPaymentHistory payments omega))) = 0 := by
  simp [hzero]

/-- Combine supported-history banking feasibility with zero-weight
elimination. At a positive-probability parent, nonnegative bank
equity follows from SOURCE feasibility and the one-child OTC identity
holds without requiring *individual* equity to be positive. At an
off-support parent, both weighted sides vanish. -/
theorem source_weighted_child_identity_without_offsupport_hypotheses
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t)
    (hfeasible : BankContinuationFeasibleAt P X t h
      (X.bankEquity t h) (sourceFullRetentionCandidate P X t h))
    (n : ℕ) (future : Fin n → S)
    (payments : Fin n → P.paymentSupport)
    (s : S) (omega : P.paymentSupport)
    (hrisk : P.workerRiskAversion = 1)
    (hconsumption : 0 <
      X.workerConsumption (t + n) (continuationHistory h future))
    (hchildConsumption : 0 <
      X.workerConsumption (t + n + 1)
        (childHistory (continuationHistory h future) s))
    (haggregate : 0 <
      X.bankEquity (t + n) (continuationHistory h future)) :
    (continuationTransitionWeight P.tree (currentState h) n future *
      continuationPaymentWeight P payments) *
      ((P.tree.transition
        (currentState (continuationHistory h future)) s *
          P.paymentProbability omega) *
        (bankCumulativeSDFAt P X t h (childFutureHistory future s) *
          (sourceFullRetentionCandidate P X t h).equity (n + 1)
            (childFutureHistory future s)
            (childPaymentHistory payments omega))) =
    (continuationTransitionWeight P.tree (currentState h) n future *
      continuationPaymentWeight P payments) *
      ((P.tree.transition
        (currentState (continuationHistory h future)) s *
          P.paymentProbability omega) *
        ((bankCumulativeSDFAt P X t h future *
          (sourceFullRetentionCandidate P X t h).equity n future payments) *
          sourceDiscountedEquityGrowthFactor P X t h n future s omega)) := by
  by_cases hzero : continuationTransitionWeight P.tree (currentState h)
      n future = 0
  · simp [hzero]
  · have hpositive : 0 <
        continuationTransitionWeight P.tree (currentState h) n future :=
      lt_of_le_of_ne
        (ProposedBankContinuationPathProbabilityMass.source_aggregate_future_path_weight_nonneg
          P.tree n (currentState h) future) (Ne.symm hzero)
    have hpath := positive_transition_weight_implies_supported
      P.tree (currentState h) n future hpositive
    have hnonneg :=
      (hfeasible.2 n future payments hpath).1
    have hchild := source_full_retention_nonnegative_parent_child_identity
      P X t h hfeasible n future payments hpath s omega
      hrisk hconsumption hchildConsumption hnonneg haggregate
    rw [hchild]

#print axioms source_zero_probability_parent_weighted_child
#print axioms source_weighted_child_identity_without_offsupport_hypotheses


/-- SOURCE finite mass transition using NONNEGATIVE individual equity
and supported-path feasibility. Unsupported Markov histories contribute
zero automatically. Consumption and aggregate bank equity remain
strictly positive on all histories for this intermediate bridge;
weakening these requirements to the supported subset is separate. -/
theorem source_discounted_bank_mass_next_of_nonnegative_equity
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t)
    (hfeasible : BankContinuationFeasibleAt P X t h
      (X.bankEquity t h) (sourceFullRetentionCandidate P X t h))
    (hrisk : P.workerRiskAversion = 1)
    (hconsumption : ∀ n (future : Fin n → S),
      0 < X.workerConsumption (t + n) (continuationHistory h future))
    (hchildConsumption : ∀ n (future : Fin n → S) s,
      0 < X.workerConsumption (t + n + 1)
        (childHistory (continuationHistory h future) s))
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
      have htrans := source_transition_weight_child P X t h n future s
      change continuationTransitionWeight P.tree (currentState h) (n + 1)
        (Fin.cons s future) =
        continuationTransitionWeight P.tree (currentState h) n future *
          P.tree.transition
            (currentState (continuationHistory h future)) s at htrans
      rw [htrans]
      have hpayment := source_payment_weight_child P payments omega
      change continuationPaymentWeight P (Fin.cons omega payments) =
        continuationPaymentWeight P payments * P.paymentProbability omega
        at hpayment
      rw [hpayment]
      have hweighted :=
        source_weighted_child_identity_without_offsupport_hypotheses
          P X t h hfeasible n future payments s omega
          hrisk (hconsumption n future)
          (hchildConsumption n future s) (haggregate n future)
      change (continuationTransitionWeight P.tree (currentState h) n future *
        P.tree.transition (currentState (continuationHistory h future)) s *
        (continuationPaymentWeight P payments * P.paymentProbability omega)) *
        (bankCumulativeSDFAt P X t h (Fin.cons s future) *
          (sourceFullRetentionCandidate P X t h).equity (n + 1)
            (Fin.cons s future) (Fin.cons omega payments)) =
        W future payments * K future s omega
      calc
        _ = (continuationTransitionWeight P.tree (currentState h) n future *
          continuationPaymentWeight P payments) *
          ((P.tree.transition
            (currentState (continuationHistory h future)) s *
            P.paymentProbability omega) *
            (bankCumulativeSDFAt P X t h (childFutureHistory future s) *
              (sourceFullRetentionCandidate P X t h).equity (n + 1)
                (childFutureHistory future s)
                (childPaymentHistory payments omega))) := by
            have hfuture :
                childFutureHistory future s = Fin.cons s future := rfl
            have hpayments :
                childPaymentHistory payments omega =
                  Fin.cons omega payments := rfl
            rw [hfuture, hpayments]
            ring
        _ = (continuationTransitionWeight P.tree (currentState h) n future *
          continuationPaymentWeight P payments) *
          ((P.tree.transition
            (currentState (continuationHistory h future)) s *
              P.paymentProbability omega) *
            ((bankCumulativeSDFAt P X t h future *
              (sourceFullRetentionCandidate P X t h).equity n future payments) *
              sourceDiscountedEquityGrowthFactor P X t h n future s omega)) :=
            hweighted
        _ = W future payments * K future s omega := by
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

#print axioms source_discounted_bank_mass_next_of_nonnegative_equity


/-- Source terminal condition for a nonnegative-equity full-retention
policy, using the newly derived source mass transition. Nonnegativity
of individual discounted equity is stated for all finite histories
here; replacing it with a merely weighted supported-path statement
is the next exact-support weakening. The OTC growth bound remains an
economic premise, not a derived equilibrium price restriction. -/
theorem source_full_retention_tvc_of_nonnegative_equity_mass_identity
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
    (hfeasible : BankContinuationFeasibleAt P X t h
      (X.bankEquity t h) (sourceFullRetentionCandidate P X t h))
    (hrisk : P.workerRiskAversion = 1)
    (hconsumption : ∀ n (future : Fin n → S),
      0 < X.workerConsumption (t + n) (continuationHistory h future))
    (hchildConsumption : ∀ n (future : Fin n → S) s,
      0 < X.workerConsumption (t + n + 1)
        (childHistory (continuationHistory h future) s))
    (haggregate : ∀ n (future : Fin n → S),
      0 < X.bankEquity (t + n) (continuationHistory h future))
    (hnonneg : ∀ n (future : Fin n → S)
      (payments : Fin n → P.paymentSupport),
      0 ≤ bankCumulativeSDFAt P X t h future *
        (sourceFullRetentionCandidate P X t h).equity n future payments)
    (hconditional : ∀ n (future : Fin n → S),
      sourceConditionalOTCGrowthFactor P X t h n future ≤ grossBound) :
    BankContinuationObjectiveWellDefinedAt P X t h
      (sourceFullRetentionCandidate P X t h) ∧
    BankContinuationTerminalConditionAt P X t h
      (sourceFullRetentionCandidate P X t h) := by
  have hnext := source_discounted_bank_mass_next_of_nonnegative_equity
    P X t h hfeasible hrisk hconsumption hchildConsumption haggregate
  exact source_full_retention_tvc_of_conditional_otc_return
    P X t h C grossBound hC hgross hsurvive hexit
    hcontraction hbase hnonneg hconditional hnext

#print axioms source_full_retention_tvc_of_nonnegative_equity_mass_identity


/-- Nonnegative SOURCE discounted bank mass on every probability-weighted
parent, requiring consumption positivity only on supported aggregate
histories. At off-support histories the joint path weight is zero,
so no source feasibility or worker-consumption condition is invoked. -/
theorem source_weighted_discounted_equity_nonneg_on_support
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t)
    (hfeasible : BankContinuationFeasibleAt P X t h
      (X.bankEquity t h) (sourceFullRetentionCandidate P X t h))
    (hinitial : 0 < X.workerConsumption t h)
    (hconsumption : ∀ n (future : Fin n → S),
      FuturePathSupported P.tree (currentState h) n future →
        0 < X.workerConsumption (t + n)
          (continuationHistory h future)) :
    ∀ n (future : Fin n → S)
      (payments : Fin n → P.paymentSupport),
      0 ≤
        (continuationTransitionWeight P.tree (currentState h) n future *
          continuationPaymentWeight P payments) *
        (bankCumulativeSDFAt P X t h future *
          (sourceFullRetentionCandidate P X t h).equity n future payments) := by
  intro n future payments
  by_cases hzero : continuationTransitionWeight P.tree (currentState h)
      n future = 0
  · simp [hzero]
  · have hpositive : 0 <
        continuationTransitionWeight P.tree (currentState h) n future :=
      lt_of_le_of_ne
        (ProposedBankContinuationPathProbabilityMass.source_aggregate_future_path_weight_nonneg
          P.tree n (currentState h) future) (Ne.symm hzero)
    have hpath := positive_transition_weight_implies_supported
      P.tree (currentState h) n future hpositive
    have hequity : 0 ≤
        (sourceFullRetentionCandidate P X t h).equity n future payments :=
      (hfeasible.2 n future payments hpath).1
    have hsdf : 0 < bankCumulativeSDFAt P X t h future :=
      source_bank_cumulative_sdf_pos P X t h n future
        hinitial (hconsumption n future hpath)
    exact mul_nonneg
      (ProposedBankContinuationPathProbabilityMass.source_joint_future_path_weight_nonneg
        P n (currentState h) future payments)
      (mul_nonneg hsdf.le hequity)

#print axioms source_weighted_discounted_equity_nonneg_on_support


/-- The exact SOURCE mass contracts with the conditional OTC return
bound imposed only at positive-probability Markov histories.
Bank solvency and worker-consumption positivity are needed only on
supported histories to establish nonnegative weighted parent mass.
The one-step source identity is supplied explicitly here, so this
lemma can later be paired with a supported-only version of it. -/
theorem source_discounted_mass_contracts_on_supported_histories
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t)
    (grossBound : ℝ)
    (hfeasible : BankContinuationFeasibleAt P X t h
      (X.bankEquity t h) (sourceFullRetentionCandidate P X t h))
    (hinitial : 0 < X.workerConsumption t h)
    (hconsumption : ∀ n (future : Fin n → S),
      FuturePathSupported P.tree (currentState h) n future →
        0 < X.workerConsumption (t + n)
          (continuationHistory h future))
    (hconditional : ∀ n (future : Fin n → S),
      FuturePathSupported P.tree (currentState h) n future →
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
  rw [hnext n]
  unfold sourceDiscountedBankEquityMassAt
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
      have hnonneg := source_weighted_discounted_equity_nonneg_on_support
        P X t h hfeasible hinitial hconsumption n future payments
      by_cases hzero : continuationTransitionWeight P.tree (currentState h)
          n future = 0
      · simp [hzero]
      · have hpositive : 0 <
          continuationTransitionWeight P.tree (currentState h) n future :=
          lt_of_le_of_ne
            (ProposedBankContinuationPathProbabilityMass.source_aggregate_future_path_weight_nonneg
              P.tree n (currentState h) future) (Ne.symm hzero)
        have hpath := positive_transition_weight_implies_supported
          P.tree (currentState h) n future hpositive
        exact mul_le_mul_of_nonneg_left
          (hconditional n future hpath) hnonneg
    _ = grossBound * (∑ future : Fin n → S,
      ∑ payments : Fin n → P.paymentSupport,
      (continuationTransitionWeight P.tree (currentState h) n future *
        continuationPaymentWeight P payments) *
        (bankCumulativeSDFAt P X t h future *
          (sourceFullRetentionCandidate P X t h).equity n future payments)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro future _hf
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro payments _hp
      ring

#print axioms source_discounted_mass_contracts_on_supported_histories


/-- SOURCE one-step OTC identity requiring real economic positivity
only for supported aggregate parent histories and positive-probability
child transitions. Zero probability edges disappear before any SDF
or aggregate equity divisibility assumption is used. -/
theorem source_weighted_child_identity_supported_only
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t)
    (hfeasible : BankContinuationFeasibleAt P X t h
      (X.bankEquity t h) (sourceFullRetentionCandidate P X t h))
    (n : ℕ) (future : Fin n → S)
    (payments : Fin n → P.paymentSupport)
    (s : S) (omega : P.paymentSupport)
    (hrisk : P.workerRiskAversion = 1)
    (hconsumption : FuturePathSupported P.tree (currentState h) n future →
      0 < X.workerConsumption (t + n) (continuationHistory h future))
    (hchildConsumption : FuturePathSupported P.tree (currentState h) n future →
      0 < P.tree.transition
        (currentState (continuationHistory h future)) s →
      0 < X.workerConsumption (t + n + 1)
        (childHistory (continuationHistory h future) s))
    (haggregate : FuturePathSupported P.tree (currentState h) n future →
      0 < X.bankEquity (t + n) (continuationHistory h future)) :
    (continuationTransitionWeight P.tree (currentState h) n future *
      continuationPaymentWeight P payments) *
      ((P.tree.transition
        (currentState (continuationHistory h future)) s *
          P.paymentProbability omega) *
        (bankCumulativeSDFAt P X t h (childFutureHistory future s) *
          (sourceFullRetentionCandidate P X t h).equity (n + 1)
            (childFutureHistory future s)
            (childPaymentHistory payments omega))) =
    (continuationTransitionWeight P.tree (currentState h) n future *
      continuationPaymentWeight P payments) *
      ((P.tree.transition
        (currentState (continuationHistory h future)) s *
          P.paymentProbability omega) *
        ((bankCumulativeSDFAt P X t h future *
          (sourceFullRetentionCandidate P X t h).equity n future payments) *
          sourceDiscountedEquityGrowthFactor P X t h n future s omega)) := by
  by_cases hzeroParent :
      continuationTransitionWeight P.tree (currentState h) n future = 0
  · simp [hzeroParent]
  by_cases hzeroEdge : P.tree.transition
      (currentState (continuationHistory h future)) s = 0
  · simp [hzeroEdge]
  have hpositiveParent : 0 <
      continuationTransitionWeight P.tree (currentState h) n future :=
    lt_of_le_of_ne
      (ProposedBankContinuationPathProbabilityMass.source_aggregate_future_path_weight_nonneg
        P.tree n (currentState h) future) (Ne.symm hzeroParent)
  have hpositiveEdge : 0 <
      P.tree.transition (currentState (continuationHistory h future)) s :=
    lt_of_le_of_ne
      (P.tree.transition_nonneg _ _) (Ne.symm hzeroEdge)
  have hpath := positive_transition_weight_implies_supported
    P.tree (currentState h) n future hpositiveParent
  have hnonneg := (hfeasible.2 n future payments hpath).1
  have hchild := source_full_retention_nonnegative_parent_child_identity
    P X t h hfeasible n future payments hpath s omega
    hrisk (hconsumption hpath)
    (hchildConsumption hpath hpositiveEdge) hnonneg (haggregate hpath)
  rw [hchild]

#print axioms source_weighted_child_identity_supported_only


/-- Aggregate OTC mass transition with individual equity allowed to be
zero; worker consumption and aggregate bank equity must be positive
only on genuinely supported Markov histories. Off-support parent and
child nodes are removed algebraically by their transition weights. The
SOURCE conditional return bound is still a separate economic premise. -/
theorem source_discounted_bank_mass_next_on_supported_histories
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t)
    (hfeasible : BankContinuationFeasibleAt P X t h
      (X.bankEquity t h) (sourceFullRetentionCandidate P X t h))
    (hrisk : P.workerRiskAversion = 1)
    (hconsumption : ∀ n (future : Fin n → S),
      FuturePathSupported P.tree (currentState h) n future →
        0 < X.workerConsumption (t + n) (continuationHistory h future))
    (hchildConsumption : ∀ n (future : Fin n → S) s,
      FuturePathSupported P.tree (currentState h) n future →
        0 < P.tree.transition
          (currentState (continuationHistory h future)) s →
        0 < X.workerConsumption (t + n + 1)
          (childHistory (continuationHistory h future) s))
    (haggregate : ∀ n (future : Fin n → S),
      FuturePathSupported P.tree (currentState h) n future →
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
      have htrans := source_transition_weight_child P X t h n future s
      change continuationTransitionWeight P.tree (currentState h) (n + 1)
        (Fin.cons s future) =
        continuationTransitionWeight P.tree (currentState h) n future *
          P.tree.transition
            (currentState (continuationHistory h future)) s at htrans
      rw [htrans]
      have hpayment := source_payment_weight_child P payments omega
      change continuationPaymentWeight P (Fin.cons omega payments) =
        continuationPaymentWeight P payments * P.paymentProbability omega
        at hpayment
      rw [hpayment]
      have hweighted :=
        source_weighted_child_identity_supported_only
          P X t h hfeasible n future payments s omega
          hrisk (hconsumption n future)
          (hchildConsumption n future s) (haggregate n future)
      change (continuationTransitionWeight P.tree (currentState h) n future *
        P.tree.transition (currentState (continuationHistory h future)) s *
        (continuationPaymentWeight P payments * P.paymentProbability omega)) *
        (bankCumulativeSDFAt P X t h (Fin.cons s future) *
          (sourceFullRetentionCandidate P X t h).equity (n + 1)
            (Fin.cons s future) (Fin.cons omega payments)) =
        W future payments * K future s omega
      calc
        _ = (continuationTransitionWeight P.tree (currentState h) n future *
          continuationPaymentWeight P payments) *
          ((P.tree.transition
            (currentState (continuationHistory h future)) s *
            P.paymentProbability omega) *
            (bankCumulativeSDFAt P X t h (childFutureHistory future s) *
              (sourceFullRetentionCandidate P X t h).equity (n + 1)
                (childFutureHistory future s)
                (childPaymentHistory payments omega))) := by
            have hfuture :
                childFutureHistory future s = Fin.cons s future := rfl
            have hpayments :
                childPaymentHistory payments omega =
                  Fin.cons omega payments := rfl
            rw [hfuture, hpayments]
            ring
        _ = (continuationTransitionWeight P.tree (currentState h) n future *
          continuationPaymentWeight P payments) *
          ((P.tree.transition
            (currentState (continuationHistory h future)) s *
              P.paymentProbability omega) *
            ((bankCumulativeSDFAt P X t h future *
              (sourceFullRetentionCandidate P X t h).equity n future payments) *
              sourceDiscountedEquityGrowthFactor P X t h n future s omega)) :=
            hweighted
        _ = W future payments * K future s omega := by
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

#print axioms source_discounted_bank_mass_next_on_supported_histories


/-- Nonnegative source surviving-equity value using feasibility only
at Markov-supported paths. Off-support contributions are identically
zero; the survival factor is assumed nonnegative. -/
theorem source_surviving_value_nonneg_on_supported_histories
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t)
    (hsurvive : 0 ≤ 1 - P.bankExit)
    (hfeasible : BankContinuationFeasibleAt P X t h
      (X.bankEquity t h) (sourceFullRetentionCandidate P X t h))
    (hinitial : 0 < X.workerConsumption t h)
    (hconsumption : ∀ n (future : Fin n → S),
      FuturePathSupported P.tree (currentState h) n future →
        0 < X.workerConsumption (t + n) (continuationHistory h future)) :
    ∀ n, 0 ≤ bankSurvivingValueTermAt P X t h
      (sourceFullRetentionCandidate P X t h) n := by
  intro n
  rw [source_surviving_value_eq_survival_pow_mul_mass]
  apply mul_nonneg (pow_nonneg hsurvive n)
  unfold sourceDiscountedBankEquityMassAt
  apply Finset.sum_nonneg
  intro future _hf
  apply Finset.sum_nonneg
  intro payments _hp
  exact source_weighted_discounted_equity_nonneg_on_support
    P X t h hfeasible hinitial hconsumption n future payments

/-- SOURCE full-retention TVC and payoff summability under OTC
conditional-growth bounds ONLY on supported histories. Individual
equity may be zero; off-support prices/consumption need no positivity.
The bound and economic feasibility are premises, not an equilibrium
existence or global BankOptimal theorem. -/
theorem source_full_retention_tvc_on_supported_histories
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
    (hfeasible : BankContinuationFeasibleAt P X t h
      (X.bankEquity t h) (sourceFullRetentionCandidate P X t h))
    (hrisk : P.workerRiskAversion = 1)
    (hinitial : 0 < X.workerConsumption t h)
    (hconsumption : ∀ n (future : Fin n → S),
      FuturePathSupported P.tree (currentState h) n future →
        0 < X.workerConsumption (t + n) (continuationHistory h future))
    (hchildConsumption : ∀ n (future : Fin n → S) s,
      FuturePathSupported P.tree (currentState h) n future →
        0 < P.tree.transition
          (currentState (continuationHistory h future)) s →
        0 < X.workerConsumption (t + n + 1)
          (childHistory (continuationHistory h future) s))
    (haggregate : ∀ n (future : Fin n → S),
      FuturePathSupported P.tree (currentState h) n future →
        0 < X.bankEquity (t + n) (continuationHistory h future))
    (hconditional : ∀ n (future : Fin n → S),
      FuturePathSupported P.tree (currentState h) n future →
        sourceConditionalOTCGrowthFactor P X t h n future ≤ grossBound) :
    BankContinuationObjectiveWellDefinedAt P X t h
      (sourceFullRetentionCandidate P X t h) ∧
    BankContinuationTerminalConditionAt P X t h
      (sourceFullRetentionCandidate P X t h) := by
  have hnext := source_discounted_bank_mass_next_on_supported_histories
    P X t h hfeasible hrisk hconsumption hchildConsumption haggregate
  have hmass := source_discounted_mass_contracts_on_supported_histories
    P X t h grossBound hfeasible hinitial hconsumption hconditional hnext
  have hnonneg := source_surviving_value_nonneg_on_supported_histories
    P X t h hsurvive hfeasible hinitial hconsumption
  have hstep : ∀ n,
      bankSurvivingValueTermAt P X t h
        (sourceFullRetentionCandidate P X t h) (n + 1) ≤
      ((1 - P.bankExit) * grossBound) *
        bankSurvivingValueTermAt P X t h
          (sourceFullRetentionCandidate P X t h) n := by
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
  exact full_retention_analytic_conditions_of_survivor_contraction
    P X t h C ((1 - P.bankExit) * grossBound)
    hC (mul_nonneg hsurvive hgross) hcontraction
    hexit hnonneg hbase hstep

#print axioms source_surviving_value_nonneg_on_supported_histories
#print axioms source_full_retention_tvc_on_supported_histories

end ProposedBankConditionalOTCTransitionIdentity
end Ventura26LiquidityAllocation

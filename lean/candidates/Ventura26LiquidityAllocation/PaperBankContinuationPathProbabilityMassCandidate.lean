import Ventura26LiquidityAllocation.PaperBankPathwiseOTCDiscountedReturnCandidate

/-!
# SOURCE probability normalization over all aggregate and payment paths

The bank owner-payoff and surviving-equity terms sum over two finite
path carriers: aggregate Markov histories and supported individual bank
payment histories. A pathwise equity bound becomes an expected bound
ONLY when these weights are nonnegative and sum to one.

These lemmas derive normalization from the SOURCE primitive assumptions:
FiniteMarkovTree.transition_sum_one and
Primitives.payment_probability_sum_one. No independent measure
normalization is postulated and no economic equilibrium is assumed.

The source's `sum_pi_snoc` convention explicitly peels the oldest
state/payment from the Fin-indexed history.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedBankContinuationPathProbabilityMass

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Every n-step future from a fixed starting Markov state has total
transition probability one, including n=0. -/
theorem source_aggregate_future_path_mass_one
    (T : FiniteMarkovTree S) (n : ℕ) (start : S) :
    (∑ future : Fin n → S,
      continuationTransitionWeight T start n future) = 1 := by
  induction n generalizing start with
  | zero =>
      simp [continuationTransitionWeight]
  | succ n ih =>
      calc
        (∑ future : Fin (n + 1) → S,
            continuationTransitionWeight T start (n + 1) future) =
          ∑ s : S, T.transition start s *
            (∑ future : Fin n → S,
              continuationTransitionWeight T s n future) := by
          rw [sum_pi_snoc]
          apply Finset.sum_congr rfl
          intro s _hs
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro future _hf
          exact continuationTransitionWeight_snoc T start s n future
        _ = ∑ s : S, T.transition start s := by simp [ih]
        _ = 1 := T.transition_sum_one start

/-- Every supported n-step payment path has probability one in total.
The support is the subtype of the primitive Finset. -/
theorem source_payment_future_path_mass_one
    (P : Primitives S) (n : ℕ) :
    (∑ payments : Fin n → P.paymentSupport,
      continuationPaymentWeight P payments) = 1 := by
  have hprob : (∑ ω : P.paymentSupport, P.paymentProbability ω) = 1 := by
    rw [Finset.sum_subtype P.paymentSupport (fun x => Iff.rfl)]
    exact P.payment_probability_sum_one
  induction n with
  | zero =>
      simp [continuationPaymentWeight]
  | succ n ih =>
      calc
        (∑ payments : Fin (n + 1) → P.paymentSupport,
            continuationPaymentWeight P payments) =
          ∑ ω : P.paymentSupport, P.paymentProbability ω *
            (∑ payments : Fin n → P.paymentSupport,
              continuationPaymentWeight P payments) := by
          rw [sum_pi_snoc]
          apply Finset.sum_congr rfl
          intro omega _hω
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro payments _hp
          exact continuationPaymentWeight_snoc P payments omega
        _ = ∑ ω : P.paymentSupport, P.paymentProbability ω := by
          simp [ih]
        _ = 1 := hprob

/-- Markov transition path weights are nonnegative at every length.
This uses only the primitive transition law. -/
theorem source_aggregate_future_path_weight_nonneg
    (T : FiniteMarkovTree S) (n : ℕ) (start : S)
    (future : Fin n → S) :
    0 ≤ continuationTransitionWeight T start n future := by
  induction n with
  | zero =>
      simp [continuationTransitionWeight]
  | succ n ih =>
      change 0 ≤
        continuationTransitionWeight T start n (fun j => future j.succ) *
        T.transition
          (if hn : n = 0 then start
            else (fun j : Fin n => future j.succ)
              ⟨0, Nat.pos_of_ne_zero hn⟩)
          (future 0)
      exact mul_nonneg (ih (fun j => future j.succ))
        (T.transition_nonneg _ _)

/-- Supported payment-history weights are nonnegative, even for
the empty payment history. -/
theorem source_payment_future_path_weight_nonneg
    (P : Primitives S) (n : ℕ)
    (payments : Fin n → P.paymentSupport) :
    0 ≤ continuationPaymentWeight P payments := by
  have hprod : ∀ F : Finset (Fin n),
      0 ≤ F.prod (fun j => P.paymentProbability (payments j)) := by
    intro F
    induction F using Finset.induction_on with
    | empty =>
        simp
    | @insert j F hj ih =>
        rw [Finset.prod_insert hj]
        exact mul_nonneg (P.payment_probability_nonneg (payments j)) ih
  exact hprod Finset.univ

/-- The exact joint source transition/payment path weights sum to
one; no extra normalization axiom is added. -/
theorem source_joint_future_path_mass_one
    (P : Primitives S) (n : ℕ) (start : S) :
    (∑ future : Fin n → S,
      ∑ payments : Fin n → P.paymentSupport,
        continuationTransitionWeight P.tree start n future *
          continuationPaymentWeight P payments) = 1 := by
  calc
    (∑ future : Fin n → S,
      ∑ payments : Fin n → P.paymentSupport,
        continuationTransitionWeight P.tree start n future *
          continuationPaymentWeight P payments) =
      ∑ future : Fin n → S,
        continuationTransitionWeight P.tree start n future *
          (∑ payments : Fin n → P.paymentSupport,
            continuationPaymentWeight P payments) := by
      apply Finset.sum_congr rfl
      intro future _hf
      rw [Finset.mul_sum]
    _ = ∑ future : Fin n → S,
        continuationTransitionWeight P.tree start n future := by
      simp [source_payment_future_path_mass_one]
    _ = 1 := source_aggregate_future_path_mass_one P.tree n start

/-- Each joint source path weight is nonnegative. -/
theorem source_joint_future_path_weight_nonneg
    (P : Primitives S) (n : ℕ) (start : S)
    (future : Fin n → S) (payments : Fin n → P.paymentSupport) :
    0 ≤ continuationTransitionWeight P.tree start n future *
        continuationPaymentWeight P payments :=
  mul_nonneg
    (source_aggregate_future_path_weight_nonneg P.tree n start future)
    (source_payment_future_path_weight_nonneg P n payments)

#print axioms source_aggregate_future_path_mass_one
#print axioms source_payment_future_path_mass_one
#print axioms source_aggregate_future_path_weight_nonneg
#print axioms source_payment_future_path_weight_nonneg
#print axioms source_joint_future_path_mass_one
#print axioms source_joint_future_path_weight_nonneg

end ProposedBankContinuationPathProbabilityMass
end Ventura26LiquidityAllocation

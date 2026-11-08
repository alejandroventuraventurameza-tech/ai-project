import Ventura26LiquidityAllocation.PaperBankSourceTransitionMonotonicityCandidate

/-!
# Joint payment and aggregate-state continuation: literal SOURCE weights

The source bank continuation integrates over payment realizations and
aggregate successors. The inequality established here covers the
surviving-franchise VALUE component with payment- and state-indexed
next values. It neither constructs a feasible bank policy nor proves
the candidate-value identity, terminality, or BankOptimal.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedBankJointContinuationMonotonicity

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The joint survivor-value component of the source Bellman operator.
There is intentionally no exit-equity term: that term cancels when
comparing two value functions at a FIXED portfolio. -/
noncomputable def jointSurvivalContinuation
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t)
    (nextValue : BankPayment → S → ℝ) : ℝ :=
  ∑ ω ∈ P.paymentSupport, P.paymentProbability ω *
    ∑ s : S, P.tree.transition (currentState h) s *
      bankStochasticDiscountAt P X t h s *
        ((1 - P.bankExit) * nextValue ω s)

/-- Monotonicity under original source transition and SDF.
Only positively supported successors require consumption positivity;
zero-mass successors have a zero contribution. -/
theorem jointSurvivalContinuation_monotone_of_consumption
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t)
    (f g : BankPayment → S → ℝ)
    (hcurrent : 0 < X.workerConsumption t h)
    (hchild : ∀ s, 0 < P.tree.transition (currentState h) s →
      0 < X.workerConsumption (t + 1) (childHistory h s))
    (hfg : ∀ ω ∈ P.paymentSupport, ∀ s, f ω s ≤ g ω s) :
    jointSurvivalContinuation P X t h f ≤
      jointSurvivalContinuation P X t h g := by
  unfold jointSurvivalContinuation
  apply Finset.sum_le_sum
  intro ω hω
  apply mul_le_mul_of_nonneg_left
  · apply Finset.sum_le_sum
    intro s hs
    by_cases hzero : P.tree.transition (currentState h) s = 0
    · simp [hzero]
    have htrans : 0 < P.tree.transition (currentState h) s :=
      lt_of_le_of_ne (P.tree.transition_nonneg _ _) (Ne.symm hzero)
    have hSDF : 0 < bankStochasticDiscountAt P X t h s :=
      bankStochasticDiscountAt_pos_of_consumption P X t h s
        hcurrent (hchild s htrans)
    have hsurvival : 0 ≤ 1 - P.bankExit :=
      sub_nonneg.mpr P.bank_exit_mem.2
    have hweight : 0 ≤
        P.tree.transition (currentState h) s *
          bankStochasticDiscountAt P X t h s :=
      mul_nonneg htrans.le hSDF.le
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (hfg ω hω s) hsurvival) hweight
  · exact (P.payment_probability_pos_on_support ω hω).le

#print axioms jointSurvivalContinuation_monotone_of_consumption

end ProposedBankJointContinuationMonotonicity
end Ventura26LiquidityAllocation

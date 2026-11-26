import Ventura26LiquidityAllocation.PaperBankJointContinuationMonotonicityCandidate

/-!
# Literal source bank Bellman monotonicity at a fixed portfolio

This theorem acts directly on bankBellmanContinuationAt rather than
a separate proxy operator. The candidate and alternative future value
functions are compared only at successor equity/history pairs generated
by the SAME portfolio. The exit-equity term is identical on both sides.

This is NOT a dynamic bank optimality theorem, nor does it compare
different current portfolios or policies.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedBankLiteralBellmanMonotonicity

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem bankBellmanContinuationAt_monotone_of_consumption
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (deficitSlope surplusSlope loans reserves deposits : ℝ)
    (V W : ℝ → History S (t + 1) → ℝ)
    (hcurrent : 0 < X.workerConsumption t h)
    (hchild : ∀ s, 0 < P.tree.transition (currentState h) s →
      0 < X.workerConsumption (t + 1) (childHistory h s))
    (hVW : ∀ ω ∈ P.paymentSupport, ∀ s,
      V (bankRealPortfolioReturnAt P X t h deficitSlope surplusSlope
          loans reserves deposits ω s) (childHistory h s) ≤
      W (bankRealPortfolioReturnAt P X t h deficitSlope surplusSlope
          loans reserves deposits ω s) (childHistory h s)) :
    bankBellmanContinuationAt P X t h
      deficitSlope surplusSlope loans reserves deposits V ≤
    bankBellmanContinuationAt P X t h
      deficitSlope surplusSlope loans reserves deposits W := by
  unfold bankBellmanContinuationAt
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
    have hV :
        (1 - P.bankExit) *
          V (bankRealPortfolioReturnAt P X t h deficitSlope surplusSlope
            loans reserves deposits ω s) (childHistory h s) ≤
        (1 - P.bankExit) *
          W (bankRealPortfolioReturnAt P X t h deficitSlope surplusSlope
            loans reserves deposits ω s) (childHistory h s) :=
      mul_le_mul_of_nonneg_left (hVW ω hω s) hsurvival
    exact mul_le_mul_of_nonneg_left
      (add_le_add_left hV
        (P.bankExit * bankRealPortfolioReturnAt P X t h deficitSlope
          surplusSlope loans reserves deposits ω s))
      hweight
  · exact (P.payment_probability_pos_on_support ω hω).le

#print axioms bankBellmanContinuationAt_monotone_of_consumption

end ProposedBankLiteralBellmanMonotonicity
end Ventura26LiquidityAllocation

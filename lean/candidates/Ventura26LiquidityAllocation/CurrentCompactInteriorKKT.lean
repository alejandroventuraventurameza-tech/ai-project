import Mathlib

/-!
# Lemma A.1.2: no simultaneous strictly interior saving and borrowing

Exact academic source: ai-project@bac3c6255da39cd1169a965df35bb5e9a230e6e8
paper/appendix_eight_results.tex, label lem:v0m_original_6_2.

The sum is a FINITE probability expectation over states W. Weights are
nonnegative and sum to one; the marginal value and gross inflation are
strictly positive on every state with positive probability. This faithfully
implements "almost surely" in finite support without asserting positive
value on null-probability states. Both gross rates are non-state-contingent.

The interior FOC equalities of the source are explicit hypotheses.
It proves incompatibility of those necessary conditions, NOT global
sufficiency of KKT or optimality for the full dynamic firm problem.
-/

namespace Ventura26LiquidityAllocation.CurrentCompact

/-- Conditional expected real marginal value under finite-support
probabilities, with no additional subjective discount factor. -/
noncomputable def expectedRealMarginal
    {W : Type*} [Fintype W]
    (probability marginalValue inflationNext : W → ℝ) : ℝ :=
  ∑ w : W, probability w * (marginalValue w / inflationNext w)

/-- The conditional expectation is strictly positive if total
probability is one, inflation and marginal value are strictly positive
almost surely, and weights are nonnegative. -/
theorem expectedRealMarginal_pos
    {W : Type*} [Fintype W]
    (probability marginalValue inflationNext : W → ℝ)
    (hprob : ∀ w, 0 ≤ probability w)
    (htotal : (∑ w : W, probability w) = 1)
    (hmarginal : ∀ w, 0 < probability w → 0 < marginalValue w)
    (hinflation : ∀ w, 0 < probability w → 0 < inflationNext w) :
    0 < expectedRealMarginal probability marginalValue inflationNext := by
  have hexists : ∃ w : W, 0 < probability w := by
    by_contra hnone
    push_neg at hnone
    have hnonpos : (∑ w : W, probability w) ≤ 0 := by
      apply Finset.sum_nonpos
      intro w hw
      exact hnone w
    linarith
  unfold expectedRealMarginal
  apply Finset.sum_pos
  · intro w hw
    by_cases hweight : 0 < probability w
    · exact le_of_lt (mul_pos hweight
        (div_pos (hmarginal w hweight) (hinflation w hweight)))
    · have hzero : probability w = 0 :=
        le_antisymm (le_of_not_gt hweight) (hprob w)
      simp [hzero]
  · rcases hexists with ⟨w, hweight⟩
    exact ⟨w, Finset.mem_univ _,
      mul_pos hweight
        (div_pos (hmarginal w hweight) (hinflation w hweight))⟩

/-- The gross rate is fixed across next-period realizations and
can therefore be factored out of the conditional finite expectation.
This connects the literal source FOC to a scalar discounted marginal. -/
theorem expectedRealMarginal_rateFactorization
    {W : Type*} [Fintype W]
    (probability marginalValue inflationNext : W → ℝ)
    (grossRate : ℝ) :
    (∑ w : W,
       probability w * (marginalValue w * grossRate / inflationNext w)) =
      expectedRealMarginal probability marginalValue inflationNext * grossRate := by
  unfold expectedRealMarginal
  calc
    (∑ w : W,
       probability w * (marginalValue w * grossRate / inflationNext w)) =
      (∑ w : W, (probability w *
        (marginalValue w / inflationNext w)) * grossRate) := by
          apply Finset.sum_congr rfl
          intro w hw
          ring
    _ = (∑ w : W,
        probability w * (marginalValue w / inflationNext w)) * grossRate := by
          rw [Finset.sum_mul]

/-- Literal Appendix A.1.2 first-order conditions (finite support):
deposit and loan gross positions are both interior, yet deposit and loan
Eulers with a common lambda, positive discounted marginal, positive spread,
and a nonnegative collateral dual would have to hold simultaneously. -/
def noSimultaneousInteriorCurrentSpec : Prop :=
  ∀ {W : Type*} [Fintype W]
      (probability marginalValue inflationNext : W → ℝ)
      (entrepreneurDiscount lambda loanRate depositRate collateralDual
       deposit loan : ℝ),
    (∀ w, 0 ≤ probability w) →
    (∑ w : W, probability w) = 1 →
    (∀ w, 0 < probability w → 0 < marginalValue w) →
    (∀ w, 0 < probability w → 0 < inflationNext w) →
    0 < entrepreneurDiscount →
    0 < depositRate →
    depositRate < loanRate →
    0 ≤ collateralDual →
    0 < deposit →
    0 < loan →
    lambda = entrepreneurDiscount *
      (∑ w : W, probability w *
        (marginalValue w * depositRate / inflationNext w)) →
    lambda = entrepreneurDiscount *
      (∑ w : W, probability w *
        (marginalValue w * loanRate / inflationNext w)) +
        collateralDual * loanRate →
    False

/-- The source's contradiction follows from RD < RL, positive normalized
expected marginal value and nonnegative collateral dual, without assuming
global sufficiency of the FOCs. -/
theorem noSimultaneousInteriorCurrent_exact :
    noSimultaneousInteriorCurrentSpec := by
  intro W inst probability marginalValue inflationNext
    entrepreneurDiscount lambda loanRate depositRate collateralDual
    deposit loan hprob htotal hmarginal hinflation
    hdiscount hdepositRate hspread hdual hdeposit hloan
    hdepositFOC hloanFOC
  let E : ℝ :=
    expectedRealMarginal probability marginalValue inflationNext
  have hE : 0 < E :=
    expectedRealMarginal_pos probability marginalValue inflationNext
      hprob htotal hmarginal hinflation
  have hnorm : 0 < entrepreneurDiscount * E :=
    mul_pos hdiscount hE
  have hrate : 0 < loanRate := lt_trans hdepositRate hspread
  have hstrict :
      (entrepreneurDiscount * E) * depositRate <
        (entrepreneurDiscount * E) * loanRate :=
    mul_lt_mul_of_pos_left hspread hnorm
  have hdualTerm : 0 ≤ collateralDual * loanRate :=
    mul_nonneg hdual hrate.le
  have hfactorDeposit :=
    expectedRealMarginal_rateFactorization
      probability marginalValue inflationNext depositRate
  have hfactorLoan :=
    expectedRealMarginal_rateFactorization
      probability marginalValue inflationNext loanRate
  rw [hfactorDeposit] at hdepositFOC
  rw [hfactorLoan] at hloanFOC
  change
    lambda = entrepreneurDiscount * (E * depositRate)
    at hdepositFOC
  change
    lambda = entrepreneurDiscount * (E * loanRate) +
      collateralDual * loanRate at hloanFOC
  nlinarith [hstrict, hdualTerm, hdepositFOC, hloanFOC]

#print axioms expectedRealMarginal_pos
#print axioms expectedRealMarginal_rateFactorization
#print axioms noSimultaneousInteriorCurrent_exact

end Ventura26LiquidityAllocation.CurrentCompact

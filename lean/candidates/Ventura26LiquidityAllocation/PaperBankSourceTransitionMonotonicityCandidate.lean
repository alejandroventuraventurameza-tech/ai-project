import Ventura26LiquidityAllocation.EconomicModel
import Ventura26LiquidityAllocation.PaperBankFiniteSupportContinuationCandidate

/-!
# Monotonicity of the SOURCE bank stochastic continuation, one history

The weights below use the literal source Markov transition and SDF.
For a fixed history t,h, this establishes the order of continuation
values on next-period aggregate states. The continuation bank's equity
can depend on payment ω; therefore this is NOT yet a proof of the
full infinite-horizon bank value or BankOptimal.

The SDF's nonnegativity is a named hypothesis: the existing source
establishes its positivity on supported successors under consumption
conditions. Keeping it visible prevents silent claims about zero-mass
states or unverified numerical paths.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedBankSourceTransitionMonotonicity

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- SOURCE-weighted survivor continuation for a fixed aggregate history. -/
noncomputable def sourceSurvivalContinuation
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (nextValue : S → ℝ) : ℝ :=
  ∑ s : S, P.tree.transition (currentState h) s *
    bankStochasticDiscountAt P X t h s *
      ((1 - P.bankExit) * nextValue s)

/-- Pointwise order of next-state values implies order of the
literal transition/SDF/survival weighted continuation. -/
theorem sourceSurvivalContinuation_monotone
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (f g : S → ℝ)
    (hSDF : ∀ s, 0 ≤ bankStochasticDiscountAt P X t h s)
    (hfg : ∀ s, f s ≤ g s) :
    sourceSurvivalContinuation P X t h f ≤
      sourceSurvivalContinuation P X t h g := by
  unfold sourceSurvivalContinuation
  apply Finset.sum_le_sum
  intro s hs
  have htransition : 0 ≤ P.tree.transition (currentState h) s :=
    P.tree.transition_nonneg _ _
  have hsurvival : 0 ≤ 1 - P.bankExit := by
    have hexit := P.bank_exit_mem.2
    linarith
  have hweight : 0 ≤
      P.tree.transition (currentState h) s *
        bankStochasticDiscountAt P X t h s := by
    exact mul_nonneg htransition (hSDF s)
  have hcontinuation :
      (1 - P.bankExit) * f s ≤ (1 - P.bankExit) * g s :=
    mul_le_mul_of_nonneg_left (hfg s) hsurvival
  exact mul_le_mul_of_nonneg_left hcontinuation hweight

#print axioms sourceSurvivalContinuation_monotone

end ProposedBankSourceTransitionMonotonicity
end Ventura26LiquidityAllocation

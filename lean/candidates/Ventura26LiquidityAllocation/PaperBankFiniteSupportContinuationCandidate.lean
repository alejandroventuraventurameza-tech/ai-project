import Ventura26LiquidityAllocation.PaperBankMonotoneBellmanEnvelopeCandidate

/-!
# Finite support, positive weighted Bellman transitions

This module proves the monotonicity of a concrete finite weighted sum
and applies the abstract finite-horizon envelope. The event weights
are ASSUMED nonnegative. No identification with the SOURCE
transition probabilities, SDF, bank equity transitions, or BankOptimal
is asserted here.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedBankFiniteSupportContinuation

variable {State Event : Type*}

/-- A time/state-dependent finite-support continuation operator. -/
def weightedContinuation
    (support : Finset Event)
    (weight : ℕ → State → Event → ℝ)
    (nextState : ℕ → State → Event → State) :
    ℕ → (State → ℝ) → State → ℝ :=
  fun t f s => ∑ ω ∈ support, weight t s ω * f (nextState t s ω)

/-- Finite sums with nonnegative weights preserve pointwise order. -/
theorem weightedContinuation_monotone
    (support : Finset Event)
    (weight : ℕ → State → Event → ℝ)
    (nextState : ℕ → State → Event → State)
    (hweight : ∀ t s ω, ω ∈ support → 0 ≤ weight t s ω) :
    ProposedBankMonotoneBellmanEnvelope.MonotoneContinuation
      (weightedContinuation support weight nextState) := by
  intro t f g hfg s
  unfold weightedContinuation
  apply Finset.sum_le_sum
  intro ω hω
  exact mul_le_mul_of_nonneg_left
    (hfg (nextState t s ω)) (hweight t s ω hω)

/-- A pointwise supersolution yields an upper envelope for arbitrary
finite horizons under the same nonnegative transition weights. -/
theorem weightedContinuation_finite_horizon_bound
    (support : Finset Event)
    (weight : ℕ → State → Event → ℝ)
    (nextState : ℕ → State → Event → State)
    (flow value : ℕ → State → ℝ)
    (hweight : ∀ t s ω, ω ∈ support → 0 ≤ weight t s ω)
    (hsuper : ∀ t s,
      flow t s +
        weightedContinuation support weight nextState t (value (t + 1)) s
          ≤ value t s) :
    ∀ n t s,
      ProposedBankMonotoneBellmanEnvelope.recurse
        flow value (weightedContinuation support weight nextState) n t s
          ≤ value t s := by
  exact ProposedBankMonotoneBellmanEnvelope.recurse_le_value
    flow value (weightedContinuation support weight nextState)
    (weightedContinuation_monotone support weight nextState hweight) hsuper

#print axioms weightedContinuation_monotone
#print axioms weightedContinuation_finite_horizon_bound

end ProposedBankFiniteSupportContinuation
end Ventura26LiquidityAllocation

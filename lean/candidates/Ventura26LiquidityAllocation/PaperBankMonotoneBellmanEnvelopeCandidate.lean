import Mathlib

/-!
# Abstract positive Bellman continuation operator

A monotone continuation operator captures the ORDER-theoretic step
behind a conditional-expectation Bellman inequality. This module
deliberately does NOT instantiate the SOURCE bank transition kernel,
stochastic discount factor, measurability, or infinite-horizon limit.
No BankOptimal/equilibrium claim follows from this abstract lemma.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedBankMonotoneBellmanEnvelope

variable {State : Type*}

/-- A finite-horizon continuation with arbitrary time-dependent
monotone operators. An expectation operator is one possible instance,
but is NOT constructed by this definition. -/
def recurse
    (flow value : ℕ → State → ℝ)
    (continuation : ℕ → (State → ℝ) → State → ℝ) :
    ℕ → ℕ → State → ℝ
  | 0, t, s => value t s
  | n + 1, t, s =>
      flow t s + continuation t (recurse flow value continuation n (t + 1)) s

/-- A time-indexed order-preserving continuation operator. -/
def MonotoneContinuation
    (continuation : ℕ → (State → ℝ) → State → ℝ) : Prop :=
  ∀ t f g, (∀ s, f s ≤ g s) →
    ∀ s, continuation t f s ≤ continuation t g s

/-- Universal finite-horizon upper envelope, uniform over ALL states.
A separate SOURCE bridge must prove that the bank's conditional
expectation is an instance of the continuation operator. -/
theorem recurse_le_value
    (flow value : ℕ → State → ℝ)
    (continuation : ℕ → (State → ℝ) → State → ℝ)
    (hmono : MonotoneContinuation continuation)
    (hsuper : ∀ t s,
      flow t s + continuation t (value (t + 1)) s ≤ value t s) :
    ∀ n t s, recurse flow value continuation n t s ≤ value t s := by
  intro n
  induction n with
  | zero =>
      intro t s
      rfl
  | succ n ih =>
      intro t s
      change
        flow t s +
            continuation t (recurse flow value continuation n (t + 1)) s
          ≤ value t s
      calc
        flow t s +
            continuation t (recurse flow value continuation n (t + 1)) s
            ≤ flow t s + continuation t (value (t + 1)) s := by
                exact add_le_add_left
                  (hmono t
                    (recurse flow value continuation n (t + 1))
                    (value (t + 1))
                    (ih (t + 1)) s)
                  (flow t s)
        _ ≤ value t s := hsuper t s

/-- Candidate equality is preserved by the finite recursion;
no monotonicity assumption is necessary for this equality. -/
theorem recurse_eq_value
    (flow value : ℕ → State → ℝ)
    (continuation : ℕ → (State → ℝ) → State → ℝ)
    (heq : ∀ t s,
      flow t s + continuation t (value (t + 1)) s = value t s) :
    ∀ n t s, recurse flow value continuation n t s = value t s := by
  intro n
  induction n with
  | zero =>
      intro t s
      rfl
  | succ n ih =>
      intro t s
      change
        flow t s +
            continuation t (recurse flow value continuation n (t + 1)) s
          = value t s
      have hfun :
          recurse flow value continuation n (t + 1) = value (t + 1) := by
        funext s'
        exact ih (t + 1) s'
      rw [hfun]
      exact heq t s

#print axioms recurse_le_value
#print axioms recurse_eq_value

end ProposedBankMonotoneBellmanEnvelope
end Ventura26LiquidityAllocation

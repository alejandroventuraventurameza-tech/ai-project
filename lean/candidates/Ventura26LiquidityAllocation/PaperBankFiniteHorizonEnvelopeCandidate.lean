import Mathlib

/-!
# Finite-horizon Bellman envelope: an algebraic kernel

This is an ABSTRACT, deterministic one-path recursion. It certifies only
the finite-horizon induction skeleton. The SOURCE bank model requires
conditional expectations, adapted discount factors, policy quantifiers,
and infinite-horizon limit arguments, which are NOT proved here.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedBankFiniteHorizonEnvelope

/-- Truncated continuation recursively retaining the terminal value. -/
def finiteHorizon (flow discount value : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, t => value t
  | n + 1, t =>
      flow t + discount t * finiteHorizon flow discount value n (t + 1)

/-- A nodewise Bellman supersolution bounds every finite recursion,
provided continuation weights are nonnegative. -/
theorem finite_horizon_le_value
    (flow discount value : ℕ → ℝ)
    (hdiscount : ∀ t, 0 ≤ discount t)
    (hsuper : ∀ t, flow t + discount t * value (t + 1) ≤ value t) :
    ∀ n t, finiteHorizon flow discount value n t ≤ value t := by
  intro n
  induction n with
  | zero =>
      intro t
      rfl
  | succ n ih =>
      intro t
      change
        flow t + discount t * finiteHorizon flow discount value n (t + 1)
          ≤ value t
      calc
        flow t + discount t * finiteHorizon flow discount value n (t + 1)
            ≤ flow t + discount t * value (t + 1) := by
              exact add_le_add_left
                (mul_le_mul_of_nonneg_left (ih (t + 1)) (hdiscount t))
                (flow t)
        _ ≤ value t := hsuper t

/-- A nodewise Bellman equality propagates through finite horizons.
This alone is NOT infinite-horizon optimality. -/
theorem finite_horizon_eq_value
    (flow discount value : ℕ → ℝ)
    (heq : ∀ t, flow t + discount t * value (t + 1) = value t) :
    ∀ n t, finiteHorizon flow discount value n t = value t := by
  intro n
  induction n with
  | zero =>
      intro t
      rfl
  | succ n ih =>
      intro t
      change
        flow t + discount t * finiteHorizon flow discount value n (t + 1)
          = value t
      rw [ih (t + 1)]
      exact heq t

#print axioms finite_horizon_le_value
#print axioms finite_horizon_eq_value

end ProposedBankFiniteHorizonEnvelope
end Ventura26LiquidityAllocation

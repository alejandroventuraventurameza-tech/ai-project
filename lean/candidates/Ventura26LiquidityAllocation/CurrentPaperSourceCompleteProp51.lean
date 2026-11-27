import Ventura26LiquidityAllocation.CurrentCompactBlock48Tail

/-!
# Compact-paper Proposition 5.1 — all three original source clauses

The original paper's Proposition 5.1 includes two finite-power
matrix norm bounds and their all-horizon/all-vector implication.
The provisional paper-scoped interface exposed the implication only.

This source-complete endpoint bundles the three clauses verbatim at
mathematical level. They are proved in the existing rational kernel
certificate. The fixed F0 is the literal decimal 6x6 matrix:
this theorem does NOT identify F0 as a SOURCE DSGE Jacobian.

Original text frozen at ai-project@bac3c6255da39cd1169a965df35bb5e9a230e6e8:
paper/body_compact_after.tex, prop:compact_exact_tail_power.
-/

open scoped NNReal Matrix Matrix.Norms.Operator

namespace Ventura26LiquidityAllocation
namespace CurrentPaperSource

/-- All clauses of compact-paper Proposition 5.1, including its two
strict finite-power bounds as mathematical conclusions, not hypotheses. -/
def prop51AllSourceClauses : Prop :=
  ‖CurrentCompact.exactDecimalF0 ^ 48‖ < (24 / 25 : ℝ) ∧
  (∀ r : ℕ, r < 48 →
    ‖CurrentCompact.exactDecimalF0 ^ r‖ < (61 / 10 : ℝ)) ∧
  (∀ (k : ℕ) (x : Fin 6 → ℝ),
    ‖(CurrentCompact.exactDecimalF0 ^ k) *ᵥ x‖ ≤
      (61 / 10 : ℝ) * (24 / 25 : ℝ) ^ (k / 48) * ‖x‖)

/-- Kernel proof of the full literal mathematical Proposition 5.1.
The rational finite-power conditions are certified by Lean, not assumed. -/
theorem prop51AllSourceClauses_proved : prop51AllSourceClauses := by
  dsimp only [prop51AllSourceClauses]
  refine ⟨CurrentCompact.prop51FiniteBound_proved.1,
    CurrentCompact.prop51FiniteBound_proved.2, ?_⟩
  intro k x
  exact CurrentCompact.prop51_unconditional_exact k x

#print axioms prop51AllSourceClauses_proved

end CurrentPaperSource
end Ventura26LiquidityAllocation

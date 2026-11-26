import Mathlib

/-!
# The current compact paper's logarithmic allocation loss

Source: ai-project@bac3c6255da39cd1169a965df35bb5e9a230e6e8
  paper/appendix_eight_results.tex, label `lem:allocation_loss_identity`.

The historical source-faithful Lean module proves the eleven-clause bundle
using `Real.log Yeff - Real.log Y`.  The compact paper *defines* its
loss as `Real.log (Yeff / Y)`.  This bridge proves equality, and
nonnegativity whenever the feasible output is positive and bounded above
by the efficient benchmark.

The upper bound is a hypothesis here, NOT established by this file;
the historical integrated module proves it from the two-type technology.
The bridge is a supporting theorem, not a certification of the entire
current-paper lemma or a competitive equilibrium.
-/

namespace Ventura26LiquidityAllocation.CurrentCompact

/-- The exact log-ratio and nonnegative-loss conclusions in Appendix A.1.4,
conditional on positivity and the physical efficient-output bound. -/
def currentCompactLogLossSpec : Prop :=
  ∀ (output efficientOutput : ℝ),
    0 < output →
    output ≤ efficientOutput →
    Real.log (efficientOutput / output) =
        Real.log efficientOutput - Real.log output ∧
      0 ≤ Real.log (efficientOutput / output)

/-- Convert the historical log difference to the compact paper's log
ratio, without assuming the log identity or nonnegative loss as premises. -/
theorem currentCompactLogLoss_exact : currentCompactLogLossSpec := by
  intro output efficientOutput hOutput hBound
  have hEff : 0 < efficientOutput := lt_of_lt_of_le hOutput hBound
  have hLogBound : Real.log output ≤ Real.log efficientOutput :=
    Real.log_le_log hOutput hBound
  constructor
  · exact Real.log_div hEff.ne' hOutput.ne'
  · rw [Real.log_div hEff.ne' hOutput.ne']
    linarith

#print axioms currentCompactLogLoss_exact

end Ventura26LiquidityAllocation.CurrentCompact

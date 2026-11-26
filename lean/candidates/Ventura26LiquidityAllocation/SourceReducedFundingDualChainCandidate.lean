import Ventura26LiquidityAllocation.SourceFundingDualPositiveLogRegularityCandidate

/-!
# Actual SOURCE reduced firm-L funding multiplier: differentiation along solutionLog

The original economic model defines localScalarReducedMap by inserting the
candidate 33-coordinate solutionLog into the genuine normalized L funding
dual. For a positive log-chart origin, the dual's differentiability is a
theorem, not an added assumption. Given differentiability of solutionLog,
the reduced dual is differentiable and its derivative obeys the exact
Fréchet chain rule. This does NOT assert such solutionLog exists or that
its derivatives solve the SOURCE economic equations.
-/

namespace Ventura26LiquidityAllocation

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Positivity of the actual log-chart origin and differentiability of
the SOURCE 33-coordinate solution are sufficient for local
differentiability of the exact SOURCE reduced funding multiplier. -/
theorem sourceReducedFundingDual_differentiableAt_of_solutionLog
    (P : Primitives S) (Z0 : LocalPrefixCoordinates)
    (hZ0 : LocalPrefixCoordinatesPositive Z0)
    (solutionLog : (Fin 5 → ℝ) → (Fin 33 → ℝ))
    (y : Fin 5 → ℝ)
    (hsolution : DifferentiableAt ℝ solutionLog y) :
    DifferentiableAt ℝ
      (localScalarReducedMap P Z0 solutionLog) y := by
  exact (sourceFundingDual_differentiableAt_positive_log
    P Z0 hZ0 (solutionLog y)).comp y hsolution

#print axioms sourceReducedFundingDual_differentiableAt_of_solutionLog

/-- Genuine SOURCE reduced-marginal Fréchet derivative is the
composition of the log-coordinate funding-dual derivative with the
derivative of the 33-row solution map. No synthetic Jacobian is used. -/
theorem sourceReducedFundingDual_fderiv_chain
    (P : Primitives S) (Z0 : LocalPrefixCoordinates)
    (hZ0 : LocalPrefixCoordinatesPositive Z0)
    (solutionLog : (Fin 5 → ℝ) → (Fin 33 → ℝ))
    (y : Fin 5 → ℝ)
    (hsolution : DifferentiableAt ℝ solutionLog y) :
    fderiv ℝ (localScalarReducedMap P Z0 solutionLog) y =
      (fderiv ℝ
        (fun z : Fin 33 → ℝ =>
          localNormalizedCollateralDualL P (localPrefixLogChart Z0 z))
        (solutionLog y)).comp (fderiv ℝ solutionLog y) := by
  exact ((sourceFundingDual_differentiableAt_positive_log
    P Z0 hZ0 (solutionLog y)).hasFDerivAt.comp
    y hsolution.hasFDerivAt).fderiv

#print axioms sourceReducedFundingDual_fderiv_chain

end Ventura26LiquidityAllocation

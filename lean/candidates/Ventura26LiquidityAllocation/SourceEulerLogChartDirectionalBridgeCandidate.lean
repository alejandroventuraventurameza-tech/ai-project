import Ventura26LiquidityAllocation.SourceEuler33RowDirectionalDerivativeCandidate

/-!
# Bridge to the genuine 33-dimensional SOURCE positive log chart

All objects here are defined from the actual localPrefixLogChart and
localReducedPrefixLogResidualVector in EconomicModel.lean. The forward
sheared log residual is defined on the SAME ordered Fin 33 rows using
localPrefixEquationOfIndex. No artificial Jacobian or detached matrix
is substituted for the actual SOURCE equations.

The derivative theorem is stated along an arbitrary path in log space
with explicit rowwise differentiability and shear coefficient
differentiability hypotheses. A Fréchet derivative identification and
the source-strength inverse norm enclosure remain OPEN.
-/

namespace Ventura26LiquidityAllocation

/-- The genuine SOURCE sheared 33-row system pulled back to the same
positive log chart used by the manuscript. -/
noncomputable def sourceNominalPledgeShearedLogResidualVector
    (branch : LocalPrefixBranch)
    (P : Primitives LocalBridgePhase) (I : InheritedState)
    (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : LocalBridgePhase)
    (tail : LocalPrefixContinuationRule) :
    (Fin 33 → ℝ) → (Fin 33 → ℝ) :=
  fun z row =>
    sourceNominalPledgeShearedResidual branch P I
      (localPrefixLogChart Z0 z) dateOne recurrent tail
      (localPrefixEquationOfIndex row)

/-- At EVERY log-coordinate vector the true SOURCE log residual and
sheared log residual are related by the exact economic state-dependent
invertible row operation. -/
theorem sourceNominalPledgeShearedLogResidualVector_eq_source_rowmap
    (branch : LocalPrefixBranch)
    (P : Primitives LocalBridgePhase) (I : InheritedState)
    (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : LocalBridgePhase)
    (tail : LocalPrefixContinuationRule)
    (z : Fin 33 → ℝ) (row : Fin 33) :
    sourceNominalPledgeShearedLogResidualVector branch P I Z0
      dateOne recurrent tail z row =
    sourceEulerRowsForward
      (sourceDateOneEulerShearCoefficient P
        (localPrefixLogChart Z0 z) dateOne recurrent tail .H)
      (sourceDateOneEulerShearCoefficient P
        (localPrefixLogChart Z0 z) dateOne recurrent tail .L)
      (localReducedPrefixResidual branch P I
        (localPrefixLogChart Z0 z) dateOne recurrent tail)
      (localPrefixEquationOfIndex row) := by
  exact congrFun
    (sourceNominalPledgeShearedResidual_eq_linear_rowmap
      branch P I (localPrefixLogChart Z0 z) dateOne recurrent tail)
    (localPrefixEquationOfIndex row)

#print axioms sourceNominalPledgeShearedLogResidualVector_eq_source_rowmap

/-- The precise manuscript SOURCE log-residual vector is the
corresponding component of its real 33-row residual map. -/
theorem sourceOriginalLogResidualVector_row_eq_source
    (branch : LocalPrefixBranch)
    (P : Primitives LocalBridgePhase) (I : InheritedState)
    (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : LocalBridgePhase)
    (tail : LocalPrefixContinuationRule)
    (z : Fin 33 → ℝ) (row : Fin 33) :
    localReducedPrefixLogResidualVector branch P I Z0
      dateOne recurrent tail z row =
    localReducedPrefixResidual branch P I
      (localPrefixLogChart Z0 z) dateOne recurrent tail
      (localPrefixEquationOfIndex row) := rfl

#print axioms sourceOriginalLogResidualVector_row_eq_source

/-- Along ANY differentiable log-coordinate path through the SOURCE
pledge row's zero set, the derivative of each of the actual 33 log
residuals after Euler shear is the original row-derivative vector
transformed by the same exact SOURCE rowmap at that point. -/
theorem sourceNominalPledgeShearedLogResidualVector_path_derivative
    (branch : LocalPrefixBranch)
    (P : Primitives LocalBridgePhase) (I : InheritedState)
    (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : LocalBridgePhase)
    (tail : LocalPrefixContinuationRule)
    (zpath : ℝ → (Fin 33 → ℝ))
    (t daH daL : ℝ)
    (dF : LocalPrefixEquation → ℝ)
    (hF : ∀ eqn, HasDerivAt
      (fun s => localReducedPrefixResidual branch P I
        (localPrefixLogChart Z0 (zpath s))
        dateOne recurrent tail eqn) (dF eqn) t)
    (haH : HasDerivAt
      (fun s => sourceDateOneEulerShearCoefficient P
        (localPrefixLogChart Z0 (zpath s))
        dateOne recurrent tail .H) daH t)
    (haL : HasDerivAt
      (fun s => sourceDateOneEulerShearCoefficient P
        (localPrefixLogChart Z0 (zpath s))
        dateOne recurrent tail .L) daL t)
    (hroot : localReducedPrefixResidual branch P I
      (localPrefixLogChart Z0 (zpath t))
      dateOne recurrent tail .commonPledgeOne = 0)
    (row : Fin 33) :
    HasDerivAt
      (fun s => sourceNominalPledgeShearedLogResidualVector branch P I Z0
        dateOne recurrent tail (zpath s) row)
      (sourceEulerRowsForward
        (sourceDateOneEulerShearCoefficient P
          (localPrefixLogChart Z0 (zpath t))
          dateOne recurrent tail .H)
        (sourceDateOneEulerShearCoefficient P
          (localPrefixLogChart Z0 (zpath t))
          dateOne recurrent tail .L)
        dF (localPrefixEquationOfIndex row)) t := by
  exact sourceNominalPledgeShearedResidual_33row_path_derivative
    branch P I
    (fun s => localPrefixLogChart Z0 (zpath s))
    dateOne recurrent tail
    t daH daL dF hF haH haL hroot (localPrefixEquationOfIndex row)

#print axioms sourceNominalPledgeShearedLogResidualVector_path_derivative

end Ventura26LiquidityAllocation

import Ventura26LiquidityAllocation.SourceEulerLogChartRowIndexCandidate
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Frechet derivative of the genuine SOURCE Euler log shears

The result is conditional on actual Frechet differentiability of
the original economic rows and the state-dependent coefficients.
No Jacobian inverse, economic regularity, or equilibrium existence
is asserted.
-/

namespace Ventura26LiquidityAllocation

theorem sourceShear_hasFDerivAt_at_pledge_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e a p : E → ℝ) (x : E)
    (de da dp : E →L[ℝ] ℝ)
    (he : HasFDerivAt e de x)
    (ha : HasFDerivAt a da x)
    (hp : HasFDerivAt p dp x)
    (hroot : p x = 0) :
    HasFDerivAt (fun y => e y + a y * p y)
      (de + (a x) • dp) x := by
  simpa [hroot, Pi.add_apply, Pi.mul_apply] using
    (he.add (ha.mul hp))

#print axioms sourceShear_hasFDerivAt_at_pledge_zero

theorem sourceLogEulerH_row_shear
    (branch : LocalPrefixBranch)
    (P : Primitives LocalBridgePhase) (I : InheritedState)
    (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : LocalBridgePhase)
    (tail : LocalPrefixContinuationRule)
    (z : Fin 33 → ℝ) :
    sourceNominalPledgeShearedLogResidualVector branch P I Z0
      dateOne recurrent tail z (19 : Fin 33) =
    localReducedPrefixLogResidualVector branch P I Z0
      dateOne recurrent tail z (19 : Fin 33) +
    sourceDateOneEulerShearCoefficient P
      (localPrefixLogChart Z0 z) dateOne recurrent tail .H *
    localReducedPrefixLogResidualVector branch P I Z0
      dateOne recurrent tail z (21 : Fin 33) := by
  rw [sourceNominalPledgeShearedLogResidualVector_eq_source_rowmap]
  rfl

#print axioms sourceLogEulerH_row_shear

theorem sourceLogEulerL_row_shear
    (branch : LocalPrefixBranch)
    (P : Primitives LocalBridgePhase) (I : InheritedState)
    (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : LocalBridgePhase)
    (tail : LocalPrefixContinuationRule)
    (z : Fin 33 → ℝ) :
    sourceNominalPledgeShearedLogResidualVector branch P I Z0
      dateOne recurrent tail z (20 : Fin 33) =
    localReducedPrefixLogResidualVector branch P I Z0
      dateOne recurrent tail z (20 : Fin 33) +
    sourceDateOneEulerShearCoefficient P
      (localPrefixLogChart Z0 z) dateOne recurrent tail .L *
    localReducedPrefixLogResidualVector branch P I Z0
      dateOne recurrent tail z (21 : Fin 33) := by
  rw [sourceNominalPledgeShearedLogResidualVector_eq_source_rowmap]
  rfl

#print axioms sourceLogEulerL_row_shear

end Ventura26LiquidityAllocation

import Ventura26LiquidityAllocation.SourceEulerLogFullJacobianShearCandidate

/-!
# Conditional invertibility transport for the actual SOURCE 33-row Jacobian

The coefficient-dependent SOURCE shears are evaluated at a genuine
common-pledge root. The derivative coefficient terms then vanish.
All 33 row derivatives refer to the genuine economic SOURCE log chart.
This module proves only equivalence of bijectivity, NOT bijectivity itself
and NOT existence or uniqueness of a dynamic competitive equilibrium.
-/

namespace Ventura26LiquidityAllocation

/-- Algebraic invertibility transport for a matrix of continuous-linear
derivative rows, with genuine SOURCE 33-equation indexing. -/
theorem sourceEulerRowsFrechetForward_bijective_iff
    (aH aL : ℝ)
    (dF : LocalPrefixEquation → (Fin 33 → ℝ) →L[ℝ] ℝ) :
    Function.Bijective
      (fun h : Fin 33 → ℝ =>
        fun row : LocalPrefixEquation =>
          sourceEulerRowsFrechetForward aH aL dF row h) ↔
    Function.Bijective
      (fun h : Fin 33 → ℝ =>
        fun row : LocalPrefixEquation => dF row h) := by
  exact sourceEulerJacobian_bijective_iff_of_rowmap
    (fun h : Fin 33 → ℝ => fun row : LocalPrefixEquation => dF row h)
    (fun h : Fin 33 → ℝ => fun row : LocalPrefixEquation =>
      sourceEulerRowsFrechetForward aH aL dF row h)
    aH aL
    (by
      intro h
      funext row
      exact sourceEulerRowsFrechetForward_apply aH aL dF h row)

#print axioms sourceEulerRowsFrechetForward_bijective_iff

/-- Real economic SOURCE 33-row Jacobian of the sheared log residual
is bijective iff that of the original log residual is bijective,
provided all 33 original rows and both shear coefficients are
Frechet differentiable at a genuine common-pledge root. -/
theorem sourceEconomicLogJacobian_bijective_iff_at_pledge_zero
    (branch : LocalPrefixBranch)
    (P : Primitives LocalBridgePhase) (I : InheritedState)
    (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : LocalBridgePhase)
    (tail : LocalPrefixContinuationRule)
    (zstar : Fin 33 → ℝ)
    (hF : ∀ row : LocalPrefixEquation,
      DifferentiableAt ℝ
        (fun z => localReducedPrefixResidual branch P I
          (localPrefixLogChart Z0 z) dateOne recurrent tail row)
        zstar)
    (haH : DifferentiableAt ℝ
      (fun z => sourceDateOneEulerShearCoefficient P
        (localPrefixLogChart Z0 z) dateOne recurrent tail .H) zstar)
    (haL : DifferentiableAt ℝ
      (fun z => sourceDateOneEulerShearCoefficient P
        (localPrefixLogChart Z0 z) dateOne recurrent tail .L) zstar)
    (hroot : localReducedPrefixResidual branch P I
      (localPrefixLogChart Z0 zstar)
      dateOne recurrent tail .commonPledgeOne = 0) :
    Function.Bijective
      (fun h : Fin 33 → ℝ => fun row : LocalPrefixEquation =>
        (fderiv ℝ (fun z => sourceNominalPledgeShearedResidual branch P I
          (localPrefixLogChart Z0 z) dateOne recurrent tail row) zstar) h) ↔
    Function.Bijective
      (fun h : Fin 33 → ℝ => fun row : LocalPrefixEquation =>
        (fderiv ℝ (fun z => localReducedPrefixResidual branch P I
          (localPrefixLogChart Z0 z) dateOne recurrent tail row) zstar) h) := by
  let dF : LocalPrefixEquation → (Fin 33 → ℝ) →L[ℝ] ℝ :=
    fun row => fderiv ℝ
      (fun z => localReducedPrefixResidual branch P I
        (localPrefixLogChart Z0 z) dateOne recurrent tail row) zstar
  let aH : ℝ := sourceDateOneEulerShearCoefficient P
    (localPrefixLogChart Z0 zstar) dateOne recurrent tail .H
  let aL : ℝ := sourceDateOneEulerShearCoefficient P
    (localPrefixLogChart Z0 zstar) dateOne recurrent tail .L
  have hall := sourceNominalPledgeShearedLog_all_rows_hasFDerivAt
    branch P I Z0 dateOne recurrent tail zstar
    dF
    (fderiv ℝ (fun z => sourceDateOneEulerShearCoefficient P
      (localPrefixLogChart Z0 z) dateOne recurrent tail .H) zstar)
    (fderiv ℝ (fun z => sourceDateOneEulerShearCoefficient P
      (localPrefixLogChart Z0 z) dateOne recurrent tail .L) zstar)
    (by
      intro row
      exact (hF row).hasFDerivAt)
    haH.hasFDerivAt haL.hasFDerivAt hroot
  apply sourceEulerJacobian_bijective_iff_of_rowmap
    (fun h : Fin 33 → ℝ => fun row : LocalPrefixEquation => dF row h)
    (fun h : Fin 33 → ℝ => fun row : LocalPrefixEquation =>
      (fderiv ℝ (fun z => sourceNominalPledgeShearedResidual branch P I
        (localPrefixLogChart Z0 z) dateOne recurrent tail row) zstar) h)
    aH aL
  intro h
  funext row
  rw [(hall row).fderiv]
  exact sourceEulerRowsFrechetForward_apply aH aL dF h row

#print axioms sourceEconomicLogJacobian_bijective_iff_at_pledge_zero

end Ventura26LiquidityAllocation

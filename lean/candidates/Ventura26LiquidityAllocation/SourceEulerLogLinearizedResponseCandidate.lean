import Ventura26LiquidityAllocation.SourceEulerLogJacobianBijectiveCandidate

/-!
# True SOURCE log-chart linearized response transport

At the genuine SOURCE common-pledge root, the 33-row sheared Jacobian
is the SOURCE row shear of the original 33-row economic Jacobian.

This file strengthens conditional invertibility transport: for EVERY
candidate direction, the ORIGINAL linearized equation with RHS b holds
if and only if the SHEARED equation with correspondingly sheared RHS
holds. This is not an economic Jacobian inverse nor an IRF result.
-/

namespace Ventura26LiquidityAllocation

/-- The actual two-sided inverse SOURCE row shear reflects and
preserves equality between arbitrary 33-row residual vectors. -/
theorem sourceEulerRowsForward_eq_iff
    (aH aL : ℝ) (u v : LocalPrefixEquation → ℝ) :
    sourceEulerRowsForward aH aL u =
      sourceEulerRowsForward aH aL v ↔ u = v := by
  constructor
  · intro h
    have hb := congrArg (sourceEulerRowsBackward aH aL) h
    simpa only [sourceEulerRows_backward_forward] using hb
  · intro h
    rw [h]

#print axioms sourceEulerRowsForward_eq_iff

/-- A consistent invertible row shear preserves the entire solution
set of any given linearized response equation, not only uniqueness. -/
theorem sourceEulerJacobian_linearized_rhs_transport
    {U : Type*}
    (J Jtilde : U → LocalPrefixEquation → ℝ)
    (aH aL : ℝ)
    (hrow : ∀ u, Jtilde u = sourceEulerRowsForward aH aL (J u))
    (u : U) (b : LocalPrefixEquation → ℝ) :
    (Jtilde u = sourceEulerRowsForward aH aL b) ↔
      J u = b := by
  rw [hrow u]
  exact sourceEulerRowsForward_eq_iff aH aL (J u) b

#print axioms sourceEulerJacobian_linearized_rhs_transport

/-- In the genuine SOURCE economic system on its original positive
log chart, any prescribed first-order perturbation b on the original
33 equation labels gives EXACTLY the same coordinate response
directions as the transformed system driven by the sheared b.

All original economic rows and both economic shear coefficients must
be Frechet differentiable at the supplied point. The common-pledge
row must vanish there. Neither an actual root of the remaining rows
nor an invertible Jacobian is assumed. -/
theorem sourceEconomicLog_linearized_response_iff_at_pledge_zero
    (branch : LocalPrefixBranch)
    (P : Primitives LocalBridgePhase) (I : InheritedState)
    (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : LocalBridgePhase)
    (tail : LocalPrefixContinuationRule)
    (zstar h : Fin 33 → ℝ)
    (b : LocalPrefixEquation → ℝ)
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
    ((fun row : LocalPrefixEquation =>
      (fderiv ℝ (fun z =>
        sourceNominalPledgeShearedResidual branch P I
          (localPrefixLogChart Z0 z) dateOne recurrent tail row)
        zstar) h) =
      sourceEulerRowsForward
        (sourceDateOneEulerShearCoefficient P
          (localPrefixLogChart Z0 zstar) dateOne recurrent tail .H)
        (sourceDateOneEulerShearCoefficient P
          (localPrefixLogChart Z0 zstar) dateOne recurrent tail .L) b) ↔
    ((fun row : LocalPrefixEquation =>
      (fderiv ℝ (fun z =>
        localReducedPrefixResidual branch P I
          (localPrefixLogChart Z0 z) dateOne recurrent tail row)
        zstar) h) = b) := by
  let dF : LocalPrefixEquation → (Fin 33 → ℝ) →L[ℝ] ℝ :=
    fun row => fderiv ℝ
      (fun z => localReducedPrefixResidual branch P I
        (localPrefixLogChart Z0 z) dateOne recurrent tail row) zstar
  let aH : ℝ := sourceDateOneEulerShearCoefficient P
    (localPrefixLogChart Z0 zstar) dateOne recurrent tail .H
  let aL : ℝ := sourceDateOneEulerShearCoefficient P
    (localPrefixLogChart Z0 zstar) dateOne recurrent tail .L
  have hall := sourceNominalPledgeShearedLog_all_rows_hasFDerivAt
    branch P I Z0 dateOne recurrent tail zstar dF
    (fderiv ℝ (fun z => sourceDateOneEulerShearCoefficient P
      (localPrefixLogChart Z0 z) dateOne recurrent tail .H) zstar)
    (fderiv ℝ (fun z => sourceDateOneEulerShearCoefficient P
      (localPrefixLogChart Z0 z) dateOne recurrent tail .L) zstar)
    (by
      intro row
      exact (hF row).hasFDerivAt)
    haH.hasFDerivAt haL.hasFDerivAt hroot
  have hrow : ∀ dir : Fin 33 → ℝ,
      (fun row : LocalPrefixEquation =>
        (fderiv ℝ (fun z =>
          sourceNominalPledgeShearedResidual branch P I
            (localPrefixLogChart Z0 z) dateOne recurrent tail row)
          zstar) dir) =
      sourceEulerRowsForward aH aL
        (fun row : LocalPrefixEquation => dF row dir) := by
    intro dir
    funext row
    rw [(hall row).fderiv]
    exact sourceEulerRowsFrechetForward_apply aH aL dF dir row
  exact sourceEulerJacobian_linearized_rhs_transport
    (fun dir : Fin 33 → ℝ =>
      fun row : LocalPrefixEquation => dF row dir)
    (fun dir : Fin 33 → ℝ =>
      fun row : LocalPrefixEquation =>
        (fderiv ℝ (fun z =>
          sourceNominalPledgeShearedResidual branch P I
            (localPrefixLogChart Z0 z) dateOne recurrent tail row)
          zstar) dir)
    aH aL hrow h b

#print axioms sourceEconomicLog_linearized_response_iff_at_pledge_zero

end Ventura26LiquidityAllocation

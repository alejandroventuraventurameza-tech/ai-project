import Ventura26LiquidityAllocation.SourceFirmEulerThreeRowZeroSetCandidate

/-!
# Derivative of a genuine SOURCE date-one Euler shear on a pledge root

Unlike a numerical 33x33 finite-difference Jacobian, this uses the Lean
calculus theorem HasDerivAt.mul along an arbitrary REAL differentiable
path of SOURCE coordinates. The state-dependent shear coefficient need
NOT be locally constant. At a SOURCE pledge root the coefficient-
derivative term vanishes by the exact product rule.

Hypotheses explicitly supply differentiability of the ORIGINAL economic
SOURCE residuals and of the shear coefficient along the path. This
module proves neither those differentiability hypotheses nor a 33x33
full SOURCE Jacobian certificate or a SOURCE/Python functional bridge.
-/

namespace Ventura26LiquidityAllocation

/-- Generic exact scalar-path product-rule identity at a zero of p. -/
theorem sourceShear_derivative_at_pledge_zero
    (e a p : ℝ → ℝ) (t de da dp : ℝ)
    (he : HasDerivAt e de t)
    (ha : HasDerivAt a da t)
    (hp : HasDerivAt p dp t)
    (hroot : p t = 0) :
    HasDerivAt (fun x => e x + a x * p x)
      (de + a t * dp) t := by
  have h : HasDerivAt (fun x => e x + a x * p x)
      (de + (da * p t + a t * dp)) t := by
    simpa only [Pi.add_apply, Pi.mul_apply] using he.add (ha.mul hp)
  simpa only [hroot, mul_zero, zero_add] using h

#print axioms sourceShear_derivative_at_pledge_zero

/-- Original SOURCE date-one binding Euler evaluated along arbitrary
coordinates Z(t), with the genuine SOURCE continuation tail fixed. -/
noncomputable def sourceFirmEulerOriginalPath
    (P : Primitives LocalBridgePhase) (dateOne recurrent : LocalBridgePhase)
    (tail : LocalPrefixContinuationRule)
    (i : FirmType) (Zpath : ℝ → LocalPrefixCoordinates) : ℝ → ℝ :=
  fun t => localReducedFirmCapitalEulerResidual .binding P
    (localPrefixDateOneData P (Zpath t) dateOne recurrent tail) i

/-- Genuine SOURCE common pledge residual along the same path. -/
noncomputable def sourceFirmCommonPledgePath
    (branch : LocalPrefixBranch)
    (P : Primitives LocalBridgePhase) (I : InheritedState)
    (dateOne recurrent : LocalBridgePhase)
    (tail : LocalPrefixContinuationRule)
    (Zpath : ℝ → LocalPrefixCoordinates) : ℝ → ℝ :=
  fun t => localReducedPrefixResidual branch P I
    (Zpath t) dateOne recurrent tail .commonPledgeOne

/-- The genuinely state-dependent SOURCE coefficient of the Euler
nominal-pledge shear, not a constant imported from Python. -/
noncomputable def sourceFirmShearCoefficientPath
    (P : Primitives LocalBridgePhase) (dateOne recurrent : LocalBridgePhase)
    (tail : LocalPrefixContinuationRule)
    (i : FirmType) (Zpath : ℝ → LocalPrefixCoordinates) : ℝ → ℝ :=
  fun t =>
    let d := localPrefixDateOneData P (Zpath t) dateOne recurrent tail
    P.pledgeability i *
      (localPrefixEntrepreneurSDF P d i / d.nextControls.inflation -
        1 / d.controls.loanRate)

/-- Alternative SOURCE Euler evaluated with the actual common nominal
pledge coordinate. -/
noncomputable def sourceFirmNominalEulerPath
    (P : Primitives LocalBridgePhase) (dateOne recurrent : LocalBridgePhase)
    (tail : LocalPrefixContinuationRule)
    (i : FirmType) (Zpath : ℝ → LocalPrefixCoordinates) : ℝ → ℝ :=
  fun t => sourceFirmEulerNominalPledge P
    (localPrefixDateOneData P (Zpath t) dateOne recurrent tail) i
    (Zpath t).stateTwo.commonPledgeValue

/-- Identity between genuine SOURCE paths for ALL t, without supposing
a root, differentiability, or a numerical Python transcription. -/
theorem sourceFirmNominalEulerPath_shear_identity
    (branch : LocalPrefixBranch)
    (P : Primitives LocalBridgePhase) (I : InheritedState)
    (dateOne recurrent : LocalBridgePhase)
    (tail : LocalPrefixContinuationRule) (i : FirmType)
    (Zpath : ℝ → LocalPrefixCoordinates) :
    sourceFirmNominalEulerPath P dateOne recurrent tail i Zpath =
    (fun t => sourceFirmEulerOriginalPath P dateOne recurrent tail i Zpath t +
      sourceFirmShearCoefficientPath P dateOne recurrent tail i Zpath t *
      sourceFirmCommonPledgePath branch P I dateOne recurrent tail Zpath t) := by
  funext t
  exact sourceFirmEuler_dateOne_nominalPledge_shear branch P I
    (Zpath t) dateOne recurrent tail i

#print axioms sourceFirmNominalEulerPath_shear_identity

/-- At a root of the ORIGINAL SOURCE pledge row, the derivative of the
state-dependent Euler shear is exactly the original Euler derivative
plus the current shear coefficient times the SOURCE pledge derivative.
The Da*pledge term disappears without assuming Da=0. -/
theorem sourceFirmNominalEulerPath_derivative_at_pledge_zero
    (branch : LocalPrefixBranch)
    (P : Primitives LocalBridgePhase) (I : InheritedState)
    (dateOne recurrent : LocalBridgePhase)
    (tail : LocalPrefixContinuationRule) (i : FirmType)
    (Zpath : ℝ → LocalPrefixCoordinates) (t de da dp : ℝ)
    (he : HasDerivAt
      (sourceFirmEulerOriginalPath P dateOne recurrent tail i Zpath) de t)
    (ha : HasDerivAt
      (sourceFirmShearCoefficientPath P dateOne recurrent tail i Zpath) da t)
    (hp : HasDerivAt
      (sourceFirmCommonPledgePath branch P I dateOne recurrent tail Zpath) dp t)
    (hroot : sourceFirmCommonPledgePath branch P I
      dateOne recurrent tail Zpath t = 0) :
    HasDerivAt (sourceFirmNominalEulerPath P dateOne recurrent tail i Zpath)
      (de + sourceFirmShearCoefficientPath P dateOne recurrent tail i Zpath t *
        dp) t := by
  rw [sourceFirmNominalEulerPath_shear_identity branch P I
    dateOne recurrent tail i Zpath]
  exact sourceShear_derivative_at_pledge_zero
    (sourceFirmEulerOriginalPath P dateOne recurrent tail i Zpath)
    (sourceFirmShearCoefficientPath P dateOne recurrent tail i Zpath)
    (sourceFirmCommonPledgePath branch P I dateOne recurrent tail Zpath)
    t de da dp he ha hp hroot

#print axioms sourceFirmNominalEulerPath_derivative_at_pledge_zero

end Ventura26LiquidityAllocation

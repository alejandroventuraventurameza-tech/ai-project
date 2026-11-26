import Ventura26LiquidityAllocation.SourceEulerJacobianBijectiveTransportCandidate
import Ventura26LiquidityAllocation.SourceFirmEulerShearDerivativeCandidate

/-!
# Genuine SOURCE 33-row directional derivative identity at a pledge root

For an arbitrary path of REAL 33-coordinate SOURCE data, assume the
original SOURCE rows and the two economic shear coefficients have real
derivatives along that path.  The proof uses the ALREADY kernel-checked
SOURCE functional identity at all Z and the kernel-checked scalar
root-product rule, and shows the derivative of EACH of the 33 sheared
SOURCE rows is the invertible SOURCE linear rowmap of the 33 derivatives.

We do not derive the supplied economic regularity assumptions, nor
identify the Python chart/P0 or claim a 33-by-33 Jacobian inverse.
-/

namespace Ventura26LiquidityAllocation

/-- General variable-coefficient double shear: at a zero of the
underlying pledge row, its 33 directional derivatives are exactly
the CONSTANT-at-the-root linear shear of the 33 original derivatives. -/
theorem sourceEulerRowsForward_path_derivative_at_pledge_zero
    (F : ℝ → LocalPrefixEquation → ℝ)
    (aH aL : ℝ → ℝ)
    (t daH daL : ℝ)
    (dF : LocalPrefixEquation → ℝ)
    (hF : ∀ row, HasDerivAt (fun s => F s row) (dF row) t)
    (haH : HasDerivAt aH daH t)
    (haL : HasDerivAt aL daL t)
    (hroot : F t .commonPledgeOne = 0)
    (row : LocalPrefixEquation) :
    HasDerivAt (fun s => sourceEulerRowsForward
      (aH s) (aL s) (F s) row)
      (sourceEulerRowsForward (aH t) (aL t) dF row) t := by
  cases row <;> simp only [sourceEulerRowsForward] <;> try { exact hF _ }
  · exact sourceShear_derivative_at_pledge_zero
      (fun s => F s .firmCapitalEulerOneH) aH
      (fun s => F s .commonPledgeOne)
      t (dF .firmCapitalEulerOneH) daH (dF .commonPledgeOne)
      (hF .firmCapitalEulerOneH) haH (hF .commonPledgeOne) hroot
  · exact sourceShear_derivative_at_pledge_zero
      (fun s => F s .firmCapitalEulerOneL) aL
      (fun s => F s .commonPledgeOne)
      t (dF .firmCapitalEulerOneL) daL (dF .commonPledgeOne)
      (hF .firmCapitalEulerOneL) haL (hF .commonPledgeOne) hroot

#print axioms sourceEulerRowsForward_path_derivative_at_pledge_zero

/-- The full true SOURCE sheared residual has the predicted directional
derivative at a genuine common-pledge root, provided ALL of its original
economic rows and the two state-dependent coefficients are differentiable
along the chosen coordinate path. -/
theorem sourceNominalPledgeShearedResidual_33row_path_derivative
    (branch : LocalPrefixBranch)
    (P : Primitives LocalBridgePhase) (I : InheritedState)
    (Zpath : ℝ → LocalPrefixCoordinates)
    (dateOne recurrent : LocalBridgePhase)
    (tail : LocalPrefixContinuationRule)
    (t daH daL : ℝ)
    (dF : LocalPrefixEquation → ℝ)
    (hF : ∀ row, HasDerivAt
      (fun s => localReducedPrefixResidual branch P I
        (Zpath s) dateOne recurrent tail row) (dF row) t)
    (haH : HasDerivAt
      (fun s => sourceDateOneEulerShearCoefficient P
        (Zpath s) dateOne recurrent tail .H) daH t)
    (haL : HasDerivAt
      (fun s => sourceDateOneEulerShearCoefficient P
        (Zpath s) dateOne recurrent tail .L) daL t)
    (hroot : localReducedPrefixResidual branch P I
      (Zpath t) dateOne recurrent tail .commonPledgeOne = 0)
    (row : LocalPrefixEquation) :
    HasDerivAt
      (fun s => sourceNominalPledgeShearedResidual branch P I
        (Zpath s) dateOne recurrent tail row)
      (sourceEulerRowsForward
        (sourceDateOneEulerShearCoefficient P
          (Zpath t) dateOne recurrent tail .H)
        (sourceDateOneEulerShearCoefficient P
          (Zpath t) dateOne recurrent tail .L)
        dF row) t := by
  have hid :
      (fun s => sourceNominalPledgeShearedResidual branch P I
        (Zpath s) dateOne recurrent tail row) =
      (fun s => sourceEulerRowsForward
        (sourceDateOneEulerShearCoefficient P
          (Zpath s) dateOne recurrent tail .H)
        (sourceDateOneEulerShearCoefficient P
          (Zpath s) dateOne recurrent tail .L)
        (localReducedPrefixResidual branch P I
          (Zpath s) dateOne recurrent tail) row) := by
    funext s
    exact congrFun (sourceNominalPledgeShearedResidual_eq_linear_rowmap
      branch P I (Zpath s) dateOne recurrent tail) row
  rw [hid]
  exact sourceEulerRowsForward_path_derivative_at_pledge_zero
    (fun s => localReducedPrefixResidual branch P I
      (Zpath s) dateOne recurrent tail)
    (fun s => sourceDateOneEulerShearCoefficient P
      (Zpath s) dateOne recurrent tail .H)
    (fun s => sourceDateOneEulerShearCoefficient P
      (Zpath s) dateOne recurrent tail .L)
    t daH daL dF hF haH haL hroot row

#print axioms sourceNominalPledgeShearedResidual_33row_path_derivative

end Ventura26LiquidityAllocation

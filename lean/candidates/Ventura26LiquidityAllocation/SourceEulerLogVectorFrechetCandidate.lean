import Ventura26LiquidityAllocation.SourceEulerLogJacobianBijectiveCandidate
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Genuine SOURCE 33-vector Frechet derivative after economic Euler shear

The original economic model's log residual is R^33 -> R^33, not just
a collection of scalar rows. This module assembles the previously
verified SOURCE rowwise derivatives using Mathlib's finite Pi theorem.

The result identifies the genuine fderiv of the WHOLE sheared residual
vector with the continuous-linear map assembled from the exact
SOURCE Euler shear of the original scalar row derivatives.

It does not prove the economic input differentiability assumptions,
the existence of a common-pledge root or Jacobian nonsingularity.
-/

namespace Ventura26LiquidityAllocation

/-- Fréchet differentiability of the entire SOURCE 33-row sheared
log residual vector. The derivative is a genuine bounded linear map
from 33 log-coordinate perturbations into 33 residual perturbations. -/
theorem sourceNominalPledgeShearedLog_vector_hasFDerivAt
    (branch : LocalPrefixBranch)
    (P : Primitives LocalBridgePhase) (I : InheritedState)
    (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : LocalBridgePhase)
    (tail : LocalPrefixContinuationRule)
    (zstar : Fin 33 → ℝ)
    (dF : LocalPrefixEquation → (Fin 33 → ℝ) →L[ℝ] ℝ)
    (daH daL : (Fin 33 → ℝ) →L[ℝ] ℝ)
    (hF : ∀ eqn : LocalPrefixEquation,
      HasFDerivAt
        (fun z => localReducedPrefixResidual branch P I
          (localPrefixLogChart Z0 z) dateOne recurrent tail eqn)
        (dF eqn) zstar)
    (haH : HasFDerivAt
      (fun z => sourceDateOneEulerShearCoefficient P
        (localPrefixLogChart Z0 z) dateOne recurrent tail .H)
      daH zstar)
    (haL : HasFDerivAt
      (fun z => sourceDateOneEulerShearCoefficient P
        (localPrefixLogChart Z0 z) dateOne recurrent tail .L)
      daL zstar)
    (hroot : localReducedPrefixResidual branch P I
      (localPrefixLogChart Z0 zstar)
      dateOne recurrent tail .commonPledgeOne = 0) :
    HasFDerivAt
      (sourceNominalPledgeShearedLogResidualVector branch P I Z0
        dateOne recurrent tail)
      (ContinuousLinearMap.pi (fun row : Fin 33 =>
        sourceEulerRowsFrechetForward
          (sourceDateOneEulerShearCoefficient P
            (localPrefixLogChart Z0 zstar) dateOne recurrent tail .H)
          (sourceDateOneEulerShearCoefficient P
            (localPrefixLogChart Z0 zstar) dateOne recurrent tail .L)
          dF (localPrefixEquationOfIndex row)))
      zstar := by
  have hall := sourceNominalPledgeShearedLog_all_rows_hasFDerivAt
    branch P I Z0 dateOne recurrent tail zstar
    dF daH daL hF haH haL hroot
  change HasFDerivAt
    (fun z row =>
      sourceNominalPledgeShearedResidual branch P I
        (localPrefixLogChart Z0 z) dateOne recurrent tail
        (localPrefixEquationOfIndex row))
    (ContinuousLinearMap.pi (fun row : Fin 33 =>
      sourceEulerRowsFrechetForward
        (sourceDateOneEulerShearCoefficient P
          (localPrefixLogChart Z0 zstar) dateOne recurrent tail .H)
        (sourceDateOneEulerShearCoefficient P
          (localPrefixLogChart Z0 zstar) dateOne recurrent tail .L)
        dF (localPrefixEquationOfIndex row)))
    zstar
  apply hasFDerivAt_pi.mpr
  intro row
  exact hall (localPrefixEquationOfIndex row)

#print axioms sourceNominalPledgeShearedLog_vector_hasFDerivAt

/-- Exact SOURCE 33-by-33 operator identity in the paper's own
positive log chart, now using fderiv of the actual vector residual.
All economic regularity conditions remain explicit hypotheses. -/
theorem sourceNominalPledgeShearedLog_vector_fderiv_eq
    (branch : LocalPrefixBranch)
    (P : Primitives LocalBridgePhase) (I : InheritedState)
    (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : LocalBridgePhase)
    (tail : LocalPrefixContinuationRule)
    (zstar : Fin 33 → ℝ)
    (hF : ∀ eqn : LocalPrefixEquation,
      DifferentiableAt ℝ
        (fun z => localReducedPrefixResidual branch P I
          (localPrefixLogChart Z0 z) dateOne recurrent tail eqn) zstar)
    (haH : DifferentiableAt ℝ
      (fun z => sourceDateOneEulerShearCoefficient P
        (localPrefixLogChart Z0 z) dateOne recurrent tail .H) zstar)
    (haL : DifferentiableAt ℝ
      (fun z => sourceDateOneEulerShearCoefficient P
        (localPrefixLogChart Z0 z) dateOne recurrent tail .L) zstar)
    (hroot : localReducedPrefixResidual branch P I
      (localPrefixLogChart Z0 zstar)
      dateOne recurrent tail .commonPledgeOne = 0) :
    fderiv ℝ
      (sourceNominalPledgeShearedLogResidualVector branch P I Z0
        dateOne recurrent tail) zstar =
      ContinuousLinearMap.pi (fun row : Fin 33 =>
        sourceEulerRowsFrechetForward
          (sourceDateOneEulerShearCoefficient P
            (localPrefixLogChart Z0 zstar) dateOne recurrent tail .H)
          (sourceDateOneEulerShearCoefficient P
            (localPrefixLogChart Z0 zstar) dateOne recurrent tail .L)
          (fun eqn => fderiv ℝ
            (fun z => localReducedPrefixResidual branch P I
              (localPrefixLogChart Z0 z) dateOne recurrent tail eqn)
            zstar)
          (localPrefixEquationOfIndex row)) := by
  exact (sourceNominalPledgeShearedLog_vector_hasFDerivAt
    branch P I Z0 dateOne recurrent tail zstar
    (fun eqn => fderiv ℝ
      (fun z => localReducedPrefixResidual branch P I
        (localPrefixLogChart Z0 z) dateOne recurrent tail eqn)
      zstar)
    (fderiv ℝ (fun z => sourceDateOneEulerShearCoefficient P
      (localPrefixLogChart Z0 z) dateOne recurrent tail .H) zstar)
    (fderiv ℝ (fun z => sourceDateOneEulerShearCoefficient P
      (localPrefixLogChart Z0 z) dateOne recurrent tail .L) zstar)
    (fun eqn => (hF eqn).hasFDerivAt)
    haH.hasFDerivAt haL.hasFDerivAt hroot).fderiv

#print axioms sourceNominalPledgeShearedLog_vector_fderiv_eq

end Ventura26LiquidityAllocation

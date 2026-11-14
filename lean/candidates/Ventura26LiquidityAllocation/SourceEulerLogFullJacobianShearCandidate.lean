import Ventura26LiquidityAllocation.SourceEulerLogEconomicFrechetCandidate

/-!
# Complete SOURCE Euler shear: all 33 Frechet derivative rows

This candidate works on the genuine SOURCE residuals and the original
positive log chart. Regularity is an explicit input, not inferred.
The proposition is rowwise for all 33 actual economic equation labels.
It does not assert invertibility of the economic Jacobian.
-/

namespace Ventura26LiquidityAllocation

/-- The genuine SOURCE 33-row economic Frechet derivatives after the
double Euler shear are the SOURCE rowmap of the original derivatives,
at any point where the common pledge residual vanishes. -/
theorem sourceNominalPledgeShearedLog_all_rows_hasFDerivAt
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
    ∀ eqn : LocalPrefixEquation,
      HasFDerivAt
        (fun z => sourceNominalPledgeShearedResidual branch P I
          (localPrefixLogChart Z0 z) dateOne recurrent tail eqn)
        (sourceEulerRowsForward
          (sourceDateOneEulerShearCoefficient P
            (localPrefixLogChart Z0 zstar) dateOne recurrent tail .H)
          (sourceDateOneEulerShearCoefficient P
            (localPrefixLogChart Z0 zstar) dateOne recurrent tail .L)
          dF eqn) zstar := by
  intro eqn
  have hrow :
      (fun z => sourceNominalPledgeShearedResidual branch P I
        (localPrefixLogChart Z0 z) dateOne recurrent tail eqn) =
      (fun z => sourceEulerRowsForward
        (sourceDateOneEulerShearCoefficient P
          (localPrefixLogChart Z0 z) dateOne recurrent tail .H)
        (sourceDateOneEulerShearCoefficient P
          (localPrefixLogChart Z0 z) dateOne recurrent tail .L)
        (fun row => localReducedPrefixResidual branch P I
          (localPrefixLogChart Z0 z) dateOne recurrent tail row)
        eqn) := by
    funext z
    exact congrFun
      (sourceNominalPledgeShearedResidual_eq_linear_rowmap
        branch P I (localPrefixLogChart Z0 z) dateOne recurrent tail) eqn
  rw [hrow]
  cases eqn <;> simp only [sourceEulerRowsForward] <;> try { exact hF _ }
  · exact sourceShear_hasFDerivAt_at_pledge_zero
      (fun z => localReducedPrefixResidual branch P I
        (localPrefixLogChart Z0 z) dateOne recurrent tail .firmCapitalEulerOneH)
      (fun z => sourceDateOneEulerShearCoefficient P
        (localPrefixLogChart Z0 z) dateOne recurrent tail .H)
      (fun z => localReducedPrefixResidual branch P I
        (localPrefixLogChart Z0 z) dateOne recurrent tail .commonPledgeOne)
      zstar (dF .firmCapitalEulerOneH) daH (dF .commonPledgeOne)
      (hF .firmCapitalEulerOneH) haH (hF .commonPledgeOne) hroot
  · exact sourceShear_hasFDerivAt_at_pledge_zero
      (fun z => localReducedPrefixResidual branch P I
        (localPrefixLogChart Z0 z) dateOne recurrent tail .firmCapitalEulerOneL)
      (fun z => sourceDateOneEulerShearCoefficient P
        (localPrefixLogChart Z0 z) dateOne recurrent tail .L)
      (fun z => localReducedPrefixResidual branch P I
        (localPrefixLogChart Z0 z) dateOne recurrent tail .commonPledgeOne)
      zstar (dF .firmCapitalEulerOneL) daL (dF .commonPledgeOne)
      (hF .firmCapitalEulerOneL) haL (hF .commonPledgeOne) hroot

#print axioms sourceNominalPledgeShearedLog_all_rows_hasFDerivAt

end Ventura26LiquidityAllocation

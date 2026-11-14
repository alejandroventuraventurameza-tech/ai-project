import Ventura26LiquidityAllocation.SourceEulerLogEconomicFrechetCandidate

/-!
# Complete SOURCE Euler shear: all 33 Frechet derivative rows

All rows are the genuine economic SOURCE rows on the original
positive logarithmic chart. The original residual derivatives and
the two coefficient derivatives are explicit hypotheses.

The SOURCE row shear on scalar residuals has to be lifted to
continuous linear maps before it can act on Frechet derivatives.
This module does not assume that the economic Jacobian is invertible.
-/

namespace Ventura26LiquidityAllocation

/-- Lift the actual economic SOURCE double row shear from real residual
values to continuous linear derivative rows at a fixed point. -/
noncomputable def sourceEulerRowsFrechetForward
    (aH aL : ℝ)
    (dF : LocalPrefixEquation → (Fin 33 → ℝ) →L[ℝ] ℝ) :
    LocalPrefixEquation → (Fin 33 → ℝ) →L[ℝ] ℝ :=
  fun row => match row with
  | .firmCapitalEulerOneH =>
      dF .firmCapitalEulerOneH + aH • dF .commonPledgeOne
  | .firmCapitalEulerOneL =>
      dF .firmCapitalEulerOneL + aL • dF .commonPledgeOne
  | _ => dF row

/-- Pointwise compatibility: applying each Frechet row to a direction
agrees with the earlier, already verified scalar SOURCE row shear. -/
theorem sourceEulerRowsFrechetForward_apply
    (aH aL : ℝ)
    (dF : LocalPrefixEquation → (Fin 33 → ℝ) →L[ℝ] ℝ)
    (h : Fin 33 → ℝ) (row : LocalPrefixEquation) :
    sourceEulerRowsFrechetForward aH aL dF row h =
      sourceEulerRowsForward aH aL (fun r => dF r h) row := by
  cases row <;>
    simp [sourceEulerRowsFrechetForward, sourceEulerRowsForward, smul_eq_mul]

#print axioms sourceEulerRowsFrechetForward_apply

/-- The genuine 33-row sheared residual has the Frechet derivative
given by the fixed-at-the-root SOURCE row shear of the original
economic derivative rows. Every SOURCE row is included. -/
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
        (sourceEulerRowsFrechetForward
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
  cases eqn <;>
    simp only [sourceEulerRowsForward, sourceEulerRowsFrechetForward] <;>
    try { exact hF _ }
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

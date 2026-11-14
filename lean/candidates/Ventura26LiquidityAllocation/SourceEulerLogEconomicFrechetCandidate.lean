import Ventura26LiquidityAllocation.SourceEulerLogFrechetShearCandidate

/-!
# Genuine SOURCE economic Euler Frechet derivatives

Both firms H and L are treated in the exact SOURCE log chart.
Economic row and coefficient differentiability remain explicit
hypotheses. No inverse Jacobian is asserted.
-/

namespace Ventura26LiquidityAllocation

private def sourceEconomicEulerLogRow : FirmType → Fin 33
  | .H => 19
  | .L => 20

theorem sourceEconomicEulerLog_fderiv_at_pledge_zero
    (branch : LocalPrefixBranch)
    (P : Primitives LocalBridgePhase) (I : InheritedState)
    (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : LocalBridgePhase)
    (tail : LocalPrefixContinuationRule)
    (i : FirmType)
    (zstar : Fin 33 → ℝ)
    (hE : DifferentiableAt ℝ
      (fun z => localReducedPrefixLogResidualVector
        branch P I Z0 dateOne recurrent tail z
        (sourceEconomicEulerLogRow i)) zstar)
    (ha : DifferentiableAt ℝ
      (fun z => sourceDateOneEulerShearCoefficient P
        (localPrefixLogChart Z0 z)
        dateOne recurrent tail i) zstar)
    (hp : DifferentiableAt ℝ
      (fun z => localReducedPrefixLogResidualVector
        branch P I Z0 dateOne recurrent tail z
        (21 : Fin 33)) zstar)
    (hroot : localReducedPrefixLogResidualVector
      branch P I Z0 dateOne recurrent tail
      zstar (21 : Fin 33) = 0) :
    fderiv ℝ
      (fun z => sourceNominalPledgeShearedLogResidualVector
        branch P I Z0 dateOne recurrent tail z
        (sourceEconomicEulerLogRow i)) zstar =
    fderiv ℝ
      (fun z => localReducedPrefixLogResidualVector
        branch P I Z0 dateOne recurrent tail z
        (sourceEconomicEulerLogRow i)) zstar +
    (sourceDateOneEulerShearCoefficient P
      (localPrefixLogChart Z0 zstar)
      dateOne recurrent tail i) •
    fderiv ℝ
      (fun z => localReducedPrefixLogResidualVector
        branch P I Z0 dateOne recurrent tail z
        (21 : Fin 33)) zstar := by
  let e : (Fin 33 → ℝ) → ℝ :=
    fun z => localReducedPrefixLogResidualVector
      branch P I Z0 dateOne recurrent tail z
      (sourceEconomicEulerLogRow i)
  let a : (Fin 33 → ℝ) → ℝ :=
    fun z => sourceDateOneEulerShearCoefficient P
      (localPrefixLogChart Z0 z) dateOne recurrent tail i
  let p : (Fin 33 → ℝ) → ℝ :=
    fun z => localReducedPrefixLogResidualVector
      branch P I Z0 dateOne recurrent tail z
      (21 : Fin 33)
  have hderiv : HasFDerivAt
      (fun z => e z + a z * p z)
      (fderiv ℝ e zstar + (a zstar) • fderiv ℝ p zstar)
      zstar := by
    exact sourceShear_hasFDerivAt_at_pledge_zero
      e a p zstar
      (fderiv ℝ e zstar)
      (fderiv ℝ a zstar)
      (fderiv ℝ p zstar)
      hE.hasFDerivAt ha.hasFDerivAt hp.hasFDerivAt
      hroot
  have hrow :
      (fun z => sourceNominalPledgeShearedLogResidualVector
        branch P I Z0 dateOne recurrent tail z
        (sourceEconomicEulerLogRow i)) =
      (fun z => e z + a z * p z) := by
    funext z
    cases i with
    | H =>
        exact sourceLogEulerH_row_shear
          branch P I Z0 dateOne recurrent tail z
    | L =>
        exact sourceLogEulerL_row_shear
          branch P I Z0 dateOne recurrent tail z
  rw [hrow]
  exact hderiv.fderiv

#print axioms sourceEconomicEulerLog_fderiv_at_pledge_zero

end Ventura26LiquidityAllocation

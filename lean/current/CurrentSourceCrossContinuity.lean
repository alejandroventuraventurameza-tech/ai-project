import Ventura26LiquidityAllocation.CurrentSourceExpSecantContinuity

/-!
# Exact SOURCE cross-coefficient continuity: four economic formulas per date

The four genuine SOURCE cross-coefficients are NOT arbitrary constants.
Each factors as a pre-secant economic term times the exact exponential
secant of the rate or quantity monetary residual.

We reduce their pointwise continuity to:
  * continuity of the corresponding pre-secant economic factors;
  * continuity of the genuine SOURCE rate/quantity residuals;
  * zero monetary residuals at the common root.

The SOURCE secant continuity is kernel-proved in
CurrentSourceExpSecantContinuity. This module does NOT assert the
pre-secant factors are continuous for the actual date-data chart
without separate economic/denominator lemmas, nor the original 33-row
Fréchet derivative or invertibility.
-/

namespace Ventura26LiquidityAllocation
namespace CurrentSourceCrossContinuity

open CurrentSourceFiveBankBridge
open scoped Topology

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The true SOURCE loan cross multiplier before the exponential secant. -/
noncomputable def sourceLoanPreSecant
    (P : Primitives S) (d : LocalPrefixDateData) : ℝ :=
  sourceRateRuleTarget P d

/-- The true SOURCE deposit cross multiplier before the exponential secant. -/
noncomputable def sourceDepositPreSecant
    (P : Primitives S) (d : LocalPrefixDateData) : ℝ :=
  -(sourceRateRuleTarget P d *
      (1 +
        d.controls.depositRate *
          localPrefixMeanAbsolutePaymentShock P *
          (sourceFrozenPythonDeficitSlope d -
            sourceFrozenPythonSurplusSlope d) /
          (2 * d.currentReserveRate * sourceRateRuleTarget P d)))

/-- The exact SOURCE balance-rate cross multiplier, before the secant. -/
noncomputable def sourceBalanceRatePreSecant
    (P : Primitives S) (d : LocalPrefixDateData) : ℝ :=
  sourceBankRateCrossCoefficient P d

/-- The exact SOURCE balance-quantity cross multiplier, before the secant. -/
noncomputable def sourceBalanceQuantityPreSecant
    (P : Primitives S) (d : LocalPrefixDateData) : ℝ :=
  sourceBankQuantityCrossCoefficient P d

/-- A continuously varying economic prefactor multiplied by the
SOURCE extended secant remains continuous at a monetary-rule root. -/
theorem prefactor_times_expSecant_continuousAt
    {X : Type*} [TopologicalSpace X]
    (prefactor residual : X → ℝ) (x : X)
    (hp : ContinuousAt prefactor x)
    (hr : ContinuousAt residual x)
    (hroot : residual x = 0) :
    ContinuousAt (fun y => prefactor y * expSecant (residual y)) x :=
  hp.mul (expSecant_comp_continuousAt_at_zero residual x hr hroot)

#print axioms prefactor_times_expSecant_continuousAt

/-- Genuine SOURCE loan cross coefficient: only continuity of the
SOURCE rate target and original rate-policy residual is needed. -/
theorem sourceLoanCross_continuousAt_of_prefactor
    {X : Type*} [TopologicalSpace X]
    (P : Primitives S) (d : X → LocalPrefixDateData) (x : X)
    (hp : ContinuousAt (fun y => sourceLoanPreSecant P (d y)) x)
    (hr : ContinuousAt
      (fun y => localReducedRemainingResidual P (d y) 6) x)
    (hroot : localReducedRemainingResidual P (d x) 6 = 0) :
    ContinuousAt (fun y => sourceLoanCross P (d y)) x := by
  simpa only [sourceLoanCross, sourceLoanPreSecant] using
    (prefactor_times_expSecant_continuousAt
      (fun y => sourceLoanPreSecant P (d y))
      (fun y => localReducedRemainingResidual P (d y) 6)
      x hp hr hroot)

#print axioms sourceLoanCross_continuousAt_of_prefactor

/-- Genuine SOURCE deposit cross coefficient, including the OTC
mean-absolute-payment term and actual reserve-rate denominator. -/
theorem sourceDepositCross_continuousAt_of_prefactor
    {X : Type*} [TopologicalSpace X]
    (P : Primitives S) (d : X → LocalPrefixDateData) (x : X)
    (hp : ContinuousAt (fun y => sourceDepositPreSecant P (d y)) x)
    (hr : ContinuousAt
      (fun y => localReducedRemainingResidual P (d y) 6) x)
    (hroot : localReducedRemainingResidual P (d x) 6 = 0) :
    ContinuousAt (fun y => sourceDepositCross P (d y)) x := by
  simpa only [sourceDepositCross, sourceDepositPreSecant] using
    (prefactor_times_expSecant_continuousAt
      (fun y => sourceDepositPreSecant P (d y))
      (fun y => localReducedRemainingResidual P (d y) 6)
      x hp hr hroot)

#print axioms sourceDepositCross_continuousAt_of_prefactor

/-- Genuine SOURCE bank balance-rate multiplier, using the original
banking ratio and actual policy-rule residual. -/
theorem sourceBalanceRateCross_continuousAt_of_prefactor
    {X : Type*} [TopologicalSpace X]
    (P : Primitives S) (d : X → LocalPrefixDateData) (x : X)
    (hp : ContinuousAt (fun y => sourceBalanceRatePreSecant P (d y)) x)
    (hr : ContinuousAt
      (fun y => localReducedRemainingResidual P (d y) 6) x)
    (hroot : localReducedRemainingResidual P (d x) 6 = 0) :
    ContinuousAt (fun y => sourceBalanceRateCross P (d y)) x := by
  simpa only [sourceBalanceRateCross, sourceBalanceRatePreSecant] using
    (prefactor_times_expSecant_continuousAt
      (fun y => sourceBalanceRatePreSecant P (d y))
      (fun y => localReducedRemainingResidual P (d y) 6)
      x hp hr hroot)

#print axioms sourceBalanceRateCross_continuousAt_of_prefactor

/-- Genuine SOURCE bank balance-quantity multiplier: the
reserve-quantity rule residual is the correct donor, not the rate. -/
theorem sourceBalanceQuantityCross_continuousAt_of_prefactor
    {X : Type*} [TopologicalSpace X]
    (P : Primitives S) (d : X → LocalPrefixDateData) (x : X)
    (hp : ContinuousAt (fun y => sourceBalanceQuantityPreSecant P (d y)) x)
    (hr : ContinuousAt
      (fun y => localReducedRemainingResidual P (d y) 7) x)
    (hroot : localReducedRemainingResidual P (d x) 7 = 0) :
    ContinuousAt (fun y => sourceBalanceQuantityCross P (d y)) x := by
  simpa only [sourceBalanceQuantityCross, sourceBalanceQuantityPreSecant] using
    (prefactor_times_expSecant_continuousAt
      (fun y => sourceBalanceQuantityPreSecant P (d y))
      (fun y => localReducedRemainingResidual P (d y) 7)
      x hp hr hroot)

#print axioms sourceBalanceQuantityCross_continuousAt_of_prefactor

/-- All four actual SOURCE date-specific coefficients are continuous,
given the explicitly named prefactor and policy-residual obligations. -/
theorem sourceFourCross_continuousAt_of_prefactors
    {X : Type*} [TopologicalSpace X]
    (P : Primitives S) (d : X → LocalPrefixDateData) (x : X)
    (hpLoan : ContinuousAt (fun y => sourceLoanPreSecant P (d y)) x)
    (hpDeposit : ContinuousAt (fun y => sourceDepositPreSecant P (d y)) x)
    (hpRate : ContinuousAt (fun y => sourceBalanceRatePreSecant P (d y)) x)
    (hpQuantity : ContinuousAt
      (fun y => sourceBalanceQuantityPreSecant P (d y)) x)
    (hrate : ContinuousAt
      (fun y => localReducedRemainingResidual P (d y) 6) x)
    (hquantity : ContinuousAt
      (fun y => localReducedRemainingResidual P (d y) 7) x)
    (hrootRate : localReducedRemainingResidual P (d x) 6 = 0)
    (hrootQuantity : localReducedRemainingResidual P (d x) 7 = 0) :
    ContinuousAt (fun y => sourceLoanCross P (d y)) x ∧
    ContinuousAt (fun y => sourceDepositCross P (d y)) x ∧
    ContinuousAt (fun y => sourceBalanceRateCross P (d y)) x ∧
    ContinuousAt (fun y => sourceBalanceQuantityCross P (d y)) x := by
  exact ⟨
    sourceLoanCross_continuousAt_of_prefactor P d x
      hpLoan hrate hrootRate,
    sourceDepositCross_continuousAt_of_prefactor P d x
      hpDeposit hrate hrootRate,
    sourceBalanceRateCross_continuousAt_of_prefactor P d x
      hpRate hrate hrootRate,
    sourceBalanceQuantityCross_continuousAt_of_prefactor P d x
      hpQuantity hquantity hrootQuantity⟩

#print axioms sourceFourCross_continuousAt_of_prefactors

end CurrentSourceCrossContinuity
end Ventura26LiquidityAllocation

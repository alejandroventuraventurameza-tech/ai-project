import Ventura26LiquidityAllocation.CurrentSourceDepositPreSecantRegularity

/-!
# SOURCE balance-row pre-secant coefficients: exact cancellation and continuity

In the genuine economic SOURCE bank balance, two monetary donor
residuals multiply different pre-secant coefficients. Rate and
quantity donors must not be interchanged. The quantity coefficient
depends on the realized reserve/deposit ratio and quantity policy
target. The rate coefficient also involves the TARGET reserve/deposit
ratio and deposit/current reserve rates.

The apparent target-rate factor in the rate coefficient cancels
exactly whenever its exponential target is nonzero. This is NOT an
approximation; it does not erase dependence through the target ratio.

We prove a generic differentiability-free continuity bridge from
the true individual atoms. To instantiate at the pinned SOURCE root,
future modules must supply policy targets, realized and target
bank-ratio continuity; these are being verified separately.
No claim of full 33-row differentiability, inverse or Python identity.
-/

namespace Ventura26LiquidityAllocation
namespace CurrentSourceBankBalancePreSecantRegularity

open CurrentSourceFiveBankBridge
open CurrentSourceCrossContinuity
open scoped Topology

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- True SOURCE target-reserve bank ratio, including the economic
payment mismatch factor and the genuine rate policy target. -/
noncomputable def economicTargetBankRatio
    (P : Primitives S) (d : LocalPrefixDateData) : ℝ :=
  sourceBankRatioAtRate d.reserveRequirement d.controls.depositRate
    (localPrefixMeanAbsolutePaymentShock P *
      (1 - d.controls.tightness) / (1 + d.controls.tightness))
    (sourceRateRuleTarget P d)

/-- The SOURCE rate-rule target occurs in numerator and denominator;
positivity of this exponential permits an exact algebraic cancellation. -/
theorem balance_rate_target_factor_cancellation
    (q deposit payment target reserve realRatio targetRatio : ℝ)
    (ht : target ≠ 0) (hr : reserve ≠ 0)
    (hReal : realRatio ≠ 0) (hTarget : targetRatio ≠ 0) :
    q * (deposit * payment * target /
        (reserve * target * realRatio * targetRatio)) =
      q * (deposit * payment /
        (reserve * realRatio * targetRatio)) := by
  field_simp [ht, hr, hReal, hTarget]
  <;> ring

#print axioms balance_rate_target_factor_cancellation

/-- Actual SOURCE rate prefactor simplified, under the original
bank-domain restrictions. It still depends on target rates through
economicTargetBankRatio, and this is not hidden. -/
theorem sourceBalanceRatePreSecant_eq_simplified
    (P : Primitives S) (d : LocalPrefixDateData)
    (hReserve : d.currentReserveRate ≠ 0)
    (hReal : localPrefixReserveDepositRatio P d ≠ 0)
    (hTarget : economicTargetBankRatio P d ≠ 0) :
    sourceBalanceRatePreSecant P d =
      sourceQuantityRuleTarget P d *
      (d.controls.depositRate *
        (localPrefixMeanAbsolutePaymentShock P *
          (1 - d.controls.tightness) / (1 + d.controls.tightness)) /
        (d.currentReserveRate *
          localPrefixReserveDepositRatio P d *
          economicTargetBankRatio P d)) := by
  unfold sourceBalanceRatePreSecant sourceBankRateCrossCoefficient
    economicTargetBankRatio
  exact balance_rate_target_factor_cancellation
    (sourceQuantityRuleTarget P d)
    d.controls.depositRate
    (localPrefixMeanAbsolutePaymentShock P *
      (1 - d.controls.tightness) / (1 + d.controls.tightness))
    (sourceRateRuleTarget P d)
    d.currentReserveRate
    (localPrefixReserveDepositRatio P d)
    (sourceBankRatioAtRate d.reserveRequirement d.controls.depositRate
      (localPrefixMeanAbsolutePaymentShock P *
        (1 - d.controls.tightness) / (1 + d.controls.tightness))
      (sourceRateRuleTarget P d))
    (ne_of_gt (Real.exp_pos _)) hReserve hReal hTarget

#print axioms sourceBalanceRatePreSecant_eq_simplified

/-- Original SOURCE quantity-donor prefactor continuity from the
genuine realized reserve/deposit ratio and quantity-rule target. -/
theorem sourceBalanceQuantityPreSecant_continuousAt_of_atoms
    {X : Type*} [TopologicalSpace X]
    (P : Primitives S) (d : X → LocalPrefixDateData) (x : X)
    (hRealRatio : ContinuousAt
      (fun y => localPrefixReserveDepositRatio P (d y)) x)
    (hQuantity : ContinuousAt
      (fun y => sourceQuantityRuleTarget P (d y)) x)
    (hRealNonzero : localPrefixReserveDepositRatio P (d x) ≠ 0) :
    ContinuousAt
      (fun y => sourceBalanceQuantityPreSecant P (d y)) x := by
  have hInv : ContinuousAt
      (fun y => (1 : ℝ) / localPrefixReserveDepositRatio P (d y)) x :=
    continuousAt_const.div hRealRatio hRealNonzero
  have hCoeff : ContinuousAt
      (fun y => (1 : ℝ) / localPrefixReserveDepositRatio P (d y) - 1) x :=
    hInv.sub continuousAt_const
  simpa only [sourceBalanceQuantityPreSecant,
    sourceBankQuantityCrossCoefficient] using hCoeff.mul hQuantity

#print axioms sourceBalanceQuantityPreSecant_continuousAt_of_atoms

/-- The TRUE SOURCE rate-donor balance coefficient is continuous if
the underlying monetary and banking economic atoms are. The actual
formula, not a frozen Python surrogate, is differentiated nowhere. -/
theorem sourceBalanceRatePreSecant_continuousAt_of_atoms
    {X : Type*} [TopologicalSpace X]
    (P : Primitives S) (d : X → LocalPrefixDateData) (x : X)
    (hQuantity : ContinuousAt
      (fun y => sourceQuantityRuleTarget P (d y)) x)
    (hDeposit : ContinuousAt
      (fun y => (d y).controls.depositRate) x)
    (hMismatch : ContinuousAt (fun y =>
      localPrefixMeanAbsolutePaymentShock P *
        (1 - (d y).controls.tightness) /
          (1 + (d y).controls.tightness)) x)
    (hRateTarget : ContinuousAt
      (fun y => sourceRateRuleTarget P (d y)) x)
    (hReserve : ContinuousAt (fun y => (d y).currentReserveRate) x)
    (hRealRatio : ContinuousAt
      (fun y => localPrefixReserveDepositRatio P (d y)) x)
    (hTargetRatio : ContinuousAt
      (fun y => economicTargetBankRatio P (d y)) x)
    (hReserveNe : (d x).currentReserveRate ≠ 0)
    (hRealNe : localPrefixReserveDepositRatio P (d x) ≠ 0)
    (hTargetNe : economicTargetBankRatio P (d x) ≠ 0) :
    ContinuousAt (fun y => sourceBalanceRatePreSecant P (d y)) x := by
  have hNum : ContinuousAt (fun y =>
      (d y).controls.depositRate *
        (localPrefixMeanAbsolutePaymentShock P *
          (1 - (d y).controls.tightness) /
            (1 + (d y).controls.tightness)) *
          sourceRateRuleTarget P (d y)) x :=
    (hDeposit.mul hMismatch).mul hRateTarget
  have hDen : ContinuousAt (fun y =>
      (d y).currentReserveRate * sourceRateRuleTarget P (d y) *
        localPrefixReserveDepositRatio P (d y) *
        economicTargetBankRatio P (d y)) x :=
    ((hReserve.mul hRateTarget).mul hRealRatio).mul hTargetRatio
  have hDenNe :
      (d x).currentReserveRate * sourceRateRuleTarget P (d x) *
        localPrefixReserveDepositRatio P (d x) *
        economicTargetBankRatio P (d x) ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero hReserveNe (ne_of_gt (Real.exp_pos _))) hRealNe)
      hTargetNe
  have hQuotient : ContinuousAt (fun y =>
      ((d y).controls.depositRate *
        (localPrefixMeanAbsolutePaymentShock P *
          (1 - (d y).controls.tightness) /
            (1 + (d y).controls.tightness)) *
          sourceRateRuleTarget P (d y)) /
      ((d y).currentReserveRate * sourceRateRuleTarget P (d y) *
        localPrefixReserveDepositRatio P (d y) *
        economicTargetBankRatio P (d y))) x :=
    hNum.div hDen hDenNe
  simpa only [sourceBalanceRatePreSecant,
    sourceBankRateCrossCoefficient, economicTargetBankRatio] using
    hQuantity.mul hQuotient

#print axioms sourceBalanceRatePreSecant_continuousAt_of_atoms

end CurrentSourceBankBalancePreSecantRegularity
end Ventura26LiquidityAllocation

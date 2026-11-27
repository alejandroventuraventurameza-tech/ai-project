import Ventura26LiquidityAllocation.CurrentPinnedSourcePricePrefactorContinuity
import Ventura26LiquidityAllocation.CurrentSourcePinnedBankRatioContinuity
import Ventura26LiquidityAllocation.CurrentSourceBankBalancePreSecantRegularity
import Ventura26LiquidityAllocation.CurrentSourcePinnedQuantityTargetContinuity

/-!
# All eight economic SOURCE bank shear pre-secant coefficients are continuous

The eight ORIGINAL economic coefficients are not arbitrary or frozen:
loan, deposit, balance-rate and balance-quantity in both SOURCE dates.

We combine previously kernel-certified building blocks:
- exact stationary SOURCE aggregate output and its continuity;
- both monetary rate targets and quantity targets;
- original OTC deficit/surplus slopes, deposit and reserve rates;
- both realized and target reserve/deposit ratios on both dates;
- strictly positive ratios and reserve rates at the common root;
- actual off-root bank balance cross formulas.

Result: continuity of all EIGHT pre-secant economic coefficients at the
genuine 33-log-coordinate stationary root with NO assumption of
HasFDerivAt F, no Python equality, and no Jacobian inverse.

The separate residuals' exponential secant terms are dealt with by
the monetary-donor continuity module and the prior secant theorem.
-/

namespace Ventura26LiquidityAllocation
namespace CurrentPinnedEightEconomicPrefactorContinuity

open CurrentSourceFullFDeriv
open CurrentPinnedBankDomain
open CurrentPinnedEightCrossContinuity
open CurrentSourceCrossContinuity
open CurrentSourcePinnedBankRatioContinuity
open CurrentSourceBankBalancePreSecantRegularity
open CurrentSourcePinnedOTCSlopes
open CurrentSourceDepositPreSecantRegularity
open CurrentPinnedQuantitativeBank
open CurrentPinnedLocalNeighborhood
open scoped Topology

/-- TRUE economic SOURCE pre-secant loan, deposit and both balance
coefficients are continuous on both pinned dates without any
regularity assumption from the original 33-vector F. -/
theorem pinned_eight_preSecants_continuousAt (G : ℝ) :
    FourPreSecantContinuousAt G (pinnedDateZero G) ∧
      FourPreSecantContinuousAt G (pinnedDateOne G) := by
  let P := ProposedStationaryPrimitives.primitives G
  obtain ⟨hT0, hT1⟩ :=
    CurrentPinnedSourcePricePrefactorContinuity.
      pinned_two_genuine_rate_targets_continuousAt G
  obtain ⟨hQ0, hQ1⟩ :=
    CurrentSourcePinnedQuantityTargetContinuity.
      pinned_two_quantity_targets_continuousAt G
  obtain ⟨⟨hLoan0, hDeposit0⟩, ⟨hLoan1, hDeposit1⟩⟩ :=
    CurrentPinnedSourcePricePrefactorContinuity.
      pinned_four_bank_price_prefactors_continuousAt G
  obtain ⟨⟨hReal0, hTarget0⟩, ⟨hReal1, hTarget1⟩⟩ :=
    pinned_four_bank_ratios_continuousAt_of_targets G hT0 hT1
  obtain ⟨hD0, hR0, hD1, hR1⟩ :=
    pinned_deposit_and_reserve_coordinates_continuousAt G
  obtain ⟨hTheta0, hTheta1⟩ :=
    pinned_two_tightness_coordinates_continuousAt G
  have hDen0 : 1 +
      (pinnedDateZero G (0 : Row33)).controls.tightness ≠ 0 := by
    have htheta := (pinned_tightness_coordinates G (0 : Row33)).1
    rw [htheta]
    have hExp : 0 < Real.exp ((0 : Row33) 16) := Real.exp_pos _
    have hp : (0 : ℝ) < 1 + (1 / 2 : ℝ) * Real.exp ((0 : Row33) 16) := by
      nlinarith
    exact ne_of_gt hp
  have hDen1 : 1 +
      (pinnedDateOne G (0 : Row33)).controls.tightness ≠ 0 := by
    have htheta := (pinned_tightness_coordinates G (0 : Row33)).2
    rw [htheta]
    have hExp : 0 < Real.exp ((0 : Row33) 32) := Real.exp_pos _
    have hp : (0 : ℝ) < 1 + (1 / 2 : ℝ) * Real.exp ((0 : Row33) 32) := by
      nlinarith
    exact ne_of_gt hp
  have hMismatch0 : ContinuousAt (fun z : Row33 =>
      localPrefixMeanAbsolutePaymentShock P *
        (1 - (pinnedDateZero G z).controls.tightness) /
          (1 + (pinnedDateZero G z).controls.tightness))
      (0 : Row33) :=
    source_payment_factor_continuousAt
      P (pinnedDateZero G) (0 : Row33) hTheta0 hDen0
  have hMismatch1 : ContinuousAt (fun z : Row33 =>
      localPrefixMeanAbsolutePaymentShock P *
        (1 - (pinnedDateOne G z).controls.tightness) /
          (1 + (pinnedDateOne G z).controls.tightness))
      (0 : Row33) :=
    source_payment_factor_continuousAt
      P (pinnedDateOne G) (0 : Row33) hTheta1 hDen1
  have hTargetRatio0 : ContinuousAt (fun z : Row33 =>
      economicTargetBankRatio P (pinnedDateZero G z)) (0 : Row33) := by
    simpa only [economicTargetBankRatio] using hTarget0
  have hTargetRatio1 : ContinuousAt (fun z : Row33 =>
      economicTargetBankRatio P (pinnedDateOne G z)) (0 : Row33) := by
    simpa only [economicTargetBankRatio] using hTarget1
  obtain ⟨⟨hRealPos0, hTargetPos0⟩, ⟨hRealPos1, hTargetPos1⟩⟩ :=
    pinned_bank_ratios_gt_two_twentyfifths G (0 : Row33)
      pinnedBankLogRegion_zero_mem
  have hZero : (0 : ℝ) < 2 / 25 := by norm_num
  have hRealNe0 :
      localPrefixReserveDepositRatio P (pinnedDateZero G (0 : Row33)) ≠ 0 :=
    ne_of_gt (lt_trans hZero hRealPos0)
  have hRealNe1 :
      localPrefixReserveDepositRatio P (pinnedDateOne G (0 : Row33)) ≠ 0 :=
    ne_of_gt (lt_trans hZero hRealPos1)
  have hTargetNe0 :
      economicTargetBankRatio P (pinnedDateZero G (0 : Row33)) ≠ 0 :=
    ne_of_gt (lt_trans hZero hTargetPos0)
  have hTargetNe1 :
      economicTargetBankRatio P (pinnedDateOne G (0 : Row33)) ≠ 0 :=
    ne_of_gt (lt_trans hZero hTargetPos1)
  have hReserveNe0 :
      (pinnedDateZero G (0 : Row33)).currentReserveRate ≠ 0 :=
    ne_of_gt (pinned_positive_reserve_states G (0 : Row33)).1
  have hReserveNe1 :
      (pinnedDateOne G (0 : Row33)).currentReserveRate ≠ 0 :=
    ne_of_gt (pinned_positive_reserve_states G (0 : Row33)).2.2.1
  have hBalanceRate0 : ContinuousAt (fun z : Row33 =>
      sourceBalanceRatePreSecant P (pinnedDateZero G z)) (0 : Row33) :=
    sourceBalanceRatePreSecant_continuousAt_of_atoms
      P (pinnedDateZero G) (0 : Row33)
      hQ0 hD0 hMismatch0 hT0 hR0 hReal0 hTargetRatio0
      hReserveNe0 hRealNe0 hTargetNe0
  have hBalanceQuantity0 : ContinuousAt (fun z : Row33 =>
      sourceBalanceQuantityPreSecant P (pinnedDateZero G z)) (0 : Row33) :=
    sourceBalanceQuantityPreSecant_continuousAt_of_atoms
      P (pinnedDateZero G) (0 : Row33) hReal0 hQ0 hRealNe0
  have hBalanceRate1 : ContinuousAt (fun z : Row33 =>
      sourceBalanceRatePreSecant P (pinnedDateOne G z)) (0 : Row33) :=
    sourceBalanceRatePreSecant_continuousAt_of_atoms
      P (pinnedDateOne G) (0 : Row33)
      hQ1 hD1 hMismatch1 hT1 hR1 hReal1 hTargetRatio1
      hReserveNe1 hRealNe1 hTargetNe1
  have hBalanceQuantity1 : ContinuousAt (fun z : Row33 =>
      sourceBalanceQuantityPreSecant P (pinnedDateOne G z)) (0 : Row33) :=
    sourceBalanceQuantityPreSecant_continuousAt_of_atoms
      P (pinnedDateOne G) (0 : Row33) hReal1 hQ1 hRealNe1
  unfold FourPreSecantContinuousAt
  exact ⟨⟨hLoan0, hDeposit0, hBalanceRate0, hBalanceQuantity0⟩,
    ⟨hLoan1, hDeposit1, hBalanceRate1, hBalanceQuantity1⟩⟩

#print axioms pinned_eight_preSecants_continuousAt

end CurrentPinnedEightEconomicPrefactorContinuity
end Ventura26LiquidityAllocation

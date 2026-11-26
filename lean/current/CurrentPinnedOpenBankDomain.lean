import Ventura26LiquidityAllocation.CurrentPinnedBankDomain

/-!
# Explicit open SOURCE banking domain around the stationary log origin

The prior domain bridge reduced actual SOURCE bank admissibility to
four nonzero reserve/deposit ratios across two dates.  This module
discharges them on the explicit region
    z(16) < log 2  and  z(32) < log 2.
The actual SOURCE payment shock moment equals 1/5, reserve
requirement is 1/10, and the actual/target reserve rates are
positive; no floating-point or Python functions are substituted.

This establishes an OPEN local banking regime about log origin, not
a root, Jacobian regularity, inverse norm or full equilibrium.
-/

namespace Ventura26LiquidityAllocation
namespace CurrentPinnedOpenBankDomain

open CurrentPinnedBankDomain
open CurrentSourceTwoDateBank
open CurrentSourceFiveBankBridge
open scoped Topology

/-- A positive convex mixture of the reserve requirement and the
deposit/reserve rate ratio.  Only the sign assumptions are needed. -/
theorem sourceBankRatioAtRate_pos_of_factor
    (a deposit c rate : ℝ)
    (ha : 0 < a) (hdeposit : 0 < deposit) (hrate : 0 < rate)
    (hc : 0 ≤ c) (hcbound : c < 1) :
    0 < sourceBankRatioAtRate a deposit c rate := by
  have hfirst : 0 < a * (1 - c) :=
    mul_pos ha (sub_pos.mpr hcbound)
  have hsecond : 0 ≤ (deposit / rate) * c :=
    mul_nonneg (le_of_lt (div_pos hdeposit hrate)) hc
  calc
    0 < a * (1 - c) + (deposit / rate) * c :=
      add_pos_of_pos_of_nonneg hfirst hsecond
    _ = sourceBankRatioAtRate a deposit c rate := by
      unfold sourceBankRatioAtRate
      ring

#print axioms sourceBankRatioAtRate_pos_of_factor

/-- Under 0<theta<1 the actual binary SOURCE payment factor belongs
to the unit interval; no numerical root enclosure is used. -/
theorem stationaryPaymentFactor_bounds
    (theta : ℝ) (htheta0 : 0 < theta) (htheta1 : theta < 1) :
    0 ≤ (1 / 5 : ℝ) * (1 - theta) / (1 + theta) ∧
    (1 / 5 : ℝ) * (1 - theta) / (1 + theta) < 1 := by
  have hden : 0 < 1 + theta := by linarith
  have hnum : 0 < 1 - theta := by linarith
  constructor
  · exact le_of_lt (div_pos (mul_pos (by norm_num) hnum) hden)
  · apply (div_lt_iff₀ hden).2
    nlinarith

#print axioms stationaryPaymentFactor_bounds

/-- Both realized and policy-target reserve/deposit ratios of an
ACTUAL SOURCE date with the stationary primitives are positive.
The target reserve rate is an exp(...) and is strictly positive. -/
theorem stationaryPrimitives_two_bank_ratios_pos
    (G : ℝ) (d : LocalPrefixDateData)
    (hrequirement : d.reserveRequirement = 1 / 10)
    (hdeposit : 0 < d.controls.depositRate)
    (hreserve : 0 < d.currentReserveRate)
    (htheta0 : 0 < d.controls.tightness)
    (htheta1 : d.controls.tightness < 1) :
    0 < localPrefixReserveDepositRatio
      (ProposedStationaryPrimitives.primitives G) d ∧
    0 < sourceBankRatioAtRate
      d.reserveRequirement d.controls.depositRate
      (localPrefixMeanAbsolutePaymentShock
        (ProposedStationaryPrimitives.primitives G) *
          (1 - d.controls.tightness) /
          (1 + d.controls.tightness))
      (sourceRateRuleTarget
        (ProposedStationaryPrimitives.primitives G) d) := by
  let P := ProposedStationaryPrimitives.primitives G
  have hmean : localPrefixMeanAbsolutePaymentShock P = 1 / 5 :=
    localPrefixMeanAbsolutePaymentShock_eq_of_binarySymmetric
      P 0 1 (1 / 5)
      (ProposedStationaryPrimitives.binary_payment_law G)
  have hfactor := stationaryPaymentFactor_bounds
    d.controls.tightness htheta0 htheta1
  have hreal :
      0 < sourceBankRatioAtRate
        d.reserveRequirement d.controls.depositRate
        (localPrefixMeanAbsolutePaymentShock P *
          (1 - d.controls.tightness) /
          (1 + d.controls.tightness))
        d.currentReserveRate := by
    rw [hrequirement, hmean]
    exact sourceBankRatioAtRate_pos_of_factor
      (1 / 10) d.controls.depositRate
      ((1 / 5 : ℝ) * (1 - d.controls.tightness) /
        (1 + d.controls.tightness))
      d.currentReserveRate
      (by norm_num) hdeposit hreserve hfactor.1 hfactor.2
  have htarget :
      0 < sourceBankRatioAtRate
        d.reserveRequirement d.controls.depositRate
        (localPrefixMeanAbsolutePaymentShock P *
          (1 - d.controls.tightness) /
          (1 + d.controls.tightness))
        (sourceRateRuleTarget P d) := by
    rw [hrequirement, hmean]
    exact sourceBankRatioAtRate_pos_of_factor
      (1 / 10) d.controls.depositRate
      ((1 / 5 : ℝ) * (1 - d.controls.tightness) /
        (1 + d.controls.tightness))
      (sourceRateRuleTarget P d)
      (by norm_num) hdeposit (Real.exp_pos _) hfactor.1 hfactor.2
  constructor
  · rw [← sourceBankRatioAtRealized_eq_SOURCE P d]
    exact hreal
  · exact htarget

#print axioms stationaryPrimitives_two_bank_ratios_pos

/-- The real pinned SOURCE 33-log chart satisfies *both* date-wise
banking admissibility conditions throughout the explicit open set.
No unverified nonzero-ratio hypothesis remains. -/
theorem pinned_both_dates_bank_admissible
    (G : ℝ) (z : Row33)
    (h16 : z 16 < Real.log 2)
    (h32 : z 32 < Real.log 2) :
    TargetBankAdmissible
      (ProposedStationaryPrimitives.primitives G)
      (pinnedDateZero G z) ∧
    TargetBankAdmissible
      (ProposedStationaryPrimitives.primitives G)
      (pinnedDateOne G z) := by
  have hsmall := pinned_strict_tightness_two_dates G z h16 h32
  have hreserve := pinned_positive_reserve_states G z
  have hcoords := pinned_tightness_coordinates G z
  have htheta0 : 0 < (pinnedDateZero G z).controls.tightness := by
    rw [hcoords.1]
    exact mul_pos (by norm_num) (Real.exp_pos _)
  have htheta1 : 0 < (pinnedDateOne G z).controls.tightness := by
    rw [hcoords.2]
    exact mul_pos (by norm_num) (Real.exp_pos _)
  have hd0 : 0 < (pinnedDateZero G z).controls.depositRate := by
    change 0 < localPrefixCoordinatesVector
      fullyPinnedStationarySOURCEZ0 14 * Real.exp (z 14)
    exact mul_pos (fullyPinnedStationarySOURCEZ0_positive 14)
      (Real.exp_pos _)
  have hd1 : 0 < (pinnedDateOne G z).controls.depositRate := by
    change 0 < localPrefixCoordinatesVector
      fullyPinnedStationarySOURCEZ0 30 * Real.exp (z 30)
    exact mul_pos (fullyPinnedStationarySOURCEZ0_positive 30)
      (Real.exp_pos _)
  have hreq0 : (pinnedDateZero G z).reserveRequirement = 1 / 10 := by
    rfl
  have hreq1 : (pinnedDateOne G z).reserveRequirement = 1 / 10 := by
    rfl
  obtain ⟨hratio0, htarget0⟩ :=
    stationaryPrimitives_two_bank_ratios_pos G
      (pinnedDateZero G z) hreq0 hd0 hreserve.1
      htheta0 hsmall.1
  obtain ⟨hratio1, htarget1⟩ :=
    stationaryPrimitives_two_bank_ratios_pos G
      (pinnedDateOne G z) hreq1 hd1 hreserve.2.2.1
      htheta1 hsmall.2
  exact
    (pinned_target_admissible_iff_two_ratio_checks
      G z h16 h32).mpr
      ⟨⟨ne_of_gt hratio0, ne_of_gt htarget0⟩,
        ⟨ne_of_gt hratio1, ne_of_gt htarget1⟩⟩

#print axioms pinned_both_dates_bank_admissible

end CurrentPinnedOpenBankDomain
end Ventura26LiquidityAllocation

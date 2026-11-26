import Ventura26LiquidityAllocation.CurrentPinnedLocalNeighborhood

/-!
# Quantitative banking domain margins for the exact pinned SOURCE chart

The banking-domain proof previously established that both reserve/deposit
ratios are nonzero on z(16), z(32) < log 2. This module strengthens that
fact to a uniform, explicit rational lower bound 2/25 for the ACTUAL
and target reserve/deposit ratios of BOTH economic dates, independent
of G, z, and any unverified Python or floating-point computation.

We also give an explicit sup-norm log-ball inside the bank-domain
region. This is only a BANKING certificate, not an interval enclosure
for the full 33-equation SOURCE Jacobian, its inverse or an IRF.
-/

namespace Ventura26LiquidityAllocation
namespace CurrentPinnedQuantitativeBank

open CurrentPinnedLocalNeighborhood
open CurrentPinnedOpenBankDomain
open CurrentPinnedBankDomain
open CurrentSourceFullFDeriv
open CurrentSourceTwoDateBank
open scoped Topology

/-- A concrete sup-norm ball about the exact root lies inside the
SOURCE admissible banking region. The bound is strict. -/
theorem pinned_half_log_ball_subset_bank_region (z : Row33)
    (hz : ‖z‖ < Real.log 2 / 2) :
    z ∈ pinnedBankLogRegion := by
  have hlog : 0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num)
  have hnorm16 : ‖z (16 : Fin 33)‖ ≤ ‖z‖ :=
    norm_le_pi_norm z (16 : Fin 33)
  have hnorm32 : ‖z (32 : Fin 33)‖ ≤ ‖z‖ :=
    norm_le_pi_norm z (32 : Fin 33)
  have hz16 : z (16 : Fin 33) ≤ ‖z (16 : Fin 33)‖ := by
    rw [Real.norm_eq_abs]
    exact le_abs_self _
  have hz32 : z (32 : Fin 33) ≤ ‖z (32 : Fin 33)‖ := by
    rw [Real.norm_eq_abs]
    exact le_abs_self _
  change z (16 : Fin 33) < Real.log 2 ∧
    z (32 : Fin 33) < Real.log 2
  constructor <;> linarith

#print axioms pinned_half_log_ball_subset_bank_region

/-- In the strict-matching region, the exact SOURCE payment-mismatch
factor is between zero and one fifth. -/
theorem stationaryPaymentFactor_lt_one_fifth
    (theta : ℝ) (h0 : 0 < theta) (h1 : theta < 1) :
    0 ≤ (1 / 5 : ℝ) * (1 - theta) / (1 + theta) ∧
    (1 / 5 : ℝ) * (1 - theta) / (1 + theta) < 1 / 5 := by
  have hden : 0 < 1 + theta := by linarith
  have hnum : 0 < 1 - theta := by linarith
  constructor
  · exact le_of_lt (div_pos (mul_pos (by norm_num) hnum) hden)
  · apply (div_lt_iff₀ hden).2
    nlinarith [h0]

#print axioms stationaryPaymentFactor_lt_one_fifth

/-- In a banking system with 10% reserves, positive deposit/interest
rates and a payment factor below 1/5, the ratio exceeds 2/25. -/
theorem sourceBankRatioAtRate_gt_two_twentyfifths
    (deposit rate c : ℝ)
    (hd : 0 < deposit) (hr : 0 < rate)
    (hc : 0 ≤ c) (hcbound : c < 1 / 5) :
    (2 / 25 : ℝ) <
      sourceBankRatioAtRate (1 / 10) deposit c rate := by
  have hsecond : 0 ≤ (deposit / rate) * c :=
    mul_nonneg (le_of_lt (div_pos hd hr)) hc
  have hfirst : (2 / 25 : ℝ) < (1 / 10) * (1 - c) := by
    nlinarith [hcbound]
  calc
    (2 / 25 : ℝ) < (1 / 10) * (1 - c) + (deposit / rate) * c := by
      linarith
    _ = sourceBankRatioAtRate (1 / 10) deposit c rate := by
      unfold sourceBankRatioAtRate
      ring

#print axioms sourceBankRatioAtRate_gt_two_twentyfifths

/-- Both economic reserve/deposit ratios are uniformly bounded below
by 2/25 for an actual stationary-SOURCE date, irrespective of G. -/
theorem stationaryPrimitives_two_bank_ratios_gt_two_twentyfifths
    (G : ℝ) (d : LocalPrefixDateData)
    (hrequirement : d.reserveRequirement = 1 / 10)
    (hdeposit : 0 < d.controls.depositRate)
    (hreserve : 0 < d.currentReserveRate)
    (htheta0 : 0 < d.controls.tightness)
    (htheta1 : d.controls.tightness < 1) :
    (2 / 25 : ℝ) <
      localPrefixReserveDepositRatio
        (ProposedStationaryPrimitives.primitives G) d ∧
    (2 / 25 : ℝ) <
      sourceBankRatioAtRate d.reserveRequirement
        d.controls.depositRate
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
  obtain ⟨hfactor0, hfactor1⟩ :=
    stationaryPaymentFactor_lt_one_fifth
      d.controls.tightness htheta0 htheta1
  have hreal :
      (2 / 25 : ℝ) <
        sourceBankRatioAtRate
          d.reserveRequirement d.controls.depositRate
          (localPrefixMeanAbsolutePaymentShock P *
            (1 - d.controls.tightness) /
              (1 + d.controls.tightness))
          d.currentReserveRate := by
    rw [hrequirement, hmean]
    exact sourceBankRatioAtRate_gt_two_twentyfifths
      d.controls.depositRate d.currentReserveRate
      ((1 / 5 : ℝ) * (1 - d.controls.tightness) /
        (1 + d.controls.tightness))
      hdeposit hreserve hfactor0 hfactor1
  have htarget :
      (2 / 25 : ℝ) <
        sourceBankRatioAtRate
          d.reserveRequirement d.controls.depositRate
          (localPrefixMeanAbsolutePaymentShock P *
            (1 - d.controls.tightness) /
              (1 + d.controls.tightness))
          (sourceRateRuleTarget P d) := by
    rw [hrequirement, hmean]
    exact sourceBankRatioAtRate_gt_two_twentyfifths
      d.controls.depositRate (sourceRateRuleTarget P d)
      ((1 / 5 : ℝ) * (1 - d.controls.tightness) /
        (1 + d.controls.tightness))
      hdeposit (Real.exp_pos _) hfactor0 hfactor1
  constructor
  · rw [← sourceBankRatioAtRealized_eq_SOURCE P d]
    exact hreal
  · exact htarget

#print axioms stationaryPrimitives_two_bank_ratios_gt_two_twentyfifths

/-- Quantitative SOURCE denominator margins for BOTH dates on the
open region, proved from the economic law of payments and the
positive log-coordinate levels. -/
theorem pinned_bank_ratios_gt_two_twentyfifths
    (G : ℝ) (z : Row33)
    (hz : z ∈ pinnedBankLogRegion) :
    ((2 / 25 : ℝ) <
       localPrefixReserveDepositRatio
         (ProposedStationaryPrimitives.primitives G)
         (pinnedDateZero G z) ∧
     (2 / 25 : ℝ) <
       sourceBankRatioAtRate
         (pinnedDateZero G z).reserveRequirement
         (pinnedDateZero G z).controls.depositRate
         (localPrefixMeanAbsolutePaymentShock
           (ProposedStationaryPrimitives.primitives G) *
           (1 - (pinnedDateZero G z).controls.tightness) /
             (1 + (pinnedDateZero G z).controls.tightness))
         (sourceRateRuleTarget
           (ProposedStationaryPrimitives.primitives G)
           (pinnedDateZero G z))) ∧
    ((2 / 25 : ℝ) <
       localPrefixReserveDepositRatio
         (ProposedStationaryPrimitives.primitives G)
         (pinnedDateOne G z) ∧
     (2 / 25 : ℝ) <
       sourceBankRatioAtRate
         (pinnedDateOne G z).reserveRequirement
         (pinnedDateOne G z).controls.depositRate
         (localPrefixMeanAbsolutePaymentShock
           (ProposedStationaryPrimitives.primitives G) *
           (1 - (pinnedDateOne G z).controls.tightness) /
             (1 + (pinnedDateOne G z).controls.tightness))
         (sourceRateRuleTarget
           (ProposedStationaryPrimitives.primitives G)
           (pinnedDateOne G z))) := by
  have hsmall := pinned_strict_tightness_two_dates G z hz.1 hz.2
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
  exact ⟨stationaryPrimitives_two_bank_ratios_gt_two_twentyfifths
      G (pinnedDateZero G z) hreq0 hd0 hreserve.1
      htheta0 hsmall.1,
    stationaryPrimitives_two_bank_ratios_gt_two_twentyfifths
      G (pinnedDateOne G z) hreq1 hd1 hreserve.2.2.1
      htheta1 hsmall.2⟩

#print axioms pinned_bank_ratios_gt_two_twentyfifths

/-- Ready for a certified interval enclosure: one concrete sup-norm
ball around the already-proven binding root has four uniform economic
bank-ratio lower bounds, for every possible government bond input. -/
theorem pinned_bank_ratios_gt_in_half_log_ball
    (G : ℝ) (z : Row33)
    (hz : ‖z‖ < Real.log 2 / 2) :
    ((2 / 25 : ℝ) <
       localPrefixReserveDepositRatio
         (ProposedStationaryPrimitives.primitives G)
         (pinnedDateZero G z) ∧
     (2 / 25 : ℝ) <
       sourceBankRatioAtRate
         (pinnedDateZero G z).reserveRequirement
         (pinnedDateZero G z).controls.depositRate
         (localPrefixMeanAbsolutePaymentShock
           (ProposedStationaryPrimitives.primitives G) *
           (1 - (pinnedDateZero G z).controls.tightness) /
             (1 + (pinnedDateZero G z).controls.tightness))
         (sourceRateRuleTarget
           (ProposedStationaryPrimitives.primitives G)
           (pinnedDateZero G z))) ∧
    ((2 / 25 : ℝ) <
       localPrefixReserveDepositRatio
         (ProposedStationaryPrimitives.primitives G)
         (pinnedDateOne G z) ∧
     (2 / 25 : ℝ) <
       sourceBankRatioAtRate
         (pinnedDateOne G z).reserveRequirement
         (pinnedDateOne G z).controls.depositRate
         (localPrefixMeanAbsolutePaymentShock
           (ProposedStationaryPrimitives.primitives G) *
           (1 - (pinnedDateOne G z).controls.tightness) /
             (1 + (pinnedDateOne G z).controls.tightness))
         (sourceRateRuleTarget
           (ProposedStationaryPrimitives.primitives G)
           (pinnedDateOne G z))) := by
  exact pinned_bank_ratios_gt_two_twentyfifths G z
    (pinned_half_log_ball_subset_bank_region z hz)

#print axioms pinned_bank_ratios_gt_in_half_log_ball

end CurrentPinnedQuantitativeBank
end Ventura26LiquidityAllocation

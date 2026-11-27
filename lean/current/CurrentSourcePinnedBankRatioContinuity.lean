import Ventura26LiquidityAllocation.CurrentSourceDepositPreSecantRegularity
import Ventura26LiquidityAllocation.CurrentSourcePinnedOTCSlopes

/-!
# SOURCE banking ratios: continuity of realized and target denominations

This treats both genuinely economic reserve/deposit ratios used by the
SOURCE bank balance. The actual ratio depends on realized reserve rate;
the target ratio uses the original SOURCE policy rate target. Both
depend on date-wise reserve requirement, deposit rate and the payment
mismatch factor m*(1-theta)/(1+theta).

The four strict positivity margins at the pinned root already follow
from CurrentPinnedQuantitativeBankMargins. We show their continuity
from the *primitive* inputs, with only policy target continuity still
conditional. No Jacobian inverse, Python identification or 34-root.
-/

namespace Ventura26LiquidityAllocation
namespace CurrentSourcePinnedBankRatioContinuity

open CurrentSourceFullFDeriv
open CurrentPinnedBankDomain
open CurrentSourceFiveBankBridge
open CurrentSourceDepositPreSecantRegularity
open CurrentSourcePinnedOTCSlopes
open scoped Topology

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- SOURCE payment-mismatch factor: continuity requires only tightness
continuity and the economically satisfied nonzero 1+theta denominator. -/
theorem source_payment_factor_continuousAt
    {X : Type*} [TopologicalSpace X]
    (P : Primitives S) (d : X → LocalPrefixDateData) (x : X)
    (hTheta : ContinuousAt (fun y => (d y).controls.tightness) x)
    (hDen : 1 + (d x).controls.tightness ≠ 0) :
    ContinuousAt (fun y =>
      localPrefixMeanAbsolutePaymentShock P *
        (1 - (d y).controls.tightness) /
          (1 + (d y).controls.tightness)) x := by
  exact (continuousAt_const.mul
      (continuousAt_const.sub hTheta)).div
      (continuousAt_const.add hTheta) hDen

#print axioms source_payment_factor_continuousAt

/-- The SOURCE realized reserve/deposit ratio is a continuous
composition of actual deposit and reserve rates, the policy reserve
requirement, and the mismatch factor. -/
theorem source_realized_bank_ratio_continuousAt
    {X : Type*} [TopologicalSpace X]
    (P : Primitives S) (d : X → LocalPrefixDateData) (x : X)
    (hReq : ContinuousAt (fun y => (d y).reserveRequirement) x)
    (hD : ContinuousAt (fun y => (d y).controls.depositRate) x)
    (hR : ContinuousAt (fun y => (d y).currentReserveRate) x)
    (hTheta : ContinuousAt (fun y => (d y).controls.tightness) x)
    (hRne : (d x).currentReserveRate ≠ 0)
    (hDen : 1 + (d x).controls.tightness ≠ 0) :
    ContinuousAt
      (fun y => localPrefixReserveDepositRatio P (d y)) x := by
  have hRatio : ContinuousAt
      (fun y => (d y).controls.depositRate / (d y).currentReserveRate) x :=
    hD.div hR hRne
  have hTerm : ContinuousAt (fun y =>
      ((d y).controls.depositRate / (d y).currentReserveRate -
        (d y).reserveRequirement) *
        localPrefixMeanAbsolutePaymentShock P *
        (1 - (d y).controls.tightness) /
          (1 + (d y).controls.tightness)) x :=
    (((hRatio.sub hReq).mul continuousAt_const).mul
      (continuousAt_const.sub hTheta)).div
      (continuousAt_const.add hTheta) hDen
  change ContinuousAt (fun y =>
    (d y).reserveRequirement +
      ((d y).controls.depositRate / (d y).currentReserveRate -
        (d y).reserveRequirement) *
        localPrefixMeanAbsolutePaymentShock P *
        (1 - (d y).controls.tightness) /
          (1 + (d y).controls.tightness)) x
  exact hReq.add hTerm

#print axioms source_realized_bank_ratio_continuousAt

/-- SOURCE target reserve/deposit ratio from the original real
sourceBankRatioAtRate, not a Python surrogate. The monetary target
enters as a function of the economic data; it is not frozen off root. -/
theorem source_target_bank_ratio_continuousAt
    {X : Type*} [TopologicalSpace X]
    (P : Primitives S) (d : X → LocalPrefixDateData) (x : X)
    (hReq : ContinuousAt (fun y => (d y).reserveRequirement) x)
    (hD : ContinuousAt (fun y => (d y).controls.depositRate) x)
    (hTheta : ContinuousAt (fun y => (d y).controls.tightness) x)
    (hTarget : ContinuousAt (fun y => sourceRateRuleTarget P (d y)) x)
    (hDen : 1 + (d x).controls.tightness ≠ 0) :
    ContinuousAt (fun y =>
      sourceBankRatioAtRate
        (d y).reserveRequirement (d y).controls.depositRate
        (localPrefixMeanAbsolutePaymentShock P *
          (1 - (d y).controls.tightness) /
            (1 + (d y).controls.tightness))
        (sourceRateRuleTarget P (d y))) x := by
  have hC := source_payment_factor_continuousAt P d x hTheta hDen
  have hQuotient : ContinuousAt (fun y =>
      (d y).controls.depositRate / sourceRateRuleTarget P (d y)) x :=
    hD.div hTarget (ne_of_gt (Real.exp_pos _))
  have hExpression : ContinuousAt (fun y =>
      (d y).reserveRequirement *
        (1 - (localPrefixMeanAbsolutePaymentShock P *
          (1 - (d y).controls.tightness) /
            (1 + (d y).controls.tightness))) +
      ((d y).controls.depositRate / sourceRateRuleTarget P (d y)) *
        (localPrefixMeanAbsolutePaymentShock P *
          (1 - (d y).controls.tightness) /
            (1 + (d y).controls.tightness))) x :=
    (hReq.mul (continuousAt_const.sub hC)).add (hQuotient.mul hC)
  have hEq :
      (fun y : X => sourceBankRatioAtRate
        (d y).reserveRequirement (d y).controls.depositRate
        (localPrefixMeanAbsolutePaymentShock P *
          (1 - (d y).controls.tightness) /
            (1 + (d y).controls.tightness))
        (sourceRateRuleTarget P (d y))) =
      (fun y : X =>
        (d y).reserveRequirement *
          (1 - (localPrefixMeanAbsolutePaymentShock P *
            (1 - (d y).controls.tightness) /
              (1 + (d y).controls.tightness))) +
        ((d y).controls.depositRate / sourceRateRuleTarget P (d y)) *
          (localPrefixMeanAbsolutePaymentShock P *
            (1 - (d y).controls.tightness) /
              (1 + (d y).controls.tightness))) := by
    funext y
    unfold sourceBankRatioAtRate
    ring
  rw [hEq]
  exact hExpression

#print axioms source_target_bank_ratio_continuousAt

/-- Both actual SOURCE dates: all four ratios (realized and target)
are continuous at the pinned root as soon as the two genuine policy
rate targets are continuous. All other component regularities are
already kernel-proven for the actual pinned log chart. -/
theorem pinned_four_bank_ratios_continuousAt_of_targets
    (G : ℝ)
    (hTarget0 : ContinuousAt (fun z : Row33 =>
      sourceRateRuleTarget (ProposedStationaryPrimitives.primitives G)
        (pinnedDateZero G z)) (0 : Row33))
    (hTarget1 : ContinuousAt (fun z : Row33 =>
      sourceRateRuleTarget (ProposedStationaryPrimitives.primitives G)
        (pinnedDateOne G z)) (0 : Row33)) :
    (ContinuousAt (fun z : Row33 =>
      localPrefixReserveDepositRatio
        (ProposedStationaryPrimitives.primitives G) (pinnedDateZero G z))
      (0 : Row33) ∧
     ContinuousAt (fun z : Row33 =>
       sourceBankRatioAtRate
         (pinnedDateZero G z).reserveRequirement
         (pinnedDateZero G z).controls.depositRate
         (localPrefixMeanAbsolutePaymentShock
           (ProposedStationaryPrimitives.primitives G) *
             (1 - (pinnedDateZero G z).controls.tightness) /
               (1 + (pinnedDateZero G z).controls.tightness))
         (sourceRateRuleTarget
           (ProposedStationaryPrimitives.primitives G)
           (pinnedDateZero G z))) (0 : Row33)) ∧
    (ContinuousAt (fun z : Row33 =>
       localPrefixReserveDepositRatio
         (ProposedStationaryPrimitives.primitives G) (pinnedDateOne G z))
       (0 : Row33) ∧
     ContinuousAt (fun z : Row33 =>
       sourceBankRatioAtRate
         (pinnedDateOne G z).reserveRequirement
         (pinnedDateOne G z).controls.depositRate
         (localPrefixMeanAbsolutePaymentShock
           (ProposedStationaryPrimitives.primitives G) *
             (1 - (pinnedDateOne G z).controls.tightness) /
               (1 + (pinnedDateOne G z).controls.tightness))
         (sourceRateRuleTarget
           (ProposedStationaryPrimitives.primitives G)
           (pinnedDateOne G z))) (0 : Row33)) := by
  let P := ProposedStationaryPrimitives.primitives G
  obtain ⟨hD0, hR0, hD1, hR1⟩ :=
    pinned_deposit_and_reserve_coordinates_continuousAt G
  obtain ⟨hTheta0, hTheta1⟩ :=
    pinned_two_tightness_coordinates_continuousAt G
  have hReq0 : ContinuousAt
      (fun z : Row33 => (pinnedDateZero G z).reserveRequirement)
      (0 : Row33) := by
    change ContinuousAt (fun _ : Row33 =>
      P.reserveRequirementPath 0 (bridgeDateZeroHistory P))
      (0 : Row33)
    exact continuousAt_const
  have hReq1 : ContinuousAt
      (fun z : Row33 => (pinnedDateOne G z).reserveRequirement)
      (0 : Row33) := by
    change ContinuousAt (fun _ : Row33 =>
      P.reserveRequirementPath 1 (bridgeDateOneHistory P .dateOne))
      (0 : Row33)
    exact continuousAt_const
  have hR0ne :
      (pinnedDateZero G (0 : Row33)).currentReserveRate ≠ 0 :=
    ne_of_gt (pinned_positive_reserve_states G (0 : Row33)).1
  have hR1ne :
      (pinnedDateOne G (0 : Row33)).currentReserveRate ≠ 0 :=
    ne_of_gt (pinned_positive_reserve_states G (0 : Row33)).2.2.1
  have hDen0 : 1 + (pinnedDateZero G (0 : Row33)).controls.tightness ≠ 0 := by
    have htheta := (pinned_tightness_coordinates G (0 : Row33)).1
    rw [htheta]
    have hexp : 0 < Real.exp ((0 : Row33) 16) := Real.exp_pos _
    have : 0 < (1 : ℝ) + (1 / 2 : ℝ) * Real.exp ((0 : Row33) 16) := by
      nlinarith
    exact ne_of_gt this
  have hDen1 : 1 + (pinnedDateOne G (0 : Row33)).controls.tightness ≠ 0 := by
    have htheta := (pinned_tightness_coordinates G (0 : Row33)).2
    rw [htheta]
    have hexp : 0 < Real.exp ((0 : Row33) 32) := Real.exp_pos _
    have : 0 < (1 : ℝ) + (1 / 2 : ℝ) * Real.exp ((0 : Row33) 32) := by
      nlinarith
    exact ne_of_gt this
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact source_realized_bank_ratio_continuousAt
      P (pinnedDateZero G) (0 : Row33) hReq0 hD0 hR0 hTheta0 hR0ne hDen0
  · exact source_target_bank_ratio_continuousAt
      P (pinnedDateZero G) (0 : Row33) hReq0 hD0 hTheta0 hTarget0 hDen0
  · exact source_realized_bank_ratio_continuousAt
      P (pinnedDateOne G) (0 : Row33) hReq1 hD1 hR1 hTheta1 hR1ne hDen1
  · exact source_target_bank_ratio_continuousAt
      P (pinnedDateOne G) (0 : Row33) hReq1 hD1 hTheta1 hTarget1 hDen1

#print axioms pinned_four_bank_ratios_continuousAt_of_targets

end CurrentSourcePinnedBankRatioContinuity
end Ventura26LiquidityAllocation

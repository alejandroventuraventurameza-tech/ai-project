import Ventura26LiquidityAllocation.CurrentSourceTwoDateFDerivInverse
import Ventura26LiquidityAllocation.SourceFullyPinnedStationaryP0OperatorCandidate

/-!
# Exact partial banking-domain certificate for the pinned SOURCE log chart

This module applies directly to the SOURCE stationary reference, its
stationary primitives and inherited financial state, and the fixed P0
tail. It does not evaluate the SOURCE residual or assume it vanishes.

For both economic dates, the baseline tightness is 1/2 and the
reserve-rate and pre-settlement-reserve coordinates are positive.
Consequently their bank-domain conditions are automatic throughout
the explicit log-chart region z(16) < log 2 and z(32) < log 2.

The only remaining pointwise banking-domain premises are the two
nonzero reserve/deposit ratios on each date. This is NOT an assertion
that those ratios are nonzero, an enclosure of them over a ball,
differentiability, or existence of an equilibrium root.
-/

namespace Ventura26LiquidityAllocation
namespace CurrentPinnedBankDomain

open CurrentSourceTwoDateBank
open CurrentSourceFiveBankBridge
open CurrentSourceFullFDeriv

/-- Actual SOURCE date-zero data at the pinned stationary reference,
not a Python surrogate. Only the government bond parameter G is free. -/
noncomputable def pinnedDateZero (G : ℝ) (z : Row33) :
    LocalPrefixDateData :=
  dateZero (ProposedStationaryPrimitives.primitives G)
    (ProposedStationaryInheritedState.inheritedState G)
    (localPrefixLogChart fullyPinnedStationarySOURCEZ0 z) .dateOne

/-- Date-one SOURCE data from the same pinned reference and fixed real
P0 continuation. -/
noncomputable def pinnedDateOne (G : ℝ) (z : Row33) :
    LocalPrefixDateData :=
  dateOne (ProposedStationaryPrimitives.primitives G)
    (localPrefixLogChart fullyPinnedStationarySOURCEZ0 z)
    .dateOne .recurrent
    (sourceLogLinearContinuation
      ProposedStationaryRealScale.stateSix
      ProposedStationaryRealScale.controls
      sourceFrozenP0TenControls)

/-- The true SOURCE log chart maps tightness in dates zero and one
to coordinates 16 and 32, respectively. -/
theorem pinned_tightness_coordinates (G : ℝ) (z : Row33) :
    (pinnedDateZero G z).controls.tightness =
      (1 / 2 : ℝ) * Real.exp (z 16) ∧
    (pinnedDateOne G z).controls.tightness =
      (1 / 2 : ℝ) * Real.exp (z 32) := by
  constructor <;> rfl

#print axioms pinned_tightness_coordinates

/-- Strictly interior SOURCE OTC matching condition on BOTH dates,
under explicit coordinate restrictions in the original log chart. -/
theorem pinned_strict_tightness_two_dates (G : ℝ) (z : Row33)
    (h16 : z 16 < Real.log 2)
    (h32 : z 32 < Real.log 2) :
    (pinnedDateZero G z).controls.tightness < 1 ∧
    (pinnedDateOne G z).controls.tightness < 1 := by
  obtain ⟨hzero, hone⟩ := pinned_tightness_coordinates G z
  constructor
  · rw [hzero]
    have he : Real.exp (z 16) < 2 := by
      calc
        Real.exp (z 16) < Real.exp (Real.log (2 : ℝ)) :=
          Real.exp_lt_exp.mpr h16
        _ = 2 := Real.exp_log (by norm_num)
    nlinarith
  · rw [hone]
    have he : Real.exp (z 32) < 2 := by
      calc
        Real.exp (z 32) < Real.exp (Real.log (2 : ℝ)) :=
          Real.exp_lt_exp.mpr h32
        _ = 2 := Real.exp_log (by norm_num)
    nlinarith

#print axioms pinned_strict_tightness_two_dates

/-- The reserve rate and pre-settlement reserves remain strictly
positive on both economic dates at EVERY finite log-coordinate z:
positivity is supplied by the genuine SOURCE basepoint, not Python. -/
theorem pinned_positive_reserve_states (G : ℝ) (z : Row33) :
    0 < (pinnedDateZero G z).currentReserveRate ∧
    0 < (pinnedDateZero G z).currentReservesPre ∧
    0 < (pinnedDateOne G z).currentReserveRate ∧
    0 < (pinnedDateOne G z).currentReservesPre := by
  constructor
  · change 0 < localPrefixCoordinatesVector fullyPinnedStationarySOURCEZ0 5 *
        Real.exp (z 5)
    exact mul_pos (fullyPinnedStationarySOURCEZ0_positive 5)
      (Real.exp_pos _)
  constructor
  · change 0 < localPrefixCoordinatesVector fullyPinnedStationarySOURCEZ0 6 *
        Real.exp (z 6)
    exact mul_pos (fullyPinnedStationarySOURCEZ0_positive 6)
      (Real.exp_pos _)
  constructor
  · change 0 < localPrefixCoordinatesVector fullyPinnedStationarySOURCEZ0 21 *
        Real.exp (z 21)
    exact mul_pos (fullyPinnedStationarySOURCEZ0_positive 21)
      (Real.exp_pos _)
  · change 0 < localPrefixCoordinatesVector fullyPinnedStationarySOURCEZ0 22 *
        Real.exp (z 22)
    exact mul_pos (fullyPinnedStationarySOURCEZ0_positive 22)
      (Real.exp_pos _)

#print axioms pinned_positive_reserve_states

/-- Only the two nonzero ratios are not settled by the explicit
log-domain restriction and source-coordinate positivity. -/
def BankRatiosNonzero
    {S : Type*} [Fintype S] (P : Primitives S)
    (d : LocalPrefixDateData) : Prop :=
  localPrefixReserveDepositRatio P d ≠ 0 ∧
  sourceBankRatioAtRate d.reserveRequirement
    d.controls.depositRate
    (localPrefixMeanAbsolutePaymentShock P *
      (1 - d.controls.tightness) /
        (1 + d.controls.tightness))
    (sourceRateRuleTarget P d) ≠ 0

/-- Full SOURCE banking-domain equivalence on the actual pinned
chart. This is a reduction of proof obligations, NOT a proof that
either of the two remaining ratios is nonzero. -/
theorem pinned_target_admissible_iff_two_ratio_checks (G : ℝ)
    (z : Row33)
    (h16 : z 16 < Real.log 2)
    (h32 : z 32 < Real.log 2) :
    (TargetBankAdmissible
       (ProposedStationaryPrimitives.primitives G)
       (pinnedDateZero G z) ∧
     TargetBankAdmissible
       (ProposedStationaryPrimitives.primitives G)
       (pinnedDateOne G z)) ↔
    (BankRatiosNonzero
       (ProposedStationaryPrimitives.primitives G)
       (pinnedDateZero G z) ∧
     BankRatiosNonzero
       (ProposedStationaryPrimitives.primitives G)
       (pinnedDateOne G z)) := by
  obtain ⟨hθ0, hθ1⟩ :=
    pinned_strict_tightness_two_dates G z h16 h32
  obtain ⟨hr0, hm0, hr1, hm1⟩ :=
    pinned_positive_reserve_states G z
  constructor
  · rintro ⟨h0, h1⟩
    rcases h0 with ⟨_, _, _, hratio0, htarget0⟩
    rcases h1 with ⟨_, _, _, hratio1, htarget1⟩
    exact ⟨⟨hratio0, htarget0⟩, ⟨hratio1, htarget1⟩⟩
  · rintro ⟨⟨hratio0, htarget0⟩, ⟨hratio1, htarget1⟩⟩
    exact ⟨⟨hθ0.le, hr0, hm0, hratio0, htarget0⟩,
      ⟨hθ1.le, hr1, hm1, hratio1, htarget1⟩⟩

#print axioms pinned_target_admissible_iff_two_ratio_checks

end CurrentPinnedBankDomain
end Ventura26LiquidityAllocation

import Ventura26LiquidityAllocation.CurrentPinnedEightCrossContinuity
import Ventura26LiquidityAllocation.CurrentPinnedQuantitativeBankMargins

/-!
# SOURCE deposit pre-secant: remove a spurious target-rate denominator

The genuine economic SOURCE deposit row-shear prefactor contains
  -T * (1 + D * m * (chiMinus - chiPlus) / (2 * R * T)).
The target reserve rate T is strictly positive because it is exp(...).
For nonzero realized reserve rate R, this is identically
  -T - D * m * (chiMinus - chiPlus) / (2 * R).

We prove that exact algebraic identity and derive continuity from
the economically primitive chart inputs. The genuine pinned log chart
already has globally positive R and continuous R/D coordinates; hence
the remaining premises are continuity of the target rate and the two
frozen SOURCE OTC slopes. We do not assert these last premises here.

No assumption about the Python finite IRF or the 33x33 inverse is used.
-/

namespace Ventura26LiquidityAllocation
namespace CurrentSourceDepositPreSecantRegularity

open CurrentSourceCrossContinuity
open CurrentSourceFiveBankBridge
open CurrentPinnedBankDomain
open scoped Topology

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- An exact algebraic cancellation: both rate denominators are nonzero.
This is an identity, not a first-order or numerical approximation. -/
theorem deposit_prefactor_cancel_target (target numerator reserve : ℝ)
    (hTarget : target ≠ 0) (hReserve : reserve ≠ 0) :
    -(target * (1 + numerator / (2 * reserve * target))) =
      -target - numerator / (2 * reserve) := by
  field_simp [hTarget, hReserve]
  <;> ring

#print axioms deposit_prefactor_cancel_target

/-- Genuine SOURCE deposit prefactor equals the expression without
the target-rate denominator whenever realized reserves pay a nonzero
rate (automatically true in the pinned economic log chart). -/
theorem sourceDepositPreSecant_eq_simplified
    (P : Primitives S) (d : LocalPrefixDateData)
    (hReserve : d.currentReserveRate ≠ 0) :
    sourceDepositPreSecant P d =
      -sourceRateRuleTarget P d -
        (d.controls.depositRate *
          localPrefixMeanAbsolutePaymentShock P *
          (sourceFrozenPythonDeficitSlope d -
            sourceFrozenPythonSurplusSlope d)) /
          (2 * d.currentReserveRate) := by
  unfold sourceDepositPreSecant
  exact deposit_prefactor_cancel_target
    (sourceRateRuleTarget P d)
    (d.controls.depositRate *
      localPrefixMeanAbsolutePaymentShock P *
        (sourceFrozenPythonDeficitSlope d -
          sourceFrozenPythonSurplusSlope d))
    d.currentReserveRate
    (ne_of_gt (Real.exp_pos _)) hReserve

#print axioms sourceDepositPreSecant_eq_simplified

/-- Real SOURCE deposit prefactor continuity, reduced to the five
primitive input functions. The blanket reserve nonzero condition
is convenient for the exact pinned log chart, where reserve rates are
strictly positive at every displacement. -/
theorem sourceDepositPreSecant_continuousAt_of_atoms
    {X : Type*} [TopologicalSpace X]
    (P : Primitives S) (d : X → LocalPrefixDateData) (x : X)
    (hReserveAll : ∀ y : X, (d y).currentReserveRate ≠ 0)
    (hTarget : ContinuousAt (fun y => sourceRateRuleTarget P (d y)) x)
    (hDeposit : ContinuousAt (fun y => (d y).controls.depositRate) x)
    (hReserve : ContinuousAt (fun y => (d y).currentReserveRate) x)
    (hMinus : ContinuousAt
      (fun y => sourceFrozenPythonDeficitSlope (d y)) x)
    (hPlus : ContinuousAt
      (fun y => sourceFrozenPythonSurplusSlope (d y)) x) :
    ContinuousAt (fun y => sourceDepositPreSecant P (d y)) x := by
  have hMean : ContinuousAt
      (fun _ : X => localPrefixMeanAbsolutePaymentShock P) x :=
    continuousAt_const
  have hTwo : ContinuousAt (fun _ : X => (2 : ℝ)) x :=
    continuousAt_const
  have hNumerator : ContinuousAt
      (fun y => (d y).controls.depositRate *
        localPrefixMeanAbsolutePaymentShock P *
        (sourceFrozenPythonDeficitSlope (d y) -
          sourceFrozenPythonSurplusSlope (d y))) x :=
    (hDeposit.mul hMean).mul (hMinus.sub hPlus)
  have hDenominator : ContinuousAt
      (fun y => (2 : ℝ) * (d y).currentReserveRate) x :=
    hTwo.mul hReserve
  have hQuotient : ContinuousAt
      (fun y => ((d y).controls.depositRate *
        localPrefixMeanAbsolutePaymentShock P *
        (sourceFrozenPythonDeficitSlope (d y) -
          sourceFrozenPythonSurplusSlope (d y))) /
        (2 * (d y).currentReserveRate)) x :=
    hNumerator.div hDenominator
      (mul_ne_zero (by norm_num) (hReserveAll x))
  have hSimple : ContinuousAt
      (fun y => -sourceRateRuleTarget P (d y) -
        ((d y).controls.depositRate *
          localPrefixMeanAbsolutePaymentShock P *
          (sourceFrozenPythonDeficitSlope (d y) -
            sourceFrozenPythonSurplusSlope (d y))) /
        (2 * (d y).currentReserveRate)) x :=
    hTarget.neg.sub hQuotient
  have hFunction :
      (fun y : X => sourceDepositPreSecant P (d y)) =
      (fun y : X => -sourceRateRuleTarget P (d y) -
        ((d y).controls.depositRate *
          localPrefixMeanAbsolutePaymentShock P *
          (sourceFrozenPythonDeficitSlope (d y) -
            sourceFrozenPythonSurplusSlope (d y))) /
          (2 * (d y).currentReserveRate)) := by
    funext y
    exact sourceDepositPreSecant_eq_simplified P (d y)
      (hReserveAll y)
  rw [hFunction]
  exact hSimple

#print axioms sourceDepositPreSecant_continuousAt_of_atoms

/-- The actual pinned SOURCE log chart has continuous deposit and
realized-reserve-rate coordinates at the common origin at BOTH dates.
These are the real economic coordinates 14/5 and 30/21, not
stand-ins from Python. -/
theorem pinned_deposit_and_reserve_coordinates_continuousAt (G : ℝ) :
    ContinuousAt (fun z : Row33 =>
      (CurrentPinnedBankDomain.pinnedDateZero G z).controls.depositRate)
      (0 : Row33) ∧
    ContinuousAt (fun z : Row33 =>
      (CurrentPinnedBankDomain.pinnedDateZero G z).currentReserveRate)
      (0 : Row33) ∧
    ContinuousAt (fun z : Row33 =>
      (CurrentPinnedBankDomain.pinnedDateOne G z).controls.depositRate)
      (0 : Row33) ∧
    ContinuousAt (fun z : Row33 =>
      (CurrentPinnedBankDomain.pinnedDateOne G z).currentReserveRate)
      (0 : Row33) := by
  have hcoordinate (i : Fin 33) (c : ℝ) :
      ContinuousAt (fun z : Row33 => c * Real.exp (z i))
        (0 : Row33) := by
    exact continuousAt_const.mul
      (Real.continuous_exp.continuousAt.comp
        ((continuous_apply i).continuousAt))
  refine ⟨?_, ?_, ?_, ?_⟩
  · change ContinuousAt (fun z : Row33 =>
      localPrefixCoordinatesVector fullyPinnedStationarySOURCEZ0 14 *
        Real.exp (z 14)) (0 : Row33)
    exact hcoordinate 14 _
  · change ContinuousAt (fun z : Row33 =>
      localPrefixCoordinatesVector fullyPinnedStationarySOURCEZ0 5 *
        Real.exp (z 5)) (0 : Row33)
    exact hcoordinate 5 _
  · change ContinuousAt (fun z : Row33 =>
      localPrefixCoordinatesVector fullyPinnedStationarySOURCEZ0 30 *
        Real.exp (z 30)) (0 : Row33)
    exact hcoordinate 30 _
  · change ContinuousAt (fun z : Row33 =>
      localPrefixCoordinatesVector fullyPinnedStationarySOURCEZ0 21 *
        Real.exp (z 21)) (0 : Row33)
    exact hcoordinate 21 _

#print axioms pinned_deposit_and_reserve_coordinates_continuousAt

/-- In the true pinned SOURCE two-date chart, the two deposit
prefactors are continuous assuming only continuity of the TRUE
target reserve rate and the two OTC slope formulas per date.
The deposit/reserve coordinate continuity and strict reserve-rate
positivity premises are now discharged by SOURCE proofs. -/
theorem pinned_two_deposit_preSecants_continuousAt
    (G : ℝ)
    (hTarget0 : ContinuousAt (fun z : Row33 =>
      sourceRateRuleTarget (ProposedStationaryPrimitives.primitives G)
        (CurrentPinnedBankDomain.pinnedDateZero G z)) (0 : Row33))
    (hMinus0 : ContinuousAt (fun z : Row33 =>
      sourceFrozenPythonDeficitSlope
        (CurrentPinnedBankDomain.pinnedDateZero G z)) (0 : Row33))
    (hPlus0 : ContinuousAt (fun z : Row33 =>
      sourceFrozenPythonSurplusSlope
        (CurrentPinnedBankDomain.pinnedDateZero G z)) (0 : Row33))
    (hTarget1 : ContinuousAt (fun z : Row33 =>
      sourceRateRuleTarget (ProposedStationaryPrimitives.primitives G)
        (CurrentPinnedBankDomain.pinnedDateOne G z)) (0 : Row33))
    (hMinus1 : ContinuousAt (fun z : Row33 =>
      sourceFrozenPythonDeficitSlope
        (CurrentPinnedBankDomain.pinnedDateOne G z)) (0 : Row33))
    (hPlus1 : ContinuousAt (fun z : Row33 =>
      sourceFrozenPythonSurplusSlope
        (CurrentPinnedBankDomain.pinnedDateOne G z)) (0 : Row33)) :
    ContinuousAt (fun z : Row33 =>
      sourceDepositPreSecant (ProposedStationaryPrimitives.primitives G)
        (CurrentPinnedBankDomain.pinnedDateZero G z)) (0 : Row33) ∧
    ContinuousAt (fun z : Row33 =>
      sourceDepositPreSecant (ProposedStationaryPrimitives.primitives G)
        (CurrentPinnedBankDomain.pinnedDateOne G z)) (0 : Row33) := by
  rcases pinned_deposit_and_reserve_coordinates_continuousAt G with
    ⟨hDeposit0, hReserve0, hDeposit1, hReserve1⟩
  have hReserve0All (z : Row33) :
      (CurrentPinnedBankDomain.pinnedDateZero G z).currentReserveRate ≠ 0 :=
    ne_of_gt (CurrentPinnedBankDomain.pinned_positive_reserve_states G z).1
  have hReserve1All (z : Row33) :
      (CurrentPinnedBankDomain.pinnedDateOne G z).currentReserveRate ≠ 0 :=
    ne_of_gt (CurrentPinnedBankDomain.pinned_positive_reserve_states G z).2.2.1
  constructor
  · exact sourceDepositPreSecant_continuousAt_of_atoms
      (ProposedStationaryPrimitives.primitives G)
      (CurrentPinnedBankDomain.pinnedDateZero G) (0 : Row33)
      hReserve0All hTarget0 hDeposit0 hReserve0 hMinus0 hPlus0
  · exact sourceDepositPreSecant_continuousAt_of_atoms
      (ProposedStationaryPrimitives.primitives G)
      (CurrentPinnedBankDomain.pinnedDateOne G) (0 : Row33)
      hReserve1All hTarget1 hDeposit1 hReserve1 hMinus1 hPlus1

#print axioms pinned_two_deposit_preSecants_continuousAt

end CurrentSourceDepositPreSecantRegularity
end Ventura26LiquidityAllocation

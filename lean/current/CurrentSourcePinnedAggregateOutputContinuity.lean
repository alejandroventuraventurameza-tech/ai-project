import Ventura26LiquidityAllocation.CurrentPinnedMonetaryRoots
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Actual SOURCE aggregate-output continuity from original firm primitives

For the genuinely pinned SOURCE two-date log chart the objects
localPrefixLabor, localPrefixOutput, and localPrefixAggregateOutput
are defined in EconomicModel from Cobb-Douglas production and
intratemporal labor choice. We do not postulate continuity of output.

An abstract economic lemma obtains aggregate-output continuity from
continuity of capital, input price, wage and productivity, the
strict nonzero wage at the basepoint, and nonnegative power exponents.
These restrictions hold for the actual stationary SOURCE primitives
alpha=2/5, beta=1/2 and positive-log wage coordinates.

The specialization discharges all these premises for actual SOURCE
date zero and date one. This is local CONTINUITY, not Fréchet
differentiability or a certified inverse of the 33x33 Jacobian.
-/

namespace Ventura26LiquidityAllocation
namespace CurrentSourcePinnedAggregateOutputContinuity

open CurrentSourceFullFDeriv
open CurrentPinnedBankDomain
open scoped Topology BigOperators

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Continuity of the exact original SOURCE aggregate output follows
from standard continuity of power, product, quotient and finite sum.
No SOURCE--Python normalization or approximate labor function. -/
theorem localPrefixAggregateOutput_continuousAt_of_atoms
    {X : Type*} [TopologicalSpace X]
    (P : Primitives S) (d : X → LocalPrefixDateData) (x : X)
    (hK : ∀ i : FirmType,
      ContinuousAt (fun y => (d y).currentCapital i) x)
    (hA : ContinuousAt (fun y => (d y).currentAggregateProductivity) x)
    (hPrice : ContinuousAt (fun y => (d y).controls.inputPrice) x)
    (hWage : ContinuousAt (fun y => (d y).controls.wage) x)
    (hWageNe : (d x).controls.wage ≠ 0)
    (hAlpha : 0 ≤ P.alpha)
    (hBeta : 0 ≤ P.beta)
    (hLaborPower : 0 ≤ 1 / (1 - P.beta)) :
    ContinuousAt (fun y => localPrefixAggregateOutput P (d y)) x := by
  have hKpow (i : FirmType) : ContinuousAt
      (fun y => (d y).currentCapital i ^ P.alpha) x :=
    (hK i).rpow_const (.inr hAlpha)
  have hLabor (i : FirmType) : ContinuousAt
      (fun y => localPrefixLabor P (d y) i) x := by
    have hNum : ContinuousAt (fun y =>
        P.beta * (d y).controls.inputPrice *
          (d y).currentAggregateProductivity *
          P.productivity i * (d y).currentCapital i ^ P.alpha) x :=
      ((((continuousAt_const.mul hPrice).mul hA).mul
        continuousAt_const).mul (hKpow i))
    have hBase : ContinuousAt (fun y =>
        (P.beta * (d y).controls.inputPrice *
          (d y).currentAggregateProductivity *
          P.productivity i * (d y).currentCapital i ^ P.alpha) /
            (d y).controls.wage) x :=
      hNum.div hWage hWageNe
    change ContinuousAt (fun y =>
      ((P.beta * (d y).controls.inputPrice *
          (d y).currentAggregateProductivity *
          P.productivity i * (d y).currentCapital i ^ P.alpha) /
            (d y).controls.wage) ^ (1 / (1 - P.beta))) x
    exact hBase.rpow_const (.inr hLaborPower)
  have hFirmOutput (i : FirmType) : ContinuousAt
      (fun y => localPrefixOutput P (d y) i) x := by
    change ContinuousAt (fun y =>
      (d y).currentAggregateProductivity * P.productivity i *
        (d y).currentCapital i ^ P.alpha *
        (localPrefixLabor P (d y) i) ^ P.beta) x
    exact (((hA.mul continuousAt_const).mul (hKpow i)).mul
      ((hLabor i).rpow_const (.inr hBeta)))
  have hSum :
      (fun y : X => localPrefixAggregateOutput P (d y)) =
      (fun y : X =>
        P.mass .H * localPrefixOutput P (d y) .H +
        P.mass .L * localPrefixOutput P (d y) .L) := by
    funext y
    change (∑ i : FirmType, P.mass i * localPrefixOutput P (d y) i) =
      P.mass .H * localPrefixOutput P (d y) .H +
      P.mass .L * localPrefixOutput P (d y) .L
    rw [sum_firmType_eq_H_add_L]
  rw [hSum]
  exact (continuousAt_const.mul (hFirmOutput .H)).add
    (continuousAt_const.mul (hFirmOutput .L))

#print axioms localPrefixAggregateOutput_continuousAt_of_atoms

/-- All genuine pinned SOURCE primitive inputs satisfy the continuity
premises at both dates; their positive log coordinates encode capital,
real activity input price and wage with no hidden Python variables. -/
theorem pinned_two_actual_aggregate_outputs_continuousAt (G : ℝ) :
    ContinuousAt (fun z : Row33 =>
      localPrefixAggregateOutput
        (ProposedStationaryPrimitives.primitives G)
        (pinnedDateZero G z)) (0 : Row33) ∧
    ContinuousAt (fun z : Row33 =>
      localPrefixAggregateOutput
        (ProposedStationaryPrimitives.primitives G)
        (pinnedDateOne G z)) (0 : Row33) := by
  let P := ProposedStationaryPrimitives.primitives G
  have hCoord (i : Fin 33) :
      ContinuousAt (fun z : Row33 =>
        localPrefixCoordinatesVector fullyPinnedStationarySOURCEZ0 i *
          Real.exp (z i)) (0 : Row33) :=
    continuousAt_const.mul
      (Real.continuous_exp.continuousAt.comp
        ((continuous_apply i).continuousAt))
  have hK0 (i : FirmType) :
      ContinuousAt (fun z : Row33 =>
        (pinnedDateZero G z).currentCapital i) (0 : Row33) := by
    change ContinuousAt (fun _ : Row33 =>
      (ProposedStationaryInheritedState.inheritedState G).capital i)
      (0 : Row33)
    exact continuousAt_const
  have hK1 (i : FirmType) :
      ContinuousAt (fun z : Row33 =>
        (pinnedDateOne G z).currentCapital i) (0 : Row33) := by
    cases i
    · change ContinuousAt (fun z : Row33 =>
        localPrefixCoordinatesVector fullyPinnedStationarySOURCEZ0 0 *
          Real.exp (z 0)) (0 : Row33)
      exact hCoord 0
    · change ContinuousAt (fun z : Row33 =>
        localPrefixCoordinatesVector fullyPinnedStationarySOURCEZ0 1 *
          Real.exp (z 1)) (0 : Row33)
      exact hCoord 1
  have hA0 : ContinuousAt (fun z : Row33 =>
      (pinnedDateZero G z).currentAggregateProductivity)
      (0 : Row33) := by
    change ContinuousAt (fun _ : Row33 =>
      P.aggregateProductivity P.tree.initial) (0 : Row33)
    exact continuousAt_const
  have hA1 : ContinuousAt (fun z : Row33 =>
      (pinnedDateOne G z).currentAggregateProductivity)
      (0 : Row33) := by
    change ContinuousAt (fun _ : Row33 =>
      P.aggregateProductivity .dateOne) (0 : Row33)
    exact continuousAt_const
  have hPrice0 : ContinuousAt (fun z : Row33 =>
      (pinnedDateZero G z).controls.inputPrice) (0 : Row33) := by
    change ContinuousAt (fun z : Row33 =>
      localPrefixCoordinatesVector fullyPinnedStationarySOURCEZ0 11 *
        Real.exp (z 11)) (0 : Row33)
    exact hCoord 11
  have hPrice1 : ContinuousAt (fun z : Row33 =>
      (pinnedDateOne G z).controls.inputPrice) (0 : Row33) := by
    change ContinuousAt (fun z : Row33 =>
      localPrefixCoordinatesVector fullyPinnedStationarySOURCEZ0 27 *
        Real.exp (z 27)) (0 : Row33)
    exact hCoord 27
  have hWage0 : ContinuousAt (fun z : Row33 =>
      (pinnedDateZero G z).controls.wage) (0 : Row33) := by
    change ContinuousAt (fun z : Row33 =>
      localPrefixCoordinatesVector fullyPinnedStationarySOURCEZ0 10 *
        Real.exp (z 10)) (0 : Row33)
    exact hCoord 10
  have hWage1 : ContinuousAt (fun z : Row33 =>
      (pinnedDateOne G z).controls.wage) (0 : Row33) := by
    change ContinuousAt (fun z : Row33 =>
      localPrefixCoordinatesVector fullyPinnedStationarySOURCEZ0 26 *
        Real.exp (z 26)) (0 : Row33)
    exact hCoord 26
  have hWage0Ne :
      (pinnedDateZero G (0 : Row33)).controls.wage ≠ 0 := by
    change localPrefixCoordinatesVector fullyPinnedStationarySOURCEZ0 10 *
      Real.exp ((0 : Row33) 10) ≠ 0
    exact ne_of_gt (mul_pos
      (fullyPinnedStationarySOURCEZ0_positive 10) (Real.exp_pos _))
  have hWage1Ne :
      (pinnedDateOne G (0 : Row33)).controls.wage ≠ 0 := by
    change localPrefixCoordinatesVector fullyPinnedStationarySOURCEZ0 26 *
      Real.exp ((0 : Row33) 26) ≠ 0
    exact ne_of_gt (mul_pos
      (fullyPinnedStationarySOURCEZ0_positive 26) (Real.exp_pos _))
  have hAlpha : 0 ≤ P.alpha := by
    change (0 : ℝ) ≤ 2 / 5
    norm_num
  have hBeta : 0 ≤ P.beta := by
    change (0 : ℝ) ≤ 1 / 2
    norm_num
  have hLaborPower : 0 ≤ 1 / (1 - P.beta) := by
    change (0 : ℝ) ≤ 1 / (1 - 1 / 2)
    norm_num
  constructor
  · exact localPrefixAggregateOutput_continuousAt_of_atoms
      P (pinnedDateZero G) (0 : Row33)
      hK0 hA0 hPrice0 hWage0 hWage0Ne
      hAlpha hBeta hLaborPower
  · exact localPrefixAggregateOutput_continuousAt_of_atoms
      P (pinnedDateOne G) (0 : Row33)
      hK1 hA1 hPrice1 hWage1 hWage1Ne
      hAlpha hBeta hLaborPower

#print axioms pinned_two_actual_aggregate_outputs_continuousAt

end CurrentSourcePinnedAggregateOutputContinuity
end Ventura26LiquidityAllocation

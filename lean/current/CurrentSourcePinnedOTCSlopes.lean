import Ventura26LiquidityAllocation.CurrentPinnedBankDomain
import Ventura26LiquidityAllocation.CurrentSourceCrossContinuity

/-!
# Exact two-date SOURCE OTC slope continuity in the pinned log chart

The SOURCE frozen-formula OTC slopes chi_minus and chi_plus are
rational expressions in the corridor width, tightness theta, and
sqrt(2-theta). The denominator 1 + sqrt(2-theta) is strictly
positive for every real theta, using the genuine Lean real sqrt.

We first establish continuity under scalar data continuity and then
prove both hypotheses outright for the pinned SOURCE log coordinates:
  theta_0 = (1/2) exp z_16, theta_1 = (1/2) exp z_32;
  the corridor widths are path primitives fixed by P, independently
  of each of the 33 log deviations.

Thus all FOUR slope continuities are proved at the actual pinned root,
not treated as assumptions. This does not prove differentiability of
the 33 original residuals or sourceRateRuleTarget continuity.
-/

namespace Ventura26LiquidityAllocation
namespace CurrentSourcePinnedOTCSlopes

open CurrentPinnedBankDomain
open CurrentSourceCrossContinuity
open CurrentSourceFullFDeriv
open scoped Topology

/-- The actual two frozen SOURCE OTC slope formulas are continuous
when the source corridor width and tightness are continuous. No
condition theta<=1 is needed for continuity of these explicit
sqrt formulas, because 1+sqrt(2-theta)>0 for every theta in R. -/
theorem sourceFrozenPythonSlopes_continuousAt_of_data
    {X : Type*} [TopologicalSpace X]
    (d : X → LocalPrefixDateData) (x : X)
    (hWidth : ContinuousAt (fun y => (d y).corridorWidth) x)
    (hTheta : ContinuousAt (fun y => (d y).controls.tightness) x) :
    ContinuousAt (fun y => sourceFrozenPythonDeficitSlope (d y)) x ∧
    ContinuousAt (fun y => sourceFrozenPythonSurplusSlope (d y)) x := by
  have hShift : ContinuousAt
      (fun y => (2 : ℝ) - (d y).controls.tightness) x :=
    continuousAt_const.sub hTheta
  have hRoot : ContinuousAt
      (fun y => Real.sqrt (2 - (d y).controls.tightness)) x :=
    Real.continuous_sqrt.continuousAt.comp hShift
  have hDen : ContinuousAt
      (fun y => (1 : ℝ) +
        Real.sqrt (2 - (d y).controls.tightness)) x :=
    continuousAt_const.add hRoot
  have hDenNe :
      (1 : ℝ) +
        Real.sqrt (2 - (d x).controls.tightness) ≠ 0 := by
    have hNonneg := Real.sqrt_nonneg (2 - (d x).controls.tightness)
    linarith
  constructor
  · change ContinuousAt (fun y =>
      (d y).corridorWidth *
        (1 - (1 / 2 : ℝ) +
          (1 / 2 : ℝ) /
            (1 + Real.sqrt (2 - (d y).controls.tightness)))) x
    exact hWidth.mul
      ((continuousAt_const.sub continuousAt_const).add
        (continuousAt_const.div hDen hDenNe))
  · change ContinuousAt (fun y =>
      (d y).corridorWidth * (d y).controls.tightness * (1 / 2 : ℝ) /
        (1 + Real.sqrt (2 - (d y).controls.tightness))) x
    exact ((hWidth.mul hTheta).mul continuousAt_const).div hDen hDenNe

#print axioms sourceFrozenPythonSlopes_continuousAt_of_data

/-- Continuity of the two genuine pinned log-chart tightness
coordinates at the common stationary origin. -/
theorem pinned_two_tightness_coordinates_continuousAt (G : ℝ) :
    ContinuousAt
      (fun z : Row33 => (pinnedDateZero G z).controls.tightness)
        (0 : Row33) ∧
    ContinuousAt
      (fun z : Row33 => (pinnedDateOne G z).controls.tightness)
        (0 : Row33) := by
  have hcoord (i : Fin 33) :
      ContinuousAt (fun z : Row33 => (1 / 2 : ℝ) * Real.exp (z i))
        (0 : Row33) := by
    exact continuousAt_const.mul
      (Real.continuous_exp.continuousAt.comp
        ((continuous_apply i).continuousAt))
  constructor
  · change ContinuousAt
      (fun z : Row33 => (1 / 2 : ℝ) * Real.exp (z 16)) (0 : Row33)
    exact hcoord 16
  · change ContinuousAt
      (fun z : Row33 => (1 / 2 : ℝ) * Real.exp (z 32)) (0 : Row33)
    exact hcoord 32

#print axioms pinned_two_tightness_coordinates_continuousAt

/-- The pinned SOURCE corridor widths depend on the primitives
and dated history, not on the 33 log deviations, hence both
date-specific width functions are continuous at the origin. -/
theorem pinned_two_corridor_widths_continuousAt (G : ℝ) :
    ContinuousAt (fun z : Row33 => (pinnedDateZero G z).corridorWidth)
      (0 : Row33) ∧
    ContinuousAt (fun z : Row33 => (pinnedDateOne G z).corridorWidth)
      (0 : Row33) := by
  constructor
  · change ContinuousAt (fun _ : Row33 =>
      (ProposedStationaryPrimitives.primitives G).corridorWidthPath
        0 (bridgeDateZeroHistory (ProposedStationaryPrimitives.primitives G)))
      (0 : Row33)
    exact continuousAt_const
  · change ContinuousAt (fun _ : Row33 =>
      (ProposedStationaryPrimitives.primitives G).corridorWidthPath
        1 (bridgeDateOneHistory
          (ProposedStationaryPrimitives.primitives G) .dateOne))
      (0 : Row33)
    exact continuousAt_const

#print axioms pinned_two_corridor_widths_continuousAt

/-- Four ACTUAL SOURCE frozen-OTC slopes are continuous at the
same pinned economic root: deficit and surplus in dates 0 and 1.
The conclusion is unconditional for every government-bond G. -/
theorem pinned_four_frozen_OTC_slopes_continuousAt (G : ℝ) :
    ContinuousAt (fun z : Row33 =>
      sourceFrozenPythonDeficitSlope (pinnedDateZero G z)) (0 : Row33) ∧
    ContinuousAt (fun z : Row33 =>
      sourceFrozenPythonSurplusSlope (pinnedDateZero G z)) (0 : Row33) ∧
    ContinuousAt (fun z : Row33 =>
      sourceFrozenPythonDeficitSlope (pinnedDateOne G z)) (0 : Row33) ∧
    ContinuousAt (fun z : Row33 =>
      sourceFrozenPythonSurplusSlope (pinnedDateOne G z)) (0 : Row33) := by
  obtain ⟨hTheta0, hTheta1⟩ :=
    pinned_two_tightness_coordinates_continuousAt G
  obtain ⟨hWidth0, hWidth1⟩ :=
    pinned_two_corridor_widths_continuousAt G
  obtain ⟨hMinus0, hPlus0⟩ :=
    sourceFrozenPythonSlopes_continuousAt_of_data
      (pinnedDateZero G) (0 : Row33) hWidth0 hTheta0
  obtain ⟨hMinus1, hPlus1⟩ :=
    sourceFrozenPythonSlopes_continuousAt_of_data
      (pinnedDateOne G) (0 : Row33) hWidth1 hTheta1
  exact ⟨hMinus0, hPlus0, hMinus1, hPlus1⟩

#print axioms pinned_four_frozen_OTC_slopes_continuousAt

end CurrentSourcePinnedOTCSlopes
end Ventura26LiquidityAllocation

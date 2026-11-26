import Ventura26LiquidityAllocation.CurrentPinnedSourceDateParity
import Ventura26LiquidityAllocation.SourceAugmented34FundingDualObstructionCandidate
import Ventura26LiquidityAllocation.SourceFundingDualSigmaOneStationaryFrontierCandidate

/-!
# Exact SOURCE normalized L funding-dual obstruction at stationary baseline

The binding-branch stationary 33-row root and the 34-row SOURCE
switching-boundary problem are economically distinct. The latter
adds the normalized firm-L funding-dual ZERO equation. This module
proposes to prove its value at the pinned stationary reference is
strictly POSITIVE, using the exact stationary loan-rate inequality
R_L < 25/24 and the entrepreneurial discount factor 24/25.

Consequently NO innovation h changes the fact that the 34-row source
map is nonzero at the SAME fixed log coordinates z=0. The economic
coordinates themselves must change to reach an S/B boundary.
Nothing here prohibits a 34-root at some other z, nor is a global
equilibrium or an IRF constructed.
-/

namespace Ventura26LiquidityAllocation
namespace CurrentPinnedStationaryDual

open ProposedLocalScalarAugmented34Source

theorem pinned_stationary_funding_dual_pos (G : ℝ) :
    0 < localNormalizedCollateralDualL
      (ProposedStationaryPrimitives.primitives G)
      (localPrefixLogChart fullyPinnedStationarySOURCEZ0
        (0 : Fin 33 → ℝ)) := by
  let P := ProposedStationaryPrimitives.primitives G
  let Z := fullyPinnedStationarySOURCEZ0
  have hdiscount : P.entrepreneurRiskAversion = 1 := by rfl
  have hc_same :
      Z.controlsZero.consumptionL = Z.controlsOne.consumptionL := by rfl
  have hc_pos : 0 < Z.controlsZero.consumptionL := by
    change 0 < ProposedStationaryRealScale.firmConsumption .L
    exact ProposedStationaryRealScale.firmConsumption_pos .L
  have hpi : Z.controlsOne.inflation = 1 := by rfl
  have hsource :=
    sourceFundingDual_sigmaOne_stationary_fourLog
      P Z (0 : Fin 33 → ℝ) hdiscount hc_same hc_pos hpi
  have hvalue :
      localNormalizedCollateralDualL P
        (localPrefixLogChart Z (0 : Fin 33 → ℝ)) =
      1 / ProposedStationaryBank.loanRate - (24 / 25 : ℝ) := by
    calc
      _ = 1 / (Z.controlsZero.loanRate *
            Real.exp ((0 : Fin 33 → ℝ) 15)) -
          P.entrepreneurDiscount *
            Real.exp ((0 : Fin 33 → ℝ) 8) /
            (Real.exp ((0 : Fin 33 → ℝ) 24) *
              Real.exp ((0 : Fin 33 → ℝ) 28)) := hsource
      _ = 1 / ProposedStationaryBank.loanRate - (24 / 25 : ℝ) := by
        simp [Z, P, fullyPinnedStationarySOURCEZ0,
          ProposedStationaryRealScale.controls,
          ProposedStationaryPrimitives.primitives]
  have hloanUpper : ProposedStationaryBank.loanRate < 25 / 24 := by
    rcases ProposedStationaryBank.bank_margins_and_pricing with
      ⟨_, _, _, _, _, _, hu⟩
    exact hu
  have hloanPos : 0 < ProposedStationaryBank.loanRate :=
    ProposedStationaryRealScale.loanRate_pos
  have hpositive : 0 < 1 / ProposedStationaryBank.loanRate -
      (24 / 25 : ℝ) := by
    have hcomp : (24 / 25 : ℝ) < 1 / ProposedStationaryBank.loanRate := by
      apply (lt_div_iff₀ hloanPos).2
      nlinarith [hloanUpper]
    linarith
  rw [hvalue]
  exact hpositive

#print axioms pinned_stationary_funding_dual_pos

/-- At the fixed stationary SOURCE log coordinates z=0, the original
34-row boundary-zero map cannot vanish for ANY reserve remuneration
innovation h: its final firm-L funding dual remains positive. -/
theorem pinned_stationary_SOURCE34_not_boundary_root (G h : ℝ) :
    fullyPinnedStationaryP0SOURCE34 G (0 : Fin 33 → ℝ) h ≠
      (0, 0) := by
  change augmentedBoundaryZeroResidual
    (ProposedStationaryPrimitives.primitives G)
    (ProposedStationaryInheritedState.inheritedState G)
    fullyPinnedStationarySOURCEZ0
    .dateOne .recurrent
    (sourceLogLinearContinuation
      ProposedStationaryRealScale.stateSix
      ProposedStationaryRealScale.controls
      sourceFrozenP0TenControls)
    (0 : Fin 33 → ℝ) h ≠ (0, 0)
  exact augmentedBoundary_not_root_of_source_funding_dual_pos
    (ProposedStationaryPrimitives.primitives G)
    (ProposedStationaryInheritedState.inheritedState G)
    fullyPinnedStationarySOURCEZ0
    .dateOne .recurrent
    (sourceLogLinearContinuation
      ProposedStationaryRealScale.stateSix
      ProposedStationaryRealScale.controls
      sourceFrozenP0TenControls)
    (0 : Fin 33 → ℝ) h (pinned_stationary_funding_dual_pos G)

#print axioms pinned_stationary_SOURCE34_not_boundary_root

end CurrentPinnedStationaryDual
end Ventura26LiquidityAllocation

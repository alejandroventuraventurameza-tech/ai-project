import Ventura26LiquidityAllocation.CurrentPinnedMonetaryRoots
import Ventura26LiquidityAllocation.CurrentSourceCrossContinuity
import Ventura26LiquidityAllocation.CurrentSourceTwoDateFDerivTransport

/-!
# Pinned SOURCE: eight actual cross-coefficient continuities from original F

The four monetary donor residuals are EXACTLY zero at the pinned
two-date stationary SOURCE root (PR #52). The four genuine economic
cross coefficients per date are prefactor times the continuous
expSecant of a monetary donor (PR #49).

We prove conditional continuity of all EIGHT economic cross coefficients
at the same pinned SOURCE origin assuming:
  (1) Fréchet differentiability of the genuine SOURCE 33-log-row F there;
  (2) continuity of the eight PRE-SECANT economic prefactors there.

Condition (1) supplies continuity of all four original monetary rules;
their zeros come from the genuine source stationary system.
No derivative of any cross-coefficient is requested.

This module DOES NOT prove premises (1)-(2) for the concrete source
formulas. It is a precise reduction of those regularity obligations,
not a certified inverse Jacobian or an infinite-horizon equilibrium.
-/

namespace Ventura26LiquidityAllocation
namespace CurrentPinnedEightCrossContinuity

open CurrentSourceFullFDeriv
open CurrentSourceCrossContinuity
open CurrentPinnedBankDomain
open CurrentPinnedMonetaryRoots
open CurrentSourceTwoDateBank
open scoped Topology

/-- The original SOURCE 33-by-1 log-residual in the exact stationary
fiscal fiber and frozen P0 continuation. -/
noncomputable def pinnedOriginalF (G : ℝ) : Row33 → Row33 :=
  localReducedPrefixLogResidualVector .binding
    (ProposedStationaryPrimitives.primitives G)
    (ProposedStationaryInheritedState.inheritedState G)
    fullyPinnedStationarySOURCEZ0 .dateOne .recurrent
    (sourceLogLinearContinuation
      ProposedStationaryRealScale.stateSix
      ProposedStationaryRealScale.controls
      sourceFrozenP0TenControls)

/-- Continuity of the four genuine SOURCE pre-secant economic
multipliers at one of the two original economic dates. -/
def FourPreSecantContinuousAt (G : ℝ)
    (d : Row33 → LocalPrefixDateData) : Prop :=
  ContinuousAt
      (fun z => sourceLoanPreSecant
        (ProposedStationaryPrimitives.primitives G) (d z))
      (0 : Row33) ∧
    ContinuousAt
      (fun z => sourceDepositPreSecant
        (ProposedStationaryPrimitives.primitives G) (d z))
      (0 : Row33) ∧
    ContinuousAt
      (fun z => sourceBalanceRatePreSecant
        (ProposedStationaryPrimitives.primitives G) (d z))
      (0 : Row33) ∧
    ContinuousAt
      (fun z => sourceBalanceQuantityPreSecant
        (ProposedStationaryPrimitives.primitives G) (d z))
      (0 : Row33)

/-- Continuity of the four ACTUAL SOURCE banking-row cross
coefficients in the same date and log chart. -/
def FourCrossContinuousAt (G : ℝ)
    (d : Row33 → LocalPrefixDateData) : Prop :=
  ContinuousAt
      (fun z => sourceLoanCross
        (ProposedStationaryPrimitives.primitives G) (d z))
      (0 : Row33) ∧
    ContinuousAt
      (fun z => sourceDepositCross
        (ProposedStationaryPrimitives.primitives G) (d z))
      (0 : Row33) ∧
    ContinuousAt
      (fun z => sourceBalanceRateCross
        (ProposedStationaryPrimitives.primitives G) (d z))
      (0 : Row33) ∧
    ContinuousAt
      (fun z => sourceBalanceQuantityCross
        (ProposedStationaryPrimitives.primitives G) (d z))
      (0 : Row33)

/-- Genuine SOURCE rate and quantity rows at both economic dates
are continuous whenever the original 33-row F has a Fréchet
derivative at the pinned origin. No SOURCE-to-Python identification. -/
theorem pinned_four_policy_donors_continuousAt_of_F_hasFDerivAt
    (G : ℝ) (J : Row33 →L[ℝ] Row33)
    (hF : HasFDerivAt (pinnedOriginalF G) J (0 : Row33)) :
    ContinuousAt
      (fun z : Row33 => localReducedRemainingResidual
        (ProposedStationaryPrimitives.primitives G)
        (pinnedDateZero G z) 6) (0 : Row33) ∧
    ContinuousAt
      (fun z : Row33 => localReducedRemainingResidual
        (ProposedStationaryPrimitives.primitives G)
        (pinnedDateZero G z) 7) (0 : Row33) ∧
    ContinuousAt
      (fun z : Row33 => localReducedRemainingResidual
        (ProposedStationaryPrimitives.primitives G)
        (pinnedDateOne G z) 6) (0 : Row33) ∧
    ContinuousAt
      (fun z : Row33 => localReducedRemainingResidual
        (ProposedStationaryPrimitives.primitives G)
        (pinnedDateOne G z) 7) (0 : Row33) := by
  have hcoord (i : Fin 33) :
      ContinuousAt (fun z : Row33 => pinnedOriginalF G z i)
        (0 : Row33) :=
    (rowCoord i).continuousAt.comp hF.continuousAt
  have h0r : ContinuousAt
      (fun z : Row33 => localReducedRemainingResidual
        (ProposedStationaryPrimitives.primitives G)
        (pinnedDateZero G z) 6) (0 : Row33) := by
    change ContinuousAt (fun z : Row33 => pinnedOriginalF G z 12)
      (0 : Row33)
    exact hcoord 12
  have h0q : ContinuousAt
      (fun z : Row33 => localReducedRemainingResidual
        (ProposedStationaryPrimitives.primitives G)
        (pinnedDateZero G z) 7) (0 : Row33) := by
    change ContinuousAt (fun z : Row33 => pinnedOriginalF G z 13)
      (0 : Row33)
    exact hcoord 13
  have h1r : ContinuousAt
      (fun z : Row33 => localReducedRemainingResidual
        (ProposedStationaryPrimitives.primitives G)
        (pinnedDateOne G z) 6) (0 : Row33) := by
    change ContinuousAt (fun z : Row33 => pinnedOriginalF G z 28)
      (0 : Row33)
    exact hcoord 28
  have h1q : ContinuousAt
      (fun z : Row33 => localReducedRemainingResidual
        (ProposedStationaryPrimitives.primitives G)
        (pinnedDateOne G z) 7) (0 : Row33) := by
    change ContinuousAt (fun z : Row33 => pinnedOriginalF G z 29)
      (0 : Row33)
    exact hcoord 29
  exact ⟨h0r, h0q, h1r, h1q⟩

#print axioms pinned_four_policy_donors_continuousAt_of_F_hasFDerivAt

/-- Combining genuine monetary-root zeros (unconditional) with the
conditional policy continuity and economic pre-secant factors gives
all EIGHT real banking cross coefficients continuous at the common
pinned SOURCE root. -/
theorem pinned_eight_cross_continuousAt_of_prefactors_and_F
    (G : ℝ) (J : Row33 →L[ℝ] Row33)
    (hF : HasFDerivAt (pinnedOriginalF G) J (0 : Row33))
    (hp0 : FourPreSecantContinuousAt G (pinnedDateZero G))
    (hp1 : FourPreSecantContinuousAt G (pinnedDateOne G)) :
    FourCrossContinuousAt G (pinnedDateZero G) ∧
      FourCrossContinuousAt G (pinnedDateOne G) := by
  obtain ⟨h0r, h0q, h1r, h1q⟩ :=
    pinned_four_policy_donors_continuousAt_of_F_hasFDerivAt
      G J hF
  obtain ⟨hz0r, hz0q, hz1r, hz1q⟩ :=
    pinned_four_monetary_donor_rows_zero G
  rcases hp0 with ⟨h0loan, h0deposit, h0rate, h0quantity⟩
  rcases hp1 with ⟨h1loan, h1deposit, h1rate, h1quantity⟩
  exact ⟨
    sourceFourCross_continuousAt_of_prefactors
      (ProposedStationaryPrimitives.primitives G)
      (pinnedDateZero G) (0 : Row33)
      h0loan h0deposit h0rate h0quantity h0r h0q hz0r hz0q,
    sourceFourCross_continuousAt_of_prefactors
      (ProposedStationaryPrimitives.primitives G)
      (pinnedDateOne G) (0 : Row33)
      h1loan h1deposit h1rate h1quantity h1r h1q hz1r hz1q⟩

#print axioms pinned_eight_cross_continuousAt_of_prefactors_and_F

end CurrentPinnedEightCrossContinuity
end Ventura26LiquidityAllocation

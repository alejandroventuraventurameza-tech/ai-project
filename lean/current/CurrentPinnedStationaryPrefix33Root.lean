import Ventura26LiquidityAllocation.CurrentPinnedSourceDateParity

/-!
# Candidate exact binding-branch root of the genuine SOURCE 33-row
# stationary two-date finite prefix at ZERO log displacement.

This attempts to combine:
- kernel-checked stationary reduced one-date equations,
- actual date-zero/date-one SOURCE parity at the pinned reference,
- the exact source common-pledge date-one equation.

If the proof elaborates and #print axioms is clean, it proves a
FINITE-PREFIX 33-ROW ROOT for the binding branch at zero policy shock.
It does NOT prove the 34-row nonzero-intervention dual-zero system,
source Jacobian invertibility, slack branch S, a full dynamic allocation,
global optimality/KKT sufficiency or transversality.
-/

namespace Ventura26LiquidityAllocation
namespace CurrentPinnedStationaryRoot

open CurrentPinnedDateParity

/-- The remaining date-one common pledge equation matches the
stationary liquidation value exactly: (1 - 1/40)*1*(81/80). -/
theorem pinned_stationary_common_pledge_zero (G : ℝ) :
    fullyPinnedStationarySOURCEZ0.stateTwo.commonPledgeValue -
      (1 - (ProposedStationaryPrimitives.primitives G).depreciation) *
        ProposedStationaryRealScale.controls.inflation *
        ProposedStationaryRealScale.controls.capitalPrice = 0 := by
  change ProposedStationaryRealScale.liquidationValue -
    (1 - (1 / 40 : ℝ)) * 1 *
      ProposedStationaryRealScale.capitalPrice = 0
  unfold ProposedStationaryRealScale.liquidationValue
  ring

#print axioms pinned_stationary_common_pledge_zero

/-- The genuinely pinned stationary SOURCE binding residual vanishes
exactly in all 33 rows, provided the separate source date-data parity
results and the one-date stationary system are applied to the same G.
No Python floating-point residual is used. -/
theorem pinned_stationary_binding_prefix33_root (G : ℝ) :
    localReducedPrefixLogResidualVector .binding
      (ProposedStationaryPrimitives.primitives G)
      (ProposedStationaryInheritedState.inheritedState G)
      fullyPinnedStationarySOURCEZ0 .dateOne .recurrent
      (sourceLogLinearContinuation
        ProposedStationaryRealScale.stateSix
        ProposedStationaryRealScale.controls
        sourceFrozenP0TenControls)
      (0 : Fin 33 → ℝ) = 0 := by
  let P := ProposedStationaryPrimitives.primitives G
  let I := ProposedStationaryInheritedState.inheritedState G
  let Z := fullyPinnedStationarySOURCEZ0
  let tail :=
    sourceLogLinearContinuation
      ProposedStationaryRealScale.stateSix
      ProposedStationaryRealScale.controls
      sourceFrozenP0TenControls
  have hdata0 :
      localPrefixDateZeroData P I Z .dateOne =
      ProposedStationaryRealScale.dateData :=
    sourcePinnedDateZero_eq_stationary G
  have hdata1 :
      localPrefixDateOneData P Z .dateOne .recurrent tail =
      ProposedStationaryRealScale.dateData :=
    sourcePinnedDateOne_eq_stationary G
  have hremaining :
      ∀ row : Fin 11,
        localReducedRemainingResidual P
          ProposedStationaryRealScale.dateData row = 0 :=
    (ProposedStationaryPrimitives.concrete_reduced_system G).1
  have hfirm :
      ∀ i : FirmType,
        localReducedFirmBudgetResidual P
            ProposedStationaryRealScale.dateData i = 0 ∧
        localReducedFirmCapitalEulerResidual .binding P
            ProposedStationaryRealScale.dateData i = 0 ∧
        localReducedFirmRegimeResidual .binding P
            ProposedStationaryRealScale.dateData i = 0 :=
    (ProposedStationaryPrimitives.concrete_reduced_system G).2
  have hH := hfirm .H
  have hL := hfirm .L
  have hpledge :
      Z.stateTwo.commonPledgeValue -
        (1 - P.depreciation) *
        ProposedStationaryRealScale.controls.inflation *
        ProposedStationaryRealScale.controls.capitalPrice = 0 :=
    pinned_stationary_common_pledge_zero G
  have hrow (eq : LocalPrefixEquation) :
      localReducedPrefixResidual .binding P I Z
        .dateOne .recurrent tail eq = 0 := by
    cases eq <;>
      simp [localReducedPrefixResidual, hdata0, hdata1,
        hremaining, hH.1, hH.2.1, hH.2.2,
        hL.1, hL.2.1, hL.2.2, hpledge]
  funext i
  change localReducedPrefixResidual .binding P I
    (localPrefixLogChart Z (0 : Fin 33 → ℝ))
    .dateOne .recurrent tail (localPrefixEquationOfIndex i) = 0
  rw [sourcePinnedLogChart_zero]
  exact hrow (localPrefixEquationOfIndex i)

#print axioms pinned_stationary_binding_prefix33_root

end CurrentPinnedStationaryRoot
end Ventura26LiquidityAllocation

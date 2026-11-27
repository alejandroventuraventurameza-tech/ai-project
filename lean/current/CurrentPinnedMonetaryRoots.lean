import Ventura26LiquidityAllocation.CurrentPinnedFiscalFiberWitness
import Ventura26LiquidityAllocation.CurrentPinnedBankDomain

/-!
# All four genuine SOURCE monetary donor rows vanish at the pinned origin

The true two-date SOURCE reduced prefix has monetary rate/quantity
donor rows 12/13 (date zero) and 28/29 (date one).
These are the donor equations for the six bank-row shears.

This module recovers both actual SOURCE date-data objects at the
pinned logarithmic origin and applies the stationary reduced-system
identity to show the exact corresponding rate/quantity residuals
vanish for any stationary fiscal parameter G, hence in particular
the admissible fiscal witness G*=2*Mpre.

No numerical rounding, Python row permutation or independent
assumption of a policy-root zero is used. This is a finite-prefix
stationary result, not differentiability or an infinite equilibrium.
-/

namespace Ventura26LiquidityAllocation
namespace CurrentPinnedMonetaryRoots

open CurrentPinnedBankDomain
open CurrentPinnedDateParity
open CurrentPinnedFiscalFiber
open CurrentSourceFullFDeriv

/-- The actual SOURCE date-zero bank-data structure at the origin
is literally the kernel-verified stationary economic date witness. -/
theorem pinned_actual_dateZero_eq_stationary (G : ℝ) :
    pinnedDateZero G (0 : Row33) =
      ProposedStationaryRealScale.dateData := by
  change localPrefixDateZeroData
    (ProposedStationaryPrimitives.primitives G)
    (ProposedStationaryInheritedState.inheritedState G)
    (localPrefixLogChart
      fullyPinnedStationarySOURCEZ0 (0 : Fin 33 → ℝ))
    .dateOne = ProposedStationaryRealScale.dateData
  rw [sourcePinnedLogChart_zero]
  exact sourcePinnedDateZero_eq_stationary G

#print axioms pinned_actual_dateZero_eq_stationary

/-- The same holds at date one with the IDENTICAL frozen P0
continuation and common pledge of the SOURCE stationary root. -/
theorem pinned_actual_dateOne_eq_stationary (G : ℝ) :
    pinnedDateOne G (0 : Row33) =
      ProposedStationaryRealScale.dateData := by
  change localPrefixDateOneData
    (ProposedStationaryPrimitives.primitives G)
    (localPrefixLogChart
      fullyPinnedStationarySOURCEZ0 (0 : Fin 33 → ℝ))
    .dateOne .recurrent
    (sourceLogLinearContinuation
      ProposedStationaryRealScale.stateSix
      ProposedStationaryRealScale.controls
      sourceFrozenP0TenControls) =
      ProposedStationaryRealScale.dateData
  rw [sourcePinnedLogChart_zero]
  exact sourcePinnedDateOne_eq_stationary G

#print axioms pinned_actual_dateOne_eq_stationary

/-- Genuine date-zero RATE and QUANTITY, date-one RATE and QUANTITY
SOURCE monetary residuals vanish, not merely auxiliary policy rows. -/
theorem pinned_four_monetary_donor_rows_zero (G : ℝ) :
    localReducedRemainingResidual
      (ProposedStationaryPrimitives.primitives G)
      (pinnedDateZero G (0 : Row33)) 6 = 0 ∧
    localReducedRemainingResidual
      (ProposedStationaryPrimitives.primitives G)
      (pinnedDateZero G (0 : Row33)) 7 = 0 ∧
    localReducedRemainingResidual
      (ProposedStationaryPrimitives.primitives G)
      (pinnedDateOne G (0 : Row33)) 6 = 0 ∧
    localReducedRemainingResidual
      (ProposedStationaryPrimitives.primitives G)
      (pinnedDateOne G (0 : Row33)) 7 = 0 := by
  have hremaining :
      ∀ i : Fin 11,
        localReducedRemainingResidual
          (ProposedStationaryPrimitives.primitives G)
          ProposedStationaryRealScale.dateData i = 0 :=
    (ProposedStationaryPrimitives.concrete_reduced_system G).1
  rw [pinned_actual_dateZero_eq_stationary,
    pinned_actual_dateOne_eq_stationary]
  exact ⟨hremaining 6, hremaining 7, hremaining 6, hremaining 7⟩

#print axioms pinned_four_monetary_donor_rows_zero

/-- Specialization to the same fiscally admissible witness G*
employed by the exact 33-row binding SOURCE root. -/
theorem pinned_fiscal_witness_four_monetary_donor_rows_zero :
    localReducedRemainingResidual
      (ProposedStationaryPrimitives.primitives pinnedFiscalG)
      (pinnedDateZero pinnedFiscalG (0 : Row33)) 6 = 0 ∧
    localReducedRemainingResidual
      (ProposedStationaryPrimitives.primitives pinnedFiscalG)
      (pinnedDateZero pinnedFiscalG (0 : Row33)) 7 = 0 ∧
    localReducedRemainingResidual
      (ProposedStationaryPrimitives.primitives pinnedFiscalG)
      (pinnedDateOne pinnedFiscalG (0 : Row33)) 6 = 0 ∧
    localReducedRemainingResidual
      (ProposedStationaryPrimitives.primitives pinnedFiscalG)
      (pinnedDateOne pinnedFiscalG (0 : Row33)) 7 = 0 :=
  pinned_four_monetary_donor_rows_zero pinnedFiscalG

#print axioms pinned_fiscal_witness_four_monetary_donor_rows_zero

end CurrentPinnedMonetaryRoots
end Ventura26LiquidityAllocation

import Ventura26LiquidityAllocation.CurrentPinnedLogCoordinateFrechet
import Ventura26LiquidityAllocation.CurrentPinnedMonetaryRoots

/-!
# Original SOURCE monetary QUANTITY rows: exact off-root formulas and Frechet derivatives

For the exact binding stationary SOURCE 33-log chart and its genuine
two-date economic data, the monetary quantity residual is
  log(M_t) - rho_M * log(M_{t-1}) -
    (1-rho_M) * log(Mbar) - innovation_t.

The dated quantity innovations are stationary primitive inputs,
independent of all 33 log deviations. Date zero's lag is inherited;
date one's lag is the true date-zero reserve quantity (index 6).

By using the exact stationary root and the globally affine log
coordinates certified in CurrentPinnedLogCoordinateFrechet, we
obtain exact OFF-ROOT residual equalities:
  F_13(z) = z_6
  F_29(z) = z_22 - (1/2) * z_6
where the SOURCE equation indices and state indices are zero based.

These are source-defined genuine economic equations, not Python
finite-IRF surrogate rows. This module makes no claim about other
31 SOURCE rows, C1 of the whole F, inverse Jacobian, or equilibrium.
-/

namespace Ventura26LiquidityAllocation
namespace CurrentPinnedQuantityRuleRowFrechet

open CurrentSourceFullFDeriv
open CurrentPinnedBankDomain
open CurrentPinnedMonetaryRoots
open CurrentPinnedLogCoordinateFrechet
open scoped Topology

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Generic exact cancellation in the original reserve QUANTITY
equation: a known stationary zero eliminates all constant terms.
Only the realized log-coordinate shift and the lag shift remain. -/
theorem source_quantity_row_affine_of_log_inputs
    (P : Primitives S) (d : Row33 → LocalPrefixDateData)
    (currentBase lagBase innovation : ℝ)
    (currentShift lagShift : Row33 → ℝ)
    (hCurrent : ∀ z : Row33,
      Real.log (d z).currentReservesPre = currentBase + currentShift z)
    (hLag : ∀ z : Row33,
      Real.log (d z).lagReservesPre = lagBase + lagShift z)
    (hInnovation : ∀ z : Row33,
      (d z).reserveQuantityInnovation = innovation)
    (hCurrentZero : currentShift (0 : Row33) = 0)
    (hLagZero : lagShift (0 : Row33) = 0)
    (hRoot : localReducedRemainingResidual P (d (0 : Row33)) 7 = 0)
    (z : Row33) :
    localReducedRemainingResidual P (d z) 7 =
      currentShift z - P.reserveQuantityPersistence * lagShift z := by
  have hForm (u : Row33) :
      localReducedRemainingResidual P (d u) 7 =
        currentBase + currentShift u -
          (P.reserveQuantityPersistence * (lagBase + lagShift u) +
            (1 - P.reserveQuantityPersistence) *
              Real.log P.reserveQuantitySteady + innovation) := by
    change Real.log (d u).currentReservesPre -
      (P.reserveQuantityPersistence * Real.log (d u).lagReservesPre +
        (1 - P.reserveQuantityPersistence) *
          Real.log P.reserveQuantitySteady +
        (d u).reserveQuantityInnovation) = _
    rw [hCurrent u, hLag u, hInnovation u]
  have hBase :
      currentBase -
        (P.reserveQuantityPersistence * lagBase +
          (1 - P.reserveQuantityPersistence) *
            Real.log P.reserveQuantitySteady + innovation) = 0 := by
    have h := hRoot
    rw [hForm (0 : Row33)] at h
    rw [hCurrentZero, hLagZero] at h
    simpa only [add_zero] using h
  rw [hForm z]
  calc
    _ = (currentBase -
          (P.reserveQuantityPersistence * lagBase +
            (1 - P.reserveQuantityPersistence) *
              Real.log P.reserveQuantitySteady + innovation)) +
            (currentShift z -
              P.reserveQuantityPersistence * lagShift z) := by ring
    _ = currentShift z -
          P.reserveQuantityPersistence * lagShift z := by rw [hBase]; ring

#print axioms source_quantity_row_affine_of_log_inputs

/-- Exact ORIGINAL SOURCE date-zero reserve-quantity residual,
for every 33-log displacement: only its own coordinate 6 enters. -/
theorem pinned_quantity_row_dateZero_eq_coordinate
    (G : ℝ) (z : Row33) :
    localReducedRemainingResidual
      (ProposedStationaryPrimitives.primitives G)
      (pinnedDateZero G z) 7 = z 6 := by
  let P := ProposedStationaryPrimitives.primitives G
  let d := pinnedDateZero G
  let c := localPrefixCoordinatesVector fullyPinnedStationarySOURCEZ0 6
  have hCurrent (u : Row33) :
      Real.log (d u).currentReservesPre = Real.log c + u 6 := by
    change Real.log (c * Real.exp (u 6)) = Real.log c + u 6
    exact pinned_log_level_eq_affine 6 u
  have hLag (u : Row33) :
      Real.log (d u).lagReservesPre =
        Real.log (d (0 : Row33)).lagReservesPre + (0 : ℝ) := by
    change Real.log
      (ProposedStationaryInheritedState.inheritedState G).reservesPreLag =
        Real.log
          (ProposedStationaryInheritedState.inheritedState G).reservesPreLag + 0
    ring
  have hInnovation (u : Row33) :
      (d u).reserveQuantityInnovation =
        (d (0 : Row33)).reserveQuantityInnovation := by
    rfl
  have hRoot : localReducedRemainingResidual
      P (d (0 : Row33)) 7 = 0 := by
    exact (pinned_four_monetary_donor_rows_zero G).2.1
  have hResult :=
    source_quantity_row_affine_of_log_inputs
      P d (Real.log c)
      (Real.log (d (0 : Row33)).lagReservesPre)
      ((d (0 : Row33)).reserveQuantityInnovation)
      (fun u : Row33 => u 6) (fun _ : Row33 => (0 : ℝ))
      hCurrent hLag hInnovation
      (by simp) (by simp) hRoot z
  simpa using hResult

#print axioms pinned_quantity_row_dateZero_eq_coordinate

/-- Exact ORIGINAL SOURCE date-one reserve-quantity residual:
realized reserves are coordinate 22 and inherited lag reserves are
date-zero coordinate 6, with exact persistence rho_M = 1/2. -/
theorem pinned_quantity_row_dateOne_eq_affine
    (G : ℝ) (z : Row33) :
    localReducedRemainingResidual
      (ProposedStationaryPrimitives.primitives G)
      (pinnedDateOne G z) 7 =
        z 22 - (1 / 2 : ℝ) * z 6 := by
  let P := ProposedStationaryPrimitives.primitives G
  let d := pinnedDateOne G
  let cNow := localPrefixCoordinatesVector fullyPinnedStationarySOURCEZ0 22
  let cLag := localPrefixCoordinatesVector fullyPinnedStationarySOURCEZ0 6
  have hCurrent (u : Row33) :
      Real.log (d u).currentReservesPre = Real.log cNow + u 22 := by
    change Real.log (cNow * Real.exp (u 22)) = Real.log cNow + u 22
    exact pinned_log_level_eq_affine 22 u
  have hLag (u : Row33) :
      Real.log (d u).lagReservesPre = Real.log cLag + u 6 := by
    change Real.log (cLag * Real.exp (u 6)) = Real.log cLag + u 6
    exact pinned_log_level_eq_affine 6 u
  have hInnovation (u : Row33) :
      (d u).reserveQuantityInnovation =
        (d (0 : Row33)).reserveQuantityInnovation := by
    rfl
  have hRoot : localReducedRemainingResidual
      P (d (0 : Row33)) 7 = 0 := by
    exact (pinned_four_monetary_donor_rows_zero G).2.2.2
  have hResult :=
    source_quantity_row_affine_of_log_inputs
      P d (Real.log cNow) (Real.log cLag)
      ((d (0 : Row33)).reserveQuantityInnovation)
      (fun u : Row33 => u 22) (fun u : Row33 => u 6)
      hCurrent hLag hInnovation
      (by simp) (by simp) hRoot z
  change localReducedRemainingResidual
      (ProposedStationaryPrimitives.primitives G)
      (pinnedDateOne G z) 7 =
      z 22 - (1 / 2 : ℝ) * z 6 at hResult
  exact hResult

#print axioms pinned_quantity_row_dateOne_eq_affine

/-- Exact row derivatives in the original 33-equation SOURCE map.
No finite difference, no auxiliary Python equation, and no
full-Jacobian differentiability assumption. -/
theorem pinned_two_monetary_quantity_rows_hasFDerivAt (G : ℝ) :
    HasFDerivAt
      (fun z : Row33 => localReducedRemainingResidual
        (ProposedStationaryPrimitives.primitives G)
        (pinnedDateZero G z) 7)
      (rowCoord 6) (0 : Row33) ∧
    HasFDerivAt
      (fun z : Row33 => localReducedRemainingResidual
        (ProposedStationaryPrimitives.primitives G)
        (pinnedDateOne G z) 7)
      (rowCoord 22 - (1 / 2 : ℝ) • rowCoord 6) (0 : Row33) := by
  have hZero :
      (fun z : Row33 => localReducedRemainingResidual
        (ProposedStationaryPrimitives.primitives G)
        (pinnedDateZero G z) 7) =
      (fun z : Row33 => (rowCoord 6) z) := by
    funext z
    change localReducedRemainingResidual
      (ProposedStationaryPrimitives.primitives G)
      (pinnedDateZero G z) 7 = z 6
    exact pinned_quantity_row_dateZero_eq_coordinate G z
  have hOne :
      (fun z : Row33 => localReducedRemainingResidual
        (ProposedStationaryPrimitives.primitives G)
        (pinnedDateOne G z) 7) =
      (fun z : Row33 =>
        (rowCoord 22 - (1 / 2 : ℝ) • rowCoord 6) z) := by
    funext z
    change localReducedRemainingResidual
      (ProposedStationaryPrimitives.primitives G)
      (pinnedDateOne G z) 7 = z 22 - (1 / 2 : ℝ) * z 6
    exact pinned_quantity_row_dateOne_eq_affine G z
  constructor
  · rw [hZero]
    exact (rowCoord 6).hasFDerivAt
  · rw [hOne]
    exact (rowCoord 22 - (1 / 2 : ℝ) • rowCoord 6).hasFDerivAt

#print axioms pinned_two_monetary_quantity_rows_hasFDerivAt

end CurrentPinnedQuantityRuleRowFrechet
end Ventura26LiquidityAllocation

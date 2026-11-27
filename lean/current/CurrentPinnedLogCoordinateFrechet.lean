import Ventura26LiquidityAllocation.CurrentPinnedBankDomain
import Ventura26LiquidityAllocation.CurrentSourceTwoDateFDerivTransport

/-!
# Actual SOURCE log chart: exact affine identities and Frechet derivatives

SOURCE uses c_i * exp(z_i) for stationary positive c_i. Thus
log(c_i * exp z_i) = log(c_i) + z_i and
log((c_i * exp z_i)/c_i) = z_i, exactly off root.
Their Frechet derivatives are the continuous projections rowCoord i.

Applied to both genuine SOURCE dates' realized reserve rates and
quantities: indices 5, 6, 21, 22 (Fin 33, zero-based).
No claims about target-rate derivatives, full F or J inverse.
-/

namespace Ventura26LiquidityAllocation
namespace CurrentPinnedLogCoordinateFrechet

open CurrentSourceFullFDeriv
open CurrentPinnedBankDomain
open scoped Topology

theorem pinned_log_level_eq_affine (i : Fin 33) (z : Row33) :
    Real.log
      (localPrefixCoordinatesVector fullyPinnedStationarySOURCEZ0 i *
        Real.exp (z i)) =
      Real.log (localPrefixCoordinatesVector fullyPinnedStationarySOURCEZ0 i) +
        z i := by
  rw [Real.log_mul
      (ne_of_gt (fullyPinnedStationarySOURCEZ0_positive i))
      (ne_of_gt (Real.exp_pos _)), Real.log_exp]

#print axioms pinned_log_level_eq_affine

theorem pinned_log_ratio_eq_coordinate (i : Fin 33) (z : Row33) :
    Real.log
      ((localPrefixCoordinatesVector fullyPinnedStationarySOURCEZ0 i *
        Real.exp (z i)) /
        localPrefixCoordinatesVector fullyPinnedStationarySOURCEZ0 i) =
      z i := by
  have hc :
      localPrefixCoordinatesVector fullyPinnedStationarySOURCEZ0 i ≠ 0 :=
    ne_of_gt (fullyPinnedStationarySOURCEZ0_positive i)
  have hNum :
      localPrefixCoordinatesVector fullyPinnedStationarySOURCEZ0 i *
        Real.exp (z i) ≠ 0 :=
    mul_ne_zero hc (ne_of_gt (Real.exp_pos _))
  rw [Real.log_div hNum hc, pinned_log_level_eq_affine]
  ring

#print axioms pinned_log_ratio_eq_coordinate

theorem pinned_log_level_hasFDerivAt (i : Fin 33) (x : Row33) :
    HasFDerivAt
      (fun z : Row33 =>
        Real.log
          (localPrefixCoordinatesVector fullyPinnedStationarySOURCEZ0 i *
            Real.exp (z i)))
      (rowCoord i) x := by
  let c := localPrefixCoordinatesVector fullyPinnedStationarySOURCEZ0 i
  have hAffine :
      HasFDerivAt
        (fun z : Row33 => Real.log c + (rowCoord i) z)
        (rowCoord i) x := by
    simpa only [zero_add, Pi.add_apply] using
      (hasFDerivAt_const (Real.log c) x).add
        ((rowCoord i).hasFDerivAt)
  have hEq :
      (fun z : Row33 => Real.log (c * Real.exp (z i))) =
        (fun z : Row33 => Real.log c + (rowCoord i) z) := by
    funext z
    change Real.log
      (localPrefixCoordinatesVector fullyPinnedStationarySOURCEZ0 i *
        Real.exp (z i)) =
      Real.log (localPrefixCoordinatesVector fullyPinnedStationarySOURCEZ0 i) +
        z i
    exact pinned_log_level_eq_affine i z
  change HasFDerivAt (fun z : Row33 => Real.log (c * Real.exp (z i)))
    (rowCoord i) x
  rw [hEq]
  exact hAffine

#print axioms pinned_log_level_hasFDerivAt

theorem pinned_log_ratio_hasFDerivAt (i : Fin 33) (x : Row33) :
    HasFDerivAt
      (fun z : Row33 =>
        Real.log
          ((localPrefixCoordinatesVector fullyPinnedStationarySOURCEZ0 i *
            Real.exp (z i)) /
            localPrefixCoordinatesVector fullyPinnedStationarySOURCEZ0 i))
      (rowCoord i) x := by
  have hEq :
      (fun z : Row33 =>
        Real.log
          ((localPrefixCoordinatesVector fullyPinnedStationarySOURCEZ0 i *
            Real.exp (z i)) /
            localPrefixCoordinatesVector fullyPinnedStationarySOURCEZ0 i)) =
      (fun z : Row33 => (rowCoord i) z) := by
    funext z
    change Real.log
      ((localPrefixCoordinatesVector fullyPinnedStationarySOURCEZ0 i *
        Real.exp (z i)) /
          localPrefixCoordinatesVector fullyPinnedStationarySOURCEZ0 i) = z i
    exact pinned_log_ratio_eq_coordinate i z
  rw [hEq]
  exact (rowCoord i).hasFDerivAt

#print axioms pinned_log_ratio_hasFDerivAt

theorem pinned_four_realized_monetary_log_hasFDerivAt (G : ℝ) :
    (HasFDerivAt
      (fun z : Row33 => Real.log (pinnedDateZero G z).currentReserveRate)
      (rowCoord 5) (0 : Row33) ∧
     HasFDerivAt
      (fun z : Row33 => Real.log (pinnedDateZero G z).currentReservesPre)
      (rowCoord 6) (0 : Row33)) ∧
    (HasFDerivAt
      (fun z : Row33 => Real.log (pinnedDateOne G z).currentReserveRate)
      (rowCoord 21) (0 : Row33) ∧
     HasFDerivAt
      (fun z : Row33 => Real.log (pinnedDateOne G z).currentReservesPre)
      (rowCoord 22) (0 : Row33)) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · change HasFDerivAt
      (fun z : Row33 => Real.log
        (localPrefixCoordinatesVector fullyPinnedStationarySOURCEZ0 5 *
          Real.exp (z 5))) (rowCoord 5) (0 : Row33)
    exact pinned_log_level_hasFDerivAt 5 0
  · change HasFDerivAt
      (fun z : Row33 => Real.log
        (localPrefixCoordinatesVector fullyPinnedStationarySOURCEZ0 6 *
          Real.exp (z 6))) (rowCoord 6) (0 : Row33)
    exact pinned_log_level_hasFDerivAt 6 0
  · change HasFDerivAt
      (fun z : Row33 => Real.log
        (localPrefixCoordinatesVector fullyPinnedStationarySOURCEZ0 21 *
          Real.exp (z 21))) (rowCoord 21) (0 : Row33)
    exact pinned_log_level_hasFDerivAt 21 0
  · change HasFDerivAt
      (fun z : Row33 => Real.log
        (localPrefixCoordinatesVector fullyPinnedStationarySOURCEZ0 22 *
          Real.exp (z 22))) (rowCoord 22) (0 : Row33)
    exact pinned_log_level_hasFDerivAt 22 0

#print axioms pinned_four_realized_monetary_log_hasFDerivAt

end CurrentPinnedLogCoordinateFrechet
end Ventura26LiquidityAllocation
